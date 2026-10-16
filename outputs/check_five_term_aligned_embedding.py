"""Exact original-array audit for the rank-two shared-baseline embedding.

Signed original matrices are Walsh transformed only on their opposite outer
index. This constructs the complete raw source arrays, then contracts the
local output tensor and degree filters independently for each checked output.
"""

from itertools import combinations, product
from random import Random


# Normal variables: x1,x2,p1,p2. Opposite variables: s,t,q.
PHI = ((1,0,1,1), (1,0,1,0), (0,1,0,-1), (0,1,0,0), (-1,-1,0,0))
PSI = ((1,1,0), (1,-1,0), (1,1,-1), (1,-1,1), (2,0,0))
INNER = 4


def support(vector):
    return [(i, value) for i, value in enumerate(vector) if value]


def local_tensor(label, swapped=False):
    if label == INNER:
        terms = [(2,0,2), (3,2,1)]
    else:
        terms = [(i,j,a*b) for i,a in support(PHI[label]) for j,b in support(PSI[label])]
    return [(j,i,c) for i,j,c in terms] if swapped else terms


def linear_map(columns, subset):
    value = 0
    for index in subset:
        value ^= columns[index]
    return value


def independent(columns):
    pivots = {}
    for column in columns:
        while column:
            lead = column.bit_length()-1
            if lead not in pivots:
                pivots[lead] = column
                break
            column ^= pivots[lead]
        if not column:
            return False
    return True


def parity(value):
    return value.bit_count() & 1


def pack(bits):
    return sum(bit << i for i, bit in enumerate(bits))


def walsh_inputs(X, Y, slots, outer, middle):
    width = 1 << outer
    Xhat, Yhat = {}, {}
    for slot in slots:
        Xhat[slot] = [[0]*middle for _ in range(width*width)]
        Yhat[slot] = [[0]*(width*width) for _ in range(middle)]
        for normal, frequency, k in product(range(width), range(width), range(middle)):
            Xhat[slot][normal*width+frequency][k] = sum(
                (-1)**parity(frequency & v) * X[slot][normal*width+v][k]
                for v in range(width)
            )
            Yhat[slot][k][frequency*width+normal] = sum(
                (-1)**parity(frequency & v) * Y[slot][k][v*width+normal]
                for v in range(width)
            )
    return Xhat, Yhat


def source_arrays(matrix, length, inner, gamma, delta, slots, side):
    arrays = {}
    normal_words = list(product(range(4), repeat=length))
    opposite_words = list(product(range(3), repeat=length))
    width = 1 << (length-inner)
    middle_width = 1 << inner
    for normal in normal_words:
        slot = tuple(i for i,v in enumerate(normal) if v >= 2)
        if slot not in slots:
            continue
        normal_outer = pack(normal[i] for i in range(length) if i not in slot)
        p2 = tuple(i for i,v in enumerate(normal) if v == 3)
        for opposite in opposite_words:
            t = tuple(i for i,v in enumerate(opposite) if v == 1)
            q = tuple(i for i,v in enumerate(opposite) if v == 2)
            opposite_outer = linear_map(delta,t)
            if side == 'left':
                run = len(q)-len(p2)
                mid = middle_width*linear_map(gamma,p2)+linear_map(gamma,q)
                value = matrix[slot][normal_outer*width+opposite_outer][mid]
                word = normal+opposite
            else:
                run = len(p2)-len(q)
                mid = middle_width*linear_map(gamma,q)+linear_map(gamma,p2)
                value = matrix[slot][mid][opposite_outer*width+normal_outer]
                word = opposite+normal
            if -inner <= run <= inner:
                arrays[word] = (run, (1 << len(p2))*value)
    return arrays


def output_word(qleft, qright, xleft, vleft, vright, xright, length, delta):
    result = []
    for slot, normal, opposite in ((qleft,xleft,vright),(qright,xright,vleft)):
        normal_index = 0
        for i in range(length):
            if i in slot:
                result.append(INNER)
            else:
                # Character locator Delta_outside^T v, not Delta_outside^-1 v.
                j = parity(delta[i] & opposite)
                result.append(2*((normal >> normal_index) & 1)+j)
                normal_index += 1
    return tuple(result)


def contract(word, left, right, length):
    result = 0
    terms = [local_tensor(label, i>=length) for i,label in enumerate(word)]
    for selected in product(*terms):
        u = tuple(term[0] for term in selected)
        v = tuple(term[1] for term in selected)
        a, b = left.get(u), right.get(v)
        if a is None or b is None or a[0] != b[0]:
            continue
        weight = 1
        for _,_,factor in selected:
            weight *= factor
        result += weight*a[1]*b[1]
    return result


def check_case(length, inner, gamma, delta, full=True):
    slots = [slot for slot in combinations(range(length),inner)
             if independent([gamma[i] for i in slot])
             and independent([delta[i] for i in range(length) if i not in slot])]
    assert len(slots) == len(list(combinations(range(length),inner)))
    outer = length-inner
    width, middle = 1 << outer, 1 << (2*inner)
    rng = Random(20261015048+10*length+inner)
    X = {q:[[rng.randrange(-3,4) for _ in range(middle)] for _ in range(width*width)] for q in slots}
    Y = {q:[[rng.randrange(-3,4) for _ in range(width*width)] for _ in range(middle)] for q in slots}
    Xhat,Yhat = walsh_inputs(X,Y,slots,outer,middle)
    left = source_arrays(Xhat,length,inner,gamma,delta,slots,'left')
    right = source_arrays(Yhat,length,inner,gamma,delta,slots,'right')
    checked = 0
    for qi,qleft in enumerate(slots):
        for ri,qright in enumerate(slots):
            normal_pairs = product(range(width),repeat=2) if full else [(qi%width,(ri+1)%width)]
            for xleft,xright in normal_pairs:
                for vleft,vright in product(range(width),repeat=2):
                    word = output_word(qleft,qright,xleft,vleft,vright,xright,length,delta)
                    got = contract(word,left,right,length)
                    row,column = xleft*width+vleft, vright*width+xright
                    expected = sum(X[qleft][row][k]*Y[qright][k][column] for k in range(middle))
                    assert got == (4**length)*expected, (length,inner,qleft,qright,row,column,got,expected)
                    checked += 1
    return checked, len(left)+len(right), len(slots)


def main():
    tensor = [[sum(PHI[label][i]*PSI[label][j] for label in range(5))
               for j in range(3)] for i in range(4)]
    assert tensor == [[0,0,0],[0,0,0],[2,0,0],[0,0,1]]
    totals = [0,0]
    for args in ((2,1,(1,1),(1,1),True),
                 (3,2,(1,2,3),(1,1,1),True),
                 (3,1,(1,1,1),(1,2,3),False)):
        queries, entries, slots = check_case(*args)
        totals[0] += queries
        totals[1] += entries
        print(f'PASS L={args[0]}, m={args[1]}: {slots} good slots, {queries} exact original-matrix outputs, {entries} source entries.')
    print(f'PASS total: {totals[0]} outputs, {totals[1]} source entries; normalization 4^L.')


if __name__ == '__main__':
    main()
