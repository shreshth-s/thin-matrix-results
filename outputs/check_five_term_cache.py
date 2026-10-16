#!/usr/bin/env python3
"""Partial direct-projection caches on actual signed source embeddings.

Finite Cartesian enumeration is an oracle only. The asymptotic construction
generates the capped and truncated states directly, as the proof requires.
Integer tests exercise complete original matrix products. Additional exact
cyclic-ring tests exercise the requested-coefficient residual and box reads.
Schoolbook ring products are finite oracles, not a fast implementation.
"""
import importlib.util
from functools import lru_cache
from itertools import combinations, product
from math import comb
from pathlib import Path
from random import Random

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('profile', ROOT/'outputs/check_five_term_profile.py')
p = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p)


def encode(array, L, m, ell, side, stats):
    table, volume = {}, [0]*(2*L+1)
    def visit(values, pos, word, private, direct):
        volume[pos] += len(values)
        if pos == 2*L:
            table[word] = values[0]
            return
        normal = p.normal(pos, L, side)
        forms, dim = (p.PHI, 4) if normal else (p.PSI, 3)
        width = len(values)//dim
        choices = {label: forms[label] for label in range(4)}
        half = pos//L
        used = private[half] + (direct if normal else 0)
        if used < m:
            choices[p.P] = forms[p.P]
            if normal and direct < ell:
                choices[p.NEW1], choices[p.NEW2] = ((2, 1),), ((3, 1),)
        for label, form in choices.items():
            child = [sum(coef*values[i*width+j] for i, coef in form) for j in range(width)]
            newprivate = list(private)
            newprivate[half] += label == p.P
            visit(child, pos+1, word+(label,), newprivate, direct+(label in (p.NEW1, p.NEW2)))
    visit(array, 0, (), [0, 0], 0)
    ordinary = sum(comb(L, j)*4**(L-j) for j in range(m+1))
    normal = sum(comb(L, j)*4**(L-j)*sum(comb(j, a)*2**a for a in range(min(j, ell)+1))
                 for j in range(m+1))
    assert len(table) == ordinary*normal
    assert all(v <= len(table) for v in volume)
    assert sum(volume) <= (2*L+1)*len(table)
    stats['encoders'] += 1
    stats['stored_entries'] += len(table)
    stats['intermediate_entries'] += sum(volume)
    return table


def projected_group(table, fixed, inner, forced, free, L, m, ell, t, side, stats):
    """One left- or right-specific lexicographic group, keyed globally."""
    cutoff = t-sum(v != 'z' for v in forced.values())
    transforms = [p.S_NORMAL if p.normal(inner[axis], L, side) else p.S_OPPOSITE for axis in free]
    dims = [sorted({label for form in forms.values() for label, _ in form}) for forms in transforms]
    zero = [p.P]*len(free)
    values = {}
    for word in product(*dims):
        if sum(x != p.P for x in word) >= cutoff:
            continue
        leaf = list(fixed)
        for axis, symbol in forced.items():
            assert p.normal(inner[axis], L, side)
            leaf[inner[axis]] = {'z': p.P, 'a': p.NEW1, 'b': p.NEW2}[symbol]
        for axis, label in zip(free, word):
            leaf[inner[axis]] = label
        direct = sum(label in (p.NEW1, p.NEW2) for label in leaf)
        assert direct <= ell
        for half in range(2):
            part = leaf[half*L:(half+1)*L]
            assert sum(label in (p.P, p.NEW1, p.NEW2) for label in part) <= m
        values[word] = table[tuple(leaf)]
    count = len(values)
    stats['source_reads'] += count
    for axis, forms in enumerate(transforms):
        old_zero = list(zero)
        dims[axis], zero[axis] = list(forms), 'z'
        updated = {}
        for word in product(*dims):
            degree = sum(word[j] != zero[j] for j in range(len(free)))
            if degree >= cutoff:
                continue
            value = 0
            for label, coefficient in forms[word[axis]]:
                predecessor = word[:axis]+(label,)+word[axis+1:]
                before = sum(predecessor[j] != old_zero[j] for j in range(len(free)))
                assert before <= degree < cutoff and predecessor in values
                value += coefficient*values[predecessor]
                stats['predecessors'] += 1
            updated[word] = value
        values = updated
        assert len(values) <= count
    result = {}
    for word, value in values.items():
        output = ['z']*len(inner)
        for axis, symbol in forced.items():
            output[axis] = symbol
        for axis, symbol in zip(free, word):
            output[axis] = symbol
        result[tuple(output)] = value
    return result


def residual_table(table, fixed, inner, L, m, ell, t, side, stats):
    normal = tuple(axis for axis, pos in enumerate(inner) if p.normal(pos, L, side))
    opposite = tuple(axis for axis in range(len(inner)) if axis not in normal)
    result = {}
    start_reads = stats['source_reads']
    def add(forced, free):
        values = projected_group(table, fixed, inner, forced, free, L, m, ell, t, side, stats)
        assert not result.keys() & values.keys(), 'duplicated output across lex groups'
        result.update(values)
        stats['groups'] += 1
    if ell == 0:
        add({}, tuple(range(len(inner))))
    else:
        for a in range(min(ell, t)):
            for selected in combinations(normal, a):
                for assignment in product(('a', 'b'), repeat=a):
                    forced = dict.fromkeys(normal, 'z')
                    forced.update(zip(selected, assignment))
                    add(forced, opposite)
        if ell < t:
            for first in combinations(normal, ell):
                pivot = max(first)
                for assignment in product(('a', 'b'), repeat=ell):
                    forced = {axis: 'z' for axis in normal if axis <= pivot}
                    forced.update(zip(first, assignment))
                    free = tuple(axis for axis in range(len(inner)) if axis not in forced)
                    add(forced, free)
    expected_reads = sum(comb(m, a)*comb(m, b)*2**b*(2**a if a < ell else 2**ell*3**(a-ell))
                         for a, b in product(range(m+1), repeat=2) if a+b < t)
    assert stats['source_reads']-start_reads == expected_reads
    expected_keys = {word for word in product(('z', 'a', 'b'), repeat=2*m)
                     if sum(x != 'z' for x in word) < t}
    assert result.keys() == expected_keys
    return result


def complete_query(left, right, fixed, inner, L, m, ell, t, stats,
                   coefficient_query=None):
    lv = residual_table(left, fixed, inner, L, m, ell, t, 'left', stats)
    rv = residual_table(right, fixed, inner, L, m, ell, t, 'right', stats)
    assert lv.keys() == rv.keys()
    answer = 0
    for word, value in lv.items():
        degree = sum(x != 'z' for x in word)
        if coefficient_query is None:
            term = value*rv[word]
        else:
            ring, q, target = coefficient_query
            # Source arrays contain literal integer zeros at inactive cells.
            left_value = value if isinstance(value, ring.r0_Ring) else ring.r0_Ring((value,)+(0,)*(q-1))
            right_value = rv[word] if isinstance(rv[word], ring.r0_Ring) else ring.r0_Ring((rv[word],)+(0,)*(q-1))
            before = ring.r0_OPS['target_coefficient_products']
            term = ring.r0_target_product(left_value, right_value, target)
            assert ring.r0_OPS['target_coefficient_products']-before == q
        answer += (-1)**(t-degree-1)*comb(2*m-degree-1, t-degree-1)*term
        a, b = sum(x != 'z' for x in word[:m]), sum(x != 'z' for x in word[m:])
        stats['asymmetric_keys'] += (a < ell <= b or b < ell <= a)
    @lru_cache(None)
    def box(word):
        assert p.valid_box(word, L, 0, m, t)
        stars = [i for i in p.block_order(L, 0) if word[i] == p.STAR]
        if not stars:
            return left[word]*right[word]
        pos = stars[-1]
        return sum(box(word[:pos]+(label,)+word[pos+1:]) for label in range(5))
    for marked_tuple in combinations(inner, len(inner)-t):
        marked, stars = set(marked_tuple), set()
        for pos in inner:
            if pos not in marked:
                break
            stars.add(pos)
        switched = tuple(pos for pos in inner if pos not in marked)
        for labels in product(range(4), repeat=t):
            word = list(fixed)
            for pos in stars:
                word[pos] = p.STAR
            for pos, label in zip(switched, labels):
                word[pos] = label
            value = box(tuple(word))
            if coefficient_query is None:
                answer += value
            elif isinstance(value, int):
                answer += value if target == 0 else 0
            else:
                # Only one already stored coefficient is read here.
                answer += value.coefficients[target]
    return answer


def bits(value, length):
    return tuple((value >> (length-1-i)) & 1 for i in range(length))


def number(word):
    value = 0
    for bit in word:
        value = 2*value+bit
    return value


def image(matrix, word):
    return number(tuple(sum(a*b for a, b in zip(row, word)) % 2 for row in matrix))


def source_array(matrix, L, m, gamma, delta, slots, run, side):
    dims = [4 if p.normal(pos, L, side) else 3 for pos in range(2*L)]
    result = []
    for word in product(*(range(d) for d in dims)):
        x, y = (word[:L], word[L:]) if side == 'left' else (word[L:], word[:L])
        slot = tuple(i for i, val in enumerate(x) if val >= 2)
        value = 0
        if slot in slots:
            p2, q = tuple(val == 3 for val in x), tuple(val == 2 for val in y)
            degree = sum(q)-sum(p2) if side == 'left' else sum(p2)-sum(q)
            if degree == run:
                outer_normal = number(tuple(x[i] for i in range(L) if i not in slot))
                outer_opposite = image(delta, tuple(val == 1 for val in y))
                base = slots.index(slot)*4**(L-m)
                if side == 'left':
                    outer = base+outer_normal*2**(L-m)+outer_opposite
                    middle = image(gamma, p2)*2**m+image(gamma, q)
                    value = matrix[outer][middle]
                else:
                    outer = base+outer_opposite*2**(L-m)+outer_normal
                    middle = image(gamma, q)*2**m+image(gamma, p2)
                    value = matrix[middle][outer]
        result.append(value)
    return result


def locate(row, col, L, m, delta, slots):
    block = 4**(L-m)
    qi, row_rest = divmod(row, block)
    ri, col_rest = divmod(col, block)
    x0, y1 = divmod(row_rest, 2**(L-m))
    y0, x1 = divmod(col_rest, 2**(L-m))
    fixed = [p.P]*(2*L)
    for half, slot, normal, opposite in ((0, slots[qi], x0, y0), (1, slots[ri], x1, y1)):
        outer = tuple(i for i in range(L) if i not in slot)
        inverses = []
        for candidate in product(range(2), repeat=L-m):
            word = [0]*L
            for pos, val in zip(outer, candidate):
                word[pos] = val
            if image(delta, word) == opposite:
                inverses.append(candidate)
        assert len(inverses) == 1
        for pos, a, b in zip(outer, bits(normal, L-m), inverses[0]):
            fixed[half*L+pos] = 2*a+b
    return tuple(fixed), slots[qi]+tuple(L+pos for pos in slots[ri])


def new_stats():
    return dict.fromkeys(('encoders', 'stored_entries', 'intermediate_entries', 'source_reads',
                         'predecessors', 'groups', 'asymmetric_keys', 'queries'), 0)


def check_ring_queries():
    spec = importlib.util.spec_from_file_location('cache_ring_oracle', ROOT/'outputs/check_five_term_ring.py')
    ring = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ring)
    rng = Random(2026101631)
    L, m, ell = 3, 2, 1
    gamma, delta = ((1, 0, 1), (0, 1, 1)), ((1, 1, 1),)
    slots = list(combinations(range(L), m))
    N, D = len(slots)*4**(L-m), 4**m
    stats = new_stats()
    outputs, coefficients = 0, 0
    for q in (3, 5):
        x = [[ring.r0_Ring(rng.randrange(-2, 3) for _ in range(q))
              for _ in range(D)] for _ in range(N)]
        y = [[ring.r0_Ring(rng.randrange(-2, 3) for _ in range(q))
              for _ in range(N)] for _ in range(D)]
        tables = []
        for run in range(-m, m+1):
            left = source_array(x, L, m, gamma, delta, slots, run, 'left')
            right = source_array(y, L, m, gamma, delta, slots, run, 'right')
            tables.append((encode(left, L, m, ell, 'left', stats),
                           encode(right, L, m, ell, 'right', stats)))
        positions = rng.sample(list(product(range(N), repeat=2)), 4)
        for t in (2, 3, 4):
            for row, col in positions:
                fixed, inner = locate(row, col, L, m, delta, slots)
                # Independent original-matrix oracle: tuple coefficients and
                # direct cyclic convolution, with no encoded source lookup.
                expected = [0]*q
                for k in range(D):
                    for a in range(q):
                        for b in range(q):
                            expected[(a+b) % q] += x[row][k].coefficients[a]*y[k][col].coefficients[b]
                for target in range(q):
                    answer = sum(complete_query(left, right, fixed, inner, L, m, ell, t, stats,
                                                (ring, q, target)) for left, right in tables)
                    assert answer == expected[target], (q, t, row, col, target, answer, expected[target])
                    coefficients += 1
                outputs += 1
    assert stats['asymmetric_keys'] > 0
    assert ring.r0_OPS['target_coefficient_products'] > 0
    print(f'PASS cyclic-ring original-array queries: {outputs} complete outputs, {coefficients} coefficients, q=3 and q=5.')
    print('PASS each residual product reads exactly q coefficient pairs; every stored-box lookup reads one coefficient.')


def main():
    rng = Random(2026101611)
    stats = new_stats()
    fixtures = [(2, 1, ((1, 1),), ((1, 1),)),
                (3, 2, ((1, 0, 1), (0, 1, 1)), ((1, 1, 1),))]
    for L, m, gamma, delta in fixtures:
        slots = list(combinations(range(L), m))
        N, D = len(slots)*4**(L-m), 4**m
        x = [[rng.randrange(-3, 4) for _ in range(D)] for _ in range(N)]
        y = [[rng.randrange(-3, 4) for _ in range(N)] for _ in range(D)]
        arrays = [(source_array(x, L, m, gamma, delta, slots, run, 'left'),
                   source_array(y, L, m, gamma, delta, slots, run, 'right'))
                  for run in range(-m, m+1)]
        positions = list(product(range(N), repeat=2))
        if L == 3:
            positions = rng.sample(positions, 24)
        for ell in range(m+1):
            tables = [(encode(left, L, m, ell, 'left', stats), encode(right, L, m, ell, 'right', stats))
                      for left, right in arrays]
            for t in range(1, 2*m+1):
                for row, col in positions:
                    fixed, inner = locate(row, col, L, m, delta, slots)
                    answer = sum(complete_query(left, right, fixed, inner, L, m, ell, t, stats)
                                 for left, right in tables)
                    expected = sum(x[row][k]*y[k][col] for k in range(D))
                    assert answer == expected, (L, m, ell, t, row, col, answer, expected)
                    stats['queries'] += 1
    assert stats['asymmetric_keys'] > 0
    print('PASS actual signed source embeddings and complete matrix-product queries:', stats)
    print('PASS exact cache counts, all intermediate volumes, lex-group disjointness, sparse closure, and matching full output keys.')
    print('Includes ell=0, partial caching, full caching, and different left/right low/high group assignments.')
    check_ring_queries()
    print('Finite algebra validation only; no numerical exponent certificate or complete fast algorithm.')


if __name__ == '__main__':
    main()
