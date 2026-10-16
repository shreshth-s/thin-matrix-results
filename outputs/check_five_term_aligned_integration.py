"""Walsh source arrays -> compact caches -> complete queries -> original XY.

The cyclic test stores coefficient fibers separately, then performs the exact
cyclic coefficient pairing. This is the coefficientwise execution of the same
integer bilinear construction; the formal truncation variable remains distinct.
"""

import importlib.util
from itertools import combinations, product
from pathlib import Path
from random import Random


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


HERE = Path(__file__).resolve().parent
embedding = load('baseline_embedding', HERE/'check_five_term_aligned_embedding.py')
query = load('baseline_query', HERE/'check_five_term_aligned_cache.py')


def fixture(length, inner, gamma, delta, cyclic, full, seed):
    slots = list(combinations(range(length), inner))
    width, middle = 1 << (length-inner), 1 << (2*inner)
    outer = width*width
    rng = Random(seed)
    X = [{q:[[0]*middle for _ in range(outer)] for q in slots} for _ in range(cyclic)]
    Y = [{q:[[0]*outer for _ in range(middle)] for q in slots} for _ in range(cyclic)]
    for slot in slots:
        for row,k in product(range(outer), range(middle)):
            X[rng.randrange(cyclic)][slot][row][k] = rng.randrange(-3,4)
            Y[rng.randrange(cyclic)][slot][k][row] = rng.randrange(-3,4)
    sources = []
    for residue in range(cyclic):
        xhat,yhat = embedding.walsh_inputs(X[residue],Y[residue],slots,length-inner,middle)
        sources.append((
            embedding.source_arrays(xhat,length,inner,gamma,delta,slots,'left'),
            embedding.source_arrays(yhat,length,inner,gamma,delta,slots,'right'),
        ))
    requests = []
    for qi,qleft in enumerate(slots):
        for ri,qright in enumerate(slots):
            entries = (product(range(outer),repeat=2) if full else
                       [((3*qi+ri)%outer,(qi+2*ri)%outer)])
            for row,column in entries:
                xleft,vleft = divmod(row,width)
                vright,xright = divmod(column,width)
                fixed = embedding.output_word(qleft,qright,xleft,vleft,vright,xright,length,delta)
                inner_positions = qleft+tuple(length+p for p in qright)
                expected = [sum(X[r][qleft][row][k]*Y[(target-r)%cyclic][qright][k][column]
                                for r in range(cyclic) for k in range(middle))
                            for target in range(cyclic)]
                requests.append((fixed,inner_positions,expected))
    return sources,requests


def dense_source(source, length, run, side):
    dims = ([4]*length+[3]*length if side == 'left' else [3]*length+[4]*length)
    result = []
    for word in product(*(range(d) for d in dims)):
        entry = source.get(word)
        result.append(entry[1] if entry is not None and entry[0] == run else 0)
    return result


def check_case(length, inner, gamma, delta, cyclic, full, thresholds, seed):
    sources,requests = fixture(length,inner,gamma,delta,cyclic,full,seed)
    stats = query.new_stats()
    checked = 0
    for threshold in thresholds:
        numerators = [[0]*cyclic for _ in requests]
        for run in range(-inner,inner+1):
            left,right = [],[]
            for residue in range(cyclic):
                x = dense_source(sources[residue][0],length,run,'left')
                y = dense_source(sources[residue][1],length,run,'right')
                left.append(query.encode(x,length,inner,threshold,'left',stats))
                right.append(query.encode(y,length,inner,threshold,'right',stats))
            for index,(fixed,positions,_) in enumerate(requests):
                for target in range(cyclic):
                    for residue in range(cyclic):
                        numerators[index][target] += query.complete_query(
                            left[residue],right[(target-residue)%cyclic],fixed,positions,
                            length,inner,threshold,stats)
                        stats['queries'] += 1
        for index,(_,_,expected) in enumerate(requests):
            for target in range(cyclic):
                numerator = numerators[index][target]
                assert numerator % (4**length) == 0
                assert numerator//(4**length) == expected[target], (
                    length,inner,cyclic,threshold,index,target,numerator,expected[target])
                checked += 1
    print(f'PASS L={length}, m={inner}, q={cyclic}: {checked} normalized original-product '
          f'coefficients; {stats["encoders"]} compact encoders; '
          f'{stats["queries"]} complete residual+box contractions.')
    return checked,stats


def main():
    totals = query.new_stats()
    checked = 0
    for args in (
        (2,1,(1,1),(1,1),1,True,(1,2),20261015049),
        (3,2,(1,2,3),(1,1,1),1,False,(1,2),20261015050),
        (2,1,(1,1),(1,1),3,True,(1,2),20261015051),
    ):
        count,stats = check_case(*args)
        checked += count
        for key,value in stats.items():
            totals[key] += value
    print(f'PASS total: {checked} exact normalized original-product coefficients; '
          f'{totals["encoders"]} compact encoders; '
          f'{totals["intermediate_entries"]} retained encoder/intermediate entries; '
          f'{totals["box_reads"]} high-box reads.')
    print('The signed cyclic fixture has q=3; all coefficient targets are checked.')


if __name__ == '__main__':
    main()
