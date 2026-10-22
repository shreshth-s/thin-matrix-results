#!/usr/bin/env python3
"""Actual shrinking-bias lists in complete source contractions.

This checks the gauge/source interface, including cyclic coefficients. It
does not establish a polynomial-size small-bias construction asymptotically.
"""
from pathlib import Path
import importlib.util
from itertools import combinations, product
from random import Random
from check_half_bias import construct

P = Path(__file__).resolve().parents[2]/'outputs/check_five_term_aligned_embedding.py'
spec = importlib.util.spec_from_file_location('original_embedding', P)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)


def run(L, m, gamma, delta, q, budget):
    slots = tuple(Q for Q in combinations(range(L), m)
                  if base.independent([gamma[i] for i in Q])
                  and base.independent([delta[i] for i in range(L) if i not in Q]))
    outer = L-m
    W, H = 1 << outer, 1 << m
    translations = construct(m)
    gauges = tuple(range(len(translations)))
    inv = {}
    for Q in slots:
        inv[Q] = {base.linear_map(gamma, [Q[i] for i in range(m) if (a>>i)&1]):a
                  for a in range(H)}
        assert len(inv[Q]) == H
    choice = {(Q,h):next(d for d in gauges if inv[Q][h^translations[d]].bit_count() <= budget)
              for Q in slots for h in range(H)}
    gauges = tuple(sorted(set(choice.values())))
    assert len(gauges) > 1
    # Every omitted list index has an identically zero mask on this fixture.
    if m > 1:
        assert any(len({choice[Q,h] for Q in slots}) > 1 for h in range(H))
    rng = Random(202610200503 + L + 17*m)
    X = [{Q:[[rng.randrange(-3,4) for _ in range(H*H)] for _ in range(W*W)]
          for Q in slots} for _ in range(q)]
    Y = [{Q:[[rng.randrange(-3,4) for _ in range(W*W)] for _ in range(H*H)]
          for Q in slots} for _ in range(q)]
    requests = []
    for QL, QR in product(slots, repeat=2):
        for iL,aL,aR,iR in product(range(W), repeat=4):
            word = base.output_word(QL, QR, iL,aL,aR,iR,L,delta)
            row, col = iL*W+aL, aR*W+iR
            expected = [sum(X[r][QL][row][h]*Y[(target-r)%q][QR][h][col]
                            for r in range(q) for h in range(H*H))
                        for target in range(q)]
            requests.append((word,expected))
    actual = [[0]*q for _ in requests]
    deleted = nonzero = 0
    for d1,d2 in product(gauges, repeat=2):
        sources = []
        for residue in range(q):
            Xm,Ym = {},{}
            for Q in slots:
                Xm[Q] = [[0]*(H*H) for _ in range(W*W)]
                Ym[Q] = [[0]*(W*W) for _ in range(H*H)]
                for h1,h2 in product(range(H),repeat=2):
                    translated = h1*H+h2
                    old1,old2 = h1^translations[d1],h2^translations[d2]
                    original = old1*H+old2
                    if choice[Q,old1] == d1:
                        for row in range(W*W):
                            Xm[Q][row][translated] = X[residue][Q][row][original]
                    if choice[Q,old2] == d2:
                        for col in range(W*W):
                            Ym[Q][translated][col] = Y[residue][Q][original][col]
            Xh,Yh = base.walsh_inputs(Xm,Ym,slots,outer,H*H)
            pair = []
            for side,matrix in (('left',Xh),('right',Yh)):
                raw = base.source_arrays(matrix,L,m,gamma,delta,slots,side)
                cropped = {}
                for word,value in raw.items():
                    normal,opposite = (word[:L],word[L:]) if side=='left' else (word[L:],word[:L])
                    if value[1]:
                        nonzero += 1
                        assert normal.count(3) <= budget
                    if opposite.count(2) <= budget:
                        cropped[word] = value
                    else:
                        deleted += int(value[1] != 0)
                pair.append(cropped)
            sources.append(pair)
        for index,(word,_) in enumerate(requests):
            for target,residue in product(range(q),repeat=2):
                actual[index][target] += base.contract(
                    word,sources[residue][0],sources[(target-residue)%q][1],L)
    for values,(_,expected) in zip(actual,requests):
        assert all(x % (4**L) == 0 for x in values)
        assert [x//(4**L) for x in values] == expected
    assert deleted > 0
    print('PASS actual-list half-source cyclic embedding:', dict(
        L=L,m=m,q=q,budget=budget,good_sets=len(slots),
        gauge_pairs=len(gauges)**2,list_entries=len(translations),coefficients=len(requests)*q,
        nonzero_source_entries=nonzero,cropped_nonzeros=deleted))
    return len(requests)*q


if __name__ == '__main__':
    total = run(2,1,(1,1),(1,1),2,0)
    total += run(3,2,(1,2,3),(1,1,1),2,1)
    print('PASS complete normalized coefficients:', total)
    print('Masks depend only on own good-set block and original normal middle coordinate.')
    print('Both middle coordinates are translated identically on both inputs.')
