#!/usr/bin/env python3
"""Independent exact-rational test of simultaneous-product batching."""
from fractions import Fraction as F
from itertools import product
from math import prod


def main():
    for r in range(24):
        for t in range(1, 8):
            routes = [(j // t, j % t) for j in range(r)]
            assert len(set(routes)) == r
            assert all(g < (r+t-1)//t and c < t for g, c in routes)
    print('PASS: 168 padded-routing cases, including empty and incomplete batches.')
    weights = list(map(F, ['2/3', '-5/7', '3/11', '-11/13']))
    # All coefficient matrices include both independent copy labels.
    L = [[weights[j] if j == 2*c+i else F(0) for c, i in product(range(2), repeat=2)]
         if j < 4 else [F(0)]*4 for j in range(5)]
    M = [[1/weights[j] if j == 2*c+i else F(0) for c, i in product(range(2), repeat=2)]
         if j < 4 else [F(0)]*4 for j in range(5)]
    R = [[F(j//2 == c) if j < 4 else F(0) for c in range(2)] for j in range(5)]
    d = prod(v.denominator for a in (L, M, R) for row in a for v in row)
    H = 1+sum(abs(v) for a in (L, M, R) for row in a for v in row)
    arrays = [[[F(c == j) for c in range(2)] for j in range(2)] for _ in range(3)]
    for k in range(4):
        width = 2**k
        assert len(arrays[0]) == 2*3**k
        checked = 0
        for a in arrays:
            for row in a:
                for v in row:
                    assert d**k % v.denominator == 0 and abs(v) <= (5*H)**k
                    checked += 1
        vals = [1]
        for _ in range(k):
            vals = [3*v+i-2 for i in range(2) for v in vals]
        for seed in range(3):
            x = [F(v+seed-2*c) for c in range(2) for v in vals]
            y = [F(2*v-seed+c) for c in range(2) for v in vals]
            pairs = [sum(a*b for a, b in zip(l, x))*sum(a*b for a, b in zip(m, y))
                     for l, m in zip(arrays[0], arrays[1])]
            for c in range(2):
                got = sum(row[c]*v for row, v in zip(arrays[2], pairs))
                expected = sum(x[c*width+i]*y[c*width+i] for i in range(width))
                assert got == expected
        print(f'PASS: depth {k}, {len(arrays[0])} terms, {checked} coefficient checks, six independent dot products.')
        next_arrays = []
        for side, top in enumerate((L, M, R)):
            inner = 1 if side == 2 else width
            outer = 1 if side == 2 else 2
            out = []
            for group in range(3):
                for old in arrays[side]:
                    out.append([sum(top[j][c*outer+i]*old[(j%2)*inner+v]
                                    for j in range(5) if j//2 == group)
                                for c in range(2) for i in range(outer) for v in range(inner)])
            next_arrays.append(out)
        arrays = next_arrays
    print('SCOPE: exact finite coefficient/product checks; the asymptotic statements are Lean proofs.')


if __name__ == '__main__':
    main()
