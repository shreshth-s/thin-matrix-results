#!/usr/bin/env python3
"""Finite checks of weighted restriction covers and signed subset convolution.

Uses brute-force oracles, not the asymptotically fast matrix primitive.
"""
from fractions import Fraction as F
from itertools import product
from random import Random


def weight(s):
    x, y, z = (s.count(i) for i in range(3))
    # Exact rational surrogate monomials check the general identity.
    return F(3, 4)**(y+z) + F(2, 3)**y + F(2, 3)**z + F(1, 2)**x


def compatible(candidate, restriction):
    # Candidate labels 0=A,1=B,2=C. X forbids C, Y forbids A, Z forbids B.
    return all(c != (s+2) % 3 for c, s in zip(candidate, restriction))


def local_cover(r):
    strings = list(product(range(3), repeat=r))
    sets = [{i for i, c in enumerate(strings) if compatible(c, s)}
            for s in strings]
    for i in range(len(strings)):
        assert sum(i in st for st in sets) == 2**r
    costs = [weight(s) for s in strings]
    total = sum(costs)
    assert total == (1+2*F(3, 4))**r + 2*(2+F(2, 3))**r + (2+F(1, 2))**r
    rem = set(range(len(strings)))
    chosen = []
    while rem:
        options = [(cost/len(st & rem), i) for i, (cost, st)
                   in enumerate(zip(costs, sets)) if st & rem]
        _, i = min(options)
        chosen.append(strings[i])
        rem -= sets[i]
    harmonic = sum((F(1, j) for j in range(1, 3**r+1)), F())
    assert sum(map(weight, chosen)) <= harmonic * total / 2**r
    return chosen


def submasks(mask):
    at = mask
    while True:
        yield at
        if not at:
            return
        at = (at-1) & mask


def apply_restriction(f, g, h, restriction, infinity):
    x, y, z = (sum(1 << i for i, s in enumerate(restriction) if s == j)
               for j in range(3))
    for u in submasks(z):
        for v in submasks(y):
            # This is the (u,v) entry of the restricted min-plus product.
            best = min(f[u | t] + g[(x ^ t) | v] for t in submasks(x))
            if best > 2*infinity:
                continue
            out = x | u | v
            h[out] = min(h[out], best)


def main():
    families = {r: local_cover(r) for r in range(1, 5)}
    rng = Random(20261013)
    checks = 0
    for n in range(1, 7):
        sizes = [min(3, n)] + ([n-3] if n > 3 else [])
        family = [sum((tuple(s) for s in parts), ())
                  for parts in product(*(families[r] for r in sizes))]
        for candidate in product(range(3), repeat=n):
            assert any(compatible(candidate, s) for s in family)
        for _ in range(20):
            W = 10
            sentinel = 4*W+1
            f = [rng.choice(list(range(-W, W+1)) + [sentinel]*5)
                 for _ in range(1 << n)]
            g = [rng.choice(list(range(-W, W+1)) + [sentinel]*5)
                 for _ in range(1 << n)]
            h = [sentinel] * (1 << n)
            for restriction in family:
                apply_restriction(f, g, h, restriction, W)
            direct = [min(f[a] + g[s ^ a] for a in submasks(s))
                      for s in range(1 << n)]
            direct = [sentinel if v > 2*W else v for v in direct]
            assert h == direct, (n, f, g, h, direct)
            checks += 1
    print('PASS: weighted sum, greedy bound, and local coverage for sizes 1..4')
    print('PASS: Cartesian-product cover completeness for sizes 1..6')
    print(f'PASS: {checks} signed/infinite subset-convolution table comparisons')


if __name__ == '__main__':
    main()
