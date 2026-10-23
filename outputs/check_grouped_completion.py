#!/usr/bin/env python3
"""Independent finite storage/duplication checks, not asymptotic proofs."""
from collections import Counter
from itertools import combinations, product
from math import comb


def check(n, r):
    subsets = [frozenset(js) for j in range(min(n, r) + 1)
               for js in combinations(range(n), j)]
    size = sum(comb(n, j) for j in range(min(n, r) + 1))
    assert len(subsets) == size
    assert len(set(subsets)) == size
    copies = Counter()
    for pair in product((0, 1), repeat=n):
        for rare in subsets:
            copies[tuple(2 if i in rare else pair[i] for i in range(n))] += 1
    volume = 0
    for raw in product((0, 1, 2), repeat=n):
        j = raw.count(2)
        assert copies[raw] == (2**j if j <= r else 0)
        volume += (j <= r)
    assert sum(copies.values()) == 2**n * size
    assert volume == sum(comb(n, j) * 2**(n-j) for j in range(min(n, r) + 1))
    assert volume <= 2**n * size
    for prefix in range(6):
        for depth in range(prefix + 1):
            assert 4**depth * 3**(prefix-depth) * volume <= 4**prefix * 2**n * size


def main():
    if not __debug__:
        raise SystemExit("Assertions must be enabled.")
    for n in range(7):
        for r in range(n + 2):
            check(n, r)
    print("PASS: n=0..6, capped support counts, exactly 2^j copies per rare word, full group storage, and every mixed prefix layer.")


if __name__ == '__main__':
    main()
