#!/usr/bin/env python3
"""Independent exhaustive CW type-class, ordered-collision and multinomial checks.
Finite exact arithmetic only; no entropy-rate or execution-cost assertion.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from math import factorial, isqrt

BLOCKS = ((0, 1, 1), (1, 0, 1), (1, 1, 0), (0, 0, 2), (0, 2, 0), (2, 0, 0))

def multinomial(counts):
    denominator = 1
    for c in counts:
        denominator *= factorial(c)
    return factorial(sum(counts)) // denominator

def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))

def check(n):
    groups = defaultdict(list)
    for word in product(range(6), repeat=n):
        groups[tuple(word.count(b) for b in range(6))].append(word)
    fibers_checked = pairs_checked = 0
    for hist, words in groups.items():
        T = len(words)
        assert T == multinomial(hist)
        keys = {w: tuple(tuple(BLOCKS[b][a] for b in w) for a in range(3)) for w in words}
        Ds = []
        image_sizes = []
        for axis in range(3):
            fibers = Counter(keys[w][axis] for w in words)
            ref = keys[words[0]][axis]
            counts = tuple(ref.count(a) for a in range(3))
            expected = {x for x in product(range(3), repeat=n)
                        if tuple(x.count(a) for a in range(3)) == counts}
            assert set(fibers) == expected
            assert len(fibers) == multinomial(counts)
            assert T % len(fibers) == 0
            D = T // len(fibers)
            assert D >= 1 and set(fibers.values()) == {D}
            Ds.append(D)
            image_sizes.append(len(fibers))
            fibers_checked += len(fibers)
        P = 0
        for u in words:
            for v in words:
                if u == v:
                    continue
                shared = sum(x == y for x, y in zip(keys[u], keys[v]))
                assert shared <= 1
                P += shared > 0
                pairs_checked += 1
        D = sum(Ds)
        assert D >= 3 and P == T * (D - 3)
        M = next(m for m in range(2 * D + 1, 4 * D + 1) if prime(m))
        assert M > 2 and 2 * D < M <= 4 * D
        S = min(image_sizes)
        assert S * D <= 3 * T and S * M <= 12 * T
        # Every possible bucket cardinality: exact rational simplification.
        for b in range(M + 1):
            assert Fraction(S * b, 24 * M) <= Fraction(T * b, 2 * M**2)
            assert Fraction(T * b, 2 * M**2) <= Fraction(T * b, M**2) - Fraction(P * b, M**3)
    print(f"PASS: n={n}: {len(groups)} actual type classes, {6**n} words, "
          f"{fibers_checked} coordinate fibers, {pairs_checked} ordered distinct pairs.")
    return len(groups), 6**n, fibers_checked, pairs_checked

def main():
    totals = tuple(map(sum, zip(*(check(n) for n in range(6)))))
    assert totals == (462, 9331, 11952, 394200)
    print("PASS: totals %d classes, %d words, %d coordinate fibers, %d ordered distinct pairs." % totals)
    print("SCOPE: exact constructed type classes, full marginal images, regular fibers, "
          "ordered collisions and least admissible prime; no large progression-free set or cost bound.")

if __name__ == '__main__':
    main()
