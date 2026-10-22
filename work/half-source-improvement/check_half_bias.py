#!/usr/bin/env python3
"""Exact shrinking-bias construction and half-weight coverage checks.

The all-m proof is in PROOF.md. These finite checks use rational conditional
expectations, independently recompute character sums, and test affine
Hamming-ball coverage under invertible binary changes of basis.
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from random import Random


@lru_cache(None)
def construct(m):
    count = 64 * m**3
    r = F(4*m+1, 4*m)
    c = (r + 1/r) / 2
    threshold = count // (2*m)
    assert 2*((1 << m)-1)*c**count < r**threshold
    characters = tuple(range(1, 1 << m))
    sums = dict.fromkeys(characters, 0)

    @lru_cache(None)
    def power(j):
        return r**j

    def expectation(prefix, exposed):
        total = F(0)
        for a, value in sums.items():
            if a >> exposed:
                total += (power(value) + power(-value)) * c
            else:
                sign = 1 if (a & prefix).bit_count() % 2 == 0 else -1
                total += power(value+sign) + power(-value-sign)
        return total

    result = []
    for _ in range(count):
        prefix = 0
        previous = sum((power(s)+power(-s) for s in sums.values()), F(0))
        before = expectation(0, 0)
        assert before == previous*c
        for bit in range(m):
            choices = [expectation(prefix | (value << bit), bit+1)
                       for value in (0, 1)]
            assert sum(choices) == 2*before
            choice = int(choices[1] < choices[0])
            assert choices[choice] <= before
            before = choices[choice]
            prefix |= choice << bit
        result.append(prefix)
        for a in characters:
            sums[a] += 1 if (a & prefix).bit_count() % 2 == 0 else -1
        assert sum((power(s)+power(-s) for s in sums.values()), F(0)) == before
        assert before <= previous*c
    histogram = Counter(result)
    fresh = {a: sum(n * (1 if (a & d).bit_count() % 2 == 0 else -1)
                    for d, n in histogram.items()) for a in characters}
    assert fresh == sums
    assert all(abs(s) < threshold for s in fresh.values())
    assert sum((power(s)+power(-s) for s in fresh.values()), F(0)) < power(threshold)
    return tuple(result)


def binary_map(rows, x):
    return sum(((row & x).bit_count() % 2) << i for i, row in enumerate(rows))


def check_coverage(m, translations):
    # Exhaust all invertible matrices through m=3; sample deterministically at 4.
    rng = Random(20261020)
    candidates = (product(range(1, 1 << m), repeat=m) if m <= 3 else
                  (tuple(rng.randrange(1, 1 << m) for _ in range(m))
                   for _ in range(256)))
    matrices = cases = 0
    histogram = Counter(translations)
    for rows in candidates:
        images = [binary_map(rows, x) for x in range(1 << m)]
        if len(set(images)) != 1 << m:
            continue
        matrices += 1
        for h in range(1 << m):
            total = sum(n*images[h ^ d].bit_count() for d, n in histogram.items())
            assert F(total, len(translations)) < F(m, 2)+F(1, 4)
            first = next(i for i, d in enumerate(translations)
                         if images[h ^ d].bit_count() <= m//2)
            assert images[h ^ translations[first]].bit_count() <= m//2
            assert all(images[h ^ translations[i]].bit_count() > m//2
                       for i in range(first))
            cases += 1
    return matrices, cases


def main():
    total_bits = 0
    for m in range(1, 5):
        translations = construct(m)
        matrices, cases = check_coverage(m, translations)
        total_bits += m*len(translations)
        print(f"PASS m={m}: entries={len(translations)}, exact bit choices="
              f"{m*len(translations)}, invertible maps={matrices}, "
              f"affine half-weight cases={cases}")
    print(f"PASS exact half-weight construction: {total_bits} rational bit choices.")


if __name__ == "__main__":
    main()
