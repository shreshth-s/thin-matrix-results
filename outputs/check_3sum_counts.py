#!/usr/bin/env python3
"""Finite exact checks for the proposed one-sided Monte Carlo #3SUM reduction.

These small brute-force oracles check folded residue multiplicities,
sub-query aggregation, and the one-set distinct-element correction. They
neither implement the asymptotically fast data structure nor establish the
prime-divisor probability estimate or a literature-priority claim.
"""
from collections import Counter, defaultdict
from itertools import combinations, product
from math import isqrt
import random
import unittest


def folded_count(alpha, beta, z, p):
    """One product entry using multiplicities rather than Boolean support."""
    p1 = isqrt(p - 1) + 1
    rho1 = (z % p) % p1
    rho2 = (z % p) // p1
    left = Counter((x - rho1) % p for x in alpha)
    right = Counter((p1 * rho2 - y) % p for y in beta)
    return sum(count * right[sigma] for sigma, count in left.items())


def sub_buckets(values, r, size):
    buckets = defaultdict(list)
    for value in values:
        buckets[value % r].append(value)
    result = {}
    for residue, values_in_bucket in buckets.items():
        result[residue] = [
            values_in_bucket[start : start + size]
            for start in range(0, len(values_in_bucket), size)
        ]
    return result


def overcount_3sum(a, b, c, bucket_prime, universe_primes, size):
    """Finite oracle: enumerate every compatible sub-query and sum its minimum."""
    assert universe_primes and all(p != bucket_prime for p in universe_primes)
    ab = sub_buckets(a, bucket_prime, size)
    bb = sub_buckets(b, bucket_prime, size)
    total = 0
    for z in c:
        for residue, a_groups in ab.items():
            b_groups = bb.get((z - residue) % bucket_prime, [])
            for alpha, beta in product(a_groups, b_groups):
                total += min(folded_count(alpha, beta, z, p) for p in universe_primes)
    return total


def exact_3sum(a, b, c):
    return sum(x + y == z for x, y, z in product(a, b, c))


def repeated_element_count(values):
    value_set = set(values)
    assert len(value_set) == len(values), "The theorem here is for sets."
    return 3 * sum(-2 * x in value_set for x in values) - 2 * (0 in value_set)


def distinct_one_set_upper_bound(values, ordered_overcount):
    numerator = ordered_overcount - repeated_element_count(values)
    assert numerator >= 0
    return (numerator + 5) // 6


class Counting3SUMChecks(unittest.TestCase):
    def test_colliding_residues_require_multiplicity(self):
        alpha, beta, p = [0, 6, 12], [0, -6], 3
        self.assertEqual(folded_count(alpha, beta, 0, p), 6)
        boolean_answer = len({x % p for x in alpha} & {(-y) % p for y in beta})
        self.assertEqual(boolean_answer, 1)
        self.assertEqual(sum(x + y == 0 for x, y in product(alpha, beta)), 2)

    def test_folded_entries_match_direct_modular_pair_counts(self):
        rng = random.Random(31013)
        for _ in range(500):
            alpha = rng.sample(range(-40, 41), rng.randrange(1, 9))
            beta = rng.sample(range(-40, 41), rng.randrange(1, 9))
            z = rng.randrange(-80, 81)
            p = rng.choice([2, 3, 5, 7, 11, 13])
            expected = sum((x + y - z) % p == 0 for x, y in product(alpha, beta))
            self.assertEqual(folded_count(alpha, beta, z, p), expected)

    def test_aggregation_never_undercounts(self):
        rng = random.Random(64157)
        strict_overcounts = 0
        for _ in range(300):
            a, b, c = [rng.sample(range(-18, 19), rng.randrange(1, 10)) for _ in range(3)]
            r = rng.choice([2, 3, 5])
            primes = [p for p in rng.choices([2, 3, 5, 7, 11], k=3) if p != r] or [13]
            result = overcount_3sum(a, b, c, r, primes, rng.randrange(1, 5))
            actual = exact_3sum(a, b, c)
            self.assertGreaterEqual(result, actual)
            strict_overcounts += result > actual
        self.assertGreater(strict_overcounts, 0, "The finite examples exercise overcount errors.")

    def test_aggregation_exact_with_a_false_pair_free_prime(self):
        rng = random.Random(33401)
        for _ in range(100):
            a, b, c = [rng.sample(range(-20, 21), rng.randrange(1, 10)) for _ in range(3)]
            result = overcount_3sum(a, b, c, 3, [2, 5, 101], rng.randrange(1, 5))
            self.assertEqual(result, exact_3sum(a, b, c))

    def test_one_set_repeated_element_correction_exhaustively(self):
        universe = list(range(-4, 5))
        for mask in range(1 << len(universe)):
            values = [v for index, v in enumerate(universe) if mask & (1 << index)]
            repeated = sum(
                x + y + z == 0 and len({x, y, z}) < 3
                for x, y, z in product(values, repeat=3)
            )
            ordered = sum(x + y + z == 0 for x, y, z in product(values, repeat=3))
            unordered = sum(sum(triple) == 0 for triple in combinations(values, 3))
            self.assertEqual(repeated_element_count(values), repeated)
            self.assertEqual(distinct_one_set_upper_bound(values, ordered), unordered)
            for excess in range(16):
                self.assertGreaterEqual(
                    distinct_one_set_upper_bound(values, ordered + excess), unordered
                )

    def test_signed_one_set_pipeline(self):
        rng = random.Random(9743)
        for _ in range(150):
            values = rng.sample(range(-30, 31), rng.randrange(1, 13))
            result = overcount_3sum(values, values, [-x for x in values], 3, [2, 5, 7], 3)
            actual = sum(sum(triple) == 0 for triple in combinations(values, 3))
            self.assertGreaterEqual(distinct_one_set_upper_bound(values, result), actual)
            exact_result = overcount_3sum(values, values, [-x for x in values], 3, [2, 5, 101], 3)
            self.assertEqual(distinct_one_set_upper_bound(values, exact_result), actual)


if __name__ == "__main__":
    unittest.main(verbosity=2)
