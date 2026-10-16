#!/usr/bin/env python3
"""Finite checks of rank-prefix hashing and complementary certification.

The matrices below are multiplied directly on small examples. These checks
validate the encoding, nonnegative overcounts, and exactness of the stopping
certificate; they do not implement or prove the fast asymptotic data structure
or the prime-density argument. Python standard library only.
"""
from collections import Counter, defaultdict
from itertools import product
import random
import unittest


def rank_lists(rows, columns, weak=False):
    """Give each occurrence a distinct per-color rank, with the required ties.

An input list contains (color, real_value) pairs. Columns precede rows on ties
for <; rows precede columns for <=. Returned ranks use one common bit length.
"""
    by_color = defaultdict(list)
    for side, lists in enumerate((rows, columns)):
        for outer, values in enumerate(lists):
            for occurrence, (color, value) in enumerate(values):
                tie_side = side if weak else 1 - side
                by_color[color].append((value, tie_side, outer, occurrence, side))
    ranked_rows = [[] for _ in rows]
    ranked_columns = [[] for _ in columns]
    largest_color = 0
    for color, values in by_color.items():
        largest_color = max(largest_color, len(values))
        for rank, (_, _, outer, _, side) in enumerate(sorted(values)):
            destination = ranked_rows if side == 0 else ranked_columns
            destination[outer].append((color, rank))
    bits = max(1, largest_color.bit_length())
    return ranked_rows, ranked_columns, bits


def modular_products(rows, columns, prime, weak=False):
    """Explicit matrix products for rank-< and rank-> prefix-hash counts."""
    ranked_rows, ranked_columns, bits = rank_lists(rows, columns, weak)
    results = []
    for row_bit in (0, 1):
        row_vectors, column_vectors = [], []
        for side, lists, destination in (
                (0, ranked_rows, row_vectors),
                (1, ranked_columns, column_vectors)):
            for values in lists:
                vector = Counter()
                wanted_bit = row_bit if side == 0 else 1 - row_bit
                for color, rank in values:
                    for bit in range(bits - 1, -1, -1):
                        if ((rank >> bit) & 1) == wanted_bit:
                            prefix = rank >> (bit + 1)
                            vector[(color, bit, prefix % prime)] += 1
                destination.append(vector)
        results.append([
            [sum(value * column_vectors[j].get(key, 0)
                 for key, value in row_vectors[i].items())
             for j in range(len(columns))]
            for i in range(len(rows))])
    return results


def oracle_counts(rows, columns, weak=False):
    """Brute-force comparison counts and an independent color-incidence total."""
    positive, complement, totals = [], [], []
    for row in rows:
        prow, crow, trow = [], [], []
        for column in columns:
            pairs = [(x, y) for k, x in row for ell, y in column if k == ell]
            count = sum(x <= y if weak else x < y for x, y in pairs)
            prow.append(count)
            crow.append(len(pairs) - count)
            rm = Counter(k for k, _ in row)
            cm = Counter(k for k, _ in column)
            total = sum(value * cm[color] for color, value in rm.items())
            assert total == len(pairs)
            trow.append(total)
        positive.append(prow)
        complement.append(crow)
        totals.append(trow)
    return [positive, complement], totals


def take_minima(previous, current):
    if previous is None:
        return [[row[:] for row in direction] for direction in current]
    return [[[min(previous[direction][i][j], current[direction][i][j])
              for j in range(len(current[direction][i]))]
             for i in range(len(current[direction]))]
            for direction in range(2)]


class PrefixCountChecks(unittest.TestCase):
    def check_fixture(self, rows, columns, weak):
        exact, totals = oracle_counts(rows, columns, weak)
        upper = None
        # The final prime exceeds every rank in these finite fixtures.
        for prime in (2, 3, 5, 7, 11, 101):
            observed = modular_products(rows, columns, prime, weak)
            for direction in range(2):
                for i in range(len(rows)):
                    for j in range(len(columns)):
                        self.assertGreaterEqual(observed[direction][i][j],
                                                exact[direction][i][j])
            upper = take_minima(upper, observed)
            for i in range(len(rows)):
                for j in range(len(columns)):
                    total = upper[0][i][j] + upper[1][i][j]
                    self.assertGreaterEqual(total, totals[i][j])
                    if total == totals[i][j]:
                        self.assertEqual(upper[0][i][j], exact[0][i][j])
                        self.assertEqual(upper[1][i][j], exact[1][i][j])
        self.assertEqual(upper, exact)

    def test_exhaustive_ties_and_both_relations(self):
        # 162 fixtures include every tie pattern on two row and column lists.
        for values in product((-1, 0, 1), repeat=4):
            rows = [[(0, value)] for value in values[:2]]
            columns = [[(0, value)] for value in values[2:]]
            for weak in (False, True):
                self.check_fixture(rows, columns, weak)

    def test_single_color_duplicates_and_empty_lists(self):
        rng = random.Random(7130)
        # 400 fixtures of the structural type used by the 3SUM reduction.
        for _ in range(200):
            rows, columns = [
                [[(0, rng.randrange(-3, 4)) for _ in range(rng.randrange(5))]
                 for _ in range(4)] for _ in range(2)]
            for weak in (False, True):
                self.check_fixture(rows, columns, weak)

    def test_missing_colors(self):
        rng = random.Random(7131)
        # 400 fixtures of the type used by the min-plus reduction.
        for _ in range(200):
            rows, columns = [
                [[(color, rng.randrange(-3, 4)) for color in range(4)
                  if rng.randrange(4) != 0]
                 for _ in range(4)] for _ in range(2)]
            for weak in (False, True):
                self.check_fixture(rows, columns, weak)

    def test_repeated_bad_prime_and_complementary_certificate(self):
        rows = [[(0, value)] for value in range(3)]
        columns = [[(0, value)] for value in range(3, 6)]
        exact, totals = oracle_counts(rows, columns)
        bad = modular_products(rows, columns, 2)
        # A false match occurs in each direction, including the complement of
        # a true < pair. Merely inspecting the positive count is insufficient.
        for direction in range(2):
            self.assertTrue(any(bad[direction][i][j] > exact[direction][i][j]
                                for i in range(3) for j in range(3)))
        upper = None
        for _ in range(3):
            upper = take_minima(upper, bad)
            self.assertTrue(any(upper[0][i][j] + upper[1][i][j] > totals[i][j]
                                for i in range(3) for j in range(3)))
        upper = take_minima(upper, modular_products(rows, columns, 101))
        self.assertEqual(upper, exact)
        self.assertTrue(all(upper[0][i][j] + upper[1][i][j] == totals[i][j]
                            for i in range(3) for j in range(3)))

    def test_arbitrary_prime_sequence_minima(self):
        rows = [[(0, -2), (0, -2), (0, 5)], [], [(0, 1), (0, 5)]]
        columns = [[(0, -2), (0, 1)], [(0, 5), (0, 5)], []]
        exact, _ = oracle_counts(rows, columns, weak=True)
        upper = None
        # Repetitions are allowed: the algorithm samples with replacement.
        for prime in (3, 2, 2, 7, 3, 5, 101):
            upper = take_minima(upper, modular_products(rows, columns, prime,
                                                       weak=True))
        self.assertEqual(upper, exact)


if __name__ == '__main__':
    unittest.main(verbosity=2)
