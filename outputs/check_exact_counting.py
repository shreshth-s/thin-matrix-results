#!/usr/bin/env python3
"""Finite original-matrix audit of deterministic signed-window counting.

The algorithm uses known old-window counts and a folded cyclic oracle.
An independent direct original-sum oracle checks every queried coefficient.
Sparse monomial dictionaries are used only to make these finite checks small;
this is not an implementation or proof of the fast aligned data structure.
The candidate family is finite: its exact maximum divisor count certifies
the contraction inequality, rather than testing asymptotic prime density.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import gcd, isqrt
from random import Random
import unittest


WINDOW = (-1, 0, 1)
POOL = (5, 7, 11, 13, 17, 19, 23)


def blocks(middle, size):
    return [tuple(range(start, min(start + size, middle)))
            for start in range(0, middle, size)]


def direct_windows(a, b, target, partition):
    """Independent original-integer oracle, used for checking only."""
    out = {}
    for i, j, z in product(range(len(a)), range(len(target[0])),
                           range(len(partition))):
        hist = Counter(a[i][k] + b[k][j] - target[i][j]
                       for k in partition[z])
        out[i, j, z] = tuple(hist[value] for value in WINDOW)
    return out


class FoldedFiberOracle:
    """Actual residue-folded entries weighted by cyclic monomials.

    A stored nonzero is (middle index, residue) -> monomial exponent.
    Missing masked entries are absent, never numerical weight zero.
    Dot products below multiply the sparse encoded rows and columns and
    then read the requested cyclic coefficient.  They do not test the
    original integer sum; the separate checking oracle does that.
    """
    def __init__(self, a, b, target, partition, alpha, beta):
        self.a, self.b, self.target = a, b, target
        self.partition, self.alpha, self.beta = partition, alpha, beta
        self.cache = {}
        self.coefficient_checks = 0
        self.saw_negative_target = False
        self.saw_nontrivial_fiber = False
        self.saw_masked_zeros = False

    def encode(self, d, q, mask):
        assert d % 3 == 0 and gcd(d, q) == 1
        key = (d, q, mask)
        if key in self.cache:
            return self.cache[key]
        width = isqrt(d) + (isqrt(d) ** 2 < d)
        actual = {k for block in self.partition for k in block}
        left, right = {}, {}
        for i, digit in product(range(len(self.a)), range(width)):
            left[i, digit] = {
                (k, (self.a[i][k] + digit) % d): self.a[i][k] % q
                for k in actual
                if mask is None or self.alpha[i][k] == mask[0]}
        for j, digit in product(range(len(self.target[0])), range(width)):
            right[j, digit] = {
                (k, (-self.b[k][j] - width * digit) % d): self.b[k][j] % q
                for k in actual
                if mask is None or self.beta[k][j] == mask[1]}
        if mask is not None:
            self.saw_masked_zeros |= any(len(row) < len(actual)
                                         for row in left.values())
        self.saw_nontrivial_fiber |= q > 1
        self.cache[key] = (left, right, width)
        return self.cache[key]

    def count(self, incidence, ell, d, q, mask=None):
        i, j, z = incidence
        target = self.target[i][j] + ell
        self.saw_negative_target |= target < 0
        left, right, width = self.encode(d, q, mask)
        residue = (-target) % d
        row = left[i, residue % width]
        col = right[j, residue // width]
        block = set(self.partition[z])
        polynomial = Counter()
        for key, left_exponent in row.items():
            if key[0] in block and key in col:
                polynomial[(left_exponent + col[key]) % q] += 1
        actual = polynomial[target % q]
        # Independent checking path.  This value is never returned to the
        # algorithm in place of the encoded matrix product's coefficient.
        expected = sum(
            (self.a[i][k] + self.b[k][j] - target) % (d * q) == 0
            for k in self.partition[z]
            if mask is None or (self.alpha[i][k], self.beta[k][j]) == mask)
        assert actual == expected, (incidence, ell, d, q, mask, actual, expected)
        self.coefficient_checks += 1
        return actual

    def union(self, incidence, d, q):
        return sum(self.count(incidence, ell, d, q) for ell in WINDOW)


def exact_divisor_bound(a, b, target, partition, pool):
    """Finite certificate only, not a step of the proposed algorithm."""
    lam = 0
    for i, j, block in product(range(len(a)), range(len(target[0])), partition):
        for k in block:
            gap = a[i][k] + b[k][j] - target[i][j]
            ell = (gap + 1) % 3 - 1
            difference = (gap - ell) // 3
            if difference:
                lam = max(lam, sum(difference % p == 0 for p in pool))
    return lam


def purify(a, b, target, partition, known, alpha, beta,
           pool=POOL, factors=3, freeze=1):
    """All-R greedy common-prime purification, followed by four masks."""
    assert 0 <= freeze <= factors <= len(pool) and 3 not in pool
    assert len(set(pool)) == len(pool)
    oracle = FoldedFiberOracle(a, b, target, partition, alpha, beta)
    total = {key: sum(value) for key, value in known.items()}
    active = {key for key, value in total.items() if value}
    answer = {key: {(ell, i, j): 0 for ell, i, j in
                    product(WINDOW, (0, 1), (0, 1))} for key in known}
    lam = exact_divisor_bound(a, b, target, partition, pool)
    false_cap = max((len(partition[key[2]]) - total[key]
                     for key in active), default=0)
    finite_contraction = false_cap * Fraction(lam, len(pool) - factors + 1) ** factors
    assert finite_contraction <= Fraction(1, 4), finite_contraction
    trace = []
    while active:
        assert len(trace) <= len(known).bit_length() + 1
        start = set(active)
        available = list(pool)
        d, q = 3, 1
        base = {key: len(partition[key[2]]) for key in active}
        stage = []
        for step in range(factors):
            candidates = {}
            for prime in available:
                dp, qp = (d * prime, q) if step < freeze else (d, q * prime)
                candidates[prime] = {key: oracle.union(key, dp, qp)
                                     for key in sorted(active)}
            chosen = min(available, key=lambda prime:
                         (sum(candidates[prime].values()), prime))
            selected = candidates[chosen]
            old_false = sum(base[key] - total[key] for key in active)
            new_false = sum(selected[key] - total[key] for key in active)
            assert new_false >= 0
            assert len(available) * new_false <= lam * old_false
            if step < freeze:
                d *= chosen
            else:
                q *= chosen
            available.remove(chosen)
            stage.append((chosen, d, q, old_false, new_false))
            base = selected
        assert sum(base[key] - total[key] for key in active) <= Fraction(len(active), 4)
        certified = {key for key in active if base[key] == total[key]}
        assert 4 * len(certified) >= 3 * len(active)
        for parity in product((0, 1), repeat=2):
            for key in sorted(certified):
                for ell in WINDOW:
                    answer[key][(ell,) + parity] = oracle.count(key, ell, d, q, parity)
        active -= certified
        trace.append((len(start), tuple(stage), len(active)))
    # This final comparison is independent of modular arithmetic and does
    # not participate in any prime selection or certification decision.
    for key in known:
        i, j, z = key
        expected = Counter((a[i][k] + b[k][j] - target[i][j],
                            alpha[i][k], beta[k][j]) for k in partition[z])
        for group, value in answer[key].items():
            assert value == expected[group]
    return answer, trace, oracle


def exact_counts(a, b, target, block_size=3, pool=POOL, factors=3,
                 freeze=1, actual_middle=None):
    """Signed joint shifts followed by the actual window induction."""
    middle = len(b) if actual_middle is None else actual_middle
    partition = blocks(middle, block_size)
    a_shift = max(0, -min(map(min, a)))
    b_shift = max(0, -min(map(min, b)), -min(map(min, target)) - a_shift)
    aa = [[value + a_shift for value in row] for row in a]
    bb = [[value + b_shift for value in row] for row in b]
    tt = [[value + a_shift + b_shift for value in row] for row in target]
    assert min(map(min, aa)) >= 0 and min(map(min, bb)) >= 0 and min(map(min, tt)) >= 0
    depth = max(max(map(max, matrix)) for matrix in (aa, bb, tt)).bit_length()
    old_a = [[0] * len(b) for _ in a]
    old_b = [[0] * len(target[0]) for _ in b]
    old_t = [[0] * len(target[0]) for _ in a]
    known = {(i, j, z): (0, len(block), 0)
             for i, j, (z, block) in product(range(len(a)), range(len(target[0])),
                                             enumerate(partition))}
    levels = []
    for shift in reversed(range(depth)):
        new_a, new_b, new_t = ([[value >> shift for value in row] for row in matrix]
                                for matrix in (aa, bb, tt))
        alpha = [[new - 2 * old for new, old in zip(nr, oldr)]
                 for nr, oldr in zip(new_a, old_a)]
        beta = [[new - 2 * old for new, old in zip(nr, oldr)]
                for nr, oldr in zip(new_b, old_b)]
        gamma = [[new - 2 * old for new, old in zip(nr, oldr)]
                 for nr, oldr in zip(new_t, old_t)]
        refined, trace, oracle = purify(old_a, old_b, old_t, partition, known,
                                        alpha, beta, pool, factors, freeze)
        next_counts = {}
        for key in known:
            i, j, _ = key
            next_counts[key] = tuple(sum(
                count for (ell, bit_a, bit_b), count in refined[key].items()
                if 2 * ell + bit_a + bit_b - gamma[i][j] == value)
                for value in WINDOW)
            if sum(known[key]) == 0:
                assert next_counts[key] == (0, 0, 0)
        assert next_counts == direct_windows(new_a, new_b, new_t, partition)
        levels.append((trace, oracle.coefficient_checks,
                       oracle.saw_nontrivial_fiber, oracle.saw_masked_zeros))
        known = next_counts
        old_a, old_b, old_t = new_a, new_b, new_t
    result = [[sum(known[i, j, z][1] for z in range(len(partition)))
               for j in range(len(target[0]))] for i in range(len(a))]
    expected = [[sum(a[i][k] + b[k][j] == target[i][j] for k in range(middle))
                 for j in range(len(target[0]))] for i in range(len(a))]
    assert result == expected
    return result, levels


class ExactCountingChecks(unittest.TestCase):
    def test_signed_window_closure_exhaustive(self):
        for gap, alpha, beta, gamma in product(range(-12, 13), (0, 1), (0, 1), (0, 1)):
            new_gap = 2 * gap + alpha + beta - gamma
            if gap not in WINDOW:
                self.assertNotIn(new_gap, WINDOW)
        self.assertEqual(2 * (-2) + 1 + 1 - 0, -2)
        self.assertEqual(2 * 2 + 0 + 0 - 1, 3)

    def test_every_old_gap_and_parity_target_bit(self):
        # Original matrices realize all 3*2*2*2 local refinement states.
        for ell, alpha, beta, gamma in product(WINDOW, (0, 1), (0, 1), (0, 1)):
            a, b, t = [[ell]], [[0]], [[0]]
            known = direct_windows(a, b, t, [(0,)])
            refined, _, _ = purify(a, b, t, [(0,)], known, [[alpha]], [[beta]])
            self.assertEqual(refined[0, 0, 0][ell, alpha, beta], 1)
            new = 2 * ell + alpha + beta - gamma
            self.assertEqual(sum(count for (old, x, y), count in refined[0, 0, 0].items()
                                 if 2 * old + x + y - gamma == new), 1)

    def test_actual_greedy_selection_needs_two_restarts(self):
        pool = (5, 7, 11, 13, 17)
        pairs = list(combinations(pool, 2))
        a = [[0, 3 * p * q] for p, q in pairs]
        b, target = [[0], [0]], [[0] for _ in a]
        alpha, beta = [[i % 2, 1] for i in range(len(a))], [[0], [1]]
        known = direct_windows(a, b, target, [(0, 1)])
        result, trace, oracle = purify(a, b, target, [(0, 1)], known, alpha, beta,
                                       pool=pool, factors=2, freeze=1)
        self.assertEqual([entry[0::2] for entry in trace], [(10, 1), (1, 0)])
        self.assertEqual([step[0] for step in trace[0][1]], [5, 7])
        self.assertGreater(trace[0][1][-1][-1], 0)
        self.assertTrue(oracle.saw_nontrivial_fiber)
        self.assertTrue(oracle.saw_masked_zeros)
        self.assertTrue(all(sum(values.values()) == 1 for values in result.values()))

    def test_signed_target_counts_all_residue_classes(self):
        a = [[-12, -1, 0, 1, 15, 36, 84], [4, 3, 2, 1, 0, -1, -2]]
        b = [[0, k - 3] for k in range(7)]
        target = [[0, -7], [3, 8]]
        partition = blocks(7, 3)
        alpha = [[value % 2 for value in row] for row in a]
        beta = [[value % 2 for value in row] for row in b]
        known = direct_windows(a, b, target, partition)
        _, _, oracle = purify(a, b, target, partition, known, alpha, beta)
        self.assertTrue(oracle.saw_negative_target)
        self.assertGreater(oracle.coefficient_checks, 0)

    def test_signed_joint_shifts_and_arbitrary_targets(self):
        a = [[-11, -11, 7, 4, -3], [9, 2, -7, 0, 8]]
        b = [[-5, 4, 0], [-5, 4, 0], [3, -8, 0], [6, 0, 0], [2, 5, 0]]
        target = [[-16, -7, 4], [0, 6, -7]]
        result, levels = exact_counts(a, b, target, block_size=3)
        self.assertEqual(result[0][0], 2)
        self.assertTrue(any(level[2] for level in levels))
        self.assertTrue(any(level[3] for level in levels))

    def test_duplicate_labels_zero_base_and_uneven_last_block(self):
        result, levels = exact_counts([[0] * 7] * 2, [[0, 0]] * 7,
                                      [[0, 0], [0, 0]], block_size=3)
        self.assertEqual(result, [[7, 7], [7, 7]])
        self.assertEqual(levels, [])
        exact_counts([[5] * 7] * 2, [[-3, 2]] * 7,
                     [[2, 7], [3, 8]], block_size=3)

    def test_padded_middle_entries_are_absent(self):
        # Three appended numerical zeros would be false additional labels
        # unless the partition explicitly omits them from encoded matrices.
        a, b, target = [[0] * 8], [[0]] * 8, [[0]]
        result, _ = exact_counts(a, b, target, actual_middle=5, block_size=3)
        self.assertEqual(result, [[5]])
        result, _ = exact_counts([[2] * 5 + [0] * 3], b, [[2]],
                                  actual_middle=5, block_size=3)
        self.assertEqual(result, [[5]])

    def test_random_original_matrix_induction(self):
        rng = Random(734186)
        checks = 0
        for fixture in range(120):
            rows, middle, cols = 1 + fixture % 3, 1 + fixture % 7, 1 + fixture % 4
            a = [[rng.randrange(-35, 36) for _ in range(middle)] for _ in range(rows)]
            b = [[rng.randrange(-35, 36) for _ in range(cols)] for _ in range(middle)]
            target = [[rng.randrange(-60, 61) for _ in range(cols)] for _ in range(rows)]
            if fixture % 2:
                for i, j in product(range(rows), range(cols)):
                    k = rng.randrange(middle)
                    target[i][j] = a[i][k] + b[k][j]
            _, levels = exact_counts(a, b, target, block_size=1 + fixture % 3,
                                      freeze=fixture % 3)
            checks += sum(level[1] for level in levels)
        self.assertGreater(checks, 10000)

    def test_exact_minplus_multiplicities_after_value_computation(self):
        a = [[2, 2, 8, -5, -5], [0, 1, 4, -3, 6]]
        b = [[3, -1], [3, -1], [0, 7], [10, 9], [10, 9]]
        target = [[min(a[i][k] + b[k][j] for k in range(5))
                   for j in range(2)] for i in range(2)]
        result, _ = exact_counts(a, b, target)
        self.assertEqual(result[0], [4, 2])

    def test_coprimality_and_prime_three_exclusion(self):
        a, b, t = [[0]], [[0]], [[0]]
        oracle = FoldedFiberOracle(a, b, t, [(0,)], [[0]], [[0]])
        with self.assertRaises(AssertionError):
            oracle.count((0, 0, 0), 0, 3, 3)
        with self.assertRaises(AssertionError):
            purify(a, b, t, [(0,)], {(0, 0, 0): (0, 1, 0)}, [[0]], [[0]],
                    pool=(3, 5, 7), factors=1)


if __name__ == '__main__':
    unittest.main(verbosity=2)
