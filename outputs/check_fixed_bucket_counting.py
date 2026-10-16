#!/usr/bin/env python3
"""Finite fixed-original-bucket #3SUM audit using actual folded histograms.

The matrix products are evaluated directly from their sparse coefficient
arrays. This checks the reduction, not the fast thin-product algorithm.
"""

from collections import Counter, defaultdict
from itertools import combinations
from math import gcd, isqrt
from random import Random
import unittest


WINDOW = (-1, 0, 1)
STATS = Counter()


def primes(lo, hi):
    return [p for p in range(max(2, lo), hi + 1)
            if all(p % d for d in range(2, isqrt(p) + 1))]


def buckets(values, modulus, size):
    by_residue = defaultdict(list)
    for value in sorted(values):
        by_residue[value % modulus].append(value)
    result, residues = [], []
    for residue, items in sorted(by_residue.items()):
        for start in range(0, len(items), size):
            result.append(items[start:start + size])
            residues.append(residue)
    return result, residues


def fixed_instance(A, B, C, size, supplied_bucket_prime=None):
    ca, cb, cc = Counter(A), Counter(B), Counter(C)
    n = max(len(A), len(B), len(C))
    radius = (n + size - 1) // size
    pool = primes(radius, 2 * radius)
    def energy(p):
        ac = Counter(v % p for v in ca)
        bc = Counter(v % p for v in cb)
        return sum(v * v for v in ac.values()) + sum(v * v for v in bc.values())
    r = (min(pool, key=lambda p: (energy(p), p)) if supplied_bucket_prime is None
         else supplied_bucket_prime)
    assert r in pool
    aa, ar = buckets(ca, r, size)
    bb, br = buckets(cb, r, size)
    queries = [(i, j, z) for z in sorted(cc)
               for i in range(len(aa)) for j in range(len(bb))
               if (ar[i] + br[j] - z) % r == 0]
    return ca, cb, cc, aa, bb, queries, r


class FoldedHistogramProduct:
    """One d-folded product over the cyclic coefficient ring of length q."""

    def __init__(self, aa, bb, ap, bp, d, q, wa=None, wb=None,
                 alpha=None, beta=None, mask=None):
        assert gcd(d, q) == 1
        self.d, self.q = d, q
        self.d1 = isqrt(d - 1) + 1
        self.d2 = (d + self.d1 - 1) // self.d1
        self.X, self.Y = {}, {}
        for side, parts, prefix, weights, bits, width in (
                ('A', aa, ap, wa, alpha, self.d1),
                ('B', bb, bp, wb, beta, self.d2)):
            for label, part in enumerate(parts):
                hist = Counter()
                for original in part:
                    wanted = None if mask is None else mask[side == 'B']
                    if wanted is None or bits[original] == wanted:
                        hist[prefix[original] % d, prefix[original] % q] += (
                            1 if weights is None else weights[original])
                for rho in range(width):
                    entries = defaultdict(Counter)
                    for (residue, coefficient), count in hist.items():
                        sigma = ((residue - rho) if side == 'A'
                                 else (self.d1 * rho - residue)) % d
                        entries[sigma][coefficient] += count
                    (self.X if side == 'A' else self.Y)[label, rho] = entries
        STATS['folded_products'] += 1

    def query(self, i, j, target):
        residue = target % self.d
        rho1, rho2 = residue % self.d1, residue // self.d1
        X, Y = self.X[i, rho1], self.Y[j, rho2]
        result = 0
        for sigma in X.keys() & Y.keys():
            for left_degree, left in X[sigma].items():
                for right_degree, right in Y[sigma].items():
                    if (left_degree + right_degree - target) % self.q == 0:
                        result += left * right
        STATS['coefficient_queries'] += 1
        return result


def count_fixed_prefixes(A, B, C, size, supplied_bucket_prime=None):
    if not A or not B or not C:
        return 0
    ca, cb, cc, aa, bb, queries, r = fixed_instance(
        A, B, C, size, supplied_bucket_prime)
    shift_a = max(0, -min(ca), -min(cc))
    shift_b = max(0, -min(cb))
    full_a = {x: x + shift_a for x in ca}
    full_b = {y: y + shift_b for y in cb}
    full_c = {z: z + shift_a + shift_b for z in cc}
    length = max(*full_a.values(), *full_b.values(), *full_c.values()).bit_length()
    ap, bp, cp = ({x: 0 for x in full_a}, {y: 0 for y in full_b},
                  {z: 0 for z in full_c})
    G = [[0, len(aa[i]) * len(bb[j]), 0] for i, j, z in queries]
    final = [0] * len(queries)
    if length == 0:
        final = [sum(ca[x] for x in aa[i]) * sum(cb[y] for y in bb[j])
                 for i, j, z in queries]
    # Small random tests use two factors whose full product exceeds their
    # nonzero gaps. A separate structured large-gap case forces restarts.
    # The general prime-scale proof is in the accompanying note.
    prime_pool = [p for p in primes(5, 37) if p not in (r, 3)]
    for bit in reversed(range(length)):
        alpha = {x: value >> bit & 1 for x, value in full_a.items()}
        beta = {y: value >> bit & 1 for y, value in full_b.items()}
        gamma = {z: value >> bit & 1 for z, value in full_c.items()}
        active = [index for index, counts in enumerate(G) if sum(counts)]
        next_G = [[0, 0, 0] for _ in queries]
        while active:
            d, q, used = 3, 1, set()
            selected_counts = None
            for round_index in range(2):
                choices = []
                for p in prime_pool:
                    if p in used:
                        continue
                    cd, cq = (d * p, q) if round_index == 0 else (d, q * p)
                    product = FoldedHistogramProduct(aa, bb, ap, bp, cd, cq)
                    counts = [sum(product.query(i, j, cp[z] + ell)
                                  for ell in WINDOW)
                              for index in active for i, j, z in [queries[index]]]
                    for count, index in zip(counts, active):
                        assert sum(G[index]) <= count <= size * size
                    choices.append((sum(counts), p, cd, cq, counts))
                _, p, d, q, selected_counts = min(choices)
                used.add(p)
            marked = [index for count, index in zip(selected_counts, active)
                      if count == sum(G[index])]
            assert marked
            assert len(active) - len(marked) <= len(active) / 4
            if len(marked) < len(active):
                STATS['nonempty_restart_sets'] += 1
            classes = {index: {} for index in marked}
            weighted_classes = {index: {} for index in marked}
            for abit in (0, 1):
                for bbit in (0, 1):
                    product = FoldedHistogramProduct(
                        aa, bb, ap, bp, d, q, alpha=alpha, beta=beta,
                        mask=(abit, bbit))
                    weighted = None
                    if bit == 0:
                        weighted = FoldedHistogramProduct(
                            aa, bb, ap, bp, d, q, wa=ca, wb=cb,
                            alpha=alpha, beta=beta, mask=(abit, bbit))
                    for index in marked:
                        i, j, z = queries[index]
                        for ell in WINDOW:
                            value = product.query(i, j, cp[z] + ell)
                            exact = sum(ap[x] + bp[y] - cp[z] == ell
                                        and alpha[x] == abit and beta[y] == bbit
                                        for x in aa[i] for y in bb[j])
                            assert value == exact
                            classes[index][ell, abit, bbit] = value
                            if weighted is not None:
                                weighted_classes[index][ell, abit, bbit] = (
                                    weighted.query(i, j, cp[z] + ell))
            for index in marked:
                i, j, z = queries[index]
                next_G[index] = [sum(value for (ell, abit, bbit), value
                                    in classes[index].items()
                                    if 2 * ell + abit + bbit - gamma[z] == gap)
                                 for gap in WINDOW]
                if bit == 0:
                    final[index] = sum(value for (ell, abit, bbit), value
                                       in weighted_classes[index].items()
                                       if 2 * ell + abit + bbit - gamma[z] == 0)
            active = [index for index in active if index not in classes]
            STATS['purification_stages'] += 1
        G = next_G
        ap = {x: 2 * ap[x] + alpha[x] for x in ap}
        bp = {y: 2 * bp[y] + beta[y] for y in bp}
        cp = {z: 2 * cp[z] + gamma[z] for z in cp}
        for index, (i, j, z) in enumerate(queries):
            assert G[index] == [sum(ap[x] + bp[y] - cp[z] == ell
                                    for x in aa[i] for y in bb[j])
                                for ell in WINDOW]
        STATS['prefix_levels'] += 1
    result = Counter()
    for (i, j, z), count in zip(queries, final):
        result[z] += count
    for z in cc:
        assert result[z] == sum(ca[x] * cb[y] for x in ca for y in cb if x + y == z)
    STATS['fixed_incidences'] += len(queries)
    return sum(cc[z] * result[z] for z in cc)


class FixedBucketCountingTests(unittest.TestCase):
    def test_empty_inputs_and_coalesced_prefixes(self):
        for A, B, C in (([], [0], [0]), ([0], [], [0]), ([0], [0], [])):
            self.assertEqual(count_fixed_prefixes(A, B, C, 2), 0)
        self.assertEqual(count_fixed_prefixes([0], [0], [1], 1), 0)
        # All four ORIGINAL value pairs coalesce to one prefix-sum entry.
        aa, bb = [[0, 2]], [[0, 2]]
        prefix = {0: 0, 2: 0}
        product = FoldedHistogramProduct(aa, bb, prefix, prefix, 3, 5)
        self.assertEqual(product.query(0, 0, 0), 4)
        self.assertEqual(count_fixed_prefixes([0, 2], [0, 2], [2], 2), 2)
        STATS['empty_input_fixtures'] += 3

    def test_incidence_multiplicity_in_greedy_score(self):
        # The original targets 0 and 11 are different incidences but have
        # identical prefixes. The third target gives a different score.
        aa, bb = [[0]], [[0, 198, 484, 869]]
        original_targets = [0, 11, 198]
        ap = {0: 0}
        bp = {v: v // 32 for v in bb[0]}
        cp = {z: z // 32 for z in original_targets}
        scores, incorrectly_deduplicated = [], []
        for p in (5, 7):
            product = FoldedHistogramProduct(aa, bb, ap, bp, 3, p)
            score = sum(product.query(0, 0, cp[z] + ell)
                        for z in original_targets for ell in WINDOW)
            dedup = sum(product.query(0, 0, prefix + ell)
                        for prefix in sorted(set(cp.values())) for ell in WINDOW)
            scores.append(score)
            incorrectly_deduplicated.append(dedup)
        self.assertEqual(scores, [5, 4])
        self.assertEqual(incorrectly_deduplicated, [3, 3])
        self.assertEqual(min(zip(scores, (5, 7)))[1], 7)
        self.assertEqual(min(zip(incorrectly_deduplicated, (5, 7)))[1], 5)
        STATS['incidence_multiplicity_regressions'] += 1

    def test_folded_histogram_identity(self):
        rng = Random(9941)
        for _ in range(60):
            A = [rng.randrange(-12, 13) for _ in range(8)]
            B = [rng.randrange(-12, 13) for _ in range(9)]
            C = [rng.randrange(-12, 13) for _ in range(7)]
            ca, cb, cc, aa, bb, queries, r = fixed_instance(A, B, C, 3)
            ap = {x: (x + 12) // 4 for x in ca}
            bp = {y: (y + 12) // 4 for y in cb}
            alpha = {x: (x + 12) >> 1 & 1 for x in ca}
            beta = {y: (y + 12) >> 1 & 1 for y in cb}
            for d, q in ((3, 1), (3, 5), (6, 5), (15, 7)):
                for mask in (None, (0, 0), (0, 1), (1, 0), (1, 1)):
                    product = FoldedHistogramProduct(
                        aa, bb, ap, bp, d, q, wa=ca, wb=cb,
                        alpha=alpha, beta=beta, mask=mask)
                    for i, j, z in queries:
                        for target in (-1, 0, 1, 5, 9):
                            exact = sum(ca[x] * cb[y]
                                        for x in aa[i] for y in bb[j]
                                        if (ap[x] + bp[y] - target) % (d * q) == 0
                                        and (mask is None or (alpha[x], beta[y]) == mask))
                            self.assertEqual(product.query(i, j, target), exact)
                            STATS['direct_histogram_identities'] += 1

    def test_complete_original_sets(self):
        rng = Random(7297)
        for _ in range(50):
            A = rng.sample(range(-20, 21), rng.randrange(1, 10))
            B = rng.sample(range(-20, 21), rng.randrange(1, 10))
            C = rng.sample(range(-20, 21), rng.randrange(1, 10))
            actual = count_fixed_prefixes(A, B, C, rng.randrange(1, 4))
            self.assertEqual(actual, sum(x + y == z for x in A for y in B for z in C))
            STATS['complete_set_instances'] += 1

    def test_complete_occurrence_lists(self):
        rng = Random(881)
        fixtures = [([0] * 8, [0] * 7, [0] * 9),
                    ([1, 1, -2], [1, 1, -2], [-1, -1, 2]),
                    ([-4, -4, -3, -2], [1, 2, 2, 3], [-3, -2, -1, -1, 0])]
        fixtures += [([rng.randrange(-10, 11) for _ in range(rng.randrange(1, 10))],
                      [rng.randrange(-10, 11) for _ in range(rng.randrange(1, 10))],
                      [rng.randrange(-10, 11) for _ in range(rng.randrange(1, 10))])
                     for _ in range(35)]
        for A, B, C in fixtures:
            actual = count_fixed_prefixes(A, B, C, rng.randrange(1, 4))
            self.assertEqual(actual, sum(x + y == z for x in A for y in B for z in C))
            STATS['complete_occurrence_instances'] += 1

    def test_complete_sets_with_actual_restart(self):
        # A supplied bucket prime is acceptable once its same energy bound
        # is verified. Here r=37 is in [ceil(n/s),2ceil(n/s)] and every
        # original residue bucket contains exactly two A values. The full
        # original-prefix pipeline is unchanged after this bucket choice.
        r, size = 37, 2
        pool = [p for p in primes(5, 37) if p != r]
        A, C = [], []
        for index, (p, q) in enumerate(combinations(pool, 2)):
            target = r * 100000 * index + index
            A.extend((target, target + 6 * r * p * q))
            C.append(target)
        B = [0]
        energy = sum(v * v for v in Counter(x % r for x in A).values()) + 1
        self.assertEqual(energy, 2 * len(A) + 1)
        before = STATS['nonempty_restart_sets']
        actual = count_fixed_prefixes(A, B, C, size, supplied_bucket_prime=r)
        self.assertEqual(actual, len(C))
        self.assertGreater(STATS['nonempty_restart_sets'], before)
        STATS['structured_restart_instances'] += 1


if __name__ == '__main__':
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(FixedBucketCountingTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    print(dict(STATS))
    raise SystemExit(not result.wasSuccessful())
