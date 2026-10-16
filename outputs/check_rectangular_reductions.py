#!/usr/bin/env python3
"""Finite checks for rectangular convolution and singleton witness decoding.

These use brute-force product oracles. They verify the index and decoding
reductions, including exact fallback under adversarial random outcomes, not
the asymptotic data structure or its probability/running-time analysis.
Only the Python standard library is required.
"""

from fractions import Fraction
from itertools import product
from random import Random
import unittest


def rectangular_convolution(a, b, s):
    n = len(a)
    assert n == len(b) and 1 <= s <= n
    r = (n + s - 1) // s
    magnitude = max(map(abs, a + b))
    sentinel = 3 * magnitude + 1
    q = [[b[s * u + v] if s * u + v < n else sentinel
          for v in range(s)] for u in range(r)]
    out = [None] * (2 * n - 1)
    for z in range(s):
        p = [[a[s * d + z - v] if 0 <= s * d + z - v < n else sentinel
              for v in range(s)] for d in range(r + 1)]
        f = [[min(p[d][v] + q[u][v] for v in range(s))
              for u in range(r)] for d in range(r + 1)]
        for w in range(2 * r):
            k = s * w + z
            if k < 2 * n - 1:
                out[k] = min(f[w - u][u] for u in range(r)
                             if 0 <= w - u <= r)
    return out


def direct_convolution(a, b):
    n = len(a)
    return [min(a[i] + b[k - i]
                for i in range(max(0, k - n + 1), min(n - 1, k) + 1))
            for k in range(2 * n - 1)]


def masked_folded_counts(ac, cb, ab, block, mask, prime):
    """Two explicit folded products: modular count and sum of global labels."""
    na, nb = len(ac), len(cb[0])
    p1 = 1
    while p1 * p1 < prime:
        p1 += 1
    p2 = (prime + p1 - 1) // p1
    middle = [(c, sigma) for c in block for sigma in range(prime)]
    x = [[int(c in mask and sigma == (ac[a][c] + rho1) % prime)
          for c, sigma in middle]
         for a in range(na) for rho1 in range(p1)]
    y = [[int(sigma == (-cb[c][b] - p1 * rho2) % prime)
          for b in range(nb) for rho2 in range(p2)]
         for c, sigma in middle]
    counts, labels = [], []
    for a in range(na):
        count_row, label_row = [], []
        for b in range(nb):
            rho = ab[a][b] % prime
            rho1, rho2 = rho % p1, rho // p1
            row, col = a * p1 + rho1, b * p2 + rho2
            count_row.append(sum(x[row][v] * y[v][col]
                                 for v in range(len(middle))))
            label_row.append(sum(x[row][v] * (c + 1) * y[v][col]
                                 for v, (c, _) in enumerate(middle)))
        counts.append(count_row)
        labels.append(label_row)
    return counts, labels


def isolated_all_edges(ac, cb, ab, block_size, filter_primes, trials):
    """Explicit reduction for arbitrary supplied masks/primes, even all bad.

    Each trial is (prime, retained-global-index-set). The same trial may be
    shared across blocks. The implementation keeps the exact fallback.
    """
    na, nc, nb = len(ac), len(cb), len(cb[0])
    assert filter_primes and block_size > 0
    found = [[False] * nb for _ in range(na)]
    decoded = fallback_checks = 0
    for start in range(0, nc, block_size):
        block = list(range(start, min(start + block_size, nc)))
        passes = [[not found[a][b] for b in range(nb)] for a in range(na)]
        for prime in filter_primes:
            counts, _ = masked_folded_counts(ac, cb, ab, block, set(block), prime)
            for a in range(na):
                for b in range(nb):
                    passes[a][b] &= counts[a][b] > 0
        for prime, mask in trials:
            counts, labels = masked_folded_counts(ac, cb, ab, block, mask, prime)
            for a in range(na):
                for b in range(nb):
                    if found[a][b] or counts[a][b] != 1:
                        continue
                    c = labels[a][b] - 1
                    assert c in block and c in mask
                    if ac[a][c] + cb[c][b] + ab[a][b] == 0:
                        found[a][b] = True
                        decoded += 1
        for a in range(na):
            for b in range(nb):
                if found[a][b] or not passes[a][b]:
                    continue
                for c in block:
                    fallback_checks += 1
                    if ac[a][c] + cb[c][b] + ab[a][b] == 0:
                        found[a][b] = True
                        break
    return found, decoded, fallback_checks


class RectangularReductionTests(unittest.TestCase):
    def test_rectangular_all_digit_widths(self):
        rng = Random(71013)
        checks = 0
        for n in range(1, 65):
            for s in range(1, n + 1):
                for _ in range(2):
                    a = [rng.randrange(-50, 51) for _ in range(n)]
                    b = [rng.randrange(-50, 51) for _ in range(n)]
                    self.assertEqual(rectangular_convolution(a, b, s),
                                     direct_convolution(a, b), (n, s))
                    checks += 1
        self.assertEqual(checks, 4160)

    def test_convolution_negative_sentinel_and_endpoints(self):
        for a, b in [([-2, 2], [-2, 2]), ([0], [0]),
                     ([-100, 0, 100], [100, 0, -100])]:
            for s in range(1, len(a) + 1):
                self.assertEqual(rectangular_convolution(a, b, s),
                                 direct_convolution(a, b))

    def test_masked_folded_count_and_label_products(self):
        rng = Random(20261013)
        for _ in range(60):
            na, nb, nc = rng.randrange(1, 4), rng.randrange(1, 4), rng.randrange(1, 7)
            ac = [[rng.randrange(-9, 10) for _ in range(nc)] for _ in range(na)]
            cb = [[rng.randrange(-9, 10) for _ in range(nb)] for _ in range(nc)]
            ab = [[rng.randrange(-9, 10) for _ in range(nb)] for _ in range(na)]
            block = list(range(rng.randrange(nc), nc))
            for prime in [2, 3, 5, 7]:
                mask = {c for c in block if rng.randrange(2)}
                counts, labels = masked_folded_counts(ac, cb, ab, block, mask, prime)
                for a in range(na):
                    for b in range(nb):
                        exact = [c for c in block if c in mask and
                                 (ac[a][c] + cb[c][b] + ab[a][b]) % prime == 0]
                        self.assertEqual(counts[a][b], len(exact))
                        self.assertEqual(labels[a][b], sum(c + 1 for c in exact))

    def test_arbitrary_failed_isolation_preserves_exactness(self):
        rng = Random(713)
        for _ in range(100):
            na, nb, nc = rng.randrange(1, 4), rng.randrange(1, 4), rng.randrange(1, 6)
            ac = [[rng.randrange(-5, 6) for _ in range(nc)] for _ in range(na)]
            cb = [[rng.randrange(-5, 6) for _ in range(nb)] for _ in range(nc)]
            ab = [[rng.randrange(-5, 6) for _ in range(nb)] for _ in range(na)]
            expected = [[any(ac[a][c] + cb[c][b] + ab[a][b] == 0 for c in range(nc))
                         for b in range(nb)] for a in range(na)]
            for trials in [[], [(2, set())], [(2, set(range(nc)))],
                           [(3, {c for c in range(nc) if rng.randrange(2)})]]:
                actual, _, _ = isolated_all_edges(ac, cb, ab, rng.randrange(1, nc + 1), [2, 3], trials)
                self.assertEqual(actual, expected)

    def test_false_singleton_rejected_and_all_failed_fallback(self):
        # A false modular singleton must not be accepted.
        actual, decoded, scans = isolated_all_edges([[6]], [[0]], [[0]], 1, [2, 3], [(2, {0})])
        self.assertEqual(actual, [[False]])
        self.assertEqual(decoded, 0)
        self.assertEqual(scans, 1)
        # Multiple true witnesses evade an unmasked singleton test; exact fallback remains.
        actual, decoded, scans = isolated_all_edges([[0, 0]], [[0], [0]], [[0]], 2, [2, 3], [(5, {0, 1})])
        self.assertEqual(actual, [[True]])
        self.assertEqual(decoded, 0)
        self.assertGreater(scans, 0)
        # Different false witnesses may pass different original primes.
        actual, decoded, scans = isolated_all_edges([[2, 3]], [[0], [0]], [[0]], 2, [2, 3], [])
        self.assertEqual(actual, [[False]])
        self.assertEqual(scans, 2)

    def test_isolated_true_singletons_avoid_fallback_for_all_multiplicities(self):
        for z in range(1, 9):
            sums = [0] * z + [101, 103]
            ac, cb, ab = [sums], [[0] for _ in sums], [[0]]
            for retained in range(z):
                actual, decoded, scans = isolated_all_edges(ac, cb, ab, len(sums), [2, 3],
                                                            [(7, {retained, z, z + 1})])
                self.assertEqual(actual, [[True]])
                self.assertEqual(decoded, 1)
                self.assertEqual(scans, 0)

    def test_dyadic_singleton_probability_finite_exact_counts(self):
        # Exact finite probabilities support the masking formula; they do not
        # substitute for its all-z analytic proof.
        for z in range(1, 129):
            level = (z - 1).bit_length()
            probability = Fraction(1, 2**level)
            singleton = z * probability * (1 - probability)**(z - 1)
            self.assertGreaterEqual(singleton, Fraction(1, 4))
        for z in range(1, 9):
            probability = Fraction(1, 2**((z - 1).bit_length()))
            exhaustive = sum(probability**sum(mask) * (1-probability)**(z-sum(mask))
                             for mask in product([0, 1], repeat=z) if sum(mask) == 1)
            self.assertEqual(exhaustive, z * probability * (1-probability)**(z-1))


if __name__ == '__main__':
    unittest.main(verbosity=2)
