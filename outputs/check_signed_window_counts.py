#!/usr/bin/env python3
"""Independent finite audit of the signed-window exact-count lift.

All modular products here are brute-force oracles.  These tests check the
reduction on original matrices; they do not implement or prove the thin
matrix oracle or its asymptotic running time.
"""

from fractions import Fraction
from random import Random
import unittest


WINDOW = (-1, 0, 1)
STATS = {}


def union_count(sums, modulus):
    return sum((value - ell) % modulus == 0
               for value in sums for ell in WINDOW)


class SignedWindowAudit(unittest.TestCase):
    def test_local_backward_closure_and_fixed_factor(self):
        cases = 0
        for old in range(-20, 21):
            for alpha in (0, 1):
                for beta in (0, 1):
                    for gamma in (0, 1):
                        new = 2 * old + alpha + beta - gamma
                        if new in WINDOW:
                            self.assertIn(old, WINDOW)
                        cases += 1
        self.assertEqual(2 * (-2) + 2, -2)
        self.assertEqual(2 * 2 - 1, 3)
        # The factor 3 prevents counting one label in two target classes.
        self.assertEqual(union_count([1], 2), 2)
        for modulus in (3, 6, 15, 21, 105):
            for value in range(-500, 501):
                self.assertIn(union_count([value], modulus), (0, 1))
        STATS['local_bit_cases'] = cases

    def test_signed_original_matrices(self):
        rng = Random(92017)
        instances = updates = cells = modular = 0
        for _ in range(600):
            n, h = rng.randrange(1, 5), rng.randrange(1, 8)
            A = [[rng.randrange(-100, 101) for k in range(h)]
                 for i in range(n)]
            B = [[rng.randrange(-100, 101) for j in range(n)]
                 for k in range(h)]
            T = [[rng.randrange(-100, 101) for j in range(n)]
                 for i in range(n)]
            shift_a = max(0, -min(map(min, A)), -min(map(min, T)))
            shift_b = max(0, -min(map(min, B)))
            AA = [[v + shift_a for v in row] for row in A]
            BB = [[v + shift_b for v in row] for row in B]
            TT = [[v + shift_a + shift_b for v in row] for row in T]
            length = max(max(map(max, AA)), max(map(max, BB)),
                         max(map(max, TT))).bit_length()
            ap = [[0] * h for i in range(n)]
            bp = [[0] * n for k in range(h)]
            tp = [[0] * n for i in range(n)]
            width = rng.randrange(1, h + 1)
            blocks = [list(range(k, min(h, k + width)))
                      for k in range(0, h, width)]
            G = {(i, j, z): [0, len(block), 0]
                 for i in range(n) for j in range(n)
                 for z, block in enumerate(blocks)}
            for bit in reversed(range(length)):
                alpha = [[v >> bit & 1 for v in row] for row in AA]
                beta = [[v >> bit & 1 for v in row] for row in BB]
                gamma = [[v >> bit & 1 for v in row] for row in TT]
                next_G = {}
                for i in range(n):
                    for j in range(n):
                        for z, block in enumerate(blocks):
                            sums = {k: ap[i][k] + bp[k][j] - tp[i][j]
                                    for k in block}
                            old = [sum(s == ell for s in sums.values())
                                   for ell in WINDOW]
                            self.assertEqual(old, G[i, j, z])
                            for modulus in (3, 6, 15, 21, 30, 105, 2310):
                                C = union_count(sums.values(), modulus)
                                union = sum(any((s - ell) % modulus == 0
                                                for ell in WINDOW)
                                            for s in sums.values())
                                self.assertEqual(C, union)
                                self.assertLessEqual(sum(old), C)
                                self.assertLessEqual(C, len(block))
                                if C == sum(old):
                                    for ell in WINDOW:
                                        for a in (0, 1):
                                            for b in (0, 1):
                                                cm = sum(
                                                    (sums[k] - ell) % modulus == 0
                                                    and alpha[i][k] == a
                                                    and beta[k][j] == b
                                                    for k in block)
                                                exact = sum(
                                                    sums[k] == ell
                                                    and alpha[i][k] == a
                                                    and beta[k][j] == b
                                                    for k in block)
                                                self.assertEqual(cm, exact)
                                                modular += 1
                            N = {(ell, a, b): sum(
                                sums[k] == ell and alpha[i][k] == a
                                and beta[k][j] == b for k in block)
                                for ell in WINDOW for a in (0, 1)
                                for b in (0, 1)}
                            fine = [sum(count for (ell, a, b), count in N.items()
                                        if 2 * ell + a + b - gamma[i][j] == r)
                                    for r in WINDOW]
                            brute = [sum(2 * sums[k] + alpha[i][k] + beta[k][j]
                                         - gamma[i][j] == r for k in block)
                                     for r in WINDOW]
                            self.assertEqual(fine, brute)
                            next_G[i, j, z] = fine
                            cells += 1
                G = next_G
                ap = [[2 * ap[i][k] + alpha[i][k] for k in range(h)]
                      for i in range(n)]
                bp = [[2 * bp[k][j] + beta[k][j] for j in range(n)]
                      for k in range(h)]
                tp = [[2 * tp[i][j] + gamma[i][j] for j in range(n)]
                      for i in range(n)]
                updates += 1
            for i in range(n):
                for j in range(n):
                    self.assertEqual(
                        sum(G[i, j, z][1] for z in range(len(blocks))),
                        sum(A[i][k] + B[k][j] == T[i][j] for k in range(h)))
            instances += 1
        STATS.update(signed_matrix_instances=instances, prefix_updates=updates,
                     incidence_updates=cells, certified_masked_counts=modular)

    def test_common_prime_greedy_purification(self):
        rng = Random(9981)
        primes = [p for p in range(101, 200)
                  if all(p % d for d in range(2, int(p ** .5) + 1))]
        h, rounds = 12, 2
        # Every false label has at most two candidate prime divisors.
        ratio = Fraction(2, len(primes) - rounds + 1)
        self.assertLessEqual(h * ratio ** rounds, Fraction(1, 4))
        values = []
        for row in range(160):
            entries = []
            for k in range(h):
                ell = rng.choice(WINDOW)
                if k < row % 5:
                    entries.append(ell)
                else:
                    p, q = rng.sample(primes, 2)
                    entries.append(ell + rng.choice((-1, 1)) * 3 * p * q)
            values.append(entries)
        genuine = [sum(v in WINDOW for v in row) for row in values]
        active = list(range(len(values)))
        stages = calls = 0
        while active:
            old_size = len(active)
            d, used = 3, set()
            old_false = sum(h - genuine[x] for x in active)
            for _ in range(rounds):
                candidates = []
                for p in primes:
                    if p in used:
                        continue
                    counts = [union_count(values[x], d * p) for x in active]
                    candidates.append((sum(counts), p, counts))
                    calls += 1
                _, p, counts = min(candidates)
                false = sum(C - genuine[x] for C, x in zip(counts, active))
                self.assertLessEqual(false, ratio * old_false)
                d *= p
                used.add(p)
                old_false = false
            self.assertLessEqual(old_false, Fraction(old_size, 4))
            for C, x in zip(counts, active):
                if C == genuine[x]:
                    for ell in WINDOW:
                        self.assertEqual(
                            sum((v - ell) % d == 0 for v in values[x]),
                            sum(v == ell for v in values[x]))
            active = [x for C, x in zip(counts, active) if C != genuine[x]]
            self.assertLessEqual(len(active), Fraction(old_size, 4))
            stages += 1
            self.assertLess(stages, 20)
        STATS.update(greedy_initial_incidences=len(values),
                     greedy_stages=stages, candidate_calls=calls)


if __name__ == '__main__':
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(SignedWindowAudit)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    print(STATS)
    raise SystemExit(not result.wasSuccessful())
