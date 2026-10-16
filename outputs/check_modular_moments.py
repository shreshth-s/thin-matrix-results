#!/usr/bin/env python3
"""Finite oracles for the deterministic conditional-moment reductions.

This uses direct arithmetic and convolution coefficients on small instances:
the 3SUM decision certificate, and the per-pair certificates that give
all-edges Exact Triangle answers. It checks identities and decision paths,
not the asymptotic fast algorithm. Only the Python standard library is needed.
"""
from itertools import combinations, permutations, product
from math import prod
from random import Random
import unittest


def subbuckets(values, bucket_prime, size):
    result = []
    for residue in range(bucket_prime):
        bucket = [x for x in values if x % bucket_prime == residue]
        for start in range(0, len(bucket), size):
            result.append((residue, bucket[start:start + size]))
    return result


def subqueries(a, b, c, bucket_prime, size):
    return [(z, alpha, beta)
            for ia, alpha in subbuckets(a, bucket_prime, size)
            for ib, beta in subbuckets(b, bucket_prime, size)
            for z in c if (ia + ib - z) % bucket_prime == 0]


def pair_count(query, prime):
    z, alpha, beta = query
    return sum((x + y - z) % prime == 0 for x in alpha for y in beta)


def direct_objective(a, b, c, bucket_prime, size, primes):
    return sum(prod(pair_count(query, p) for p in primes)
               for query in subqueries(a, b, c, bucket_prime, size))


def crt(residues, moduli):
    assert len(set(moduli)) == len(moduli)
    modulus = prod(moduli)
    return sum(value * (modulus // base)
               * pow(modulus // base, -1, base)
               for value, base in zip(residues, moduli)) % modulus


def convolution_objective(a, b, c, bucket_prime, size, primes):
    """CRT tuple histograms followed by exact queried convolution coefficients."""
    modulus = bucket_prime * prod(primes)
    histograms = []
    for values in (a, b):
        hist = [0] * modulus
        for residue, bucket in subbuckets(values, bucket_prime, size):
            for element_tuple in product(bucket, repeat=len(primes)):
                at = crt((residue,) + element_tuple, (bucket_prime,) + primes)
                hist[at] += 1
        histograms.append(hist)
    a_hist, b_hist = histograms
    return sum(sum(a_hist[i] * b_hist[(z - i) % modulus]
                   for i in range(modulus)) for z in c)


def greedy_decision(a, b, c, bucket_prime, size, candidate_primes, stages):
    """Small direct-objective oracle for both affirmative and scanning paths."""
    chosen = ()
    candidates = tuple(p for p in candidate_primes if p != bucket_prime)
    assert len(set(candidates)) == len(candidates) and len(candidates) >= stages
    upper = max(2, max(map(abs, a), default=0)
                + max(map(abs, b), default=0) + max(map(abs, c), default=0))
    divisor_limit = upper.bit_length()
    previous = direct_objective(a, b, c, bucket_prime, size, ())
    for _ in range(stages):
        remaining = [p for p in candidates if p not in chosen]
        candidates_with_scores = [
            (direct_objective(a, b, c, bucket_prime, size, chosen + (p,)), p)
            for p in remaining
        ]
        objective, prime = min(candidates_with_scores)
        if len(remaining) * objective > divisor_limit * size * size * previous:
            return True, 'affirmative-certificate', chosen, 0
        chosen += (prime,)
        previous = objective
    scanned = 0
    for query in subqueries(a, b, c, bucket_prime, size):
        if all(pair_count(query, p) > 0 for p in chosen):
            scanned += 1
            z, alpha, beta = query
            if any(x + y == z for x in alpha for y in beta):
                assert scanned <= previous
                return True, 'scan', chosen, scanned
    assert scanned <= previous
    return False, 'scan', chosen, scanned


def per_pair_all_edges(A, B, C, block_size, candidate_primes, stages, divisor_bound=None):
    """Per-pair conditional moments for all-edges Exact Triangle on a small
    tripartite instance with S(a, b, c) = A[a][c] + B[c][b] - C[a][b].

    Returns the all-edges answers, the pairs certified without scanning, the
    chosen primes, and the number of scanned pair/blocks. It asserts the
    soundness, leak-control, contraction, and scan-charge inequalities of the
    proof at every stage.
    """
    n, middle = len(A), len(A[0])
    blocks = [tuple(range(i, min(i + block_size, middle)))
              for i in range(0, middle, block_size)]
    pairs = [(a, b) for a in range(n) for b in range(n)]

    def total(a, b, c):
        return A[a][c] + B[c][b] - C[a][b]

    def count(a, b, block, p):
        return sum(total(a, b, c) % p == 0 for c in block)

    def zeros(a, b, block):
        return sum(total(a, b, c) == 0 for c in block)

    nonzero = [total(a, b, c) for a, b in pairs for c in range(middle)
               if total(a, b, c) != 0]
    if divisor_bound is None:
        divisor_bound = max((sum(v % p == 0 for p in candidate_primes)
                             for v in nonzero), default=0)
    assert all(sum(v % p == 0 for p in candidate_primes) <= divisor_bound
               for v in nonzero)
    truth = {pi: any(total(*pi, c) == 0 for c in range(middle)) for pi in pairs}
    weight = {(pi, block): 1 for pi in pairs for block in blocks}
    previous = {pi: len(blocks) for pi in pairs}
    undecided = set(pairs)
    chosen = ()
    certified = set()
    for _ in range(stages):
        remaining = [p for p in candidate_primes if p not in chosen]
        m = len(remaining)
        table = {(pi, p): sum(weight[pi, block] * count(*pi, block, p)
                              for block in blocks)
                 for pi in undecided for p in remaining}
        newly = {pi for pi in undecided
                 if m * min(table[pi, p] for p in remaining)
                 > divisor_bound * block_size * previous[pi]}
        assert all(truth[pi] for pi in newly)                      # soundness
        rest = undecided - newly
        for pi in rest:                                            # leak control
            leak = sum(zeros(*pi, block) * weight[pi, block] for block in blocks)
            assert m * leak <= divisor_bound * block_size * previous[pi]
        objective, prime = min((sum(table[pi, p] for pi in rest), p)
                               for p in remaining)
        assert m * objective <= 2 * divisor_bound * block_size * sum(
            previous[pi] for pi in undecided)                      # contraction
        chosen += (prime,)
        for pi in rest:
            for block in blocks:
                weight[pi, block] *= count(*pi, block, prime)
            previous[pi] = table[pi, prime]
        undecided = rest
        certified |= newly
    answers = {pi: True for pi in certified}
    scanned = 0
    for pi in undecided:
        answers[pi] = False
        for block in blocks:
            if all(count(*pi, block, p) > 0 for p in chosen):
                scanned += 1
                if zeros(*pi, block):
                    answers[pi] = True
                    break
    assert scanned <= sum(previous[pi] for pi in undecided)        # scan charge
    assert answers == truth
    return answers, certified, chosen, scanned


def planted_triangle_instance(rng, n, middle, low, high, planted):
    A = [[rng.randint(low, high) for _ in range(middle)] for _ in range(n)]
    B = [[rng.randint(low, high) for _ in range(n)] for _ in range(middle)]
    C = [[rng.randint(2 * low, 2 * high) for _ in range(n)] for _ in range(n)]
    for _ in range(planted):
        a, b, c0 = rng.randrange(n), rng.randrange(n), rng.randrange(middle)
        C[a][b] = A[a][c0] + B[c0][b]
        for c in rng.sample(range(middle), rng.randrange(0, min(middle, 3) + 1)):
            A[a][c] = C[a][b] - B[c][b]          # zeros in several blocks
    return A, B, C


class ModularMomentChecks(unittest.TestCase):
    def test_signed_crt_objectives(self):
        rng = Random(710316)
        for _ in range(80):
            a = rng.sample(range(-8, 9), rng.randrange(1, 7))
            b = rng.sample(range(-8, 9), rng.randrange(1, 7))
            c = rng.sample(range(-8, 9), rng.randrange(1, 7))
            size = rng.randrange(1, 4)
            for primes in ((5,), (5, 7), (5, 7, 11)):
                self.assertEqual(
                    direct_objective(a, b, c, 3, size, primes),
                    convolution_objective(a, b, c, 3, size, primes))

    def test_pair_multiplicities_are_preserved(self):
        # All four pairs have the same sum mod 5; a Boolean residue-overlap
        # count is only one. The objective must preserve the four pairs.
        a, b, c = [0, 15], [0, 15], [0]
        self.assertEqual(direct_objective(a, b, c, 3, 2, (5,)), 4)
        self.assertEqual(convolution_objective(a, b, c, 3, 2, (5,)), 4)
        self.assertEqual(direct_objective(a, b, c, 3, 2, (5, 7)), 4)
        self.assertEqual(convolution_objective(a, b, c, 3, 2, (5, 7)), 4)

    def test_weighted_contraction_on_no_instances(self):
        rng = Random(710317)
        primes = (5, 7, 11, 13, 17)
        for _ in range(100):
            a = rng.sample(range(-20, 21, 2), 7)
            b = rng.sample(range(-20, 21, 2), 7)
            c = rng.sample(range(-19, 20, 2), 7)
            self.assertFalse(any(x + y == z for x in a for y in b for z in c))
            differences = [x + y - z for x in a for y in b for z in c]
            limit = max(sum(value % p == 0 for p in primes)
                        for value in differences)
            chosen = ()
            previous = direct_objective(a, b, c, 3, 3, chosen)
            for _ in range(3):
                remaining = [p for p in primes if p not in chosen]
                candidates = [(direct_objective(a, b, c, 3, 3, chosen + (p,)), p)
                              for p in remaining]
                objective, selected = min(candidates)
                self.assertLessEqual(len(remaining) * objective, limit * 9 * previous)
                chosen += (selected,)
                previous = objective

    def test_affirmative_certificate_path(self):
        result, route, chosen, scanned = greedy_decision(
            [0], [0], [0], 2, 1, (2, 3, 5, 7, 11, 13), 3)
        self.assertTrue(result)
        self.assertEqual(route, 'affirmative-certificate')
        self.assertEqual(chosen, ())
        self.assertEqual(scanned, 0)

    def test_nonempty_failed_scan_path(self):
        # Every universe prime divides the sole nonzero difference. This
        # reaches a failed scan rather than an affirmative certificate.
        primes = (5, 7, 11, 13, 17)
        result, route, chosen, scanned = greedy_decision(
            [0], [0], [2 * prod(primes)], 2, 1, (2,) + primes, 3)
        self.assertFalse(result)
        self.assertEqual(route, 'scan')
        self.assertEqual(scanned, 1)
        self.assertEqual(len(set(chosen)), 3)
        self.assertNotIn(2, chosen)

    def test_decisions_against_exact_oracle(self):
        rng = Random(710318)
        for _ in range(240):
            a = rng.sample(range(-12, 13), rng.randrange(1, 7))
            b = rng.sample(range(-12, 13), rng.randrange(1, 7))
            c = rng.sample(range(-12, 13), rng.randrange(1, 7))
            truth = any(x + y == z for x in a for y in b for z in c)
            result, _, chosen, _ = greedy_decision(
                a, b, c, 3, rng.randrange(1, 4), (3, 5, 7, 11, 13, 17), 3)
            self.assertEqual(result, truth)
            self.assertNotIn(3, chosen)
            self.assertEqual(len(set(chosen)), len(chosen))

    def test_two_bit_separating_family(self):
        # Every triple of distinct indices obtains three distinct two-bit
        # patterns; corresponding classes cannot repeat an element.
        for n in range(3, 25):
            bit_count = (n - 1).bit_length()
            for triple in combinations(range(n), 3):
                self.assertTrue(any(
                    len({((v >> i) & 1, (v >> j) & 1) for v in triple}) == 3
                    for i, j in combinations(range(bit_count), 2)))
        rng = Random(710319)
        instances = [[1, -2], [1, 2, -3]] + [
            rng.sample(range(-12, 13), rng.randrange(3, 9)) for _ in range(80)]
        for values in instances:
            truth = any(sum(values[v] for v in triple) == 0
                        for triple in combinations(range(len(values)), 3))
            family_answer = False
            for i, j in combinations(range((len(values) - 1).bit_length()), 2):
                groups = [[] for _ in range(4)]
                for index, value in enumerate(values):
                    pattern = ((index >> i) & 1) + 2 * ((index >> j) & 1)
                    groups[pattern].append(value)
                for left, right, target in permutations(range(4), 3):
                    family_answer |= any(x + y + z == 0
                                         for x in groups[left]
                                         for y in groups[right]
                                         for z in groups[target])
            self.assertEqual(family_answer, truth)

    def test_per_pair_all_edges_certificates(self):
        rng = Random(710320)
        primes = (5, 7, 11, 13, 17, 19, 23)
        certified_total = yes_total = scanned_total = 0
        for _ in range(300):
            n, middle = rng.randrange(2, 5), rng.randrange(2, 9)
            A, B, C = planted_triangle_instance(rng, n, middle, -15, 15,
                                                rng.randrange(0, 5))
            answers, certified, chosen, scanned = per_pair_all_edges(
                A, B, C, rng.randrange(1, 4), primes, rng.randrange(1, 4))
            self.assertEqual(len(set(chosen)), len(chosen))
            certified_total += len(certified)
            yes_total += sum(answers.values())
            scanned_total += scanned
        self.assertGreater(certified_total, 0)
        self.assertGreater(scanned_total, 0)
        self.assertGreaterEqual(yes_total, certified_total)
        for _ in range(60):          # universal divisor bound instead of the exact one
            A, B, C = planted_triangle_instance(rng, 3, 6, -40, 40, 3)
            per_pair_all_edges(A, B, C, 2, primes, 2, divisor_bound=(3 * 80).bit_length())
        # Every candidate prime divides the only nonzero sums: no certificate,
        # both blocks are scanned, and the answer is NO.
        answers, certified, _, scanned = per_pair_all_edges(
            [[0, 0]], [[0], [0]], [[prod(primes)]], 1, primes, 3)
        self.assertEqual((answers, certified, scanned), ({(0, 0): False}, set(), 2))
        # Zeros everywhere: certified at the first stage without scanning.
        answers, certified, _, scanned = per_pair_all_edges(
            [[0, 0]], [[0], [0]], [[0]], 1, primes, 3)
        self.assertEqual((answers, certified, scanned), ({(0, 0): True}, {(0, 0)}, 0))


if __name__ == '__main__':
    unittest.main(verbosity=2)
