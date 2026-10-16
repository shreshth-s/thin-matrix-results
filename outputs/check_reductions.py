#!/usr/bin/env python3
"""Small exact correctness tests for two reductions in the accompanying note.

Run with: python3 check_reductions.py

The modular filter uses explicit residue-label Boolean matrices and a brute-force
matrix-product oracle. The residue-folding test builds the single folded
instance per block, with rows (a, rho_1) and columns (b, rho_2), and compares
its product entries with direct modular counts. The bucket-pair test builds the
folded 3SUM instance over residue buckets and sub-buckets and compares its
entries with direct modular pair sums, and the deterministic modulus choice is
checked against brute-force false-positive counts. The block reduction from
min-plus convolution to min-plus products is checked on all outputs. The
min-plus reduction uses a brute-force all-edges Exact Triangle oracle. These tests check reduction correctness, including adversarial
cases; they do not implement the fast thin-matrix algorithm or verify asymptotic
running times, prime-distribution estimates, or the claimed numerical exponents.
Only the Python standard library is required.
"""

from dataclasses import dataclass
import random
import unittest


Matrix = list[list[int]]
BoolMatrix = list[list[bool]]


@dataclass
class FilterResult:
    found: BoolMatrix
    witnesses: list[list[int | None]]
    successful_scans: int
    failed_scans: int


def brute_exact_edges(ac: Matrix, cb: Matrix, ab: Matrix) -> BoolMatrix:
    """For every outer pair, test whether some original integer sum is zero."""
    return [
        [
            any(ac[a][c] + cb[c][b] + ab[a][b] == 0 for c in range(len(cb)))
            for b in range(len(ab[0]))
        ]
        for a in range(len(ac))
    ]


def modular_filter_all_edges(
    ac: Matrix, cb: Matrix, ab: Matrix, primes: list[int], block_size: int
) -> FilterResult:
    """Implement the reduction, with a slow explicit Boolean-product oracle.

    ``ac[a][c]``, ``cb[c][b]``, and ``ab[a][b]`` are the three edge weights.
    Prime choices are supplied so tests can exercise particular outcomes.
    Correctness holds for every choice, including repeated primes.
    """
    if not primes or any(p < 2 for p in primes) or block_size < 1:
        raise ValueError("Supply positive block size and nonempty primes >= 2")
    na, nc, nb = len(ac), len(cb), len(ab[0])
    found = [[False] * nb for _ in range(na)]
    witnesses: list[list[int | None]] = [[None] * nb for _ in range(na)]
    successful_scans = failed_scans = 0

    for start in range(0, nc, block_size):
        block = list(range(start, min(start + block_size, nc)))
        survives = [[not found[a][b] for b in range(nb)] for a in range(na)]

        for p in primes:
            middle = [(c, sigma) for c in block for sigma in range(p)]
            for rho in range(p):
                # These are exactly the two matrices in the residue encoding.
                x = [
                    [int(sigma == (ac[a][c] + rho) % p) for c, sigma in middle]
                    for a in range(na)
                ]
                y = [
                    [int(sigma == (-cb[c][b]) % p) for b in range(nb)]
                    for c, sigma in middle
                ]
                for a in range(na):
                    for b in range(nb):
                        if found[a][b] or ab[a][b] % p != rho:
                            continue
                        count = sum(x[a][v] * y[v][b] for v in range(len(middle)))
                        survives[a][b] = survives[a][b] and count != 0

        for a in range(na):
            for b in range(nb):
                if not survives[a][b]:
                    continue
                for c in block:
                    if ac[a][c] + cb[c][b] + ab[a][b] == 0:
                        found[a][b] = True
                        witnesses[a][b] = c
                        successful_scans += 1
                        break
                else:
                    # Passing every prime is only a candidate, never a proof.
                    failed_scans += 1

    return FilterResult(found, witnesses, successful_scans, failed_scans)


def folded_residue_instance(
    ac: Matrix, cb: Matrix, p: int, block: list[int]
) -> tuple[Matrix, Matrix, int, int]:
    """Build the folded residue-label matrices for one prime and block.

    Rows are pairs (a, rho_1) with 0 <= rho_1 < p_1 = ceil(sqrt p), columns are
    pairs (b, rho_2) with 0 <= rho_2 < p_2 = ceil(p / p_1), and the middle part
    is block x Z_p. Returns (x, y, p_1, p_2); x and y are dense 0/1 matrices.
    """
    if p < 2 or not block:
        raise ValueError("Supply a prime >= 2 and a nonempty block")
    na, nb = len(ac), len(cb[0])
    p1 = 1
    while p1 * p1 < p:
        p1 += 1
    p2 = -(-p // p1)
    middle = [(c, sigma) for c in block for sigma in range(p)]
    x = [
        [int(sigma == (ac[a][c] + rho1) % p) for c, sigma in middle]
        for a in range(na)
        for rho1 in range(p1)
    ]
    y = [
        [int(sigma == (-cb[c][b] - p1 * rho2) % p) for b in range(nb) for rho2 in range(p2)]
        for c, sigma in middle
    ]
    return x, y, p1, p2


def folded_query_position(ab_weight: int, p: int, p1: int) -> tuple[int, int]:
    """Split the residue of an outer edge into its row and column parts."""
    r = ab_weight % p
    return r % p1, r // p1


def bucket_pair_instance(
    a_set: list[int], b_set: list[int], bucket_prime: int, p: int, sub_size: int
) -> tuple[Matrix, Matrix, list[list[int]], list[list[int]], list[int], list[int], int, int]:
    """Build the bucket-pair folded instance for integer 3SUM (x + y = z).

    Elements are bucketed by residue modulo ``bucket_prime`` and each bucket is
    cut into sub-buckets of at most ``sub_size`` elements. Rows are pairs
    (sub-bucket of A, rho_1), columns are pairs (sub-bucket of B, rho_2), and
    the middle part is Z_p. Returns x, y, the sub-buckets of A and B, their
    bucket residues, and p_1, p_2.
    """
    if bucket_prime < 2 or p < 2 or sub_size < 1:
        raise ValueError("Supply primes >= 2 and a positive sub-bucket size")
    p1 = 1
    while p1 * p1 < p:
        p1 += 1
    p2 = -(-p // p1)

    def split(values: list[int]) -> tuple[list[list[int]], list[int]]:
        subs, residues = [], []
        for residue in range(bucket_prime):
            bucket = [v for v in values if v % bucket_prime == residue]
            for start in range(0, len(bucket), sub_size):
                subs.append(bucket[start:start + sub_size])
                residues.append(residue)
        return subs, residues

    a_subs, a_res = split(a_set)
    b_subs, b_res = split(b_set)
    x = [
        [int(any((v - rho1) % p == sigma for v in alpha)) for sigma in range(p)]
        for alpha in a_subs
        for rho1 in range(p1)
    ]
    y = [
        [int(any((p1 * rho2 - v) % p == sigma for v in beta)) for beta in b_subs for rho2 in range(p2)]
        for sigma in range(p)
    ]
    return x, y, a_subs, b_subs, a_res, b_res, p1, p2


def brute_min_plus_convolution(a: list[int], b: list[int]) -> list[int]:
    n = len(a)
    return [min(a[i] + b[k - i] for i in range(max(0, k - n + 1), min(k, n - 1) + 1)) for k in range(2 * n - 1)]


def block_min_plus_convolution(a: list[int], b: list[int], product) -> list[int]:
    """Reduce a length-n min-plus convolution to O(sqrt n) min-plus products.

    With s = ceil(sqrt n), indices i = s u + v and outputs k = s w + z, the
    output c[k] = min_u F_z[w - u, u] where F_z = P_z (min-plus) Q^T with
    P_z[d, v] = a[s d + z - v] for 0 <= d <= s and Q[u, v] = b[s u + v]; absent
    entries are an infinity sentinel. The row range d in [0, s] is needed: both
    endpoints occur. All 2n - 1 outputs are produced.
    """
    n = len(a)
    s = 1
    while s * s < n:
        s += 1
    inf = 1 + 2 * max(abs(v) for v in a + b)  # exceeds any genuine sum in magnitude
    sentinel = 4 * inf
    q = [[b[s * u + v] if s * u + v < n else sentinel for v in range(s)] for u in range(s)]
    out = [None] * (2 * n - 1)
    for z in range(s):
        p = [[a[s * d + z - v] if 0 <= s * d + z - v < n else sentinel for v in range(s)]
             for d in range(s + 1)]
        f = product(p, [[q[u][v] for u in range(s)] for v in range(s)])  # (s+1) x s times s x s
        for w in range(2 * s):
            k = s * w + z
            if k >= 2 * n - 1:
                continue
            best = min((f[w - u][u] for u in range(s) if 0 <= w - u <= s), default=sentinel)
            out[k] = best if best < inf else None
    return out


def false_triple_counts(a_set, b_set, c_set, bucket_prime, p):
    """Count triples with x + y = z modulo bucket_prime * p, and the exact ones."""
    m = bucket_prime * p
    hist_a = [0] * m
    for x in a_set:
        hist_a[x % m] += 1
    hist_b = [0] * m
    for y in b_set:
        hist_b[y % m] += 1
    conv = [sum(hist_a[u] * hist_b[(t - u) % m] for u in range(m)) for t in range(m)]
    total = sum(conv[z % m] for z in c_set)
    exact = sum(1 for x in a_set for y in b_set for z in c_set if x + y == z)
    return total, exact


def brute_min_plus(a: Matrix, b: Matrix) -> Matrix:
    return [
        [min(a[i][k] + b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def bit_scaling_min_plus(a: Matrix, b: Matrix) -> tuple[Matrix, int]:
    """Recover min-plus with two brute all-edges equality calls per bit."""
    shift = max(0, -min(min(map(min, a)), min(map(min, b))))
    aa = [[v + shift for v in row] for row in a]
    bb = [[v + shift for v in row] for row in b]
    oracle_calls = 0

    def nonnegative_product(left: Matrix, right: Matrix) -> Matrix:
        nonlocal oracle_calls
        n, m = len(left), len(right[0])
        if max(max(map(max, left)), max(map(max, right))) == 0:
            return [[0] * m for _ in range(n)]
        coarse = nonnegative_product(
            [[v // 2 for v in row] for row in left],
            [[v // 2 for v in row] for row in right],
        )
        equals_zero = brute_exact_edges(
            left, right, [[-2 * coarse[i][j] for j in range(m)] for i in range(n)]
        )
        equals_one = brute_exact_edges(
            left,
            right,
            [[-(2 * coarse[i][j] + 1) for j in range(m)] for i in range(n)],
        )
        oracle_calls += 2
        return [
            [
                2 * coarse[i][j]
                + (0 if equals_zero[i][j] else 1 if equals_one[i][j] else 2)
                for j in range(m)
            ]
            for i in range(n)
        ]

    shifted_answer = nonnegative_product(aa, bb)
    return [[v - 2 * shift for v in row] for row in shifted_answer], oracle_calls


class ReductionChecks(unittest.TestCase):
    def check_filter(self, ac, cb, ab, primes, block_size):
        result = modular_filter_all_edges(ac, cb, ab, primes, block_size)
        self.assertEqual(result.found, brute_exact_edges(ac, cb, ab))
        self.assertLessEqual(result.successful_scans, len(ac) * len(ab[0]))
        for a, row in enumerate(result.witnesses):
            for b, c in enumerate(row):
                self.assertEqual(c is not None, result.found[a][b])
                if c is not None:
                    self.assertEqual(ac[a][c] + cb[c][b] + ab[a][b], 0)
        return result

    def test_all_zero_many_witnesses_stops_once_per_pair(self):
        ac, cb, ab = [[0] * 7 for _ in range(4)], [[0] * 3 for _ in range(7)], [[0] * 3 for _ in range(4)]
        result = self.check_filter(ac, cb, ab, [2, 3, 5], 2)
        self.assertEqual(result.successful_scans, 12)
        self.assertEqual(result.failed_scans, 0)
        self.assertEqual(result.witnesses, [[0] * 3 for _ in range(4)])

    def test_different_primes_have_different_false_witnesses(self):
        # Sum 2 supplies the mod-2 witness; sum 3 supplies the mod-3 witness.
        # The block passes BOTH primes but contains no exact-zero witness.
        ac, cb, ab = [[2, 3]], [[0], [0]], [[0]]
        self.assertEqual([c for c in range(2) if ac[0][c] % 2 == 0], [0])
        self.assertEqual([c for c in range(2) if ac[0][c] % 3 == 0], [1])
        result = self.check_filter(ac, cb, ab, [2, 3], 2)
        self.assertEqual(result.found, [[False]])
        self.assertEqual(result.failed_scans, 1)
        self.assertEqual(result.successful_scans, 0)
        # One additional independent test can eliminate the candidate block.
        result = self.check_filter(ac, cb, ab, [2, 3, 5], 2)
        self.assertEqual(result.failed_scans, 0)

    def test_failed_block_before_success_and_later_true_blocks(self):
        ac, cb, ab = [[2, 3, -7, 0, 0, 0]], [[0]] * 6, [[0]]
        result = self.check_filter(ac, cb, ab, [2, 3], 2)
        self.assertEqual(result.failed_scans, 1)
        self.assertEqual(result.successful_scans, 1)
        self.assertEqual(result.witnesses, [[3]])

    def test_repeated_primes_and_negative_residues(self):
        self.check_filter(
            [[-8, 3, -4], [6, -5, 2]],
            [[3, -2], [-1, 5], [2, -6]],
            [[5, -8], [-1, 3]],
            [2, 2, 3, 2],
            2,
        )

    def test_random_signed_modular_instances(self):
        rng = random.Random(261006783)
        for trial in range(240):
            na, nc, nb = rng.randrange(1, 5), rng.randrange(1, 7), rng.randrange(1, 5)
            ac = [[rng.randrange(-12, 13) for _ in range(nc)] for _ in range(na)]
            cb = [[rng.randrange(-12, 13) for _ in range(nb)] for _ in range(nc)]
            ab = [[rng.randrange(-12, 13) for _ in range(nb)] for _ in range(na)]
            primes = [rng.choice([2, 3, 5, 7]) for _ in range(rng.randrange(1, 5))]
            block_size = rng.randrange(1, nc + 2)
            with self.subTest(trial=trial, primes=primes, block_size=block_size):
                self.check_filter(ac, cb, ab, primes, block_size)

    def check_folding(self, ac, cb, ab, p, block):
        x, y, p1, p2 = folded_residue_instance(ac, cb, p, block)
        na, nb, middle = len(ac), len(ab[0]), len(block) * p
        self.assertEqual((len(x), len(x[0])), (na * p1, middle))
        self.assertEqual((len(y), len(y[0])), (middle, nb * p2))
        self.assertGreaterEqual(p1 * p2, p)
        self.assertLessEqual(max(p1, p2), p1 + 1)
        for a in range(na):
            for b in range(nb):
                rho1, rho2 = folded_query_position(ab[a][b], p, p1)
                self.assertLess(rho1, p1)
                self.assertLess(rho2, p2)
                row, col = a * p1 + rho1, b * p2 + rho2
                count = sum(x[row][v] * y[v][col] for v in range(middle))
                expected = sum((ac[a][c] + cb[c][b] + ab[a][b]) % p == 0 for c in block)
                self.assertEqual(count, expected)
        # Every pair is queried at exactly one of the N^2 = (n p_1)(n p_2) positions.
        positions = {
            (a * p1 + folded_query_position(ab[a][b], p, p1)[0],
             b * p2 + folded_query_position(ab[a][b], p, p1)[1])
            for a in range(na) for b in range(nb)
        }
        self.assertEqual(len(positions), na * nb)

    def test_residue_folding_matches_modular_counts(self):
        # Hand-picked primes where p_1 p_2 > p and the top residues are unused.
        self.check_folding([[1, 4, 6], [-3, 0, 2]], [[2, -5], [7, 1], [-4, 3]],
                           [[-3, 9], [4, -8]], 7, [0, 1, 2])
        self.check_folding([[12, -7]], [[5], [-11]], [[6]], 11, [1])
        rng = random.Random(2610067831)
        for trial in range(200):
            na, nc, nb = rng.randrange(1, 5), rng.randrange(1, 6), rng.randrange(1, 5)
            ac = [[rng.randrange(-20, 21) for _ in range(nc)] for _ in range(na)]
            cb = [[rng.randrange(-20, 21) for _ in range(nb)] for _ in range(nc)]
            ab = [[rng.randrange(-20, 21) for _ in range(nb)] for _ in range(na)]
            p = rng.choice([2, 3, 5, 7, 11, 13])
            size = rng.randrange(1, nc + 1)
            start = rng.randrange(0, nc - size + 1)
            with self.subTest(trial=trial, p=p, block=(start, size)):
                self.check_folding(ac, cb, ab, p, list(range(start, start + size)))

    def check_bucket_pairs(self, a_set, b_set, c_set, bucket_prime, p, sub_size):
        x, y, a_subs, b_subs, a_res, b_res, p1, p2 = bucket_pair_instance(
            a_set, b_set, bucket_prime, p, sub_size)
        self.assertEqual(len(x), len(a_subs) * p1)
        self.assertEqual(len(y[0]), len(b_subs) * p2)
        self.assertGreaterEqual(p1 * p2, p)
        queries = 0
        for z in c_set:
            r = z % p
            rho1, rho2 = r % p1, r // p1
            for ia, alpha in enumerate(a_subs):
                for ib, beta in enumerate(b_subs):
                    if (a_res[ia] + b_res[ib]) % bucket_prime != z % bucket_prime:
                        continue
                    queries += 1
                    row, col = ia * p1 + rho1, ib * p2 + rho2
                    count = sum(x[row][sigma] * y[sigma][col] for sigma in range(p))
                    modular = any((u + v - z) % p == 0 for u in alpha for v in beta)
                    self.assertEqual(count > 0, modular)
        # Every exact solution lies in a queried sub-bucket pair.
        for u in a_set:
            for v in b_set:
                z = u + v
                if z in c_set:
                    ia = next(i for i, s in enumerate(a_subs) if u in s)
                    ib = next(i for i, s in enumerate(b_subs) if v in s)
                    self.assertEqual((a_res[ia] + b_res[ib]) % bucket_prime, z % bucket_prime)
        # The query count never exceeds the number of compatible sub-bucket pairs.
        bound = sum(
            1 for z in c_set for ra in a_res for rb in b_res
            if (ra + rb) % bucket_prime == z % bucket_prime)
        self.assertEqual(queries, bound)

    def test_bucket_pair_folding_matches_modular_sums(self):
        self.check_bucket_pairs([3, 8, -5, 14, 21], [1, -7, 10, 6], [4, 9, 31, -4], 5, 7, 2)
        self.check_bucket_pairs([0, 1, 2, 3], [0, 1, 2, 3], [0, 3, 6], 3, 2, 1)
        rng = random.Random(14076756)
        for trial in range(150):
            na, nb, ncs = (rng.randrange(1, 7) for _ in range(3))
            a_set = [rng.randrange(-30, 31) for _ in range(na)]
            b_set = [rng.randrange(-30, 31) for _ in range(nb)]
            c_set = [rng.randrange(-60, 61) for _ in range(ncs)]
            if rng.random() < 0.5 and a_set and b_set:
                c_set.append(rng.choice(a_set) + rng.choice(b_set))
            bucket_prime = rng.choice([2, 3, 5, 7, 11])
            p = rng.choice([q for q in (2, 3, 5, 7, 11, 13) if q != bucket_prime])
            with self.subTest(trial=trial, bucket_prime=bucket_prime, p=p):
                self.check_bucket_pairs(a_set, b_set, c_set, bucket_prime, p, rng.randrange(1, 4))

    def test_block_min_plus_convolution_all_outputs(self):
        rng = random.Random(2610067832)
        for n in list(range(1, 30)) + [49, 50, 64, 65, 100]:
            for _ in range(3):
                a = [rng.randrange(-50, 51) for _ in range(n)]
                b = [rng.randrange(-50, 51) for _ in range(n)]
                with self.subTest(n=n):
                    got = block_min_plus_convolution(a, b, brute_min_plus)
                    self.assertEqual(got, brute_min_plus_convolution(a, b))
        # The endpoint d = s is genuinely needed: dropping it loses an output.
        a, b = [0, 0, 0, -100], [0, -100, 0, 0]
        self.assertEqual(block_min_plus_convolution(a, b, brute_min_plus)[4], -200)

    def test_deterministic_modulus_selection_minimizes_false_positives(self):
        rng = random.Random(14076757)
        primes = [11, 13, 17, 19, 23, 29, 31]
        for trial in range(60):
            na, nb, ncs = (rng.randrange(1, 8) for _ in range(3))
            a_set = sorted(set(rng.randrange(-200, 201) for _ in range(na)))
            b_set = sorted(set(rng.randrange(-200, 201) for _ in range(nb)))
            c_set = sorted(set(rng.randrange(-400, 401) for _ in range(ncs)))
            if a_set and b_set and rng.random() < 0.5:
                c_set = sorted(set(c_set + [rng.choice(a_set) + rng.choice(b_set)]))
            bucket_prime = rng.choice([5, 7])
            counts = {p: false_triple_counts(a_set, b_set, c_set, bucket_prime, p) for p in primes}
            exact = {v[1] for v in counts.values()}
            self.assertEqual(len(exact), 1)  # exact solutions do not depend on p
            false = {p: counts[p][0] - counts[p][1] for p in primes}
            best = min(primes, key=lambda p: counts[p][0])
            with self.subTest(trial=trial):
                # Minimizing the total count minimizes the false-positive count,
                # and the minimum is at most the average over the candidate primes.
                self.assertEqual(false[best], min(false.values()))
                self.assertLessEqual(false[best] * len(primes), sum(false.values()))
                # Each failed sub-scan is charged to a distinct false triple.
                x, y, a_subs, b_subs, a_res, b_res, p1, p2 = bucket_pair_instance(
                    a_set, b_set, bucket_prime, best, 2)
                charged = set()
                for z in c_set:
                    r = z % best
                    rho1, rho2 = r % p1, r // p1
                    for ia, alpha in enumerate(a_subs):
                        for ib, beta in enumerate(b_subs):
                            if (a_res[ia] + b_res[ib]) % bucket_prime != z % bucket_prime:
                                continue
                            row, col = ia * p1 + rho1, ib * p2 + rho2
                            if sum(x[row][sig] * y[sig][col] for sig in range(best)) == 0:
                                continue
                            if any(u + v == z for u in alpha for v in beta):
                                continue  # successful scan
                            witness = next((u, v, z) for u in alpha for v in beta
                                           if (u + v - z) % best == 0)
                            self.assertNotIn(witness, charged)
                            charged.add(witness)
                self.assertLessEqual(len(charged), false[best])

    def test_bit_scaling_all_three_low_bit_cases(self):
        # For a single candidate, residual offsets zero, one, and two all occur.
        for left, right, expected in [(2, 4, 6), (3, 4, 7), (3, 5, 8)]:
            with self.subTest(left=left, right=right):
                answer, calls = bit_scaling_min_plus([[left]], [[right]])
                self.assertEqual(answer, [[expected]])
                self.assertEqual(calls, 2 * max(left, right).bit_length())

    def test_bit_scaling_zero_base_and_negative_entries(self):
        answer, calls = bit_scaling_min_plus([[0, 0]], [[0], [0]])
        self.assertEqual((answer, calls), ([[0]], 0))
        for a, b in [([[-9, -2]], [[-4], [-8]]), ([[7, -4], [-3, 2]], [[-5, 6], [8, -1]])]:
            self.assertEqual(bit_scaling_min_plus(a, b)[0], brute_min_plus(a, b))

    def test_random_signed_min_plus_instances(self):
        rng = random.Random(20261013)
        for trial in range(400):
            n, k, m = (rng.randrange(1, 6) for _ in range(3))
            a = [[rng.randrange(-100, 101) for _ in range(k)] for _ in range(n)]
            b = [[rng.randrange(-100, 101) for _ in range(m)] for _ in range(k)]
            with self.subTest(trial=trial, shape=(n, k, m)):
                answer, calls = bit_scaling_min_plus(a, b)
                self.assertEqual(answer, brute_min_plus(a, b))
                shift = max(0, -min(min(map(min, a)), min(map(min, b))))
                maximum = max(max(map(max, a)), max(map(max, b))) + shift
                self.assertEqual(calls, 2 * maximum.bit_length())


if __name__ == "__main__":
    unittest.main(verbosity=2)
