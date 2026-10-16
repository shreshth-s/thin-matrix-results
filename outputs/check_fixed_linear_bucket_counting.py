#!/usr/bin/env python3
"""Finite fixed-linear-bucket #3XOR audit using actual folded group-algebra products.

Vectors of F_2^d are Python integers (bit i is coordinate i); a linear
functional is a vector u with <u, v> = parity(u & v); a linear map is a
list of rows whose image bit j is <row_j, v>.  The matrix products over
Z[F_2^{t_2}] are evaluated directly from their sparse coefficient arrays,
and once in full by the Walsh--Hadamard product and by naive convolution.
This checks the reduction of the draft lemma, not the fast thin-product
algorithm.
"""

from collections import Counter, defaultdict
from fractions import Fraction
from random import Random
import unittest


STATS = Counter()
E_LOWER = Fraction(2718281828, 10 ** 9)      # < e
E_UPPER = Fraction(27182818285, 10 ** 10)    # > e
IRREDUCIBLE = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101,
               6: 0b1000011, 7: 0b10000011, 8: 0b100011101,
               9: 0b1000010001, 10: 0b10000001001, 11: 0b100000000101,
               12: 0b1000001010011}
FAMILIES = {}


def parity(x):
    return x.bit_count() & 1


def apply_map(rows, v):
    out = 0
    for j, u in enumerate(rows):
        out |= parity(u & v) << j
    return out


def wht(values):
    """Unnormalized integer Walsh--Hadamard transform of a length-2^m list."""
    a = list(values)
    n, h = len(a), 1
    while h < n:
        for i in range(0, n, 2 * h):
            for j in range(i, i + h):
                x, y = a[j], a[j + h]
                a[j], a[j + h] = x + y, x - y
        h *= 2
    return a


def ga_mul_naive(f, g):
    q = len(f)
    return [sum(f[v] * g[v ^ w] for v in range(q)) for w in range(q)]


def ga_mul_wht(f, g):
    q = len(f)
    product = wht([x * y for x, y in zip(wht(f), wht(g))])
    assert all(c % q == 0 for c in product)
    return [c // q for c in product]


def gf_mul(a, b, m, poly):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> m & 1:
            a ^= poly
    return r


def poly_mod(a, f):
    df = f.bit_length() - 1
    while a.bit_length() - 1 >= df and a:
        a ^= f << (a.bit_length() - 1 - df)
    return a


def is_irreducible(poly, m):
    assert poly.bit_length() == m + 1
    return all(poly_mod(poly, f) != 0
               for deg in range(1, m // 2 + 1)
               for f in range(1 << deg, 1 << (deg + 1)))


class BiasedFamily:
    """A multiset of functionals on F_2^d with a certified bias."""

    def __init__(self, d, r, kind):
        self.d, self.r, self.kind = d, r, kind
        if kind == 'aghp':
            m = 1
            while (1 << m) < d * r:
                m += 1
            poly = IRREDUCIBLE[m]
            assert is_irreducible(poly, m)
            rows = []
            for x in range(1 << m):
                powers = [1]
                for _ in range(d - 1):
                    powers.append(gf_mul(powers[-1], x, m, poly))
                for y in range(1 << m):
                    rows.append(sum(parity(p & y) << i for i, p in enumerate(powers)))
            self.m = m
            assert len(rows) == 4 ** m <= 4 * (d * r) ** 2
        elif kind == 'full':
            rows = list(range(1 << d))
        elif kind == 'nonzero':
            rows = list(range(1, 1 << d))
        else:
            raise ValueError(kind)
        self.rows = rows
        self.bias, self.transform = self.bias_on(rows, d)
        if kind == 'aghp':
            assert self.bias <= Fraction(d - 1, 1 << m)
        assert self.bias < Fraction(1, r)
        STATS['biased_families'] += 1

    @staticmethod
    def bias_on(rows, bits):
        hist = [0] * (1 << bits)
        for u in rows:
            hist[u] += 1
        transform = wht(hist)
        bias = max((Fraction(abs(w), len(rows)) for w in transform[1:]),
                   default=Fraction(0))
        return bias, transform

    def restricted(self, bits):
        """Distinct projections to the first `bits` coordinates and their bias."""
        mask = (1 << bits) - 1
        rows = [u & mask for u in self.rows]
        bias, _ = self.bias_on(rows, bits)
        assert bias <= self.bias
        return sorted(set(rows)), bias


def family(d, r, kind):
    key = (d, r, kind)
    if key not in FAMILIES:
        FAMILIES[key] = BiasedFamily(d, r, kind)
    return FAMILIES[key]


def greedy_rows(hist, bits, candidates, steps, beta):
    """Greedy rows minimizing the surviving weight of nonzero vectors.

    hist[v] is the weight of v in F_2^bits with hist[0] == 0.  Each step
    picks the candidate annihilating the least weight; the returned masses
    are the surviving weights after 0..steps rows.
    """
    assert hist[0] == 0 and len(hist) == 1 << bits
    mask = (1 << bits) - 1
    rows, masses = [], [sum(hist)]
    for _ in range(steps):
        transform = wht(hist)
        total = masses[-1]
        best = min((total + transform[u & mask], u & mask) for u in candidates)
        assert best[0] % 2 == 0
        score, u = best[0] // 2, best[1]
        assert 2 * score <= (1 + beta) * total
        hist = [c if parity(u & v) == 0 else 0 for v, c in enumerate(hist)]
        assert sum(hist) == score
        rows.append(u)
        masses.append(score)
        STATS['greedy_rows'] += 1
    return rows, masses


class LinearInstance:
    """Fixed linear buckets, sub-buckets, and the incidence list."""

    def __init__(self, S1, S2, S3, d, s, kind, supplied_rows=None):
        assert all(0 <= v < 1 << d for S in (S1, S2, S3) for v in S)
        assert len(set(S1)) == len(S1) and len(set(S2)) == len(S2)
        assert len(set(S3)) == len(S3)
        self.S1, self.S2, self.S3 = sorted(S1), sorted(S2), sorted(S3)
        self.d, self.s = d, s
        n = max(len(S1), len(S2), len(S3))
        self.n = n
        k = 0
        while (1 << k) * s < n:
            k += 1
        self.k = k
        hist = [0] * (1 << d)
        for S in (self.S1, self.S2):
            for x in S:
                for y in S:
                    if x != y:
                        hist[x ^ y] += 1
        if k == 0:
            rows = []
            assert supplied_rows in (None, [])
        elif supplied_rows is None:
            fam = family(d, k, kind)
            rows, masses = greedy_rows(hist, d, fam.rows, k, fam.bias)
            self.bucket_bias = fam.bias
        else:
            rows = list(supplied_rows)
            assert len(rows) == k
            fam = family(d, k, kind)
            assert all(u in fam.rows for u in rows)
        self.rows = rows
        pairs = sum(c for v, c in enumerate(hist)
                    if v and apply_map(rows, v) == 0)
        phi = len(S1) + len(S2) + pairs
        self.classes_a = defaultdict(list)
        self.classes_b = defaultdict(list)
        for x in self.S1:
            self.classes_a[apply_map(rows, x)].append(x)
        for y in self.S2:
            self.classes_b[apply_map(rows, y)].append(y)
        direct = (sum(len(c) ** 2 for c in self.classes_a.values())
                  + sum(len(c) ** 2 for c in self.classes_b.values()))
        assert phi == direct
        bound = 2 * n + E_UPPER * Fraction(len(S1) ** 2 + len(S2) ** 2, 1 << k)
        assert phi <= bound <= 2 * n + 2 * E_UPPER * n * s
        self.phi = phi
        self.aa, self.a_class = self.sub_buckets(self.classes_a)
        self.bb, self.b_class = self.sub_buckets(self.classes_b)
        for parts in (self.aa, self.bb):
            assert len(parts) <= Fraction(n, s) + (1 << k)
            if k >= 1:
                assert Fraction(n, s) + (1 << k) <= Fraction(3 * n, s)
            else:
                # Degenerate n <= s: one bucket, and 3n/s < 1 when n < s/3.
                assert len(parts) <= 1
                STATS['single_bucket_instances'] += 1
        by_class = defaultdict(list)
        for j, gamma in enumerate(self.b_class):
            by_class[gamma].append(j)
        self.incidences = []
        for z in self.S3:
            pz = apply_map(rows, z)
            for i, gamma in enumerate(self.a_class):
                for j in by_class.get(gamma ^ pz, ()):
                    self.incidences.append((i, j, z))
        count = len(self.incidences)
        assert count * s <= 8 * n * n
        assert count <= (Fraction(n * phi, 2 * s * s) + Fraction(2 * n * n, s)
                         + n * (1 << k))
        for i, j, z in self.incidences:
            assert all(apply_map(rows, a ^ b ^ z) == 0
                       for a in self.aa[i] for b in self.bb[j])
        STATS['fixed_incidences'] += count
        STATS['linear_instances'] += 1

    def sub_buckets(self, classes):
        parts, labels = [], []
        for gamma, items in sorted(classes.items()):
            for start in range(0, len(items), self.s):
                parts.append(items[start:start + self.s])
                labels.append(gamma)
        return parts, labels

    def check_compatibility(self):
        membership = defaultdict(list)
        for index, (i, j, z) in enumerate(self.incidences):
            for a in self.aa[i]:
                for b in self.bb[j]:
                    membership[a, b, z].append(index)
        solutions, targets = 0, set(self.S3)
        for a in self.S1:
            for b in self.S2:
                z = a ^ b
                if z in targets:
                    solutions += 1
                    assert len(membership[a, b, z]) == 1
        for key, indices in membership.items():
            assert len(indices) == 1
        STATS['compatibility_solutions'] += solutions
        return solutions


class GroupAlgebraFoldedProduct:
    """One folded N x D by D x N product over Z[F_2^{t_2}], D = 2^{t_1}."""

    def __init__(self, aa, bb, H1, H2, wa=None, wb=None):
        self.H1, self.H2 = list(H1), list(H2)
        self.t1, self.t2 = len(self.H1), len(self.H2)
        self.t1a = (self.t1 + 1) // 2
        self.t1b = self.t1 // 2
        self.D, self.q = 1 << self.t1, 1 << self.t2
        self.low = (1 << self.t1a) - 1
        self.X, self.Y = {}, {}
        for i, part in enumerate(aa):
            for rho in range(1 << self.t1a):
                entries = defaultdict(Counter)
                for a in part:
                    sigma = apply_map(self.H1, a) ^ rho
                    entries[sigma][apply_map(self.H2, a)] += 1 if wa is None else wa[a]
                self.X[i, rho] = entries
        for j, part in enumerate(bb):
            for rho in range(1 << self.t1b):
                entries = defaultdict(Counter)
                for b in part:
                    sigma = apply_map(self.H1, b) ^ (rho << self.t1a)
                    entries[sigma][apply_map(self.H2, b)] += 1 if wb is None else wb[b]
                self.Y[j, rho] = entries
        self.N = max(len(aa) << self.t1a, len(bb) << self.t1b)
        STATS['folded_products'] += 1

    def split(self, z):
        sigma = apply_map(self.H1, z)
        rho1, rho2 = sigma & self.low, sigma >> self.t1a
        assert rho1 | (rho2 << self.t1a) == sigma and rho1 & (rho2 << self.t1a) == 0
        return rho1, rho2

    def query(self, i, j, z):
        rho1, rho2 = self.split(z)
        w = apply_map(self.H2, z)
        X, Y = self.X[i, rho1], self.Y[j, rho2]
        result = 0
        for sigma in X.keys() & Y.keys():
            for v, left in X[sigma].items():
                result += left * Y[sigma].get(v ^ w, 0)
        STATS['coefficient_queries'] += 1
        return result

    def dense(self, entries, sigma):
        vector = [0] * self.q
        for v, c in entries.get(sigma, {}).items():
            vector[v] += c
        return vector

    def entry(self, i, rho1, j, rho2, method):
        mul = ga_mul_wht if method == 'wht' else ga_mul_naive
        total = [0] * self.q
        for sigma in range(self.D):
            product = mul(self.dense(self.X[i, rho1], sigma),
                          self.dense(self.Y[j, rho2], sigma))
            total = [x + y for x, y in zip(total, product)]
        return total

    def full_product(self, method):
        return {(key_a, key_b): self.entry(key_a[0], key_a[1], key_b[0], key_b[1], method)
                for key_a in self.X for key_b in self.Y}


def count_rows(inst, x, rows):
    i, j, z = x
    return sum(all(parity(u & (a ^ b ^ z)) == 0 for u in rows)
               for a in inst.aa[i] for b in inst.bb[j])


def lift_counts(inst, l1, kind, weights=None):
    """Levels, attempts, certification, and extension; returns G and weighted counts."""
    d, s = inst.d, inst.s
    h = s * s
    l = 0
    while (1 << l) < 4 * E_UPPER * h:
        l += 1
    assert (1 << (l - 1)) < 4 * E_LOWER * h
    assert 0 <= l1 <= l
    fam = family(d, l, kind)
    G = {x: len(inst.aa[x[0]]) * len(inst.bb[x[1]]) for x in inst.incidences}
    weighted = {x: 0 for x in inst.incidences}
    attempts_by_level, attempt_log = [], []
    for ell in range(d):
        mask = (1 << ell) - 1
        prefix = [1 << c for c in range(ell + 1)]
        next_G = {x: 0 for x in inst.incidences}
        for x in inst.incidences:
            assert G[x] == count_rows(inst, x, prefix[:ell])
            if G[x] == 0:
                assert count_rows(inst, x, prefix) == 0
                assert not any(a ^ b == x[2] for a in inst.aa[x[0]] for b in inst.bb[x[1]])
        active = [x for x in inst.incidences if G[x] > 0]
        initially_active = len(active)
        candidates, beta = fam.restricted(ell)
        attempts = 0
        while active:
            attempts += 1
            hist = [0] * (1 << ell)
            true_mass = 0
            for x in active:
                i, j, z = x
                true_mass += G[x]
                for a in inst.aa[i]:
                    for b in inst.bb[j]:
                        v = (a ^ b ^ z) & mask
                        if v:
                            hist[v] += 1
            initial = sum(hist)
            assert initial == sum(len(inst.aa[i]) * len(inst.bb[j]) - G[x]
                                  for x in active for i, j, z in [x])
            assert initial <= h * len(active)
            rows, masses = greedy_rows(hist, ell, candidates, l, beta)
            for t in range(l + 1):
                assert (sum(count_rows(inst, x, rows[:t]) for x in active)
                        == true_mass + masses[t])
            assert masses[-1] * (1 << l) <= E_UPPER * initial
            assert 4 * masses[-1] <= len(active)
            H1, H2 = rows[:l1], rows[l1:]
            product = GroupAlgebraFoldedProduct(inst.aa, inst.bb, H1, H2)
            extension = GroupAlgebraFoldedProduct(inst.aa, inst.bb, H1, H2 + [1 << ell])
            weighted_product = None
            if weights is not None and ell == d - 1:
                weighted_product = GroupAlgebraFoldedProduct(
                    inst.aa, inst.bb, H1, H2 + [1 << ell], wa=weights[0], wb=weights[1])
            assert product.t1 <= l1 and extension.t2 <= l - l1 + 1
            certified, false_mass = [], 0
            for x in active:
                i, j, z = x
                cnt = product.query(i, j, z)
                assert cnt == count_rows(inst, x, rows)
                assert cnt >= G[x]
                false_mass += cnt - G[x]
                survivors = [(a, b) for a in inst.aa[i] for b in inst.bb[j]
                             if all(parity(u & (a ^ b ^ z)) == 0 for u in rows)]
                genuine = [(a, b) for a in inst.aa[i] for b in inst.bb[j]
                           if (a ^ b ^ z) & mask == 0]
                assert set(genuine) <= set(survivors)
                if cnt == G[x]:
                    assert set(survivors) == set(genuine)
                    value = extension.query(i, j, z)
                    assert value == count_rows(inst, x, prefix)
                    assert value == sum((a ^ b ^ z) & (mask | 1 << ell) == 0
                                        for a, b in survivors)
                    next_G[x] = value
                    certified.append(x)
                    if weighted_product is not None:
                        total = weighted_product.query(i, j, z)
                        assert total == sum(weights[0][a] * weights[1][b]
                                            for a, b in genuine if a ^ b == z)
                        weighted[x] = total
                else:
                    assert set(survivors) > set(genuine)
                    STATS['uncertified_incidences'] += 1
            assert false_mass == masses[-1]
            assert 4 * (len(active) - len(certified)) <= len(active)
            uncertified = [x for x in active if x not in set(certified)]
            if uncertified:
                STATS['nonempty_restart_sets'] += 1
            STATS['attempts'] += 1
            attempt_log.append((ell, attempts, tuple(rows), tuple(certified),
                                tuple(uncertified)))
            active = uncertified
        assert (attempts >= 1) == (initially_active >= 1)
        attempts_by_level.append(attempts)
        G = next_G
        STATS['prefix_levels'] += 1
    for x in inst.incidences:
        i, j, z = x
        assert G[x] == sum(a ^ b == z for a in inst.aa[i] for b in inst.bb[j])
    lift_counts.last_log = attempt_log
    return G, weighted, attempts_by_level


def count_3xor(L1, L2, L3, s, d, l1=0, kind='aghp', supplied_rows=None, row_kind=None):
    """Exact #3XOR over sets and multisets, with per-target counts."""
    if not L1 or not L2 or not L3:
        return 0, Counter(), 0, Counter(), []
    # High zero coordinates preserve each integer-encoded vector, even
    # when the occurrence count exceeds the original universe size.
    ambient_n = max(len(L1), len(L2), len(L3))
    d = max(d, (ambient_n - 1).bit_length())
    m1, m2, m3 = Counter(L1), Counter(L2), Counter(L3)
    inst = LinearInstance(sorted(m1), sorted(m2), sorted(m3), d, s, kind, supplied_rows)
    inst.check_compatibility()
    G, weighted, attempts = lift_counts(inst, l1, row_kind or kind, weights=(m1, m2))
    per_target, weighted_target = Counter(), Counter()
    for x in inst.incidences:
        per_target[x[2]] += G[x]
        weighted_target[x[2]] += weighted[x]
    for z in m3:
        assert per_target[z] == sum(a ^ b == z for a in m1 for b in m2)
        assert weighted_target[z] == sum(m1[a] * m2[b] for a in m1 for b in m2 if a ^ b == z)
    total_sets = sum(per_target.values())
    total_multiset = sum(m3[z] * weighted_target[z] for z in m3)
    STATS['end_to_end_instances'] += 1
    return total_sets, per_target, total_multiset, weighted_target, attempts


def brute_count(L1, L2, L3):
    return sum(a ^ b == c for a in L1 for b in L2 for c in L3)


def random_instance(rng, n, d, planted):
    S1 = [rng.randrange(1 << d) for _ in range(rng.randrange(1, n + 1))]
    S2 = [rng.randrange(1 << d) for _ in range(rng.randrange(1, n + 1))]
    S3 = [rng.randrange(1 << d) for _ in range(rng.randrange(1, n + 1))]
    for _ in range(planted):
        S3.append(rng.choice(S1) ^ rng.choice(S2))
    return S1, S2, S3


class FixedLinearBucketCountingTests(unittest.TestCase):
    def test_group_algebra_ring(self):
        rng = Random(4201)
        for m in range(0, 6):
            q = 1 << m
            for _ in range(20):
                f = [rng.randrange(-9, 10) for _ in range(q)]
                g = [rng.randrange(-9, 10) for _ in range(q)]
                naive = ga_mul_naive(f, g)
                self.assertEqual(ga_mul_wht(f, g), naive)
                self.assertEqual(ga_mul_naive(g, f), naive)
                self.assertLessEqual(sum(map(abs, naive)),
                                     sum(map(abs, f)) * sum(map(abs, g)))
                one = [1] + [0] * (q - 1)
                self.assertEqual(ga_mul_wht(f, one), f)
                for a in range(q):
                    for b in range(q):
                        xa, xb = [0] * q, [0] * q
                        xa[a], xb[b] = 1, 1
                        expected = [0] * q
                        expected[a ^ b] = 1
                        self.assertEqual(ga_mul_wht(xa, xb), expected)
                STATS['ring_products'] += 1

    def test_biased_families(self):
        for d in range(2, 9):
            for r in (1, 2, 3, 4, 6, 7):
                fam = family(d, r, 'aghp')
                self.assertLess(fam.bias, Fraction(1, r))
                self.assertLessEqual(len(fam.rows), 4 * (d * r) ** 2)
                for w in range(1, 1 << d):
                    annihilating = sum(parity(u & w) == 0 for u in fam.rows)
                    self.assertLessEqual(2 * annihilating, (1 + fam.bias) * len(fam.rows))
                for bits in range(0, d + 1):
                    rows, bias = fam.restricted(bits)
                    self.assertLessEqual(bias, fam.bias)
                STATS['aghp_families'] += 1
            full = family(d, 2, 'full')
            self.assertEqual(full.bias, 0)
            nonzero = family(d, 2, 'nonzero')
            self.assertEqual(nonzero.bias, Fraction(1, (1 << d) - 1))
        fam = family(5, 3, 'aghp')
        for w in range(1, 32):
            direct = sum(1 - 2 * parity(u & w) for u in fam.rows)
            self.assertEqual(direct, fam.transform[w])
        STATS['direct_character_sums'] += 31

    def test_linear_buckets(self):
        rng = Random(1137)
        for _ in range(30):
            d = rng.randrange(3, 9)
            n = rng.randrange(2, 41)
            s = rng.randrange(1, 4)
            S1 = rng.sample(range(1 << d), min(n, 1 << d))
            S2 = rng.sample(range(1 << d), min(rng.randrange(1, n + 1), 1 << d))
            S3 = rng.sample(range(1 << d), min(rng.randrange(1, n + 1), 1 << d))
            for kind in ('aghp', 'full'):
                inst = LinearInstance(S1, S2, S3, d, s, kind)
                self.assertEqual(len(inst.rows), inst.k)
                self.assertLessEqual(len(inst.incidences) * s, 8 * inst.n ** 2)
                inst.check_compatibility()
                self.assertEqual(sum(len(p) for p in inst.aa), len(S1))
                self.assertTrue(all(len(p) <= s for p in inst.aa + inst.bb))
                STATS['bucket_instances'] += 1

    def test_folded_group_algebra_product(self):
        rng = Random(2203)
        d = 6
        S1 = rng.sample(range(64), 14)
        S2 = rng.sample(range(64), 12)
        S3 = rng.sample(range(64), 10) + [S1[0] ^ S2[0], S1[1] ^ S2[3]]
        inst = LinearInstance(S1, S2, sorted(set(S3)), d, 2, 'full')
        cases = []
        for t1, t2 in ((0, 0), (0, 3), (1, 2), (2, 3), (3, 2), (4, 1), (3, 0)):
            H1 = [rng.randrange(1, 64) for _ in range(t1)]
            H2 = [rng.randrange(1, 64) for _ in range(t2)]
            cases.append((H1, H2))
        # Dependent and shared rows: no coprimality condition is needed.
        cases.append(([5, 9, 5 ^ 9], [5, 17]))
        cases.append(([3, 3], [3, 3, 48]))
        cases.append(([0, 7], [0, 7 ^ 56]))
        for H1, H2 in cases:
            product = GroupAlgebraFoldedProduct(inst.aa, inst.bb, H1, H2)
            via_wht = product.full_product('wht')
            via_naive = product.full_product('naive')
            self.assertEqual(via_wht, via_naive)
            for ((i, rho1), (j, rho2)), element in via_wht.items():
                position = rho1 | (rho2 << product.t1a)
                for w, coefficient in enumerate(element):
                    expected = sum(apply_map(H1, a ^ b) == position
                                   and apply_map(H2, a ^ b) == w
                                   for a in inst.aa[i] for b in inst.bb[j])
                    self.assertEqual(coefficient, expected)
                    STATS['full_product_coefficients'] += 1
            for i, j, z in inst.incidences:
                rho1, rho2 = product.split(z)
                expected = sum(apply_map(H1, a ^ b ^ z) == 0
                               and apply_map(H2, a ^ b ^ z) == 0
                               for a in inst.aa[i] for b in inst.bb[j])
                self.assertEqual(product.query(i, j, z), expected)
                self.assertEqual(via_wht[(i, rho1), (j, rho2)][apply_map(H2, z)], expected)
                both = sum(apply_map(H1 + H2, a ^ b ^ z) == 0
                           for a in inst.aa[i] for b in inst.bb[j])
                self.assertEqual(expected, both)
            self.assertEqual(product.N, max(len(inst.aa) << product.t1a,
                                            len(inst.bb) << product.t1b))
            STATS['product_cases'] += 1

    def test_levels_and_certification(self):
        rng = Random(5503)
        for _ in range(24):
            d = rng.randrange(2, 9)
            n = rng.randrange(2, 33)
            s = rng.randrange(1, 4)
            S1, S2, S3 = random_instance(rng, n, d, rng.randrange(0, 4))
            S1, S2, S3 = sorted(set(S1)), sorted(set(S2)), sorted(set(S3))
            kind = rng.choice(('aghp', 'full'))
            inst = LinearInstance(S1, S2, S3, d, s, kind)
            l = 0
            while (1 << l) < 4 * E_UPPER * s * s:
                l += 1
            l1 = rng.choice((0, 1, 2, l // 2, l))
            G, _, attempts = lift_counts(inst, l1, kind)
            # Rows must factor through the prefix: an unrestricted row can
            # annihilate a level-genuine pair whose full vector is nonzero.
            killed = 0
            for ell in range(1, d):
                mask = (1 << ell) - 1
                for i, j, z in inst.incidences:
                    for a in inst.aa[i]:
                        for b in inst.bb[j]:
                            v = a ^ b ^ z
                            if v and v & mask == 0:
                                killed += any(parity(u & v) for u in range(1 << d))
            STATS['unrestricted_row_kills'] += killed
            # A level with no active incidence needs no attempt; lift_counts
            # asserts that attempts happen exactly when something is active.
            self.assertEqual(len(attempts), d)
            self.assertEqual(attempts[0] >= 1, bool(inst.incidences))
            STATS['level_attempts'] += sum(attempts)
            STATS['level_instances'] += 1

    def test_forced_restart_fixture(self):
        # d = 11, s = 2, n = 32, k = 4; the supplied projection reads
        # coordinates 7..10.  Every class has exactly two elements, the
        # incidence (alpha_g, beta_g', embed(g xor g')) has the genuine pair
        # of class representatives, and the false vectors of the active
        # incidences at every level >= 7 are all 127 nonzero vectors of
        # V = span(e_0..e_6), while an attempt has only l = 6 rows.  Any six
        # rows leave a nonzero vector of V, so the first attempt of each of
        # these levels cannot certify every incidence.
        d, s = 11, 2
        embed = lambda g: g << 7
        U1 = [v for v in range(1, 16)]              # nonzero of span(e_0..e_3)
        U2 = [v << 4 for v in range(1, 8)]          # nonzero of span(e_4..e_6)
        v_rows = U1 + [1]
        w_rows = U2 + [U2[i % 7] ^ U1[i] for i in range(9)]
        S1 = sorted(embed(g) ^ part for g in range(16) for part in (0, v_rows[g]))
        S2 = sorted(embed(g) ^ part for g in range(16) for part in (0, w_rows[g]))
        S3 = sorted(embed(g) for g in range(16))
        self.assertEqual((len(S1), len(S2)), (32, 32))
        supplied = [1 << c for c in range(7, 11)]
        inst = LinearInstance(S1, S2, S3, d, s, 'full', supplied_rows=supplied)
        self.assertEqual(inst.k, 4)
        self.assertEqual(inst.phi, 128)
        self.assertTrue(all(len(p) == 2 for p in inst.aa + inst.bb))
        self.assertEqual(len(inst.incidences), 256)
        inst.check_compatibility()
        false_vectors = set()
        for i, j, z in inst.incidences:
            genuine = [(a, b) for a in inst.aa[i] for b in inst.bb[j] if a ^ b == z]
            self.assertEqual(len(genuine), 1)
            false_vectors |= {a ^ b ^ z for a in inst.aa[i] for b in inst.bb[j]} - {0}
        self.assertEqual(false_vectors, set(range(1, 128)))
        before = STATS['nonempty_restart_sets']
        m1, m2, m3 = Counter(S1), Counter(S2), Counter(S3)
        G, weighted, attempts = lift_counts(inst, 3, 'full', weights=(m1, m2))
        self.assertTrue(all(a >= 2 for a in attempts[7:]), attempts)
        self.assertGreater(STATS['nonempty_restart_sets'], before)
        self.assertEqual(sum(G.values()), 256)
        self.assertEqual(sum(weighted.values()), 256)
        log = lift_counts.last_log
        for ell in range(7, d):
            entries = [e for e in log if e[0] == ell]
            self.assertGreaterEqual(len(entries), 2)
            first_rows, first_uncertified = entries[0][2], set(entries[0][4])
            self.assertTrue(first_uncertified)
            self.assertFalse(entries[-1][4])
            for later in entries[1:]:
                self.assertNotEqual(later[2], first_rows)
                self.assertTrue(set(later[3]) <= first_uncertified)
            later_certified = set().union(*(set(e[3]) for e in entries[1:]))
            self.assertEqual(later_certified, first_uncertified)
            STATS['restart_levels'] += 1
        for kind in ('aghp',):
            fam = family(d, 6, kind)
            candidates, _ = fam.restricted(10)
            # Any six rows have a kernel meeting V: verify for the greedy's
            # own first attempt at level 10 by recomputing it.
            hist = [0] * (1 << 10)
            for i, j, z in inst.incidences:
                for a in inst.aa[i]:
                    for b in inst.bb[j]:
                        v = (a ^ b ^ z) & 1023
                        if v:
                            hist[v] += 1
            rows, masses = greedy_rows(hist, 10, candidates, 6, fam.bias)
            survivors = [v for v in range(1, 128) if apply_map(rows, v) == 0]
            self.assertTrue(survivors)
            self.assertGreater(masses[-1], 0)
        for row_kind, l1 in (('full', 2), ('aghp', 0), ('aghp', 6)):
            total, per_target, multiset_total, _, attempts = count_3xor(
                S1, S2, S3, s, d, l1=l1, kind='full', supplied_rows=supplied,
                row_kind=row_kind)
            self.assertEqual(total, brute_count(S1, S2, S3))
            self.assertTrue(all(a >= 2 for a in attempts[7:]), attempts)
            STATS['structured_restart_instances'] += 1

    def test_end_to_end_sets(self):
        rng = Random(7297)
        for _ in range(30):
            d = rng.randrange(1, 9)
            n = rng.randrange(1, 41)
            S1, S2, S3 = random_instance(rng, n, d, rng.randrange(0, 6))
            S1, S2, S3 = sorted(set(S1)), sorted(set(S2)), sorted(set(S3))
            s = rng.randrange(1, 4)
            l1 = rng.choice((0, 1, 3))
            total, per_target, multiset_total, _, _ = count_3xor(S1, S2, S3, s, d, l1)
            expected = brute_count(S1, S2, S3)
            self.assertEqual(total, expected)
            self.assertEqual(multiset_total, expected)
            for z in S3:
                self.assertEqual(per_target[z], sum(a ^ b == z for a in S1 for b in S2))
            STATS['complete_set_instances'] += 1

    def test_end_to_end_multisets(self):
        rng = Random(881)
        fixtures = [([0] * 6, [0] * 5, [0] * 7, 3),
                    ([1, 1, 2], [3, 3, 2], [2, 2, 0], 2),
                    ([5, 5, 5, 9], [12, 12, 9, 9, 5], [9, 0, 0, 1, 1], 3)]
        for _ in range(24):
            d = rng.randrange(1, 9)
            n = rng.randrange(1, 41)
            L1 = [rng.randrange(1 << d) for _ in range(rng.randrange(1, n + 1))]
            L2 = [rng.randrange(1 << d) for _ in range(rng.randrange(1, n + 1))]
            L3 = [rng.randrange(1 << d) for _ in range(rng.randrange(1, n + 1))]
            for _ in range(rng.randrange(0, 5)):
                L3.append(rng.choice(L1) ^ rng.choice(L2))
            fixtures.append((L1, L2, L3, rng.randrange(1, 4)))
        for L1, L2, L3, s in fixtures:
            d = max(1, max(L1 + L2 + L3).bit_length())
            total, per_target, multiset_total, weighted_target, _ = count_3xor(
                L1, L2, L3, s, d, l1=rng.choice((0, 2)))
            self.assertEqual(multiset_total, brute_count(L1, L2, L3))
            self.assertEqual(total, brute_count(set(L1), set(L2), set(L3)))
            for z in set(L3):
                self.assertEqual(weighted_target[z], sum(a ^ b == z for a in L1 for b in L2))
            STATS['complete_occurrence_instances'] += 1

    def test_one_list_distinct_correction(self):
        rng = Random(3307)
        for trial in range(10):
            d = rng.randrange(2, 7)
            S = rng.sample(range(1 << d), rng.randrange(1, min(20, 1 << d) + 1))
            if trial % 2 == 0 and 0 not in S:
                S.append(0)
            S = sorted(S)
            n = len(S)
            Z, _, _, _, _ = count_3xor(S, S, S, rng.randrange(1, 4), d, l1=1)
            self.assertEqual(Z, brute_count(S, S, S))
            corrected = Z - 3 * n * (0 in S) + 2 * (0 in S)
            distinct = sum(a ^ b ^ c == 0 and a != b and b != c and a != c
                           for a in S for b in S for c in S)
            self.assertEqual(corrected, distinct)
            STATS['one_list_corrections'] += 1

    def test_one_list_distinct_occurrence_correction(self):
        fixtures = [[0, 0], [0, 0, 0], [0] * 8, [1, 1, 1],
                    [0, 1, 1], [0, 0, 1, 1], [0, 1, 2, 3, 3]]
        rng = Random(2117)
        fixtures += [[rng.randrange(4) for _ in range(rng.randrange(1, 10))]
                     for _ in range(24)]
        for values in fixtures:
            d = max(1, max(values).bit_length())
            _, _, Z, _, _ = count_3xor(values, values, values, 2, d, l1=1)
            self.assertEqual(Z, brute_count(values, values, values))
            N, zeros = len(values), values.count(0)
            corrected = Z - 3 * N * zeros + 2 * zeros
            distinct = sum(values[i] ^ values[j] ^ values[k] == 0
                           for i in range(N) for j in range(N) for k in range(N)
                           if i != j and j != k and i != k)
            self.assertEqual(corrected, distinct, values)
            STATS['one_list_occurrence_corrections'] += 1

    def test_zero_padding_with_duplicate_heavy_lists(self):
        fixtures = [([0] * 7, [0] * 5, [0] * 9, 1),
                    ([0, 1] * 4, [1] * 6, [0, 1] * 5, 1),
                    ([0, 1, 2, 3] * 3, [1, 2] * 5, [0, 3] * 6, 2)]
        for A, B, C, d in fixtures:
            n = max(len(A), len(B), len(C))
            self.assertGreater(n, 1 << d)
            padded_d = max(d, (n - 1).bit_length())
            self.assertLessEqual(n, 1 << padded_d)
            for l1 in (0, 2):
                counts = count_3xor(A, B, C, 2, d, l1=l1)
                self.assertEqual(len(counts[4]), padded_d)
                self.assertEqual(counts[2], brute_count(A, B, C))
                for z in set(C):
                    self.assertEqual(counts[3][z], sum(a ^ b == z for a in A for b in B))
                STATS['zero_padding_instances'] += 1

    def test_empty_and_tiny_inputs(self):
        for L1, L2, L3 in (([], [0], [0]), ([0], [], [0]), ([0], [0], [])):
            self.assertEqual(count_3xor(L1, L2, L3, 2, 1)[0], 0)
        self.assertEqual(count_3xor([0], [0], [1], 1, 1)[0], 0)
        self.assertEqual(count_3xor([0], [0], [0], 1, 1)[0], 1)
        self.assertEqual(count_3xor([3, 5], [6, 1], [5, 2], 4, 3)[0], 2)
        self.assertEqual(count_3xor([3, 5], [6, 1], [5, 2], 1, 3, l1=4)[0], 2)
        self.assertEqual(count_3xor([3, 5, 6], [6, 1, 5], [5, 2, 3], 1, 3)[0],
                         brute_count([3, 5, 6], [6, 1, 5], [5, 2, 3]))
        STATS['empty_input_fixtures'] += 3


if __name__ == '__main__':
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(FixedLinearBucketCountingTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    print(dict(STATS))
    if result.wasSuccessful():
        print(f"PASS fixed linear buckets: {STATS['fixed_incidences']} incidences, "
              f"{STATS['prefix_levels']} levels, {STATS['attempts']} attempts, "
              f"{STATS['nonempty_restart_sets']} restarts, "
              f"{STATS['folded_products']} folded group-algebra products, "
              f"{STATS['coefficient_queries']} coefficient queries.")
    raise SystemExit(not result.wasSuccessful())
