"""Finite exact checks of the conservative five-term encoding and query lemmas.

The local tensor is the five-term construction of arXiv:2610.17420v1.
The checker validates compact encoding volumes, polynomial cut orders, the
4/2 prefix reconstruction, box closure, and direct original-array answers.
It is not a proof of the asymptotic embedding or of an APSP algorithm.
Run directly with Python 3.10+; only the standard library is used.
"""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import comb
import random
import unittest

X = [((0, 1), (2, 1)), ((0, 1), (3, -1)), ((1, 1),), ((1, 1), (3, 1)), ((0, -1), (1, -1))]
Y = [((0, 1),), ((1, 1),), ((0, 1), (2, -1)), ((1, 1), (2, 1)), ((0, 1), (1, 1))]
P, STAR = 4, 5
PX = {"p1": ((0, 1), (1, -1), (3, -1), (2, 1)), "p2": ((3, 1), (2, -1))}
SX = {"z": ((P, 1),), **PX}
PY = {"p1": ((0, 1),), "p2": ((0, 1), (2, -1))}
SY = {"z": ((P, 1),), **PY}


def encode(values, forms):
    output = {}
    def visit(arr, axis, labels):
        if axis == len(forms):
            output[labels] = arr[0]
            return
        width = len(arr) // (4 if forms[axis] is X else 3)
        for label, form in enumerate(forms[axis]):
            visit([sum(c * arr[i * width + j] for i, c in form) for j in range(width)], axis + 1, labels + (label,))
    visit(values, 0, ())
    return output


def projected(encoding, fixed, inner, prefix, split, threshold, side):
    axes = list(inner)
    dimensions, transforms, zeros = [], [], []
    suffix_axes = []
    for axis, pos in enumerate(axes):
        is_x = (pos < split) == (side == "left")
        pre = pos in prefix
        forms = (PX if is_x else PY) if pre else (SX if is_x else SY)
        transforms.append(forms)
        dimensions.append(sorted({v for terms in forms.values() for v, _ in terms}))
        zeros.append(None if pre else P)
        if not pre:
            suffix_axes.append(axis)
    def allowed(word):
        return sum(word[i] != zeros[i] for i in suffix_axes) < threshold
    values = {}
    for word in product(*dimensions):
        if not allowed(word):
            continue
        leaf = list(fixed)
        for pos, value in zip(axes, word):
            leaf[pos] = value
        values[word] = encoding[tuple(leaf)]
    source_size = len(values)
    for axis, forms in enumerate(transforms):
        dimensions[axis] = list(forms)
        if axis in suffix_axes:
            zeros[axis] = "z"
        new = {}
        for word in product(*dimensions):
            if not allowed(word):
                continue
            terms = []
            for value, coefficient in forms[word[axis]]:
                predecessor = word[:axis] + (value,) + word[axis + 1:]
                # A missing predecessor would expose an invalid truncation.
                terms.append(coefficient * values[predecessor])
            new[word] = sum(terms)
        values = new
        assert len(values) <= source_size
    return values, suffix_axes, source_size


def sparse_residual(left, right, fixed, inner, prefix, split, threshold):
    a, suffix_axes, count_a = projected(left, fixed, inner, prefix, split, threshold, "left")
    b, _, count_b = projected(right, fixed, inner, prefix, split, threshold, "right")
    M = len(suffix_axes)
    answer = 0
    for word, value in a.items():
        degree = sum(word[i] != "z" for i in suffix_axes)
        coefficient = (-1) ** (threshold - degree - 1) * comb(M - degree - 1, threshold - degree - 1)
        answer += coefficient * value * b[word]
    return answer, count_a, count_b


def residual_oracle(left, right, fixed, inner, prefix, threshold):
    answer = 0
    for labels in product(range(5), repeat=len(inner)):
        if sum(label != P for pos, label in zip(inner, labels) if pos not in prefix) >= threshold:
            continue
        leaf = list(fixed)
        for pos, label in zip(inner, labels):
            leaf[pos] = label
        leaf = tuple(leaf)
        answer += left[leaf] * right[leaf]
    return answer


def valid_box(word, split, m, threshold):
    if sum(v >= P for v in word) > 2 * m - threshold:
        return False
    for half in [word[:split], word[split:]]:
        distinguished = [v for v in half if v >= P]
        if len(distinguished) > m or distinguished != sorted(distinguished, reverse=True):
            return False
    return True


class RetainedEncoding:
    """Read guard for the actual global and separate half retention budgets."""
    def __init__(self, values, split, m, ell):
        self.values, self.split, self.m, self.ell = values, split, m, ell

    def __getitem__(self, word):
        first = sum(v == P for v in word[:self.split])
        second = sum(v == P for v in word[self.split:])
        assert first <= self.m and second <= self.m
        assert first + second <= 2 * (self.m - self.ell)
        return self.values[word]


class BalancedTests(unittest.TestCase):
    def test_sparse_residual_and_source_counts(self):
        rng = random.Random(998173)
        cases = 0
        for L, m in [(1, 1), (2, 1), (2, 2), (3, 2)]:
            left = encode([rng.randrange(-3, 4) for _ in range(12 ** L)], [X] * L + [Y] * L)
            right = encode([rng.randrange(-3, 4) for _ in range(12 ** L)], [Y] * L + [X] * L)
            for q0 in combinations(range(L), m):
                for q1 in combinations(range(L, 2 * L), m):
                    inner = q0 + q1
                    fixed = [P if pos in inner else rng.randrange(4) for pos in range(2 * L)]
                    for ell in range(m):
                        prefix = set(q0[:ell] + q1[:ell])
                        for threshold in range(max(1, 2 * ell), 2 * (m - ell) + 1):
                            stored_left = RetainedEncoding(left, L, m, ell)
                            stored_right = RetainedEncoding(right, L, m, ell)
                            got, na, nb = sparse_residual(stored_left, stored_right, fixed, inner, prefix, L, threshold)
                            expected = residual_oracle(left, right, fixed, inner, prefix, threshold)
                            self.assertEqual(got, expected)
                            size = 8 ** ell * sum(comb(m - ell, a) * comb(m - ell, b) * 4 ** a * 2 ** b for a in range(m - ell + 1) for b in range(m - ell + 1) if a + b < threshold)
                            self.assertEqual(na, size)
                            self.assertEqual(nb, size)
                            cases += 1
        print("Sparse residual identities and counts:", cases)

    def test_balanced_box_dp_and_full_partition(self):
        rng = random.Random(17713)
        cases = 0
        for L, m in [(1, 1), (2, 1), (2, 2), (3, 2)]:
            left = encode([rng.randrange(-2, 3) for _ in range(12 ** L)], [X] * L + [Y] * L)
            right = encode([rng.randrange(-2, 3) for _ in range(12 ** L)], [Y] * L + [X] * L)
            for q0 in combinations(range(L), m):
                for q1 in combinations(range(L, 2 * L), m):
                    inner = q0 + q1
                    fixed = [P if pos in inner else rng.randrange(4) for pos in range(2 * L)]
                    for ell in range(m):
                        prefix = set(q0[:ell] + q1[:ell])
                        suffix = tuple(pos for pos in inner if pos not in prefix)
                        for threshold in range(max(1, 2 * ell), len(suffix) + 1):
                            stored_left = RetainedEncoding(left, L, m, ell)
                            stored_right = RetainedEncoding(right, L, m, ell)
                            @lru_cache(None)
                            def box(word):
                                assert valid_box(word, L, m, threshold)
                                if STAR not in word:
                                    return stored_left[word] * stored_right[word]
                                pos = max(i for i, v in enumerate(word) if v == STAR)
                                return sum(box(word[:pos] + (v,) + word[pos + 1:]) for v in range(5))
                            got, _, _ = sparse_residual(stored_left, stored_right, fixed, inner, prefix, L, threshold)
                            boxes = 0
                            for chosen in combinations(suffix, len(suffix) - threshold):
                                v = set(chosen)
                                stars = set(prefix)
                                for pos in suffix:
                                    if pos not in v:
                                        break
                                    stars.add(pos)
                                nonprivate = tuple(pos for pos in suffix if pos not in v)
                                for labels in product(range(4), repeat=threshold):
                                    word = list(fixed)
                                    for pos in stars:
                                        word[pos] = STAR
                                    for pos, value in zip(nonprivate, labels):
                                        word[pos] = value
                                    got += box(tuple(word))
                                    boxes += 1
                            self.assertEqual(boxes, 4 ** threshold * comb(len(suffix), threshold))
                            expected = residual_oracle(left, right, fixed, inner, set(), 2 * m + 1)
                            self.assertEqual(got, expected)
                            cases += 1
        print("Full balanced partitions with closed box DP:", cases)


def rational_rank(rows):
    a = [[Fraction(v) for v in row] for row in rows]
    r = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        scale = a[r][col]
        a[r] = [v / scale for v in a[r]]
        for i in range(len(a)):
            if i != r and a[i][col]:
                scale = a[i][col]
                a[i] = [v - scale * w for v, w in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


class EncodingVolumeTests(unittest.TestCase):
    def test_local_identity_and_conservative_access(self):
        # Sum of the five local leaf kernels is p1*y1+p2*q.
        coefficients = [[0] * 3 for _ in range(4)]
        for xf, yf in zip(X, Y):
            for i, a in xf:
                for j, b in yf:
                    coefficients[i][j] += a * b
        self.assertEqual(coefficients, [[0, 0, 0], [0, 0, 0], [1, 0, 0], [0, 0, 1]])
        for transforms, forms, dimension, targets in (
            (PX, X, 4, {"p1": 2, "p2": 3}),
            (PY, Y, 3, {"p1": 0, "p2": 2}),
        ):
            for name, terms in transforms.items():
                vector = [0] * dimension
                for label, weight in terms:
                    self.assertNotEqual(label, P)
                    for index, coefficient in forms[label]:
                        vector[index] += weight * coefficient
                self.assertEqual(vector, [int(i == targets[name]) for i in range(dimension)])
        left = [tuple(sum(c for j, c in form if j == i) for i in range(4)) for form in X]
        targets = [(0, 0, 1, 0), (0, 0, 0, 1)]
        for subset in combinations(left, 3):
            self.assertGreater(rational_rank(subset + tuple(targets)), rational_rank(subset))
        self.assertEqual(rational_rank(left[:4]), rational_rank(left[:4] + targets))
        print("Local tensor identity, conservative coordinate recovery, and three-form rank checks: 15")

    def test_per_half_prefix_array_volumes(self):
        checks = 0
        for m in range(1, 9):
            for L in range(5 * m, 10 * m + 1):
                S = sum(comb(L, j) * 4 ** (L - j) for j in range(m + 1))
                self.assertGreaterEqual(S * S, 12 ** L)
                for k in range(L + 1):
                    prefixes = sum(comb(k, j) * 4 ** (k - j) for j in range(min(k, m) + 1))
                    self.assertLessEqual(prefixes * 4 ** (L - k), S)
                    self.assertLessEqual(prefixes * 4 ** (L - k) * 3 ** L, S * S)
                    self.assertLessEqual(prefixes * 3 ** (L - k) * 4 ** L, S * S)
                    self.assertLessEqual(S * prefixes * 4 ** (L - k), S * S)
                    checks += 1
        print("Per-half prefix and internal-array volume cases:", checks)

    def test_global_retention_budget_volume(self):
        checks = 0
        for L, m in [(6, 1), (10, 2), (15, 3), (20, 4)]:
            for ell in range(m + 1):
                budget = 2 * (m - ell)
                retained = sum(comb(L, j) * comb(L, k) * 4 ** (2 * L - j - k)
                               for j in range(m + 1) for k in range(m + 1)
                               if j + k <= budget)
                # Every remaining local input alphabet has size at most four.
                self.assertGreaterEqual(retained, 4 ** (2 * L))
                for first in range(L + 1):
                    for second in range(L + 1):
                        prefixes = sum(comb(first, j) * comb(second, k) * 4 ** (first + second - j - k)
                                       for j in range(min(first, m) + 1)
                                       for k in range(min(second, m) + 1)
                                       if j + k <= budget)
                        self.assertLessEqual(prefixes * 4 ** (2 * L - first - second), retained)
                        checks += 1
        print("Global retained-region internal-array volume cases:", checks)

    def test_polynomial_cut_orders(self):
        checks = 0
        for L in range(1, 7):
            for m in range(1, L + 1):
                for q0 in combinations(range(L), m):
                    for q1 in combinations(range(L), m):
                        for ell in range(m + 1):
                            p0 = q0[ell - 1] if ell else -1
                            p1 = q1[ell - 1] if ell else -1
                            first = [(0, j) for j in range(p0 + 1)] + [(1, j) for j in range(p1 + 1)]
                            rest = [(0, j) for j in range(p0 + 1, L)] + [(1, j) for j in range(p1 + 1, L)]
                            inner = {(0, j) for j in q0} | {(1, j) for j in q1}
                            prefix = [p for p in first + rest if p in inner][:2 * ell]
                            self.assertEqual(sum(h == 0 for h, _ in prefix), ell)
                            self.assertEqual(sum(h == 1 for h, _ in prefix), ell)
                            checks += 1
        print("Balanced prefix cut-order cases:", checks)

    def test_weighted_coefficient_bound(self):
        checks = 0
        for m in range(1, 7):
            for ell in range(m + 1):
                rem = m - ell
                for threshold in range(1, 2 * rem + 1):
                    actual = sum(comb(rem, a) * comb(rem, b) * 4 ** a * 2 ** b
                                 for a in range(rem + 1) for b in range(rem + 1)
                                 if a + b < threshold)
                    coarse = sum(comb(2 * rem, d) * 3 ** d for d in range(threshold))
                    self.assertLessEqual(actual, coarse)
                    for x in (Fraction(1, 20), Fraction(1, 7), Fraction(1, 2)):
                        bound = x ** (-threshold) * ((1 + 4 * x) * (1 + 2 * x)) ** rem
                        self.assertLessEqual(actual, bound)
                        checks += 1
        print("Weighted 4/2 coefficient bounds:", checks)


if __name__ == "__main__":
    unittest.main(verbosity=2)
