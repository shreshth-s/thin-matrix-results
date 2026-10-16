#!/usr/bin/env python3
"""Finite exact checks for the five-term cyclic-ring fiber construction.

Standard library only.  Polynomials are coefficient tuples in Z[x]/(x^q-1).
Schoolbook multiplication below is a finite oracle, not the claimed fast
ring-arithmetic implementation.  These tests check the lift, its padding,
the actual local five-term identity, and the asymmetric query operations;
they do not prove asymptotic costs or implement the complete APSP algorithm.
"""
from functools import lru_cache
from itertools import combinations, product
from math import comb, gcd, isqrt
from random import Random
import unittest


def zero(q):
    return (0,) * q


def add(a, b):
    assert len(a) == len(b)
    return tuple(x + y for x, y in zip(a, b))


def scale(weight, a):
    return tuple(weight * x for x in a)


def ring_sum(values, q):
    answer = zero(q)
    for value in values:
        answer = add(answer, value)
    return answer


def multiply(a, b):
    assert len(a) == len(b)
    q = len(a)
    out = [0] * q
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[(i + j) % q] += x * y
    return tuple(out)


def target_product(a, b, target):
    """Read one product coefficient with exactly q scalar multiplications."""
    assert len(a) == len(b)
    return sum(a[j] * b[(target - j) % len(a)] for j in range(len(a)))


def ring_product(values, q):
    answer = (1,) + (0,) * (q - 1)
    for value in values:
        answer = multiply(answer, value)
    return answer


def monomial(weight, q):
    out = [0] * q
    out[weight % q] = 1
    return tuple(out)


def fold(left, right, d, q, pad_outer=1, pad_middle=1):
    """Form the old d-folded matrices with ring-valued nonzero entries.

    left[a][c] and right[c][b] are signed weights.  Only actual vertices
    contribute; appended outer and middle vertices consist entirely of zeros.
    Both outer digit dimensions are padded to ceil(sqrt(d)).  Digit pairs
    representing a number >=d are not queried and need not be zero.
    """
    if d < 1 or q < 1 or gcd(d, q) != 1:
        raise ValueError('positive coprime base and fiber moduli required')
    rows, h, cols = len(left), len(right), len(right[0])
    assert all(len(row) == h for row in left)
    assert all(len(row) == cols for row in right)
    width = isqrt(d)
    width += width * width < d
    middle = (h + pad_middle) * d
    x = [[zero(q) for _ in range(middle)]
         for __ in range((rows + pad_outer) * width)]
    y = [[zero(q) for _ in range((cols + pad_outer) * width)]
         for __ in range(middle)]
    for a in range(rows):
        for rho1 in range(width):
            for c in range(h):
                residue = (left[a][c] + rho1) % d
                x[a * width + rho1][c * d + residue] = monomial(left[a][c], q)
    for b in range(cols):
        for rho2 in range(width):
            for c in range(h):
                residue = (-right[c][b] - width * rho2) % d
                y[c * d + residue][b * width + rho2] = monomial(right[c][b], q)
    return x, y, width


def entry(x, y, row, col, q):
    return ring_sum((multiply(a, y[c][col]) for c, a in enumerate(x[row])), q)


def incidence_run(instances, pool, factors, freeze_after, stages, use_ring):
    """Finite composite certification with a scalar or cyclic-ring oracle.

    An incidence maps to (left weights, right weights, outer weight).  The
    exact maximum number of candidate-prime divisors is used as lambda;
    prime density and the asymptotic choice of an interval are not tested.
    The trace records every candidate count and the final original-sum scans.
    """
    assert 0 <= freeze_after <= factors <= len(pool)
    sums = {key: [a + b + outer for a, b in zip(left, right)]
            for key, (left, right, outer) in instances.items()}
    lam = max((sum(value % p == 0 for p in pool)
               for values in sums.values() for value in values if value), default=0)
    assert len(pool) - factors + 1 > lam
    active, marked, trace = set(instances), set(), []
    cache = {}

    def count(key, d, q):
        if not use_ring:
            return sum(value % (d * q) == 0 for value in sums[key])
        if (key, d, q) not in cache:
            left, right, outer = instances[key]
            x, y, width = fold([left], [[value] for value in right], d, q,
                               pad_outer=0, pad_middle=0)
            residue = outer % d
            polynomial = entry(x, y, residue % width, residue // width, q)
            cache[key, d, q] = polynomial[-outer % q]
        return cache[key, d, q]

    for _ in range(stages):
        if not active:
            break
        available, modulus, frozen = list(pool), 1, 1
        stage_trace = []
        base = {key: len(sums[key]) for key in active}
        for j in range(factors):
            candidates = {}
            for p in available:
                d, q = ((modulus * p, 1) if j < freeze_after else
                        (frozen, (modulus // frozen) * p))
                candidates[p] = {key: count(key, d, q) for key in sorted(active)}
            stage_trace.append(tuple((p, tuple(candidates[p].items())) for p in available))
            if j == factors - 1:
                break
            chosen = min(available, key=lambda p: sum(candidates[p].values()))
            old_false = sum(base[key] - sums[key].count(0) for key in active)
            new_false = sum(candidates[chosen][key] - sums[key].count(0) for key in active)
            assert len(available) * new_false <= lam * old_false
            modulus *= chosen
            if j + 1 <= freeze_after:
                frozen = modulus
            base = candidates[chosen]
            available.remove(chosen)
            stage_trace.append(('selected', chosen))
        mu = {key: min(candidates[p][key] for p in available) for key in active}
        statuses = {}
        for key in sorted(active):
            if mu[key] == 0:
                statuses[key] = 'false'
                assert 0 not in sums[key]
            elif len(available) * mu[key] > lam * base[key]:
                statuses[key] = 'true'
                assert 0 in sums[key]
                marked.add(key[:2])
            else:
                statuses[key] = 'uncertified'
                assert lam * (base[key] - sums[key].count(0)) >= len(available) - lam
        previous = active
        active = {key for key in previous
                  if statuses[key] == 'uncertified' and key[:2] not in marked}
        assert all(key in active for key in previous if 0 in sums[key] and key[:2] not in marked)
        assert (len(available) - lam) * len(active) <= lam * sum(
            base[key] - sums[key].count(0) for key in previous)
        trace.append((tuple(stage_trace), tuple(sorted(base.items())), tuple(sorted(mu.items())),
                      tuple(sorted(statuses.items())), tuple(sorted(active))))
    scans = []
    for key in sorted(active):
        if key[:2] in marked:
            continue
        scanned = []
        for value in sums[key]:
            scanned.append(value)
            if value == 0:
                marked.add(key[:2])
                break
        scans.append((key, tuple(scanned)))
    assert marked == {key[:2] for key in sums if 0 in sums[key]}
    return tuple(trace), tuple(scans), marked


# Complete r=0 five-term sparse-query audit, derived from the independent
# ring-audit/check_ring_query.py.  The r0_ prefix separates its instrumented
# ring operations from the elementary folding tests above.  Grid enumeration
# is a finite oracle; the asymptotic algorithm generates truncated grids.
from functools import lru_cache
from itertools import combinations, product
from math import comb
from random import Random


r0_PHI = (((0, 1), (2, 1)), ((0, 1), (3, -1)), ((1, 1),),
       ((1, 1), (3, 1)), ((0, -1), (1, -1)))
r0_PSI = (((0, 1),), ((1, 1),), ((0, 1), (2, -1)),
       ((1, 1), (2, 1)), ((0, 1), (1, 1)))
r0_P, r0_STAR = 4, 7
r0_NORMAL = {'z': ((r0_P, 1),), 'a': ((0, 1), (r0_P, 1), (2, 1)),
          'b': ((3, 1), (2, -1))}
r0_OPPOSITE = {'z': ((r0_P, 1),), 'a': ((0, 1),), 'b': ((0, 1), (2, -1))}
r0_OPS = dict(full_ring_products=0, convolution_coefficient_products=0,
           linear_coefficient_adds=0, linear_coefficient_scales=0,
           target_coefficient_products=0)


class r0_Ring:
    __slots__ = ('coefficients',)

    def __init__(self, coefficients):
        self.coefficients = tuple(coefficients)

    def __add__(self, other):
        if other == 0:
            return self
        assert isinstance(other, r0_Ring) and len(self.coefficients) == len(other.coefficients)
        r0_OPS['linear_coefficient_adds'] += len(self.coefficients)
        return r0_Ring(a + b for a, b in zip(self.coefficients, other.coefficients))

    __radd__ = __add__

    def __mul__(self, other):
        if isinstance(other, int):
            r0_OPS['linear_coefficient_scales'] += len(self.coefficients)
            return r0_Ring(other * a for a in self.coefficients)
        assert isinstance(other, r0_Ring) and len(self.coefficients) == len(other.coefficients)
        q = len(self.coefficients)
        r0_OPS['full_ring_products'] += 1
        r0_OPS['convolution_coefficient_products'] += q * q
        return r0_Ring(sum(self.coefficients[a] * other.coefficients[(b-a) % q]
                        for a in range(q)) for b in range(q))

    __rmul__ = __mul__

    def __eq__(self, other):
        return isinstance(other, r0_Ring) and self.coefficients == other.coefficients


def r0_target_product(left, right, target):
    q = len(left.coefficients)
    assert len(right.coefficients) == q and 0 <= target < q
    r0_OPS['target_coefficient_products'] += q
    return sum(left.coefficients[a] * right.coefficients[(target-a) % q] for a in range(q))


def r0_is_normal(pos, length, side):
    return (pos < length) == (side == 'left')


def r0_encode(array, length, degree, cutoff, side, full, stats):
    """Full individual caps or smaller high-box total cap; no other leaves."""
    table = {}
    volumes = [0] * (2 * length + 1)
    q = len(array[0].coefficients)

    def visit(values, pos, word, zeros):
        volumes[pos] += len(values)
        if pos == 2 * length:
            table[word] = values[0]
            return
        normal = r0_is_normal(pos, length, side)
        forms = r0_PHI if normal else r0_PSI
        dimension = 4 if normal else 3
        width = len(values) // dimension
        labels = list(range(4))
        if zeros[pos // length] < degree and (full or sum(zeros) < 2 * degree - cutoff):
            labels.append(r0_P)
        for label in labels:
            new_zeros = list(zeros)
            new_zeros[pos // length] += label == r0_P
            child = [sum(coefficient * values[index * width + j]
                         for index, coefficient in forms[label]) for j in range(width)]
            visit(child, pos + 1, word + (label,), new_zeros)

    visit(array, 0, (), [0, 0])
    expected = sum(comb(length, a) * comb(length, b) * 4 ** (2 * length - a - b)
                   for a in range(degree + 1) for b in range(degree + 1)
                   if full or a + b <= 2 * degree - cutoff)
    assert len(table) == expected
    assert all(v <= len(table) for v in volumes)
    assert sum(volumes) <= (2 * length + 1) * len(table)
    assert all(q * v <= q * len(table) for v in volumes)
    stats['encoders'] += 1
    stats['encoder_layers'] += len(volumes)
    stats['encoder_internal_coefficients'] += q * sum(volumes)
    stats['encoded_coefficients'] += q * len(table)
    return table


def r0_projected(table, fixed, inner, length, degree, cutoff, side, stats):
    transforms = [r0_NORMAL if r0_is_normal(pos, length, side) else r0_OPPOSITE for pos in inner]
    dimensions = [sorted({label for form in forms.values() for label, _ in form}) for forms in transforms]
    zero = [r0_P] * len(inner)

    def order(word):
        return sum(a != b for a, b in zip(word, zero))

    values = {}
    for word in product(*dimensions):
        if order(word) >= cutoff:
            continue
        leaf = list(fixed)
        for pos, label in zip(inner, word):
            leaf[pos] = label
        leaf = tuple(leaf)
        assert all(label <= r0_P for label in leaf)
        assert leaf[:length].count(r0_P) <= degree and leaf[length:].count(r0_P) <= degree
        values[word] = table[leaf]
        stats['source_lookups'] += 1
    initial_count = len(values)
    expected = sum(comb(degree, a) * comb(degree, b) * 3 ** a * 2 ** b
                   for a in range(degree + 1) for b in range(degree + 1) if a + b < cutoff)
    assert initial_count == expected
    q = len(next(iter(values.values())).coefficients)
    stats['transform_coefficients'] += q * len(values)
    for axis, forms in enumerate(transforms):
        old_zero = zero[:]
        dimensions[axis] = tuple(forms)
        zero[axis] = 'z'
        updated = {}
        for word in product(*dimensions):
            if order(word) >= cutoff:
                continue
            value = 0
            for label, coefficient in forms[word[axis]]:
                predecessor = word[:axis] + (label,) + word[axis+1:]
                assert sum(a != b for a, b in zip(predecessor, old_zero)) <= order(word) < cutoff
                assert predecessor in values
                value += coefficient * values[predecessor]
                stats['predecessors'] += 1
                stats['predecessor_coefficients'] += q
            updated[word] = value
        values = updated
        assert len(values) <= initial_count
        stats['transform_layers'] += 1
        stats['transform_coefficients'] += q * len(values)
    return values


def r0_valid_box(word, length, degree, cutoff):
    if sum(label in (r0_P, r0_STAR) for label in word) > 2 * degree - cutoff:
        return False
    if any(sum(label in (r0_P, r0_STAR) for label in half) > degree for half in (word[:length], word[length:])):
        return False
    special = [label for label in word if label in (r0_P, r0_STAR)]
    return special == sorted(special, reverse=True)


def r0_box_words(length, degree, cutoff):
    """Generate the permitted DP language directly, without a full grid."""
    def visit(word, counts, private_seen):
        if len(word) == 2 * length:
            yield word
            return
        for label in range(4):
            yield from visit(word + (label,), counts, private_seen)
        half = len(word) // length
        if counts[half] < degree and sum(counts) < 2 * degree - cutoff:
            new_counts = list(counts)
            new_counts[half] += 1
            yield from visit(word + (r0_P,), new_counts, True)
            if not private_seen:
                yield from visit(word + (r0_STAR,), new_counts, False)
    yield from visit((), [0, 0], False)


def r0_make_boxes(left, right, length, degree, cutoff, stats):
    @lru_cache(None)
    def box(word):
        assert r0_valid_box(word, length, degree, cutoff)
        stats['box_states'] += 1
        if r0_STAR not in word:
            stats['box_leaves'] += 1
            return left[word] * right[word]
        pos = max(j for j, label in enumerate(word) if label == r0_STAR)
        return sum(box(word[:pos] + (label,) + word[pos+1:]) for label in range(5))

    table = {}
    for word in r0_box_words(length, degree, cutoff):
        table[word] = box(word)
    assert len(table) == box.cache_info().currsize
    stats['box_coefficients'] += len(next(iter(table.values())).coefficients) * len(table)
    return table


def r0_complete_target_query(full_left, full_right, boxes, fixed, inner, length, degree, cutoff, target, stats):
    before_products = r0_OPS['full_ring_products']
    left = r0_projected(full_left, fixed, inner, length, degree, cutoff, 'left', stats)
    right = r0_projected(full_right, fixed, inner, length, degree, cutoff, 'right', stats)
    assert left.keys() == right.keys()
    answer = 0
    target_before = r0_OPS['target_coefficient_products']
    for word, value in left.items():
        order = sum(label != 'z' for label in word)
        coefficient = (-1) ** (cutoff-order-1) * comb(2*degree-order-1, cutoff-order-1)
        answer += coefficient * r0_target_product(value, right[word], target)
    q = len(next(iter(left.values())).coefficients)
    assert r0_OPS['target_coefficient_products'] - target_before == q * len(left)
    stats['residual_terms'] += len(left)
    reads = 0
    for marked_tuple in combinations(inner, 2*degree-cutoff):
        marked = set(marked_tuple)
        stars = set()
        for pos in inner:
            if pos not in marked:
                break
            stars.add(pos)
        switched = tuple(pos for pos in inner if pos not in marked)
        for labels in product(range(4), repeat=cutoff):
            word = list(fixed)
            for pos in stars:
                word[pos] = r0_STAR
            for pos, label in zip(switched, labels):
                word[pos] = label
            word = tuple(word)
            assert r0_valid_box(word, length, degree, cutoff)
            answer += boxes[word].coefficients[target]
            reads += 1
    assert reads == 4 ** cutoff * comb(2*degree, cutoff)
    assert r0_OPS['full_ring_products'] == before_products
    stats['target_box_reads'] += reads
    return answer


def r0_direct_scalar(array, dimensions, forms):
    result = 0
    for entries in product(*forms):
        index = 0
        coefficient = 1
        for dimension, (entry, weight) in zip(dimensions, entries):
            index = index * dimension + entry
            coefficient *= weight
        result += coefficient * array[index]
    return result


def r0_original_array_oracle(left, right, length, fixed, inner):
    result = 0
    for choices in product(range(2), repeat=len(inner)):
        choice = dict(zip(inner, choices))
        left_forms, right_forms = [], []
        for pos in range(2*length):
            if pos in choice:
                phi = ((2 + choice[pos], 1),)
                psi = ((0 if choice[pos] == 0 else 2, 1),)
            else:
                phi, psi = r0_PHI[fixed[pos]], r0_PSI[fixed[pos]]
            left_forms.append(phi if pos < length else psi)
            right_forms.append(psi if pos < length else phi)
        result += r0_direct_scalar(left, [4]*length+[3]*length, left_forms) * r0_direct_scalar(right, [3]*length+[4]*length, right_forms)
    return result


def r0_main():
    rng = Random(202610150299)
    stats = dict.fromkeys(('encoders', 'encoder_layers', 'encoder_internal_coefficients',
                          'encoded_coefficients', 'source_lookups', 'predecessors',
                          'predecessor_coefficients', 'transform_layers', 'transform_coefficients',
                          'box_states', 'box_leaves', 'box_coefficients', 'residual_terms',
                          'target_box_reads', 'queries', 'asymmetric_queries', 'composite_queries'), 0)
    fixtures = ((1, 1), (2, 1), (2, 2), (3, 1), (3, 2))
    for q in (1, 2, 3, 4, 6):
        for length, degree in fixtures:
            left = [r0_Ring(rng.choice((-3, -2, -1, 1, 2, 3)) for _ in range(q)) for _ in range(12**length)]
            right = [r0_Ring(rng.choice((-3, -2, -1, 1, 2, 3)) for _ in range(q)) for _ in range(12**length)]
            full_left = r0_encode(left, length, degree, 1, 'left', True, stats)
            full_right = r0_encode(right, length, degree, 1, 'right', True, stats)
            slots = list(combinations(range(length), degree))
            pairs = list(product(slots, repeat=2)) if length <= 2 else [(slots[0], slots[0]), (slots[0], slots[-1]), (slots[-1], slots[0])]
            queries = []
            for q0, q1 in pairs:
                inner = q0 + tuple(length+j for j in q1)
                fixed = tuple(r0_P if pos in inner else rng.randrange(4) for pos in range(2*length))
                expected = r0_original_array_oracle(left, right, length, fixed, inner)
                queries.append((q0, q1, inner, fixed, expected))
            for cutoff in range(1, 2*degree+1):
                ordinary_left = r0_encode(left, length, degree, cutoff, 'left', False, stats)
                ordinary_right = r0_encode(right, length, degree, cutoff, 'right', False, stats)
                boxes = r0_make_boxes(ordinary_left, ordinary_right, length, degree, cutoff, stats)
                for q0, q1, inner, fixed, expected in queries:
                    for target in range(q):
                        got = r0_complete_target_query(full_left, full_right, boxes, fixed, inner, length, degree, cutoff, target, stats)
                        assert got == expected.coefficients[target], (q, length, degree, cutoff, q0, q1, target, got, expected.coefficients)
                        stats['queries'] += 1
                        stats['asymmetric_queries'] += q0 != q1
                        stats['composite_queries'] += q in (4, 6)
    assert stats['asymmetric_queries'] and stats['composite_queries']
    assert r0_OPS['target_coefficient_products'] > stats['residual_terms']
    print('PASS original-array cyclic-ring target queries:', stats)
    print('Exact coefficient operation counts:', r0_OPS)
    print('PASS: every encoder layer and sparse-transform layer obeys its q-scaled volume bound; every predecessor and box leaf is stored; no full ring multiplication occurs during queries.')




class FiveTermRingTests(unittest.TestCase):
    def test_complete_sparse_ring_queries_against_original_arrays(self):
        r0_main()

    def test_folded_signed_composite_counts_and_padding(self):
        rng = Random(261010415)
        pair_count = 0
        for d, q in ((1, 1), (1, 6), (2, 9), (6, 35), (5, 6), (7, 10), (15, 14)):
            for trial in range(12):
                rows, cols, h = 1 + trial % 3, 1 + (trial // 3) % 3, 1 + trial % 4
                left = [[rng.randrange(-40, 41) for _ in range(h)] for __ in range(rows)]
                right = [[rng.randrange(-40, 41) for _ in range(cols)] for __ in range(h)]
                outer = [[rng.randrange(-40, 41) for _ in range(cols)] for __ in range(rows)]
                outer[0][0] = -left[0][0] - right[0][0]
                x, y, width = fold(left, right, d, q, pad_outer=1, pad_middle=2)
                self.assertEqual(len(x), (rows + 1) * width)
                self.assertEqual(len(y), (h + 2) * d)
                self.assertEqual(len(y[0]), (cols + 1) * width)
                self.assertTrue(all(v == zero(q) for row in x for v in row[h * d:]))
                self.assertTrue(all(v == zero(q) for row in y[h * d:] for v in row))
                self.assertTrue(all(v == zero(q) for row in x[rows * width:] for v in row))
                self.assertTrue(all(v == zero(q) for row in y for v in row[cols * width:]))
                for a, b in product(range(rows), range(cols)):
                    residue = outer[a][b] % d
                    rho1, rho2 = residue % width, residue // width
                    self.assertLess(rho1 + width * rho2, d)
                    actual = entry(x, y, a * width + rho1, b * width + rho2, q)
                    expected = [0] * q
                    sums = []
                    for c in range(h):
                        value = left[a][c] + right[c][b] + outer[a][b]
                        sums.append(value)
                        if value % d == 0:
                            expected[(left[a][c] + right[c][b]) % q] += 1
                    self.assertEqual(actual, tuple(expected))
                    self.assertEqual(actual[-outer[a][b] % q],
                                     sum(value % (d * q) == 0 for value in sums))
                    self.assertEqual(sum(actual), sum(value % d == 0 for value in sums))
                    pair_count += 1
                self.assertEqual(entry(x, y, rows * width, 0, q), zero(q))
                self.assertEqual(entry(x, y, 0, cols * width, q), zero(q))
        self.assertEqual(pair_count, 294)

    def test_coprimality_is_necessary(self):
        # S=30 vanishes modulo 6 and 10 but not modulo their product 60.
        self.assertEqual(30 % 6, 0)
        self.assertEqual(30 % 10, 0)
        self.assertNotEqual(30 % 60, 0)
        with self.assertRaises(ValueError):
            fold([[10]], [[20]], 6, 10)

    def test_actual_local_five_term_identity(self):
        rng = Random(502613)
        for q in (1, 2, 4, 6, 15):
            for _ in range(60):
                x1, x2, p1, p2, y1, y2, z = [
                    tuple(rng.randrange(-4, 5) for __ in range(q)) for ___ in range(7)]
                phi = (add(x1, p1), add(x1, scale(-1, p2)), x2,
                       add(x2, p2), scale(-1, add(x1, x2)))
                psi = (y1, y2, add(y1, scale(-1, z)), add(y2, z), add(y1, y2))
                actual = ring_sum((multiply(a, b) for a, b in zip(phi, psi)), q)
                expected = add(multiply(p1, y1), multiply(p2, z))
                self.assertEqual(actual, expected)
                self.assertEqual(ring_sum((multiply(b, a) for a, b in zip(phi, psi)), q), expected)
                for target in range(q):
                    self.assertEqual(sum(target_product(a, b, target) for a, b in zip(phi, psi)),
                                     expected[target])

    def test_residual_target_coefficient_dot_product(self):
        rng = Random(60426)
        for q in (1, 2, 5, 6, 21):
            for _ in range(60):
                left = tuple(rng.randrange(-8, 9) for __ in range(q))
                right = tuple(rng.randrange(-8, 9) for __ in range(q))
                full = multiply(left, right)
                for target in range(q):
                    self.assertEqual(target_product(left, right, target), full[target])

    def test_preprocessed_boxes_use_one_coefficient_each(self):
        rng = Random(20261015)
        for q in (1, 2, 6, 15):
            for _ in range(20):
                leaves = {labels: tuple(rng.randrange(-9, 10) for __ in range(q))
                          for labels in product(range(5), repeat=3)}

                @lru_cache(None)
                def box(word):
                    if -1 not in word:
                        return leaves[word]
                    pos = word.index(-1)
                    return ring_sum((box(word[:pos] + (label,) + word[pos + 1:])
                                     for label in range(5)), q)

                words = [(-1, 0, -1), (2, -1, 1), (-1, -1, -1), (3, 4, 2)]
                stored = [box(word) for word in words]
                weights = [rng.randrange(-5, 6) for __ in words]
                full = ring_sum((scale(w, value) for w, value in zip(weights, stored)), q)
                for target in range(q):
                    reads = 0
                    scalar = 0
                    for weight, value in zip(weights, stored):
                        scalar += weight * value[target]
                        reads += 1
                    self.assertEqual(scalar, full[target])
                    self.assertEqual(reads, len(words))
                for word, value in zip(words, stored):
                    direct = ring_sum((leaf for labels, leaf in leaves.items()
                                       if all(a == -1 or a == b for a, b in zip(word, labels))), q)
                    self.assertEqual(value, direct)

    def test_prefix_partition_over_cyclic_ring(self):
        rng = Random(26017420)
        for q in (1, 2, 5, 6):
            for _ in range(20):
                # Label 0 is distinguished; four remaining labels switch.
                coordinates, prefix_size = 4, 2
                leaves = [[tuple(rng.randrange(-2, 3) for ___ in range(q))
                           for __ in range(5)] for ____ in range(coordinates)]
                inner = [ring_sum(local, q) for local in leaves]
                prefix = ring_product(inner[:prefix_size], q)
                tail = coordinates - prefix_size
                for cutoff in range(1, tail + 1):
                    residual = zero(q)
                    for mask in range(1 << tail):
                        degree = mask.bit_count()
                        if degree >= cutoff:
                            continue
                        weight = (-1) ** (cutoff - degree - 1) * comb(
                            tail - degree - 1, cutoff - degree - 1)
                        factors = [inner[prefix_size + j] if mask >> j & 1 else
                                   leaves[prefix_size + j][0] for j in range(tail)]
                        residual = add(residual, scale(weight, multiply(prefix, ring_product(factors, q))))
                    boxes = ring_sum((ring_product([leaves[j][label] for j, label in enumerate(labels)], q)
                                      for labels in product(range(5), repeat=coordinates)
                                      if sum(label != 0 for label in labels[prefix_size:]) >= cutoff), q)
                    full = ring_product(inner, q)
                    self.assertEqual(add(residual, boxes), full)
                    for target in range(q):
                        self.assertEqual(residual[target] + boxes[target], full[target])

    def test_frozen_base_multi_prime_intermediates(self):
        rng = Random(123457)
        primes = (2, 3, 5, 7)
        checked = 0
        for cut in range(len(primes) + 1):
            d = 1
            for p in primes[:cut]:
                d *= p
            q = 1
            # Include the frozen-base boundary q=1 and each later prefix.
            for stage in range(cut, len(primes) + 1):
                if stage > cut:
                    q *= primes[stage - 1]
                for _ in range(3):
                    left = [[rng.randrange(-25, 26) for __ in range(3)]]
                    right = [[rng.randrange(-25, 26)] for __ in range(3)]
                    outer = rng.randrange(-25, 26)
                    x, y, width = fold(left, right, d, q, pad_outer=0, pad_middle=0)
                    residue = outer % d
                    value = entry(x, y, residue % width, residue // width, q)
                    expected = sum((left[0][c] + right[c][0] + outer) % (d * q) == 0
                                   for c in range(3))
                    self.assertEqual(value[-outer % q], expected)
                    checked += 1
        self.assertEqual(checked, 45)

    def test_incidence_selection_certification_and_scans(self):
        pool = (2, 3, 5, 7, 11, 13, 17, 19)
        # All prime pairs occur equally often.  A true incidence survives
        # round one because its five false witnesses inflate the base count.
        instances = {(0, 0, k): ([p * q] * 5 + [0 if k == 0 else 1], [0] * 6, 0)
                     for k, (p, q) in enumerate(combinations(pool, 2))}
        for stages in (1, 2):
            scalar = incidence_run(instances, pool, 3, 1, stages, False)
            ring = incidence_run(instances, pool, 3, 1, stages, True)
            self.assertEqual(ring, scalar)
            self.assertEqual(ring[0][0][-1], ((0, 0, 0),))
            self.assertEqual(ring[2], {(0, 0)})
            if stages == 1:
                self.assertEqual(ring[1], (((0, 0, 0), (6, 6, 6, 6, 6, 0)),))
            else:
                self.assertEqual(len(ring[0]), 2)
                self.assertEqual(ring[1], ())
        # Distinct primes have distinct false witnesses.  This must stay
        # uncertified at the strict equality boundary and be rejected by scan.
        six = pool[:6]
        different = {(1, 2, 0): ([six[i] * six[i + 1] for i in (0, 2, 4)], [0] * 3, 0)}
        scalar = incidence_run(different, six, 1, 0, 1, False)
        ring = incidence_run(different, six, 1, 0, 1, True)
        self.assertEqual(ring, scalar)
        self.assertEqual(ring[0][0][-2], (((1, 2, 0), 'uncertified'),))
        self.assertEqual(ring[1], (((1, 2, 0), (6, 35, 143)),))
        self.assertFalse(ring[2])
        # Multiple actual graph pairs share edge arrays and block labels.
        rng = Random(261015571)
        for trial in range(16):
            na, nb, nc, h = 2, 2, 6, 3
            ac = [[rng.randrange(-12, 13) for _ in range(nc)] for __ in range(na)]
            bc = [[rng.randrange(-12, 13) for _ in range(nb)] for __ in range(nc)]
            ab = [[rng.randrange(-12, 13) for _ in range(nb)] for __ in range(na)]
            if trial % 2:
                ab[0][0] = -ac[0][trial % nc] - bc[trial % nc][0]
            graph = {(a, b, block): (ac[a][block * h:(block + 1) * h],
                     [bc[c][b] for c in range(block * h, (block + 1) * h)], ab[a][b])
                     for a, b, block in product(range(na), range(nb), range(nc // h))}
            frozen_after, stages = 1 + trial % 3, trial % 3
            self.assertEqual(incidence_run(graph, pool, 3, frozen_after, stages, True),
                             incidence_run(graph, pool, 3, frozen_after, stages, False))


if __name__ == '__main__':
    unittest.main(verbosity=2)
