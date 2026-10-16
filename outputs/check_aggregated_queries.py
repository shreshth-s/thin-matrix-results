"""Exact finite validation of low-star box aggregation from retained encodings.

The brute-force leaf and matrix oracles are deliberately independent of the
shrinking local tensor transforms. This is not a complete fast implementation.
"""
from itertools import combinations, product
from math import comb
from pathlib import Path
import importlib.util
import random
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("pruned", ROOT / "outputs/check_pruned_encoding.py")
pruned = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pruned)

# Each pair gives original term labels and their linear-combination coefficients.
LEFT_INNER = [((0, 1), (2, -1)), ((1, 1), (2, -1)),
              ((3, 1), (5, -1)), ((4, 1), (5, -1))]
RIGHT_INNER = [((0, 1), (6, -1)), ((1, 1), (7, -1)),
               ((3, 1), (6, -1)), ((4, 1), (7, -1))]


def projected_tensor(encoding, fixed, variable_kinds, side):
    """Fetch a 6^e7^t tensor, then apply shrinking 4x6 and 5x7 transforms."""
    variables = sorted(variable_kinds)
    inner = LEFT_INNER if side == "left" else RIGHT_INNER
    alphabets = []
    transforms = []
    for position in variables:
        forms = list(inner)
        if variable_kinds[position] == "plus":
            forms.append(((9, 1),))
        transforms.append(forms)
        alphabets.append(sorted({label for form in forms for label, _ in form}))
    values = {}
    for indices in product(*alphabets):
        leaf = list(fixed)
        for position, label in zip(variables, indices):
            leaf[position] = label
        # Any missing key would expose an invalid demand beyond the retained layer.
        values[indices] = encoding[tuple(leaf)]
    fetched = len(values)
    dimensions = list(alphabets)
    for axis, forms in enumerate(transforms):
        next_values = {}
        output_axes = list(dimensions)
        output_axes[axis] = list(range(len(forms)))
        for indices in product(*output_axes):
            original = list(indices)
            total = 0
            for label, coefficient in forms[indices[axis]]:
                original[axis] = label
                total += coefficient * values[tuple(original)]
            next_values[indices] = total
        values = next_values
        dimensions[axis] = list(range(len(forms)))
    return values, variables, fetched


def contraction(left, right, fixed, variable_kinds):
    a, variables, fetched = projected_tensor(left, fixed, variable_kinds, "left")
    b, _, fetched_right = projected_tensor(right, fixed, variable_kinds, "right")
    assert fetched == fetched_right
    result = 0
    for indices, value in a.items():
        sign = (-1) ** sum(
            variable_kinds[position] == "plus" and index == 4
            for position, index in zip(variables, indices)
        )
        result += sign * value * b[indices]
    return result


def stored_box_oracle(left, right, fixed, stars):
    result = 0
    for labels in product(range(10), repeat=len(stars)):
        leaf = list(fixed)
        for position, label in zip(stars, labels):
            leaf[position] = label
        result += left[tuple(leaf)] * right[tuple(leaf)]
    return result


def low_order_oracle(left, right, output, inner, threshold):
    result = 0
    for labels in product(range(10), repeat=len(inner)):
        if sum(label != 9 for label in labels) >= threshold:
            continue
        leaf = list(output)
        for position, label in zip(inner, labels):
            leaf[position] = label
        result += left[tuple(leaf)] * right[tuple(leaf)]
    return result


def low_order_contracted(left, right, output, inner, threshold):
    m = len(inner)
    result = 0
    for degree in range(threshold):
        coefficient = (-1) ** (threshold - degree - 1) * comb(m - degree - 1, threshold - degree - 1)
        for chosen in combinations(inner, degree):
            result += coefficient * contraction(left, right, output, {position: "star" for position in chosen})
    return result


def aggregated_query(left, right, output, inner, threshold, star_cutoff):
    result = low_order_contracted(left, right, output, inner, threshold)
    m = len(inner)
    for v_tuple in combinations(inner, m - threshold):
        v = set(v_tuple)
        stars = []
        for position in inner:
            if position not in v:
                break
            stars.append(position)
        nonzero = [position for position in inner if position not in v]
        if len(stars) <= star_cutoff:
            kinds = {position: "star" for position in stars}
            kinds.update({position: "plus" for position in nonzero})
            result += contraction(left, right, output, kinds)
        else:
            for labels in product(range(9), repeat=threshold):
                fixed = list(output)
                for position, label in zip(nonzero, labels):
                    fixed[position] = label
                result += stored_box_oracle(left, right, fixed, stars)
    return result


def prefix_contracted_query(left, right, output, inner, threshold, prefix_length):
    prefix = inner[:prefix_length]
    suffix = inner[prefix_length:]
    suffix_size = len(suffix)
    result = 0
    for degree in range(threshold):
        coefficient = (-1) ** (threshold - degree - 1) * comb(suffix_size - degree - 1, threshold - degree - 1)
        for chosen in combinations(suffix, degree):
            variables = {position: "star" for position in (*prefix, *chosen)}
            result += coefficient * contraction(left, right, output, variables)
    for v_tuple in combinations(inner, len(inner) - threshold):
        v = set(v_tuple)
        stars = []
        for position in inner:
            if position not in v:
                break
            stars.append(position)
        if len(stars) < prefix_length:
            continue
        nonzero = [position for position in inner if position not in v]
        for labels in product(range(9), repeat=threshold):
            fixed = list(output)
            for position, label in zip(nonzero, labels):
                fixed[position] = label
            result += stored_box_oracle(left, right, fixed, stars)
    return result


def direct_matrix_entry(a, b, output, inner):
    result = 0
    for labels in product(range(4), repeat=len(inner)):
        left = [label // 3 if label != 9 else 0 for label in output]
        right = [label % 3 if label != 9 else 0 for label in output]
        for position, label in zip(inner, labels):
            left[position] = right[position] = label + 3
        result += a[pruned.index(left)] * b[pruned.index(right)]
    return result


class AggregatedQueryTests(unittest.TestCase):
    def test_local_projection_and_plus_identities(self):
        rng = random.Random(37990)
        for _ in range(100):
            a = [rng.randrange(-6, 7) for _ in range(7)]
            b = [rng.randrange(-6, 7) for _ in range(7)]
            left = pruned.encode(a, 1, pruned.PHI, 1)
            right = pruned.encode(b, 1, pruned.PSI, 1)
            self.assertEqual(contraction(left, right, [9], {0: "star"}), sum(a[j] * b[j] for j in range(3, 7)))
            self.assertEqual(contraction(left, right, [9], {0: "plus"}), sum(left[(j,)] * right[(j,)] for j in range(9)))

    def test_box_group_contractions_match_all_nine_choices(self):
        rng = random.Random(55609)
        for length in range(1, 5):
            a = [rng.randrange(-3, 4) for _ in range(7 ** length)]
            b = [rng.randrange(-3, 4) for _ in range(7 ** length)]
            left = pruned.encode(a, length, pruned.PHI, length)
            right = pruned.encode(b, length, pruned.PSI, length)
            for _ in range(25):
                kinds = {position: rng.choice(["star", "plus"]) for position in range(length) if rng.randrange(3)}
                fixed = [rng.randrange(10) for _ in range(length)]
                alphabets = [range(10) if kinds.get(position) == "star" else range(9) if kinds.get(position) == "plus" else [fixed[position]] for position in range(length)]
                oracle = sum(left[labels] * right[labels] for labels in product(*alphabets))
                self.assertEqual(contraction(left, right, fixed, kinds), oracle)

    def test_alternating_low_order_formula(self):
        rng = random.Random(14416)
        for length, m in [(2, 2), (3, 2), (3, 3), (4, 3)]:
            a = [rng.randrange(-3, 4) for _ in range(7 ** length)]
            b = [rng.randrange(-3, 4) for _ in range(7 ** length)]
            left = pruned.encode(a, length, pruned.PHI, m)
            right = pruned.encode(b, length, pruned.PSI, m)
            for inner in combinations(range(length), m):
                output = [9 if position in inner else rng.randrange(9) for position in range(length)]
                for threshold in range(1, m + 1):
                    self.assertEqual(low_order_contracted(left, right, output, inner, threshold), low_order_oracle(left, right, output, inner, threshold))

    def test_full_queries_match_independent_matrix_products(self):
        rng = random.Random(4195)
        for length, m in [(2, 1), (3, 2), (4, 2), (4, 3)]:
            words = list(product(range(7), repeat=length))
            a = [rng.randrange(-3, 4) if sum(label >= 3 for label in word) == m else 0 for word in words]
            b = [rng.randrange(-3, 4) if sum(label >= 3 for label in word) == m else 0 for word in words]
            left = pruned.encode(a, length, pruned.PHI, m)
            right = pruned.encode(b, length, pruned.PSI, m)
            for inner in combinations(range(length), m):
                for _ in range(4):
                    output = [9 if position in inner else rng.randrange(9) for position in range(length)]
                    expected = direct_matrix_entry(a, b, output, inner)
                    for threshold in range(1, m + 1):
                        for cutoff in range(m - threshold + 1):
                            self.assertEqual(aggregated_query(left, right, output, inner, threshold, cutoff), expected)
                            self.assertEqual(prefix_contracted_query(left, right, output, inner, threshold, cutoff), expected)

    def test_query_box_counts_and_transform_sizes(self):
        for m in range(1, 12):
            for threshold in range(1, m + 1):
                counts = [0] * (m - threshold + 1)
                for v_tuple in combinations(range(m), m - threshold):
                    v = set(v_tuple)
                    e = 0
                    while e in v:
                        e += 1
                    counts[e] += 1
                self.assertEqual(counts, [comb(m - e - 1, threshold - 1) for e in range(m - threshold + 1)])
                self.assertEqual(sum(counts), comb(m, threshold))
                for prefix_length in range(m - threshold + 1):
                    self.assertEqual(sum(counts[prefix_length:]), comb(m - prefix_length, threshold))


if __name__ == "__main__":
    unittest.main(verbosity=2)
