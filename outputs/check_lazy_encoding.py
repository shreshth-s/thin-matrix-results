"""Exact finite checks for deterministic cyclic-order lazy encodings.

The retained arrays are built with the original seven-coordinate recursion.
Missing leaves are evaluated by enumerating only the Cartesian product of the
nonzero supports of their remaining forms, so the checker measures the proved
3^R read bound rather than evaluating a dense 7^R array. Complete prefix
queries are checked against the full ten-term cube and, for fixed-weight
inputs, an independent matrix-product oracle. This is not an implementation
of the complete asymptotically fast algorithm.
"""
from itertools import combinations, product
from math import comb, prod
from random import Random
import unittest

import check_aggregated_queries as queries
import check_pruned_encoding as pruned


def fold_one(array, form):
    size = len(array) // 7
    return [sum(coefficient * array[digit * size + i]
                for digit, coefficient in form)
            for i in range(size)]


def dense_oracle(array, labels, forms):
    """Independent recursive evaluation; used only for the finite oracle."""
    for label in labels:
        array = fold_one(array, forms[label])
    return array[0]


def sparse_contract(array, labels, forms):
    """Read exactly the Cartesian support, not all 7^len(labels) entries."""
    total = 0
    reads = 0
    for choices in product(*(forms[label] for label in labels)):
        index = 0
        coefficient = 1
        for digit, weight in choices:
            index = 7 * index + digit
            coefficient *= weight
        total += coefficient * array[index]
        reads += 1
    assert reads == prod(len(forms[label]) for label in labels)
    assert reads <= 3 ** len(labels)
    return total, reads


def rotate_array(array, length, shift):
    """Permute array axes and labels together; new axes start at shift."""
    result = []
    for new_coordinates in product(range(7), repeat=length):
        old_coordinates = (new_coordinates[-shift:] + new_coordinates[:-shift]
                           if shift else new_coordinates)
        result.append(array[pruned.index(old_coordinates)])
    return result


def retained_arrays(array, length, budget, forms):
    cache = {}
    formation_reads = 0

    def visit(current, prefix, zero_count):
        nonlocal formation_reads
        cache[prefix] = current
        if len(prefix) == length:
            return
        for label, form in enumerate(forms):
            new_count = zero_count + (label == 9)
            if new_count <= budget:
                formation_reads += len(form) * (len(current) // 7)
                visit(fold_one(current, form), prefix + (label,), new_count)

    visit(array, (), 0)
    leaves = sum(comb(length, j) * 9 ** (length-j)
                 for j in range(budget+1))
    stored_entries = sum(len(value) for value in cache.values())
    assert 2 * stored_entries <= 9 * leaves
    assert formation_reads <= 3 * (stored_entries - len(array))
    assert sum(len(key) == length for key in cache) == leaves
    # Check the entire internal-array sum, not just its leaf lower bound.
    predicted_entries = sum(
        sum(comb(depth, j) * 9 ** (depth-j)
            for j in range(min(depth, budget)+1)) * 7 ** (length-depth)
        for depth in range(length+1))
    assert stored_entries == predicted_entries
    return cache, stored_entries, formation_reads


class LazyEncoding:
    """Dictionary interface expected by the existing prefix-query checker."""
    def __init__(self, array, length, budget, forms):
        self.length = length
        self.budget = budget
        self.forms = forms
        self.caches = []
        self.stored_entries = 0
        self.formation_reads = 0
        self.reconstructed = 0
        self.sparse_reads = 0
        for shift in range(length):
            rotated = rotate_array(array, length, shift)
            cache, entries, reads = retained_arrays(rotated, length, budget, forms)
            self.caches.append(cache)
            self.stored_entries += entries
            self.formation_reads += reads

    def __getitem__(self, labels):
        labels = tuple(labels)
        zero_count = labels.count(9)
        if zero_count <= self.budget:
            return self.caches[0][labels][0]
        deficit = zero_count - self.budget
        window = (self.length * deficit + zero_count - 1) // zero_count
        shift = next(s for s in range(self.length)
                     if (labels[s:] + labels[:s])[-window:].count(9) >= deficit)
        rotated = labels[shift:] + labels[:shift]
        depth = 0
        while depth < self.length and rotated[:depth+1] in self.caches[shift]:
            depth += 1
        assert self.length - depth <= window
        parent = self.caches[shift][rotated[:depth]]
        value, reads = sparse_contract(parent, rotated[depth:], self.forms)
        assert reads <= 3 ** window
        self.reconstructed += 1
        self.sparse_reads += reads
        return value


class LazyEncodingTests(unittest.TestCase):
    def test_cyclic_window_guarantee(self):
        cases = 0
        for length in range(1, 11):
            for bits in product([0, 1], repeat=length):
                zero_count = sum(bits)
                for budget in range(zero_count):
                    deficit = zero_count - budget
                    window = (length * deficit + zero_count - 1) // zero_count
                    counts = [sum((bits[s:] + bits[:s])[-window:])
                              for s in range(length)]
                    self.assertEqual(sum(counts), zero_count * window)
                    self.assertGreaterEqual(max(counts), deficit)
                    cases += 1
        self.assertEqual(cases, 9217)

    def test_sparse_contraction_reads(self):
        rng = Random(91250)
        for length in range(5):
            array = [rng.randrange(-6, 7) for _ in range(7**length)]
            for forms in (pruned.PHI, pruned.PSI):
                for _ in range(60):
                    labels = tuple(rng.randrange(10) for _ in range(length))
                    value, reads = sparse_contract(array, labels, forms)
                    self.assertEqual(value, dense_oracle(array, labels, forms))
                    self.assertLessEqual(reads, 3**length)

    def test_stored_arrays_and_lazy_leaf_retrieval(self):
        rng = Random(20261015)
        reconstructions = 0
        for length in range(1, 5):
            for budget in range(length+1):
                array = [rng.randrange(-4, 5) for _ in range(7**length)]
                for forms in (pruned.PHI, pruned.PSI):
                    lazy = LazyEncoding(array, length, budget, forms)
                    labels_list = [tuple(rng.randrange(10) for _ in range(length))
                                   for _ in range(60)]
                    labels_list += [tuple(9 if b else 0 for b in bits)
                                    for bits in product([0, 1], repeat=length)]
                    for labels in labels_list:
                        self.assertEqual(lazy[labels], dense_oracle(array, labels, forms))
                    reconstructions += lazy.reconstructed
        self.assertGreater(reconstructions, 0)

    def test_complete_prefix_queries_with_free_pruning(self):
        cases, _ = self.complete_queries(lazy=False)
        self.assertEqual(cases, 146)

    def test_complete_prefix_queries_with_lazy_reconstruction(self):
        cases, reconstructions = self.complete_queries(lazy=True)
        self.assertEqual(cases, 146)
        self.assertGreater(reconstructions, 0)

    def complete_queries(self, lazy):
        rng = Random(60723)
        cases = reconstructions = 0
        for structured in (False, True):
            for length in range(1, 5):
                words = list(product(range(7), repeat=length))
                for m in range(1, length+1):
                    a = [rng.randrange(-4, 5) if not structured or
                         sum(v >= 3 for v in word) == m else 0 for word in words]
                    b = [rng.randrange(-4, 5) if not structured or
                         sum(v >= 3 for v in word) == m else 0 for word in words]
                    full_a = pruned.encode(a, length, pruned.PHI, m)
                    full_b = pruned.encode(b, length, pruned.PSI, m)
                    retained = {}
                    for inner in combinations(range(length), m):
                        output = [9 if i in inner else rng.randrange(9)
                                  for i in range(length)]
                        expected = queries.stored_box_oracle(full_a, full_b, output, inner)
                        if structured:
                            self.assertEqual(expected,
                                queries.direct_matrix_entry(a, b, output, inner))
                        for threshold in range(1, m+1):
                            for prefix in range(min(threshold, m-threshold)+1):
                                # Budget m-t keeps every box leaf. If t>ell,
                                # residual leaves with >m-t P0 labels are lazy.
                                budget = m-threshold if lazy else m-prefix
                                if budget not in retained:
                                    if lazy:
                                        retained[budget] = (
                                            LazyEncoding(a, length, budget, pruned.PHI),
                                            LazyEncoding(b, length, budget, pruned.PSI))
                                    else:
                                        retained[budget] = (
                                            pruned.encode(a, length, pruned.PHI, budget),
                                            pruned.encode(b, length, pruned.PSI, budget))
                                left, right = retained[budget]
                                actual = queries.prefix_contracted_query(
                                    left, right, output, inner, threshold, prefix)
                                self.assertEqual(actual, expected,
                                    (lazy, structured, length, m, inner, threshold, prefix))
                                cases += 1
                    if lazy:
                        reconstructions += sum(left.reconstructed + right.reconstructed
                                               for left, right in retained.values())
        return cases, reconstructions


if __name__ == '__main__':
    unittest.main(verbosity=2)
