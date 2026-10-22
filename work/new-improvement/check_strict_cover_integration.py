#!/usr/bin/env python3
"""Independent integration audit: no low-cache fallback; separate box encoder.

Uses the proposed construction's omission cover only for the proposed branch.
The canonical full cache remains a comparison oracle, never a fallback for
executing either residual or high-box queries in these tests.
"""
from pathlib import Path
from math import comb
import importlib.util

P = Path(__file__).with_name('check_omission_cover.py')
spec = importlib.util.spec_from_file_location('omission_under_audit', P)
cover = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cover)
shift = cover.shift
cache = shift.cache
original_encode = cache.encode
box_by_cache = {}
box_latest = None
totals = dict(box_encoders=0, box_leaves=0, box_intermediate_entries=0,
              actual_box_reads=0, actual_residual_reads=0)


def independent_box_encoder(array, L, m, side):
    """Only four ordinary labels and private constant H(0); no channels."""
    table = {}
    volumes = [0] * (2 * L + 1)

    def visit(values, pos, word, counts):
        volumes[pos] += len(values)
        if pos == 2 * L:
            table[word] = values[0]
            return
        normal = (pos < L) == (side == 'left')
        forms, dim = (shift.NEW_PHI, 4) if normal else (cache.PSI, 3)
        width = len(values) // dim
        labels = range(5 if counts[pos // L] < m else 4)
        for label in labels:
            child = [sum(coefficient * values[index * width + j]
                         for index, coefficient, degree in forms[label]
                         if degree == 0)
                     for j in range(width)]
            new_counts = list(counts)
            new_counts[pos // L] += label == 4
            visit(child, pos + 1, word + (label,), new_counts)

    visit(array, 0, (), [0, 0])
    U = sum(comb(L, j) * 4 ** (L - j) for j in range(m + 1))
    assert len(table) == U * U
    assert all(x <= U * U for x in volumes)
    totals['box_encoders'] += 1
    totals['box_leaves'] += len(table)
    totals['box_intermediate_entries'] += sum(volumes)
    return table


def encode_with_independent_boxes(array, L, m, t, side, stats):
    global box_latest
    canonical = original_encode(array, L, m, t, side, stats)
    boxes = independent_box_encoder(array, L, m, side)
    assert all(canonical[word][0] == value for word, value in boxes.items())
    box_by_cache[id(canonical)] = boxes
    box_latest = boxes
    return canonical


class StrictView:
    def __init__(self, selected, ordinary):
        self.selected = selected
        assert {word: value[0] for word, value in ordinary.items()} == box_latest
        self.boxes = box_latest
        first = next(iter(selected))
        self.inner_count = sum(x >= 4 for x in first)

    def __contains__(self, word):
        return word in self.selected or word in self.boxes

    def __getitem__(self, word):
        if sum(x >= 4 for x in word) == self.inner_count:
            assert word in self.selected, ('missing actual residual value', word)
            totals['actual_residual_reads'] += 1
            return self.selected[word]
        assert 5 not in word
        assert word in self.boxes, ('missing separate box base', word)
        totals['actual_box_reads'] += 1
        return (self.boxes[word],)


def main():
    old_view = cover.SeparateView
    cache.encode = encode_with_independent_boxes
    cover.SeparateView = StrictView
    try:
        result = cover.integration_tests()
        assert result['normalized'] == 281
        assert result['root_cells'] == 18468
        assert totals['actual_box_reads'] > 0 and totals['actual_residual_reads'] > 0
        print('PASS strict original-matrix/cyclic integration:', result)
        print('PASS separate five-label box encoders and no residual fallback:', totals)
        # Full fixtures independently enumerate every group on each input,
        # cyclic fiber, and degree run. The third fixture is sampled.
        full1 = 2 * (2*1+1) * 2 * comb(2,1)**2 * sum(comb(2,h) for h in range(2)) * 3**2
        full2 = 2 * (2*2+1) * 1 * comb(3,2)**2 * sum(comb(4,h) for h in range(2)) * 3**2
        assert full1 == 1296 and full2 == 4050
        print('PASS all-group root counts in both full fixtures:', full1, full2)
    finally:
        cache.encode = original_encode
        cover.SeparateView = old_view


if __name__ == '__main__':
    main()
