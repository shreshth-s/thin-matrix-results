#!/usr/bin/env python3
"""Strict complete-output integration with the smaller box-only encoder.

The canonical full cache is a comparison oracle, never an execution fallback.
Every actual high-box base lookup must be present in the joint-cap table.
"""
from pathlib import Path
from math import comb
import importlib.util

P = Path(__file__).resolve().parents[1]/'cropped-source-improvement/check_cropped_better_half.py'
spec = importlib.util.spec_from_file_location('cropped_under_joint_cap_audit', P)
cropped = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cropped)
strict = cropped.strict
cache = strict.cache
shift = strict.shift
stats = dict(encoders=0, retained_leaves=0, omitted_leaves=0,
             intermediate_entries=0, strict_cap_encoders=0)


def joint_cap_encoder(array, L, m, t, side):
    """Generate only valid prefixes; never allocate an uncapped leaf table."""
    cap = 2*m-t
    assert 0 <= cap < 2*m
    table = {}
    volumes = [0]*(2*L+1)

    def visit(values, pos, word, counts):
        assert max(counts) <= m and sum(counts) <= cap
        volumes[pos] += len(values)
        if pos == 2*L:
            assert len(values) == 1
            table[word] = values[0]
            return
        normal = (pos < L) == (side == 'left')
        forms, dim = (shift.NEW_PHI, 4) if normal else (cache.PSI, 3)
        width = len(values)//dim
        private_allowed = counts[pos//L] < m and sum(counts) < cap
        for label in range(5 if private_allowed else 4):
            child = [sum(coef*values[index*width+j]
                         for index, coef, degree in forms[label] if degree == 0)
                     for j in range(width)]
            next_counts = list(counts)
            next_counts[pos//L] += label == 4
            visit(child, pos+1, word+(label,), next_counts)

    visit(array, 0, (), [0, 0])
    exact_count = sum(comb(L, j)*comb(L, k)*4**(2*L-j-k)
                      for j in range(m+1) for k in range(m+1) if j+k <= cap)
    broad_count = sum(comb(L, j)*4**(L-j) for j in range(m+1))**2
    assert len(table) == exact_count < broad_count
    # Every intermediate layer is charged to distinct ordinary completions.
    assert all(volume <= exact_count for volume in volumes)
    assert 12**L <= exact_count
    stats['encoders'] += 1
    stats['retained_leaves'] += exact_count
    stats['omitted_leaves'] += broad_count-exact_count
    stats['intermediate_entries'] += sum(volumes)
    stats['strict_cap_encoders'] += int(cap < 2*m)
    strict.totals['box_encoders'] += 1
    strict.totals['box_leaves'] += exact_count
    strict.totals['box_intermediate_entries'] += sum(volumes)
    return table


def encode_with_joint_cap(array, L, m, t, side, counts):
    canonical = strict.original_encode(array, L, m, t, side, counts)
    boxes = joint_cap_encoder(array, L, m, t, side)
    assert all(canonical[word][0] == value for word, value in boxes.items())
    strict.box_by_cache[id(canonical)] = boxes
    strict.box_latest = boxes
    return canonical


class JointCapView(strict.StrictView):
    def __init__(self, selected, ordinary):
        self.selected = selected
        self.boxes = strict.box_latest
        assert all(word in ordinary and ordinary[word][0] == value
                   for word, value in self.boxes.items())
        assert len(self.boxes) < len(ordinary)
        first = next(iter(selected))
        self.inner_count = sum(label >= 4 for label in first)


if __name__ == '__main__':
    strict.encode_with_independent_boxes = encode_with_joint_cap
    strict.StrictView = JointCapView
    cropped.integration_tests()
    assert stats['omitted_leaves'] > 0
    assert stats['encoders'] == stats['strict_cap_encoders']
    assert strict.totals['actual_box_reads'] > 0
    print('PASS strictly smaller joint-cap box encoder:', stats)
    print('PASS no omitted leaf is used by an actual high-box lookup.')
    print('PASS complete original outputs with crop, sparse residual, and joint-cap boxes.')
