#!/usr/bin/env python3
"""Independent sparse-normal rotation/duplication audit.

Implements every sparse prefix-transform layer and duplicates raw suffix
coordinates into base-pair groups. The final selector products are evaluated
naively, not by a fast rectangular algorithm. This tests their exact
mathematical interface, not an asymptotic matrix multiplication theorem.
"""
from itertools import product, combinations
from pathlib import Path
from math import comb, prod
import importlib.util
import random

P = Path(__file__).resolve().parents[1]/'new-improvement/check_strict_cover_integration.py'
spec = importlib.util.spec_from_file_location('strict_cover_audit', P)
strict = importlib.util.module_from_spec(spec)
spec.loader.exec_module(strict)
cover = strict.cover
shift = strict.shift
M = None
stats = dict(roots=0, root_entries=0, components=0, prefix_cells=0,
             duplicated_cells=0, selectors=0, reconstruction_reads=0,
             sparse_roots=0, strict_sparse_roots=0)


def subsets(ell, h):
    return tuple(J for j in range(h + 1) for J in combinations(range(ell), j))


def sparse_variant(array, positions, requested_ell, *_unused, selected_axes=None, forms_override=None, label_maps=None):
    """No query labels or input-band data enter the source partition."""
    normal = (tuple(i for i, (is_normal, _) in enumerate(positions) if is_normal)
              if selected_axes is None else selected_axes)
    k = len(normal)
    ell = min(requested_ell, k)
    h = min(ell, ell * M // k)
    Js = subsets(ell, h)
    B = len(Js)
    valid = tuple(v for v in product(range(3), repeat=ell) if v.count(2) <= h)
    S = sum(comb(ell, j) * 2 ** (ell - j) for j in range(h + 1))
    assert len(valid) == S and B == sum(comb(ell, j) for j in range(h + 1))
    assert S <= 2 ** ell * B
    p = len(positions) - ell
    width = len(next(iter(array.values())))
    windows = tuple(tuple(normal[(r + j) % k] for j in range(ell)) for r in range(k))
    assignments = {}
    for raw, value in array.items():
        rare = sum(raw[i] == 2 for i in normal)
        if rare > M:
            assert not any(value), ('source-budget violation', M, raw, value)
            continue
        eligible = [r for r, W in enumerate(windows) if sum(raw[i] == 2 for i in W) <= h]
        assert eligible
        assignments[raw] = eligible[0]
    tables = []
    volume = 0
    for r, W in enumerate(windows):
        prefix = tuple(i for i in range(len(positions)) if i not in W)
        current = {u + v: (0,) * width for u in product(range(3), repeat=p) for v in valid}
        assert len(current) == 3 ** p * S
        for raw, value in array.items():
            if assignments.get(raw) == r:
                key = tuple(raw[i] for i in prefix + W)
                current[key] = value
        layers = [len(current)]
        for axis, original_axis in enumerate(prefix):
            forms = ((shift.NORMAL if positions[original_axis][0] else shift.OPPOSITE)
                     if forms_override is None else forms_override[original_axis])
            following = {}
            for key in current:
                if key[axis] != 0:
                    continue
                for label in range(4):
                    value = tuple(sum(forms[label][raw] * current[key[:axis] + (raw,) + key[axis+1:]][j]
                                      for raw in range(3)) for j in range(width))
                    following[key[:axis] + (label,) + key[axis+1:]] = value
            current = following
            layers.append(len(current))
        assert len(current) == 4 ** p * S
        assert all(volume <= 4 ** p * S for volume in layers)
        duplicated = {}
        for pref in product(range(4), repeat=p):
            for i in product(range(2), repeat=ell):
                for J in Js:
                    suffix = tuple(2 if j in J else i[j] for j in range(ell))
                    sign = (-1) ** sum(i[j] == 1 for j in J)
                    duplicated[pref, i, J] = tuple(sign * x for x in current[pref + suffix])
        assert len(duplicated) == 4 ** p * 2 ** ell * B
        # Exact multiplicity, not merely an upper bound.
        for v in valid:
            multiplicity = sum(all(v[j] == 2 or v[j] == i[j] for j in range(ell))
                               for i in product(range(2), repeat=ell))
            assert multiplicity == 2 ** v.count(2)
        tables.append((prefix, W, duplicated))
        volume += sum(layers) + len(duplicated)
        stats['prefix_cells'] += sum(layers)
        stats['duplicated_cells'] += len(duplicated)
        stats['components'] += 1
    stats['roots'] += 1
    stats['root_entries'] += len(array)
    stats['sparse_roots'] += int(M < k)
    stats['strict_sparse_roots'] += int(h < ell)
    return (tables, Js, width, k, ell, label_maps or {}), volume


def read_sparse(bundle, positions, ordinary, _ell):
    tables, Js, width, k, ell, label_maps = bundle
    ordinary = tuple(label_maps[i][label] if i in label_maps else label for i, label in enumerate(ordinary))
    result = [0] * width
    reads = 0
    for prefix, W, duplicated in tables:
        pref = tuple(ordinary[j] for j in prefix)
        labels = tuple(ordinary[j] for j in W)
        i = tuple(label // 2 for label in labels)
        active = {j for j, label in enumerate(labels) if label % 2 == 0}
        # This row is a 0/1 subset-incidence selector, shared by every fiber.
        row = tuple(int(set(J) <= active) for J in Js)
        stats['selectors'] += len(row)
        for J, selector in zip(Js, row):
            if selector:
                value = duplicated[pref, i, J]
                for j, x in enumerate(value):
                    result[j] += x
                reads += 1
    assert reads <= k * len(Js)
    stats['reconstruction_reads'] += reads
    return tuple(result), reads


def arbitrary_tests():
    global M
    rng = random.Random(202610200433)
    checked = 0
    for k, opposite, m, ell in ((2, 1, 1, 1), (3, 1, 1, 2), (4, 2, 1, 2), (5, 0, 2, 3)):
        M = m
        positions = [(True, j) for j in range(k)] + [(False, j) for j in range(opposite)]
        array = {raw: tuple(rng.randrange(-5, 6) for _ in range(6)) if raw[:k].count(2) <= m else (0,) * 6
                 for raw in product(range(3), repeat=k + opposite)}
        bundle, _ = sparse_variant(array, positions, ell)
        words = list(product(range(4), repeat=k + opposite))
        if len(words) > 128:
            words = rng.sample(words, 128)
        for word in words:
            actual, _ = read_sparse(bundle, positions, word, ell)
            expected = cover.direct(array, positions, word)
            assert actual == expected, (k, opposite, m, ell, word)
            checked += 1
        print('PASS arbitrary signed 6-fiber sparse root', (k, opposite, m, ell), 'queries', len(words))
    print('PASS arbitrary sparse-source contractions:', checked)



extra = dict(cropped_nonzero=0, cropped_entries=0, normal_choices=0,
             opposite_choices=0, basis_cells=0, padded_cells=0)
metadata = {}
lengths_seen = set()
original_fixture = shift.integration.fixture
original_fixed = shift.fixed_arrays


def cropped_fixture(L, m, *args):
    sources, requests = original_fixture(L, m, *args)
    cropped = []
    for pair in sources:
        new_pair = []
        for side_index, source in enumerate(pair):
            kept = {}
            for word, value in source.items():
                opposite = word[L:] if side_index == 0 else word[:L]
                if opposite.count(2) > m:
                    extra['cropped_entries'] += 1
                    extra['cropped_nonzero'] += int(value[1] != 0)
                else:
                    kept[word] = value
            new_pair.append(kept)
        cropped.append(tuple(new_pair))
    return cropped, requests


def fixed_with_choice(source, L, Qn, Qo, Cn, Co, run, side, t):
    array, positions, scans = original_fixed(source, L, Qn, Qo, Cn, Co, run, side, t)
    m, k = len(Qn), L - len(Qn)
    for raw, value in array.items():
        if any(value):
            assert raw[:k].count(2) <= m-len(Cn)
            assert raw[k:].count(2) <= m-len(Co)
    choose_opposite = len(Co) > len(Cn)
    budget = m-max(len(Cn), len(Co))
    if choose_opposite:
        # Evaluate the opposite root on y1=s+v, y2=s-v, P=-w.
        # This is a forward integer transform, not division by two.
        transform = ((1,1,0), (1,-1,0), (0,0,-1))
        for axis in range(k, 2*k):
            following = {}
            for key in array:
                if key[axis] != 0:
                    continue
                for label in range(3):
                    following[key[:axis]+(label,)+key[axis+1:]] = tuple(
                        sum(transform[label][r]*array[key[:axis]+(r,)+key[axis+1:]][j]
                            for r in range(3)) for j in range(t))
            array = following
            extra['basis_cells'] += len(array)
        extra['opposite_choices'] += 1
    else:
        extra['normal_choices'] += 1
    metadata[id(array)] = (m, k, budget, choose_opposite)
    return array, positions, scans


def varied_variant(array, positions, requested_ell, *_unused):
    global M
    m, k, budget, choose_opposite = metadata[id(array)]
    M = budget
    # Toy finite schedule exercises different suffix lengths by channel type.
    # The asymptotic entropy-chosen schedule is proved separately.
    ell = min(k, max(1, k-budget))
    lengths_seen.add((k, budget, ell))
    selected = tuple(range(k, 2*k) if choose_opposite else range(k))
    forms = [shift.NORMAL]*(2*k) if choose_opposite else None
    maps = {axis:(1,3,0,2) for axis in range(k, 2*k)} if choose_opposite else None
    bundle, volume = sparse_variant(array, positions, ell, selected_axes=selected,
                                   forms_override=forms, label_maps=maps)
    tables, Js, width, _, _, _ = bundle
    common_S = max(sum(comb(min(k,max(1,k-b)),j)
                       for j in range(min(k,max(1,k-b))*b//k+1))
                   for b in range(min(m,k)+1))
    # Explicit common-size source vectors and selector padding. Every group
    # allocates the zeros, and we check a complete padded dot product.
    assert len(Js) <= common_S
    for prefix_axes, W, duplicated in tables:
        p = len(prefix_axes)
        for pref in product(range(4), repeat=p):
            for i in product(range(2), repeat=ell):
                F = [duplicated[pref,i,J] for J in Js] + [(0,)*width]*(common_S-len(Js))
                A = [1]*len(Js)+[0]*(common_S-len(Js))
                assert tuple(sum(A[r]*F[r][j] for r in range(common_S)) for j in range(width)) == tuple(
                    sum(duplicated[pref,i,J][j] for J in Js) for j in range(width))
                extra['padded_cells'] += common_S
    return bundle, volume


def integration_tests():
    old_variant, old_read = cover.cover_variant, cover.read_variant
    cover.cover_variant, cover.read_variant = varied_variant, read_sparse
    shift.integration.fixture = cropped_fixture
    shift.fixed_arrays = fixed_with_choice
    try:
        strict.main()
    finally:
        cover.cover_variant, cover.read_variant = old_variant, old_read
        shift.integration.fixture = original_fixture
        shift.fixed_arrays = original_fixed


if __name__ == '__main__':
    arbitrary_tests()
    integration_tests()
    assert extra['cropped_nonzero'] > 0 and extra['opposite_choices'] > 0
    assert len({ell for k,budget,ell in lengths_seen if k==2}) > 1
    print('PASS global opposite crop, better-half choices, adaptive finite padding:', extra)
    print('PASS tested channel-type suffix schedule:', sorted(lengths_seen))
    print('PASS sparse rotation/duplication accounting:', stats)
    print('Finite evidence only; the schedule above exercises changing lengths, not the asymptotic entropy formula.')
