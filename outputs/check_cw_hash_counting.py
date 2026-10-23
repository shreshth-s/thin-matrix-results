#!/usr/bin/env python3
"""Independent exact hash-space enumeration and actual symmetric cleanup."""
from fractions import Fraction
from itertools import product

COLORS = ((0, 1, 1), (1, 0, 1), (1, 1, 0), (0, 0, 2), (0, 2, 0), (2, 0, 0))


def keys(word):
    return tuple(tuple(COLORS[b][a] for b in word) for a in range(3))


def run(M, n, all_classes=True):
    B = {3: {0}, 5: {0, 1}, 7: {0, 1, 3}}[M]
    assert all(a == b == c for a, b, c in product(B, repeat=3) if (a + c - 2 * b) % M == 0)
    words = list(product(range(6), repeat=n))
    coords = [keys(w) for w in words]
    pairs = [(i, j) for i in range(len(words)) for j in range(len(words))
             if i != j and any(a == b for a, b in zip(coords[i], coords[j]))]
    assert all(sum(a == b for a, b in zip(coords[i], coords[j])) == 1 for i, j in pairs)
    groups = {}
    for i, xyz in enumerate(coords):
        marginal = tuple(tuple(v.count(c) for c in range(3)) for v in xyz)
        groups.setdefault(marginal, []).append(i)
    if not all_classes:
        reference = (0, 1, 2)
        groups = {k: v for k, v in groups.items() if words.index(reference) in v}
    classes = list(groups.values())
    class_pairs = [[(i, j) for i, j in pairs if i in E and j in E] for E in classes]
    totals = [[0, 0, 0] for _ in classes]
    singles = [[0] * M for _ in words]
    joints = [[0] * M for _ in pairs]
    samples = 0
    inv2 = pow(2, -1, M)
    for weights in product(range(M), repeat=n):
        dots = [[sum(w * c for w, c in zip(weights, v)) for v in xyz] for xyz in coords]
        for b, w0 in product(range(M), repeat=2):
            samples += 1
            hashes = [((b + x) % M, (b + w0 + y) % M,
                       (b + inv2 * (w0 + 2 * sum(weights) - z)) % M) for x, y, z in dots]
            buckets = [x if x == y == z else None for x, y, z in hashes]
            for i, (x, y, z) in enumerate(hashes):
                assert (x + y - 2 * z) % M == 0
                assert (buckets[i] in B) == (x in B and y in B and z in B)
                if buckets[i] is not None:
                    singles[i][buckets[i]] += 1
            for k, (i, j) in enumerate(pairs):
                if buckets[i] is not None and buckets[i] == buckets[j]:
                    joints[k][buckets[i]] += 1
            for k, E in enumerate(classes):
                filtered = {i for i in E if all(h in B for h in hashes[i])}
                collisions = {(i, j) for i, j in class_pairs[k] if i in filtered and j in filtered}
                kept = filtered - {i for i, _ in collisions}
                assert len(filtered) <= len(kept) + len(collisions)
                totals[k][0] += len(filtered)
                totals[k][1] += len(collisions)
                totals[k][2] = max(totals[k][2], len(kept))
    assert samples == M ** (n + 2)
    assert all(c == M**n for row in singles for c in row)
    assert all(c == M ** (n - 1) for row in joints for c in row)
    for E, P, (cand, coll, maximum) in zip(classes, class_pairs, totals):
        assert cand == len(E) * len(B) * M**n
        assert coll == len(P) * len(B) * M ** max(0, n - 1)
        lower = Fraction(len(E) * len(B), M**2) - Fraction(len(P) * len(B), M**3)
        assert maximum >= lower
        assert samples * maximum + coll >= cand
    print(f"PASS: M={M}, n={n}: {samples} samples; {len(words)*M} single fibers; {len(pairs)*M} pair fibers; {len(classes)} cleanup classes.")
    return samples, len(words)*M, len(pairs)*M, len(classes)


def main():
    totals = [0, 0, 0, 0]
    for M, n in ((3, 0), (3, 1), (3, 2), (5, 1), (5, 2), (7, 1), (7, 2)):
        totals = [a+b for a, b in zip(totals, run(M, n))]
    # The n=3 test retains the six actual words of the earlier nonempty example;
    # individual and shared-pair counts still cover every one of the 216 words.
    totals = [a+b for a, b in zip(totals, run(7, 3, False))]
    assert sum((2*w) % 4 == 0 for w in range(4)) == 2  # Not one free-coordinate fiber.
    assert 0 % 2 == 2 % 2  # The three color values are not injective modulo two.
    print(f"PASS: totals {totals[0]} samples, {totals[1]} single fibers, {totals[2]} shared-pair fibers, {totals[3]} cleanup classes.")
    print("SCOPE: exact finite cardinalities and survivor bounds; no entropy-scale extraction or execution-cost conclusion.")


if __name__ == '__main__':
    main()
