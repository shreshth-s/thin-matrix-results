#!/usr/bin/env python3
"""Independent exact finite checks; no asymptotic extraction claim."""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import prod

COLORS = ((0, 1, 1), (1, 0, 1), (1, 1, 0), (0, 0, 2), (0, 2, 0), (2, 0, 0))


def cw(q, x, y, z):
    return int((x, y, z) in {(0, 0, q + 1), (0, q + 1, 0), (q + 1, 0, 0)}) + sum(
        int((x, y, z) in {(0, a, a), (a, 0, a), (a, a, 0)}) for a in range(1, q + 1))


def keys(w):
    return tuple(tuple(COLORS[b][axis] for b in w) for axis in range(3))


def marginal(w):
    return tuple(tuple(k.count(c) for c in range(3)) for k in keys(w))


def cleanup(E):
    collisions = {(a, b) for a in E for b in E if a != b and any(x == y for x, y in zip(keys(a), keys(b)))}
    kept = E - {a for a, _ in collisions}
    assert len(E) <= len(kept) + len(collisions)
    assert len(collisions) <= len(E) ** 2
    for a, b, c in product(kept, repeat=3):
        compatible = all(x + y + z == 2 for x, y, z in zip(keys(a)[0], keys(b)[1], keys(c)[2]))
        assert not compatible or a == b == c
    return kept


def main():
    block_checks = 0
    for q in (0, 1, 2, 16):
        for x, y, z in product(range(q + 2), repeat=3):
            color = lambda a: 0 if a == 0 else 2 if a == q + 1 else 1
            triple = (color(x), color(y), color(z))
            expected = 0
            if triple in COLORS:
                b = COLORS.index(triple)
                expected = int((b == 0 and y == z) or (b == 1 and x == z) or
                               (b == 2 and x == y) or b >= 3)
            assert cw(q, x, y, z) == expected
            block_checks += 1
    word_checks = 0
    for n in range(5):
        marginals = {}
        for w in product(range(6), repeat=n):
            counts = tuple(w.count(b) for b in range(6))
            m = marginal(w)
            assert marginals.setdefault(m, counts) == counts
            word_checks += 1
    reference = (0, 1, 2)
    weights = (0, 1, 2)
    B = {0, 1, 3}
    assert all(a == b == c for a, b, c in product(B, repeat=3) if (a + c - 2 * b) % 7 == 0)
    def hashes(w):
        x, y, z = keys(w)
        hx = (5 + sum(a * b for a, b in zip(weights, x))) % 7
        hy = (6 + sum(a * b for a, b in zip(weights, y))) % 7
        hz = (5 + 4 * (1 + sum(a * (2 - b) for a, b in zip(weights, z)))) % 7
        assert (hx + hy - 2 * hz) % 7 == 0
        if hx in B and hy in B and hz in B:
            assert hx == hy == hz
        return hx, hy, hz
    E = {w for w in product(range(6), repeat=3) if marginal(w) == marginal(reference) and all(h in B for h in hashes(w))}
    assert E == {(0, 1, 2), (2, 0, 1)}
    assert cleanup(E) == E
    for n in range(4):
        classes = {}
        for w in product(range(6), repeat=n):
            classes.setdefault(marginal(w), set()).add(w)
        for values in classes.values():
            cleanup(values)
    assert cleanup(set()) == set() and cleanup({()}) == {()}
    def xaxis(copy, row, inner):
        return (0, row + 1, inner + 1) if copy == 0 else (inner + 1, 0, row + 1)
    def yaxis(copy, inner, col):
        return (col + 1, 0, inner + 1) if copy == 0 else (inner + 1, col + 1, 0)
    def zaxis(copy, col, row):
        return (col + 1, row + 1, 0) if copy == 0 else (0, col + 1, row + 1)
    axes = list(product(range(2), repeat=3))
    for axis in (xaxis, yaxis, zaxis):
        assert len({axis(*a) for a in axes}) == 8
    mixed_checks = 0
    for a, b, c in product(axes, repeat=3):
        actual = prod(cw(2, x, y, z) for x, y, z in zip(xaxis(*a), yaxis(*b), zaxis(*c)))
        expected = int(a[0] == b[0] == c[0] and a[1] == c[2] and a[2] == b[1] and b[2] == c[1])
        assert actual == expected
        mixed_checks += 1
    period = 75249000000000
    counts = (6888000000000, 4000000000000, 60000000000000, 131843770853, 4180500000000, 48656229147)
    p, e, f = Q(4000, 75249), Q(1, 18), Q(646603, 10**9)
    assert tuple(Q(c, period) for c in counts) == (Q(861, 500) * p, p, 15 * p, e - p - f, e, f)
    assert sum(counts) == period and min(counts) > 0
    assert 500 * counts[0] == 861 * counts[1] and counts[2] == 15 * counts[1]
    print(f"PASS: {block_checks} block coordinates, {word_checks} marginal-type words, {mixed_checks} mixed-copy coordinates.")
    print("PASS: actual mod-7 hash cleanup retains two copies; empty/zero cases and exact rectangular type period checked.")
    print("SCOPE: finite isolation only; no exponential copy lower bound or rectangular exponent is inferred.")


if __name__ == '__main__':
    main()
