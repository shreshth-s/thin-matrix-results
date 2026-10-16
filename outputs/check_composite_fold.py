#!/usr/bin/env python3
"""Check the integer-modulus extension of residue folding by brute force."""

import math
import random
import unittest


def check_fold(a, b, c, modulus, padded_h=None):
    rows, h, cols = len(a), len(b), len(c[0])
    assert all(len(row) == h for row in a)
    assert all(len(row) == cols for row in b)
    assert len(c) == rows
    padded_h = h if padded_h is None else padded_h
    assert padded_h >= h
    p1 = math.isqrt(modulus - 1) + 1
    p2 = (modulus + p1 - 1) // p1
    inner = padded_h * modulus
    x = [[0] * inner for _ in range(rows * p1)]
    y = [[0] * (cols * p2) for _ in range(inner)]
    for i in range(rows):
        for rho1 in range(p1):
            for w in range(h):
                x[i * p1 + rho1][w * modulus + (a[i][w] + rho1) % modulus] = 1
    for j in range(cols):
        for rho2 in range(p2):
            for w in range(h):
                y[w * modulus + (-b[w][j] - p1 * rho2) % modulus][j * p2 + rho2] = 1
    queried = set()
    for i in range(rows):
        for j in range(cols):
            rho2, rho1 = divmod(c[i][j] % modulus, p1)
            assert rho2 < p2
            pos = (i * p1 + rho1, j * p2 + rho2)
            assert pos not in queried
            queried.add(pos)
            count = sum(x[pos[0]][t] * y[t][pos[1]] for t in range(inner))
            expected = sum((a[i][w] + b[w][j] + c[i][j]) % modulus == 0
                           for w in range(h))
            assert count == expected
    assert len(queried) == rows * cols


class CompositeFoldChecks(unittest.TestCase):
    def test_composite_moduli_signed_random(self):
        rng = random.Random(17420)
        for modulus in (4, 6, 8, 9, 10, 12, 15, 16, 18, 25, 30):
            for _ in range(30):
                rows, cols, h = [rng.randrange(1, 5) for _ in range(3)]
                a = [[rng.randrange(-20, 21) for _ in range(h)] for _ in range(rows)]
                b = [[rng.randrange(-20, 21) for _ in range(cols)] for _ in range(h)]
                c = [[rng.randrange(-20, 21) for _ in range(cols)] for _ in range(rows)]
                check_fold(a, b, c, modulus, padded_h=h + 2)

    def test_unbalanced_residues_and_multiplicities(self):
        for modulus in (4, 6, 9, 12, 30):
            a = [[modulus] * 5] * 3
            b = [[-2 * modulus] * 4] * 5
            c = [[modulus] * 4] * 3
            check_fold(a, b, c, modulus, padded_h=8)


if __name__ == '__main__':
    unittest.main(verbosity=2)
