"""Finite exact checks of independent-product slots with shared band encodings.

This tests correctness and reuse, not the asymptotic box-count or runtime proof.
Run from the repository root; standard library only.
"""
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations, product
from math import comb
from pathlib import Path
from random import Random

ROOT = Path(__file__).resolve().parents[1]
spec = spec_from_file_location("encoding", ROOT / "outputs/check_pruned_encoding.py")
enc = module_from_spec(spec)
spec.loader.exec_module(enc)


def digits(value, base, length):
    out = [0] * length
    for i in reversed(range(length)):
        out[i], value = value % base, value // base
    assert value == 0
    return out


def root_array(matrices, subsets, L, m, tile, left):
    n0, D = 3 ** (L - m), 4 ** m
    root = [0] * 7 ** L
    for matrix, Q in zip(matrices, subsets):
        for outer in range(n0):
            absolute = tile * n0 + outer
            N = len(matrix) if left else len(matrix[0])
            if absolute >= N:
                continue
            outer_digits = digits(outer, 3, L - m)
            for inner in range(D):
                inner_digits = digits(inner, 4, m)
                oi, ii = iter(outer_digits), iter(inner_digits)
                word = [next(ii) + 3 if k in Q else next(oi) for k in range(L)]
                value = matrix[absolute][inner] if left else matrix[inner][absolute]
                root[enc.index(word)] = value
    return root


def decode(A, B, Q, row, col, L, m):
    row, col = digits(row, 3, L - m), digits(col, 3, L - m)
    ri, ci = iter(row), iter(col)
    leaf = [9 if k in Q else 3 * next(ri) + next(ci) for k in range(L)]
    total = 0
    for free in product(range(10), repeat=m):
        for k, digit in zip(Q, free):
            leaf[k] = digit
        word = tuple(leaf)
        total += A[word] * B[word]
    return total


def check_case(L, m, N, B, seed):
    rng = Random(seed)
    n0, D, K = 3 ** (L - m), 4 ** m, comb(L, m)
    subsets = list(combinations(range(L), m))
    X = [[[rng.randrange(-7, 8) for _ in range(D)] for _ in range(N)] for _ in range(B)]
    Y = [[[rng.randrange(-7, 8) for _ in range(N)] for _ in range(D)] for _ in range(B)]
    num_tiles = (N + n0 - 1) // n0
    checked, arrays = 0, 0
    for first in range(0, B, K):
        left = X[first:first + K]
        right = Y[first:first + K]
        # These are constructed once per row or column tile, outside the i,j loop.
        AA = [enc.encode(root_array(left, subsets, L, m, i, True), L, enc.PHI, m)
              for i in range(num_tiles)]
        BB = [enc.encode(root_array(right, subsets, L, m, j, False), L, enc.PSI, m)
              for j in range(num_tiles)]
        arrays += len(AA) + len(BB)
        for i in range(num_tiles):
            for j in range(num_tiles):
                for slot, Q in enumerate(subsets[:len(left)]):
                    for r in range(min(n0, N - i * n0)):
                        for c in range(min(n0, N - j * n0)):
                            rr, cc = i * n0 + r, j * n0 + c
                            expected = sum(left[slot][rr][k] * right[slot][k][cc] for k in range(D))
                            actual = decode(AA[i], BB[j], Q, r, c, L, m)
                            assert actual == expected, (L, m, N, B, first, slot, rr, cc, actual, expected)
                            checked += 1
    assert checked == B * N * N
    assert arrays == 2 * num_tiles * ((B + K - 1) // K)
    return checked, arrays


if __name__ == "__main__":
    entries, arrays = 0, 0
    cases = [(2, 1, 3, 2), (2, 1, 7, 5), (3, 1, 10, 7),
             (3, 2, 7, 4), (4, 1, 28, 5)]
    for seed, case in enumerate(cases):
        checked, encoded = check_case(*case, seed)
        entries += checked
        arrays += encoded
        print(f"PASS {case}: {checked} entries, {encoded} shared arrays")
    print(f"PASS total: {entries} exact signed entries and {arrays} shared encodings")
