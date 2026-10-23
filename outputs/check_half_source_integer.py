#!/usr/bin/env python3
"""Independent exact small-instance checks; not an asymptotic proof.

Compare each shared-denominator conditional score to an exhaustive average
of completed translations. Check every invertible row map through dimension
three, all affine inputs, list-index firstness, and the explicit zero case.
"""
from fractions import Fraction
from itertools import product


def character(a, d):
    return 1 if bin(a & d).count('1') % 2 == 0 else -1


def build(m):
    length = 64 * m**3
    k = length + 1
    a, b = 4*m + 1, 4*m
    pa, pb = [1], [1]
    for _ in range(2*k):
        pa.append(pa[-1]*a)
        pb.append(pb[-1]*b)
    denominator = (a*b)**k
    numerators = [pa[k+t]*pb[k-t] for t in range(-k, k+1)]
    numerator = lambda t: numerators[t+k]
    ratio = Fraction(a, b)
    sums = [0] * (1 << m)
    entries = []
    ties = 0
    for _ in range(length):
        prefix = 0
        for i in range(m):
            scores = []
            for bit in (0, 1):
                candidate = prefix | (bit << i)
                total = 0
                for char in range(1, 1 << m):
                    s = sums[char]
                    if char >> (i+1) == 0:
                        t = s + character(char, candidate)
                        total += 2*(numerator(t) + numerator(-t))
                    else:
                        total += sum(numerator(t) for t in (s+1, s-1, -s+1, -s-1))
                completions = [candidate | (tail << (i+1)) for tail in range(1 << (m-i-1))]
                exact = sum(
                    (ratio**(sums[char]+character(char, d)) +
                     ratio**(-sums[char]-character(char, d)))
                    for d in completions for char in range(1, 1 << m)
                ) / len(completions)
                assert Fraction(total, 2*denominator) == exact
                assert total.bit_length() <= m + 2 + a*(2*k) + 1
                scores.append(total)
            if scores[0] == scores[1]:
                ties += 1
            if scores[1] < scores[0]:
                prefix |= 1 << i
        entries.insert(0, prefix)  # Preserve the Lean cons order and repeated values.
        for char in range(1, 1 << m):
            sums[char] += character(char, prefix)
    assert len(entries) == length
    assert all(abs(sums[char]) < 32*m*m for char in range(1, 1 << m))
    assert ties > 0
    return entries, ties


def check_maps(m, entries):
    checked = 0
    for rows in product(range(1 << m), repeat=m):
        image = lambda x: sum((bin(row & x).count('1') % 2) << i for i, row in enumerate(rows))
        if len({image(x) for x in range(1 << m)}) != 1 << m:
            continue
        for h in range(1 << m):
            weights = [bin(image(h ^ d)).count('1') for d in entries]
            first = next(j for j, weight in enumerate(weights) if weight <= m//2)
            assert all(weight > m//2 for weight in weights[:first])
            # Full vector/row work plus callback comparison, scan control,
            # candidate-index materialization, and the successful terminal.
            per_test = m*(6*m+5)+1+4*m
            actual = (first+1)*(per_test+2)+2*len(entries)+1
            assert actual <= len(entries)*(m*(6*m+5)+4*m+5)+2
            checked += 1
    return checked


def main():
    if not __debug__:
        raise SystemExit("Assertions must be enabled.")
    assert check_maps(0, [0]) == 1
    print("PASS m=0: one empty translation, one translation pair, weight zero")
    for m in range(1, 4):
        entries, ties = build(m)
        maps = check_maps(m, entries)
        print(f"PASS m={m}: {len(entries)} entries, exact exhaustive child averages, "
              f"{ties} false-on-tie choices, {maps} invertible-map/input checks")
    print("PASS: integer scores, exact-half coverage, first-index scans; finite checks only.")


if __name__ == '__main__':
    main()
