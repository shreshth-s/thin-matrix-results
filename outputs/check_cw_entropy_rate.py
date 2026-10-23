#!/usr/bin/env python3
"""Exact finite checks; no floating-point surrogate for analytic Lean proofs."""
from fractions import Fraction
from math import comb, factorial
from itertools import product


def main():
    checked = 0
    for a, b, c in product(range(7), repeat=3):
        n = a + b + c
        coefficient = factorial(n) // (factorial(a) * factorial(b) * factorial(c))
        assert coefficient == comb(n, a) * comb(b + c, b)
        # exp(n H) = n^n / product(a_i^a_i), including 0^0=1.
        numerator, denominator = n**n, a**a * b**b * c**c
        assert coefficient * denominator <= numerator
        assert numerator <= coefficient * (n + 1)**2 * denominator
        checked += 1
    print(f"PASS: {checked} exact ternary coefficient/entropy-weight cases, including all zero endpoints.")
    P = 75249000000000
    blocks = [(0, 1, 1), (1, 0, 1), (1, 1, 0), (0, 0, 2), (0, 2, 0), (2, 0, 0)]
    probs = [Fraction(861, 500)*Fraction(4000,75249), Fraction(4000,75249),
             15*Fraction(4000,75249), Fraction(1,18)-Fraction(4000,75249)-Fraction(646603,10**9),
             Fraction(1,18), Fraction(646603,10**9)]
    assert sum(probs) == 1 and all(p > 0 for p in probs)
    counts = [int(P*p) for p in probs]
    assert all(P*p == c for p,c in zip(probs,counts))
    expected = [[11200343770853,64000000000000,48656229147],
                [4180500000000,66888000000000,4180500000000],
                [64229156229147,10888000000000,131843770853]]
    scales = [0,1,2,3,17,101]
    for s in scales:
        for axis in range(3):
            actual = [sum(s*c for b,c in zip(blocks,counts) if b[axis] == a) for a in range(3)]
            assert actual == [s*c for c in expected[axis]]
            assert sum(actual) == s*P
    assert 500*counts[0] == 861*counts[1] and counts[2] == 15*counts[1]
    print("PASS: exact six rational probabilities, 18 scaled marginal histograms and the target aspect.")
    lengths = [0,1,P-1,P,P+1,2*P-1,2*P,2*P+1,17*P-1,17*P,17*P+1,101*P+999]
    for N in lengths:
        s = N//P
        assert s*P <= N < s*P+P
        assert (s > 0) == (N >= P)
    print(f"PASS: {len(lengths)} exact floor/period boundary cases.")
    # Bounded independent word histograms, not the huge target reference word.
    words = 0
    for n in range(5):
        for word in product(range(6), repeat=n):
            joint = [word.count(b) for b in range(6)]
            for axis in range(3):
                direct = [sum(blocks[b][axis] == a for b in word) for a in range(3)]
                aggregate = [sum(joint[b] for b in range(6) if blocks[b][axis] == a) for a in range(3)]
                assert direct == aggregate and sum(direct) == n
            words += 1
    print(f"PASS: {words} bounded CW words with independently accumulated marginal histograms.")
    print("SCOPE: exact finite arithmetic; asymptotic slack and logarithmic entropy are kernel-checked in Lean. No large target word or fast-generation claim.")


if __name__ == '__main__':
    main()
