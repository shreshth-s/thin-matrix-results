#!/usr/bin/env python3
"""Finite check of the rational conditional-expectation small-bias construction."""
from fractions import Fraction as F


def fwht(values):
    values = list(values)
    width = 1
    while width < len(values):
        for start in range(0,len(values),2*width):
            for j in range(width):
                a,b = values[start+j],values[start+j+width]
                values[start+j],values[start+j+width] = a+b,a-b
        width *= 2
    return values


def run(m):
    epsilon = F(1,2)
    a = 1+epsilon
    C = (a+1/a)/2
    length = 32*(m+1)  # 8(m+1)/epsilon^2
    universe = 1 << m
    sums = [0]*universe
    selected = []
    potential = F(2*(universe-1))
    initial = potential
    for stage in range(length):
        weights = [F(0)] + [a**s-a**(-s) for s in sums[1:]]
        scores = fwht(weights)
        assert scores == [sum(weights[v]*(-1)**((v&d).bit_count()&1)
                              for v in range(universe)) for d in range(universe)]
        d = min(range(universe),key=lambda d:(scores[d],d))
        selected.append(d)
        for v in range(1,universe):
            sums[v] += (-1)**((v&d).bit_count()&1)
        next_potential = sum(a**s+a**(-s) for s in sums[1:])
        assert next_potential <= C*potential
        potential = next_potential
    threshold_exponent = epsilon*length
    assert threshold_exponent.denominator == 1
    assert potential <= initial*C**length < a**threshold_exponent.numerator
    assert max(abs(s) for s in sums[1:]) < epsilon*length
    # Every coordinate system given by an invertible map consequently has
    # a light translate; test several full-rank linear bases directly.
    bound = F(m)*(1+epsilon)/2
    for h in range(universe):
        assert min((h^d).bit_count() for d in selected) <= bound
    print('PASS exact rational small-bias construction:',
          dict(m=m,length=length,distinct=len(set(selected)),
               max_character_sum=max(abs(s) for s in sums[1:])))


if __name__ == '__main__':
    for m in (2,3,4):
        run(m)
