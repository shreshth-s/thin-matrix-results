#!/usr/bin/env python3
"""Independent exact Vandermonde/Lagrange checks and tensor-power extraction.

Rational Gaussian elimination is deliberately independent of the retained
integer polynomial recurrence. This is a finite test, not an exponent proof.
"""
from fractions import Fraction
from itertools import product
from check_cw_polynomial import certificate, tensor_entry, mul


def solve(a, b):
    rows = [[Fraction(x) for x in row]+[Fraction(v)] for row,v in zip(a,b)]
    for i in range(len(rows)):
        pivot = next(j for j in range(i,len(rows)) if rows[j][i])
        rows[i],rows[pivot] = rows[pivot],rows[i]
        s = rows[i][i]
        rows[i] = [v/s for v in rows[i]]
        for j in range(len(rows)):
            if j != i:
                s = rows[j][i]
                rows[j] = [v-s*w for v,w in zip(rows[j],rows[i])]
    return [row[-1] for row in rows]


def weights(d,k):
    return solve([[i**a for i in range(d+1)] for a in range(d+1)],
                 [int(a==k) for a in range(d+1)])


def evaluate(p,t):
    out = 0
    for c in reversed(p):
        out = c+t*out
    return out


def main():
    moments = 0
    for d in (0,1,2,3,10,20):
        delta = [(-1)**(d-i) for i in range(d+1)]
        for i in range(d+1):
            for j in range(1,i+1): delta[i] *= j
            for j in range(1,d-i+1): delta[i] *= j
        den = 1
        for z in delta: den *= z
        assert den
        for k in range(d+1):
            w = weights(d,k)
            for i in range(d+1):
                p = [1]
                for j in range(d+1):
                    if j != i: p = mul(p,[-j,1])
                assert w[i] == Fraction(p[k],delta[i])
                assert (w[i]*den).denominator == 1
            for a in range(d+1):
                assert sum(w[i]*i**a for i in range(d+1)) == int(a==k)
                moments += 1
    w = weights(10,3)
    count = 0
    for i,j,k in product(range(18),repeat=3):
        p = certificate(16,i,j,k)
        assert sum(w[t]*evaluate(p,t) for t in range(11)) == tensor_entry(16,i,j,k)
        count += 1
    w2 = weights(20,6)
    cases = [(0,1,1),(1,0,1),(1,1,0),(17,0,0),(0,17,0),(0,0,17),
             (1,2,3),(17,17,17),(0,0,0)]
    for a,b in product(cases,repeat=2):
        p = mul(certificate(16,*a),certificate(16,*b))
        assert sum(w2[t]*evaluate(p,t) for t in range(21)) == tensor_entry(16,*a)*tensor_entry(16,*b)
        count += 1
    assert weights(0,0)==[Fraction(1)]
    print(f'PASS: {moments} exact Vandermonde moments and {count} CW extraction coordinates (all n=1, 81 selected n=2); shared signed denominators and n=0 checked.')


if __name__ == '__main__':
    main()
