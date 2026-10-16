#!/usr/bin/env python3
"""Exact numerical certificate for the aligned polynomial-cache APSP bound.

This certifies numerical inequalities only. The separately supplied aligned
embedding and the two-sided polynomial-cache query/encoder lemmas must be
proved independently in outputs/exponent-improvement.tex.
Finite embedding checks alone do not establish an asymptotic algorithm.
"""

import verify_exponents as v
from verify_exponents import F, Interval, entropy, log_bounds, above


c, theta, b, delta = map(F, ('10.66550171', '.06529782140', '.04604634600', '.00705208'))
R, S = 1000000000, 768979045
eta = b / R
u, zmax = S * eta, (R - S) * eta
e = b + u
ln2, ln4 = map(log_bounds, (F(2), F(4)))
CK = c * entropy(1 / c) / ln4
T = CK + c - 1
G = (c * entropy(1 / c) - c * entropy((1 - theta) / c) - theta * ln4) / ln2
q1 = 2 * entropy(theta) / ln4
q2 = 2 * (entropy(theta) + theta * ln4) / ln4
Esource, Ebox = T + q1, T - G

print('Aligned polynomial cache: exact numerical feasibility certificate')
print('Separate proof dependencies: aligned embedding; two-sided polynomial cache and query.')
print('Numerical checks supplement the separate embedding, cache, and query proofs.')
for label, value in (
    ('c', c), ('theta', theta), ('b', b), ('R', R), ('S', S),
    ('candidate eta', eta), ('u', u), ('final ring exponent', zmax), ('e', e),
    ('CK', CK), ('T original geometry', T), ('G', G),
    ('q1 residual and cache overhead', q1), ('q2 stored', q2),
    ('E_source=T+q1', Esource), ('E_box=T-G', Ebox),
    ('target saving', delta), ('target exponent if separate lemmas hold', 3 - delta),
):
    print(f'  {label}: {Interval.cast(value).midpoint_display()}')

for label, value, target in (
    ('ordinary tail regime', c - 5, 0),
    ('positive switching threshold', theta, 0),
    ('unweighted cache cutoff increasing', F(1, 2) - theta, 0),
    ('stored cutoff increasing', F(4, 5) - theta, 0),
    ('ordinary private-cap tail geometric', 1 - 4 / (c - 1), 0),
    ('box private-cap tail geometric', 1 - 4 * (1 - theta) / (c - 1 + theta), 0),
    ('positive box gain', G, 0),
    ('box gain below one', 1 - G, 0),
    ('positive residual query exponent', q1, 0),
    ('positive stored query exponent', q2, 0),
    ('positive source encoder slope', Esource + F(1, 2), 0),
    ('positive box encoder slope', Ebox + F(1, 2), 0),
    ('positive original geometry slope', T - F(1, 2), 0),
    ('positive frozen-factor count', S, 0),
    ('at least two cyclic factors', R - S, 1),
    ('positive final ring exponent', zmax, 0),
    ('positive candidate exponent', eta, 0),
    ('middle blocks fit', 1 - b, 0),
    ('incidence bookkeeping after enumeration', b - eta, delta),
):
    above(label, value, target)

# Every scalar-phase exponent is affine in the candidate modulus exponent x.
for endpoint, x in (('initial', F(0)), ('freeze', u)):
    ep = b + x
    for label, value, target in (
        ('boxes', b - x + ep * G - eta, delta),
        ('residual queries', b - ep * q1 - eta, delta),
        ('stored queries', b - ep * q2 - eta, delta),
        ('two-sided polynomial cache encodings', 1 + b - x / 2 - ep * Esource - eta, delta),
        ('ordinary box encodings', 1 + b - x / 2 - ep * Ebox - eta, delta),
        ('matrix formation', 1 - 3 * x / 2 - eta, delta),
        ('original tile geometry', 1 + x / 2 - ep * T, 0),
    ):
        above(f'phase I {endpoint}: {label}', value, target)

# Each preprocessing value and residual contraction pays the full ring
# length n^z. A stored box query reads one already precomputed coefficient.
for endpoint, z in (('start', F(0)), ('final', zmax)):
    for label, value, target in (
        ('boxes', b - u - z + e * G - eta, delta),
        ('residual queries', b - z - e * q1 - eta, delta),
        ('stored queries', b - e * q2 - eta, delta),
        ('two-sided polynomial cache encodings', 1 + b - u / 2 - z - e * Esource - eta, delta),
        ('ordinary box encodings', 1 + b - u / 2 - z - e * Ebox - eta, delta),
        ('matrix formation', 1 - 3 * u / 2 - z - eta, delta),
        ('original tile geometry', 1 + u / 2 - e * T, 0),
    ):
        above(f'phase II {endpoint}: {label}', value, target)

assert eta == F('.000000000046046346')
assert u == F('.03540867517281957')
assert e == F('.08145502117281957')
assert u + zmax == b and R * eta == b and S * eta == u
print('Exact candidate/freeze/ring-stage identities: PASS')
print(f'PASS: {v.checked} strict rational inequalities.')
print('Numerical target: 2.99294792, conditional on the separately audited embedding/cache/query lemmas.')
