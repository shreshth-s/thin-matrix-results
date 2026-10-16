#!/usr/bin/env python3
"""Exact interval certificate for deterministic 3XOR and exact #3XOR counts.

Transplant of the fixed-bucket cyclic 3SUM certificate to F_2: linear
bucket projection, prefix-exact single-window refinement, greedy hash rows
from a (1/l)-biased set, physical hash folded into the outer dimensions and
the remaining rows in the group algebra Z[F_2^m].  The candidate pool is
polylogarithmic, so there is no candidate charge eta and no fixed stage
count (R, S); the physical exponent u is a free rational.  Numerical
inequalities supplement, not prove, the lemmas.
"""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_exponents as v
from verify_exponents import F, Interval, entropy, log_bounds, above

c, theta, b, u, delta = map(F, ('10.83107856', '.06504251269', '.04436367207',
                                 '.0785138659', '.0068945'))
zmax = 2*b-u                      # ring exponent at the last greedy row
ln2, ln4 = log_bounds(F(2)), log_bounds(F(4))
CK = c*entropy(1/c)/ln4
T = CK+c-1
G = (c*entropy(1/c)-c*entropy((1-theta)/c)-theta*ln4)/ln2
Q = entropy(theta)/ln2
q2 = Q+2*theta
Esource, Ebox = T+Q, T-G

print('Deterministic 3XOR and exact #3XOR: rational interval certificate')
print('Independent dependencies: linear-projection buckets; prefix-exact count lifting;'
      ' group-algebra histogram folding; aligned cache over Z[F_2^m].')
for label, value in (
    ('c', c), ('theta', theta), ('b', b), ('physical hash exponent u', u),
    ('final group-algebra exponent 2b-u', zmax), ('T', T), ('G', G),
    ('Q residual', Q), ('q2 stored', q2), ('E source', Esource), ('E box', Ebox),
    ('target saving', delta), ('target exponent', 2-delta),
):
    print(f'  {label}: {Interval.cast(value).midpoint_display()}')

for label, value, target in (
    ('ordinary tail regime', c-5, 0),
    ('positive threshold', theta, 0),
    ('unweighted cache cutoff increasing', F(1, 2)-theta, 0),
    ('stored cutoff increasing', F(4, 5)-theta, 0),
    ('ordinary private-cap tail geometric', 1-4/(c-1), 0),
    ('box private-cap tail geometric', 1-4*(1-theta)/(c-1+theta), 0),
    ('positive box gain', G, 0), ('box gain below one', 1-G, 0),
    ('positive residual exponent', Q, 0), ('positive stored exponent', q2, 0),
    ('positive source-encoder slope', Esource+F(1, 2), 0),
    ('positive box-encoder slope', Ebox+F(1, 2), 0),
    ('positive geometry slope', T-F(1, 2), 0),
    ('positive physical hash exponent', u, 0),
    ('positive group-algebra exponent', zmax, 0),
    ('sub-buckets fit input', 1-b, 0),
    # polylog(n) hash candidates per greedy row, O(log n) rows per attempt,
    # O(log n) attempts per level, d = O(log n) levels: no candidate charge.
    ('incidence/bucket bookkeeping', b, delta),
    ('original-input reading and bucket-projection greedy', F(1), delta),
):
    above(label, value, target)

# Scalar phase: physical hash with 2^t = n^x rows folded, x in [0,u];
# N = n^(1-b+x/2), D = n^x, O~(n^(2-b)) incidence queries, ring length 1.
for endpoint, x in (('initial', F(0)), ('freeze', u)):
    for label, value, target in (
        ('boxes', 2*b-x*(1-G), delta),
        ('residual queries', b-x*Q, delta),
        ('stored queries', b-x*q2, delta),
        ('polynomial source cache', 1+b-x*(Esource+F(1, 2)), delta),
        ('box encodings', 1+b-x*(Ebox+F(1, 2)), delta),
        ('dense histogram formation', 1+b-3*x/2, delta),
        ('tile geometry', 1-b+x/2-x*T, 0),
    ):
        above(f'phase I {endpoint}: {label}', value, target)

# Group-algebra phase: physical hash frozen at n^u; the remaining rows and
# the one extension row live in Z[F_2^m], q = 2^m = n^z, z in [0, 2b-u].
for endpoint, z in (('start', F(0)), ('final', zmax)):
    for label, value, target in (
        ('boxes', 2*b-u+u*G-z, delta),
        ('residual queries', b-u*Q-z, delta),
        ('stored queries', b-u*q2, delta),
        ('polynomial source cache', 1+b-u*(Esource+F(1, 2))-z, delta),
        ('box encodings', 1+b-u*(Ebox+F(1, 2))-z, delta),
        ('dense histogram formation', 1+b-3*u/2-z, delta),
        ('tile geometry', 1-b+u/2-u*T, 0),
    ):
        above(f'phase II {endpoint}: {label}', value, target)

assert u+zmax == 2*b
print('Exact physical/group-algebra split identity u + (2b-u) = 2b: PASS')
print(f'PASS: {v.checked} strict rational interval inequalities.')
print('Certified numerical target: 1.9931055 for 3XOR and exact #3XOR (sets);'
      ' Majdoddin reports 1.99451.')
# Recorded run: 46 PASS lines; phase II final savings 0.006894514356880 (boxes),
# 0.006894514356423 (residual), 0.006894514358140 (stored), 0.006894514476594
# (cache); tile margin 0.034150193950171; minimum slack above delta 1.4356e-8.