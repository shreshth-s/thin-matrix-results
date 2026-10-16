#!/usr/bin/env python3
"""Exact arithmetic certificate for the cyclic-factor reduction.

This certifies the displayed numerical cost inequalities ONLY.  The new
ring-valued query lemma and composite-incidence implementation are separate
proof dependencies; numerical verification alone does not prove them.

The five-term source embedding and sparse-Yates query are from the current
canonical proof.  No tensor prefix is used: r=0 and the full ordinary
encoder exponent is T.  The scalar box encoder exponent T-G is also
charged, even though it is dominated here.
"""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_exponents as v
from verify_exponents import F, Interval, entropy, log_bounds, above

c, theta, y, b = map(F, ('10.67333763', '.0590858825', '.025178142', '.04368276'))
R, S = 100000, 92277
eta = b / R
u = S * eta
zmax = (R-S) * eta
e = b + u
delta = F('.006559')
ln2, ln4 = map(log_bounds, (F(2), F(4)))
CK = c*entropy(1/c)/ln4
T = CK+c-1
G = (c*entropy(1/c)-c*entropy((1-theta)/c)-theta*ln4)/ln2
Ebox = T-G
q1 = (log_bounds((1+3*y)*(1+2*y))-2*theta*log_bounds(y))/ln4
q2 = 2*(entropy(theta)+theta*ln4)/ln4

print('Cyclic-factor APSP numerical certificate')
print('Status: numerical inequalities only; ring algorithm is a separate proof dependency.')
for label, x in (
    ('c', c), ('theta', theta), ('r', 0), ('coefficient_point_y', y),
    ('block_exponent_b', b), ('factors_per_composite_R', R),
    ('factors_before_freezing_S', S), ('candidate_exponent_eta', eta),
    ('frozen_modulus_exponent_u', u), ('final_ring_length_exponent_z', zmax),
    ('tensor_exponent_e', e), ('target_saving', delta), ('CK', CK),
    ('T', T), ('G', G), ('E_box', Ebox), ('q_residual', q1), ('q_stored', q2),
):
    print(f'  {label}: {Interval.cast(x).midpoint_display()}')

for label, x, target in (
    ('compact ordinary tail regime', c-5, 0),
    ('positive switching fraction', theta, 0),
    ('stored binomial cutoff increasing', F(4,5)-theta, 0),
    ('positive coefficient point', y, 0),
    ('coefficient point below one', 1-y, 0),
    ('ordinary leaf tail geometric', 1-4/(c-1), 0),
    ('box leaf tail geometric', 1-4*(1-theta)/(c-1+theta), 0),
    ('positive box gain', G, 0),
    ('box gain below one', 1-G, 0),
    ('positive residual query exponent', q1, 0),
    ('positive stored query exponent', q2, 0),
    ('positive ordinary encoder slope', T+F(1,2), 0),
    ('positive box encoder slope', Ebox+F(1,2), 0),
    ('positive geometry slope', T-F(1,2), 0),
    ('positive frozen-factor count', S, 0),
    ('at least two remaining factors', R-S, 1),
    ('positive final ring exponent', zmax, 0),
    ('positive candidate exponent', eta, 0),
    ('middle blocks fit', 1-b, 0),
    ('incidence bookkeeping after enumeration', b-eta, delta),
):
    above(label, x, target)

# Before freezing, the queried candidate modulus has log_n d=x in [0,u].
# Every expression is affine in x, and the explicit checks cover both
# endpoints, including the initial modulus.  Polylog factors from fixed R
# are handled by the strictly positive runtime and fit slack.
for name, x in (('initial', F(0)), ('freeze', u)):
    ep = b+x
    for label, val, target in (
        ('boxes', b-x+ep*G-eta, delta),
        ('residual queries', b-ep*q1-eta, delta),
        ('stored queries', b-ep*q2-eta, delta),
        ('ordinary encodings', 1+b-x/2-ep*T-eta, delta),
        ('box encodings', 1+b-x/2-ep*Ebox-eta, delta),
        ('matrix formation', 1-3*x/2-eta, delta),
        ('tile geometry', 1+x/2-ep*T, 0),
    ):
        above(f'phase I {name}: {label}', val, target)

# After freezing, d=d0 and the cyclic-ring length has exponent z in [0,zmax].
# All preprocessing and residual queries pay n^z.  The stored-box branch
# uses a separately indexed coefficient table, so it has no n^z query cost.
# This last assertion is an algorithmic proof dependency, not established
# by the numerical checks below.
for name, z in (('start', F(0)), ('final', zmax)):
    for label, val, target in (
        ('boxes', b-u-z+e*G-eta, delta),
        ('residual queries', b-z-e*q1-eta, delta),
        ('stored queries', b-e*q2-eta, delta),
        ('ordinary encodings', 1+b-u/2-z-e*T-eta, delta),
        ('box encodings', 1+b-u/2-z-e*Ebox-eta, delta),
        ('matrix formation', 1-3*u/2-z-eta, delta),
        ('tile geometry', 1+u/2-e*T, 0),
    ):
        above(f'phase II {name}: {label}', val, target)

assert u + zmax == b
assert S*eta == u and (R-S)*eta == zmax
assert R > S > 0
print('Exact prime-stage identities: PASS')
print('Target exponent, conditional on the separately audited ring lemma:',
      Interval(3-delta).midpoint_display())
print(f'PASS: {v.checked} strict rational interval inequalities.')
