#!/usr/bin/env python3
"""Exact interval certificate for deterministic cyclic 3SUM and exact counts.

The canonical proof supplies the fixed-bucket count-lifting and cyclic
histogram lemmas. Numerical inequalities supplement, not prove, them.
"""
import verify_exponents as v
from verify_exponents import F, Interval, entropy, log_bounds, above

c, theta, b, delta = map(F, ('10.83107856', '.06504251269', '.04436367207', '.0068945'))
R, S = 10**9, 884889170
eta = 2*b/R
u, zmax = S*eta, (R-S)*eta
ln2, ln4 = log_bounds(F(2)), log_bounds(F(4))
CK = c*entropy(1/c)/ln4
T = CK+c-1
G = (c*entropy(1/c)-c*entropy((1-theta)/c)-theta*ln4)/ln2
Q = entropy(theta)/ln2
q2 = Q+2*theta
Esource, Ebox = T+Q, T-G

print('Deterministic cyclic 3SUM and exact counts: rational interval certificate')
print('Independent dependencies: fixed original buckets; exact count lifting; cyclic histogram folding.')
for label, value in (
    ('c',c),('theta',theta),('b',b),('R',R),('S',S),
    ('candidate eta',eta),('folded exponent u',u),('final ring exponent',zmax),
    ('T',T),('G',G),('Q residual',Q),('q2 stored',q2),
    ('E source',Esource),('E box',Ebox),('target saving',delta),
    ('target exponent',2-delta),
):
    print(f'  {label}: {Interval.cast(value).midpoint_display()}')

for label,value,target in (
    ('ordinary tail regime',c-5,0),
    ('positive threshold',theta,0),
    ('unweighted cache cutoff increasing',F(1,2)-theta,0),
    ('stored cutoff increasing',F(4,5)-theta,0),
    ('ordinary private-cap tail geometric',1-4/(c-1),0),
    ('box private-cap tail geometric',1-4*(1-theta)/(c-1+theta),0),
    ('positive box gain',G,0),('box gain below one',1-G,0),
    ('positive residual exponent',Q,0),('positive stored exponent',q2,0),
    ('positive source-encoder slope',Esource+F(1,2),0),
    ('positive box-encoder slope',Ebox+F(1,2),0),
    ('positive geometry slope',T-F(1,2),0),
    ('positive frozen count',S,0),('at least two ring factors',R-S,1),
    ('positive candidate exponent',eta,0),('sub-buckets fit input',1-b,0),
    ('incidence/bucket bookkeeping after enumeration',b-eta,delta),
    ('original-input reading after enumeration',1-eta,delta),
):
    above(label,value,target)

# The matrix dimensions at folded exponent x are
# N=n^(1-b+x/2), D=n^x; there are O~(n^(2-b)) queries.
# Every exponent is affine in x, so these endpoints cover all direct stages.
for endpoint,x in (('initial',F(0)),('freeze',u)):
    for label,value,target in (
        ('boxes',2*b-x*(1-G)-eta,delta),
        ('residual queries',b-x*Q-eta,delta),
        ('stored queries',b-x*q2-eta,delta),
        ('polynomial source cache',1+b-x*(Esource+F(1,2))-eta,delta),
        ('box encodings',1+b-x*(Ebox+F(1,2))-eta,delta),
        ('dense histogram formation',1+b-3*x/2-eta,delta),
        ('tile geometry',1-b+x/2-x*T,0),
    ):
        above(f'phase I {endpoint}: {label}',value,target)

# After freezing the physical modulus, each source, box, and residual
# contraction pays full ring length n^z. Stored reads select one coefficient.
for endpoint,z in (('start',F(0)),('final',zmax)):
    for label,value,target in (
        ('boxes',2*b-u+u*G-z-eta,delta),
        ('residual queries',b-u*Q-z-eta,delta),
        ('stored queries',b-u*q2-eta,delta),
        ('polynomial source cache',1+b-u*(Esource+F(1,2))-z-eta,delta),
        ('box encodings',1+b-u*(Ebox+F(1,2))-z-eta,delta),
        ('dense histogram formation',1+b-3*u/2-z-eta,delta),
        ('tile geometry',1-b+u/2-u*T,0),
    ):
        above(f'phase II {endpoint}: {label}',value,target)

assert u+zmax == 2*b and R*eta == 2*b and S*eta == u
print('Exact candidate/freeze/ring identities: PASS')
assert delta > 0 and 8-2*delta > 0
mono = F(3,2)-delta/(8-2*delta)
above('inherited MonoConvolution exponent below 1.4991368', F('1.4991368')-mono, 0)
print(f'Exact inherited MonoConvolution exponent: {mono}')
print(f'PASS: {v.checked} strict rational interval inequalities.')
print('Certified numerical target: 1.9931055 (also the rounded exponent 1.993106).')
