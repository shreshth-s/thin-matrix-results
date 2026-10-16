#!/usr/bin/env python3
"""Exact numerical certificate for the canonical partial-cache APSP bound.

This proves strict parameter inequalities, not the asymptotic algorithm.
The source five-term embedding, partial normal-projection cache, first-ell
query partition, and cyclic-fiber reduction are justified separately in
outputs/exponent-improvement.tex. Both query branches, both phase endpoints,
all candidate calls, and the unchanged tile geometry are charged here.
"""
import verify_exponents as v
from verify_exponents import F,Interval,entropy,log_bounds,above

c,theta,rho,y,b=map(F,('10.767898969','.060343925615','.066059242397',
                       '.025749961','.04337385'))
R,S=100000,88618
eta=b/R
u=S*eta
zmax=(R-S)*eta
e=b+u
delta=F('.006599')
ln2,ln4=map(log_bounds,(F(2),F(4)))
CK=c*entropy(1/c)/ln4
T=CK+c-1
G=(c*entropy(1/c)-c*entropy((1-theta)/c)-theta*ln4)/ln2
qcache=(entropy(rho)+rho*ln2)/ln4
Esource=T+qcache
Ebox=T-G
qinner=(2*entropy(theta)+2*theta*ln2)/ln4
qold=(log_bounds((1+3*y)*(1+2*y))-2*theta*log_bounds(y))/ln4
qhigh=qold-rho*log_bounds(F(3,2))/ln4
qstored=2*(entropy(theta)+theta*ln4)/ln4

print('Partial global normal-projection cache: exact numerical certificate')
print('Separate proof dependencies: cache encoder, first-ell partition, cyclic-fiber oracle.')
for label,x in (
    ('c',c),('theta',theta),('rho',rho),('coefficient_y',y),('b',b),
    ('R',R),('S',S),('eta',eta),('u',u),('final_ring_exponent',zmax),('e',e),
    ('target_saving',delta),('CK',CK),('T',T),('G',G),('q_cache',qcache),
    ('E_source',Esource),('E_box',Ebox),('q_inner',qinner),('q_old',qold),
    ('q_high',qhigh),('q_stored',qstored),
):print(f'  {label}: {Interval.cast(x).midpoint_display()}')

for label,x,target in (
    ('ordinary tail regime',c-5,0),
    ('positive switching threshold',theta,0),
    ('stored coefficient cutoff increasing',F(4,5)-theta,0),
    ('direct inner coefficient cutoff increasing',F(2,3)-theta,0),
    ('positive cached degree',rho,0),
    ('cache coefficient cutoff increasing',F(2,3)-rho,0),
    ('cache cutoff below total residual degree',2*theta-rho,0),
    ('low-family symmetric degree lies inside cache',rho-theta,0),
    ('high-family coefficient saddle remains admissible',3*y/(1+3*y)-rho,0),
    ('positive coefficient point',y,0),
    ('coefficient point below one',1-y,0),
    ('ordinary scalar tail geometric',1-4/(c-1),0),
    ('box tail geometric',1-4*(1-theta)/(c-1+theta),0),
    ('positive box gain',G,0),
    ('box gain below one',1-G,0),
    ('positive direct query exponent',qinner,0),
    ('positive high query exponent',qhigh,0),
    ('positive stored query exponent',qstored,0),
    ('positive source encoder slope',Esource+F(1,2),0),
    ('positive box encoder slope',Ebox+F(1,2),0),
    ('positive geometry slope',T-F(1,2),0),
    ('positive frozen-stage count',S,0),
    ('at least two remaining prime factors',R-S,1),
    ('positive ring exponent',zmax,0),
    ('middle blocks fit',1-b,0),
    ('incidence bookkeeping after candidates',b-eta,delta),
):above(label,x,target)

# Scalar phase: all savings and the tile condition are affine in s.
for name,s in (('initial',F(0)),('freeze',u)):
    ep=b+s
    for label,val,target in (
        ('boxes',b-s+ep*G-eta,delta),
        ('low residual queries',b-ep*qinner-eta,delta),
        ('high residual queries',b-ep*qhigh-eta,delta),
        ('stored queries',b-ep*qstored-eta,delta),
        ('cached source encodings',1+b-s/2-ep*Esource-eta,delta),
        ('ordinary box encodings',1+b-s/2-ep*Ebox-eta,delta),
        ('matrix formation',1-3*s/2-eta,delta),
        ('tile geometry',1+s/2-ep*T,0),
    ):above(f'phase I {name}: {label}',val,target)

# Cyclic phase: q=n^z multiplies source/preprocessing and both residual
# query branches, while a stored box supplies only its requested coefficient.
for name,z in (('start',F(0)),('final',zmax)):
    for label,val,target in (
        ('boxes',b-u-z+e*G-eta,delta),
        ('low residual queries',b-z-e*qinner-eta,delta),
        ('high residual queries',b-z-e*qhigh-eta,delta),
        ('stored queries',b-e*qstored-eta,delta),
        ('cached source encodings',1+b-u/2-z-e*Esource-eta,delta),
        ('ordinary box encodings',1+b-u/2-z-e*Ebox-eta,delta),
        ('matrix formation',1-3*u/2-z-eta,delta),
        ('tile geometry',1+u/2-e*T,0),
    ):above(f'phase II {name}: {label}',val,target)

assert u+zmax==b and S*eta==u and (R-S)*eta==zmax
print('Exact fixed-stage identities: PASS')
print('Target exponent, conditional on the separately audited algorithm:',
      Interval(3-delta).midpoint_display())
print(f'PASS: {v.checked} strict rational interval inequalities.')
