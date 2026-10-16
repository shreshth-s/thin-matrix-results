#!/usr/bin/env python3
"""Exact numerical certificate for the separately proved profile-prefix DS.

Dependencies: canonical composite reduction, squared five-term embedding,
fixed-profile slot restriction, augmented encoders, and sparse-Yates query.
This verifies inequalities, not those algorithmic lemmas or optimality.
"""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import verify_exponents as v
from verify_exponents import F,Interval,entropy,log_bounds,above

c,theta,r,e,y=map(F,('10.74132662','.056740653','.038571087','.083812911','.025146880'))
b=e/2
R=100000
eta=b/R
delta=F('.006324')
ln2,ln4=map(log_bounds,(F(2),F(4)))
CK=c*entropy(1/c)/ln4
T=CK+c-1
G=(c*entropy(1/c)-c*entropy((1-theta)/c)-theta*ln4)/ln2
Jaug=r*(CK-F('1.5'))
Eaug=T-Jaug
Ebox=T-G
q1=r+((1-r)*log_bounds((1+3*y)*(1+2*y))-2*theta*log_bounds(y))/ln4
q2=2*((1-r)*entropy(theta/(1-r))+theta*ln4)/ln4

print('Fixed-profile direct-prefix five-term APSP numerical certificate')
for label,x in [('c',c),('theta',theta),('r',r),('e',e),('y',y),('b',b),
                ('prime_factors_per_composite',R),('candidate_exponent',eta),
                ('target_saving',delta),('CK',CK),('T',T),('G',G),
                ('augmented_encoder_saving',Jaug),('E_aug',Eaug),('E_box',Ebox),
                ('q1',q1),('q2',q2)]:
    print(f'  {label}: {Interval.cast(x).midpoint_display()}')
for label,x,target in (
    ('compact tail regime',c-5,0),
    ('positive prefix',r,0),
    ('prefix below one',1-r,0),
    ('positive switching fraction',theta,0),
    ('switching fits suffix',1-r-theta,0),
    ('positive rational coefficient point',y,0),
    ('coefficient point below one',1-y,0),
    ('stored binomial cutoff increasing',F(4,5)-theta/(1-r),0),
    ('prefix projection tail geometric',1-2/(c-1),0),
    ('ordinary suffix tail geometric',1-4/(c-1),0),
    ('box tail geometric',1-4*(1-theta)/(c-1+theta),0),
    ('positive box gain',G,0),
    ('box gain below one',1-G,0),
    ('positive augmented encoding gain',Jaug,0),
    ('positive residual query exponent',q1,0),
    ('positive stored query exponent',q2,0),
    ('positive augmented encoding slope',Eaug+F(1,2),0),
    ('positive box encoding slope',Ebox+F(1,2),0),
    ('positive geometry slope',T-F(1,2),0),
    ('boxes after candidate enumeration',e*G-eta,delta),
    ('residual queries after candidate enumeration',e*(F(1,2)-q1)-eta,delta),
    ('stored queries after candidate enumeration',e*(F(1,2)-q2)-eta,delta),
    ('augmented encodings after candidate enumeration',1-e*(Eaug-F(1,4))-eta,delta),
    ('ordinary box encodings after candidate enumeration',1-e*(Ebox-F(1,4))-eta,delta),
    ('matrix formation after candidate enumeration',1-3*e/4-eta,delta),
    ('incidence bookkeeping after candidate enumeration',b-eta,delta),
    ('original profile tile fits',1-e*(T-F(1,4)),0),
    ('initial-modulus tile fits',1-b*T,0),
    ('middle blocks fit',1-b,0),
):
    above(label,x,target)
print('Certified target exponent:',Interval(3-delta).midpoint_display())
print(f'PASS: {v.checked} strict rational interval inequalities.')
