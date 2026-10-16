#!/usr/bin/env python3
"""Exact rational certificates for deterministic APSP via pruned moment filters.

This checks numerical inequalities, not the asymptotic algorithms or external
matrix multiplication theorems. The first witness uses arXiv:2307.07970v2,
Table 1: omega(1,1.2,1)<=2.535063, omega(1,1.5,1)<=2.794941.
The second separately assumes arXiv:2610.10494v2, Corollary 1.2 and Lemma 6.1:
omega(1,kappa,1)<=1+kappa+1/(4*kappa), for kappa>=1/2, in characteristic zero.
Both charge a fixed positive exponent allowance 1e-8. See the canonical TeX
for the exact-integer implementation and the cyclic reconstruction proof.
The witnesses are fixed decimal rationals; searches live separately in work/.
Run from the repository root: python3 outputs/verify_deterministic_apsp.py
"""
import verify_exponents as verifier
from verify_exponents import F,log_bounds,entropy,parameters,above,Interval

cases=[
 ('Established rectangular interpolation',False,11,
 '21.8429984','.1125375917','.0254666251','.0478165400',
 '.0613141114','.00037371790','.0041108'),
 ('Recent rectangular curve',True,13,
 '21.4287303','.1128443719','.0255360478','.0483646500',
 '.0625769172','.00032059682','.0041677'),
]
for name,recent,k,*values in cases:
 c,th,r,al,e,z,delta=map(F,values)
 a,b=(e+z)/2,(e-z)/2
 G,_,_,_=parameters(c,th)
 GA,_,_,_=parameters(c,al)
 ln4,ln6,ln9,ln3=(log_bounds(F(i)) for i in (4,6,9,3))
 A=(c-1)*ln3/ln4;C=c*entropy(1/c)/ln4
 tail=(1-r)*entropy(th/(1-r))
 q1=(tail+(th+r)*ln6)/ln4;q2=(tail+th*ln9)/ln4
 X=c*(1-al)/(1-r)**2
 j=21
 # Since X>j, 3^-X < 3^-j; monotonicity of log gives a certified
 # rational-input upper bound for the lazy-query exponent.
 lazy=r*ln6/ln4+c*ln3/ln4*(al-r)/(1-r)+(1-r)*log_bounds(1+F(6,3**j))/ln4
 kap=1+(k-1)*b
 w=1+kap+1/(4*kap) if recent else F('2.535063')+F('.86626')*(kap-F('1.2'))
 epsilon=F('.00000001')
 print('\n'+name)
 for label,x in [('c',c),('theta',th),('r',r),('alpha',al),('e',e),('z',z),('a',a),('b',b),('kappa',kap),('q1',q1),('q2',q2),('q_lazy_upper',lazy),('G_alpha',GA)]:
  print('  '+label+' = '+Interval.cast(x).midpoint_display())
 for label,x,target in (
  ('c>10',c-10,0),('positive block',b,0),('positive z',z,0),
  ('prefix positive',r,0),('pruning beyond prefix',al-r,0),('pruning below box threshold',th-al,0),
  ('prefix fits',1-th-r,0),('query sum increases',F(6,7)-th/(1-r),0),
  ('exponential upper-bound domain',X-j,0),
  ('boxes',e*G-z,delta),('residual query',e*(F('.5')-q1)-z/2,delta),
  ('stored query',e*(F('.5')-q2)-z/2,delta),('lazy reconstruction query',e*(F('.5')-lazy)-z/2,delta),
  ('failed scans',k*z,delta),('pruned shared encodings',1-e*(A-GA-F('.25'))-3*z/4,delta),
  ('matrix writing',1-3*e/4-3*z/4,delta),('residue allowance',1-a,delta),
  ('input placement fits retained encodings',A-1-GA,0),
  ('original outer geometry',1+a/2-e*A,0),('independent product capacity',1-b-e*C,0),
  ('selector with explicit allowance',3-w-(k+1)*a-epsilon,delta),
 ):above(label,x,target)
 if recent:
  above('recent curve domain',kap-F('.5'),0)
 else:
  above('interpolation lower domain',kap-F('1.2'),0)
  above('interpolation upper domain',F('1.5')-kap,0)
 print('  Certified exponent: '+Interval(3-delta).midpoint_display())

print(f"\nPASS: {verifier.checked} strict rational inequalities.")
