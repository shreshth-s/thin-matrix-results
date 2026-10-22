#!/usr/bin/env python3
"""Exact certificate for the canonical light-source APSP bound 2.9926863.

Certifies the numeric consequences of the light-source, grouped-completion,
joint-box and rectangular-endpoint lemmas in exponent-improvement.tex.
The algorithmic proofs and external CW theorem are separate dependencies.
The historical work/light-source-improvement/certify_gauge.py is retained.
"""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_exponents as v
from verify_exponents import F,Interval,entropy,log_bounds,above
c=F('10.422903143551736');theta=F('.0656840679765022')
b=F('.04884094');R=10**14;S=76777119351634;source_rho=F(51,100)
delta=F('.0073137');allowance=F('1e-7')
k=15;qmm=16;ar=F(861,500);wcap=F('16.7220002')
alpha=wcap-k-1;beta=wcap-k-ar
p=F(4000,75249);ee=F(1,18);ff=F(646603,10**9);dd=ee-p-ff
rrd=dd/p;rre=ee/p;rrf=ff/p
assert p==F(qmm)/((qmm+2)*(k+ar))
assert (ar+1+k)*p+dd+ee+ff==1
assert alpha==ar-1+beta
eta=b/R;u=S*eta;zmax=b-u;e=b+u
cachez=F(1,4) # Same common inner exponent at every phase.
ln2,ln3,ln4=map(log_bounds,map(F,(2,3,4)))
def ent3(x,y,z):
 assert x+y+z==1 and min(x,y,z)>0
 return entropy(x)+(1-x)*entropy(y/(1-x))
Hx=ent3(ar*p+dd+ee,(k+1)*p,ff);Hy=ent3(p+dd+ff,(k+ar)*p,ee);Hz=ent3(k*p+ee+ff,(ar+1)*p,dd)
for name,hh in [('x',Hx),('y',Hy),('z',Hz)]:
 above('CW '+name+' marginal endpoint including positive allowance',(wcap-allowance)*p*log_bounds(F(qmm))-log_bounds(F(qmm+2))+hh,0)
CK=c*entropy(1/c)/ln4;T=CK+c-1
G=(c*entropy(1/c)-c*entropy((1-theta)/c)-theta*ln4)/ln2
Q=2*entropy(theta)/ln4;rho=source_rho/(c-1);gamma=entropy(rho)/ln4
rhot=(source_rho-theta)/(c-1);gamt=entropy(rhot)/ln4
gamprime=-log_bounds((1-rhot)/rhot)/((c-1)*ln4)
gprime=2*log_bounds((1-theta)/theta)/ln4+cachez*gamprime/(2*gamt*gamt)
above('symmetric type maximum at theta',gprime,0)
A=Interval.cast(F(1,2))/gamt-1-alpha
q2=Q+2*theta;Ebox=T-G
finalez=e*cachez
q=Q+beta*finalez/e;E=T+Q-A*finalez/e
Eroot=2*CK+(2*c-1)*ln3/ln4+Q-T
for name,z in [('c',c),('theta',theta),('global z cap',cachez),('source rare budget',source_rho),('gprime(theta)',gprime),('wcap',wcap),('row chunk exponent',ar),('alpha',alpha),('beta',beta),('kMM',k),('qMM',qmm),('d ratio',rrd),('e ratio',rre),('f ratio',rrf),('p',p),('b',b),('R',R),('S',S),('u',u),('e',e),('eta',eta),('T',T),('G',G),('q',q),('q2',q2),('gamma',gamma),('E',E),('Ebox',Ebox),('Eroot',Eroot),('target exponent',3-delta)]:print(name,Interval.cast(z).midpoint_display())
for label,z in [('row exponent above one',ar-1),('column exponent above row exponent',k-ar),('row chunk exponent positive',ar),('k>1',k-1),('alpha positive',alpha),('beta positive',beta),('c>5',c-5),('theta>0',theta),('theta<1/2',F(1,2)-theta),('rho>0',rho),('rho<1/2',F(1,2)-rho),('positive cachez',cachez),('suffix fit',(c-1)*entropy((source_rho-2*theta)/(c-1))/ln4-cachez),('2theta<1/2',F(1,2)-2*theta),('positive box gain',G),('frozen primes',S),('cyclic primes',R-S-1),('block fit',1-b),('source budget above half',source_rho-F(1,2)),('channel fit',source_rho-2*theta)]:above(label,z,0)
assert F(101,100)**200 > 4*F(20201,20200)**10000
print('PASS exact rational small-bias potential inequality')
above('bookkeeping',b-eta,delta)
for phase,x,z in [('I initial',F(0),F(0)),('I freeze',u,F(0)),('II initial',u,F(0)),('II final',u,zmax)]:
 ep=b+x
 phaseez=ep*cachez
 above(phase+' strict batch fit',1-b+z-k*phaseez,0)
 for label,value in [('boxes',b-x-z+ep*G-eta),('residual',b-z-ep*Q-beta*phaseez-eta),('stored',b-ep*q2-eta),('cache',1+b-x/2-z-ep*(T+Q)+A*phaseez-eta),('box encoder',1+b-x/2-z-ep*Ebox-eta),('source root',1+b-x/2-z-ep*Eroot-eta),('formation',1-F(3,2)*x-z-eta)]:above(phase+' '+label,value,delta)
 above(phase+' geometry',1+x/2-ep*T,0)
assert u+zmax==b and R*eta==b
print('PASS:',v.checked,'strict rational inequalities; conditional on small-bias masked translations, joint-cap box encoder, asymmetric-row constant-z cropped oracle and flat CW theorem premises.')
