#!/usr/bin/env python3
"""Exact numerical certificate for min-sum subset convolution through square
five-term tiles (Lemma lem:five-rect-tiles: Lemma lem:five-profile tiled over
an R x D by D x C product with min(R,C) >= K N_0) and rectangular isolated
witness recovery (Lemma lem:five-rect-isolation, from Lemma lem:isolation).

Restriction (x,y,z): rows 2^z, middle 2^x, columns 2^y, D = 4^floor(e b/2),
b = min(y/lam, z/lam, x/kap).  Costs in units of 2^(x+y+z) poly(n, beta):
  (2^y+2^z) 2^x D^(E_aug-1/4), (2^y+2^z) 2^x D^(E_box-1/4), 2^(x+y+z) D^-G,
  2^(x+y+z) D^(max(q1,q2)-1/2), (2^y+2^z) 2^x D^(3/4), 2^(x+y)+2^(x+z), 2^(y+z).
Geometry: min(2^y,2^z) D^(1/4) >= D^T polylog (square tile), 2^x >= sqrt D (block).
Three-term weight w = 2^(-delta y/lam) + 2^(-delta z/lam) + 2^(-delta x/kap);
block sums 2 B2^r + B3^r, B2 = 2 + 2^(-delta/lam), B3 = 2 + 2^(-delta/kap).

Dependencies: the five-term exponent functions as certified in
verify_five_term_apsp.py.  This verifies inequalities, not the lemmas.
"""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_exponents as v
from verify_exponents import F, Interval, entropy, log_bounds, above

ln2, ln4 = map(log_bounds, (F(2), F(4)))


def five_term(c, theta, r, y):
    CK = c*entropy(1/c)/ln4
    T = CK + c - 1
    G = (c*entropy(1/c) - c*entropy((1-theta)/c) - theta*ln4)/ln2
    Jaug = r*(CK - F('1.5'))
    Eaug, Ebox = T - Jaug, T - G
    q1 = r + ((1-r)*log_bounds((1+3*y)*(1+2*y)) - 2*theta*log_bounds(y))/ln4
    q2 = 2*((1-r)*entropy(theta/(1-r)) + theta*ln4)/ln4
    for label, x in [('c', c), ('theta', theta), ('r', r), ('y', y), ('T', T), ('G', G),
                     ('E_aug', Eaug), ('E_box', Ebox), ('q1', q1), ('q2', q2)]:
        print(f'  {label}: {Interval.cast(x).midpoint_display()}')
    for label, x, target in (
            ('compact tail regime', c-5, 0), ('positive prefix', r, 0), ('prefix below one', 1-r, 0),
            ('positive switching fraction', theta, 0), ('switching fits suffix', 1-r-theta, 0),
            ('positive rational coefficient point', y, 0), ('coefficient point below one', 1-y, 0),
            ('stored binomial cutoff increasing', F(4, 5)-theta/(1-r), 0),
            ('prefix projection tail geometric', 1-2/(c-1), 0),
            ('ordinary suffix tail geometric', 1-4/(c-1), 0),
            ('box tail geometric', 1-4*(1-theta)/(c-1+theta), 0),
            ('positive box gain', G, 0), ('positive augmented encoding gain', Jaug, 0)):
        above(label, x, target)
    return T, G, Eaug, Ebox, q1, q2


print('Min-sum subset convolution through square five-term tiles and isolated recovery')
c, theta, r, y, e = map(F, ('10.74132662', '.056740653', '.038571087', '.025146880', '.083812911'))
delta, lam, kap = map(F, ('.006324', '1', '.0425'))
base = F('2.995627')
print(f'  e: {e}  delta: {delta}  lambda: {lam}  kappa: {kap}  rounded base target: {base}')
T, G, Eaug, Ebox, q1, q2 = five_term(c, theta, r, y)
for label, x, target in (
        ('boxes saving', e*G, delta),
        ('residual queries saving', e*(F(1, 2)-q1), delta),
        ('stored queries saving', e*(F(1, 2)-q2), delta),
        ('augmented encodings saving on the short side', lam-e*(Eaug-F(1, 4)), delta),
        ('box encodings saving on the short side', lam-e*(Ebox-F(1, 4)), delta),
        ('folded matrix writing saving on the short side', lam-3*e/4, delta),
        ('input formation and residue saving', lam-delta, 0),
        ('output updates saving', kap-delta, 0),
        ('short side holds a square tile', lam-e*(T-F(1, 4)), 0),
        ('middle part holds a block', kap-e/2, 0),
        ('outer rounding exponent below one', 1-delta/lam, 0),
        ('middle rounding exponent below one', 1-delta/kap, 0),
        ('outer-side base below rounded target', log_bounds(base-2)+(delta/lam)*ln2, 0),
        ('middle-side base below rounded target', log_bounds(base-2)+(delta/kap)*ln2, 0),
        ('improves the ten-term rectangular base', log_bounds(F('2.997190')-2)-log_bounds(base-2), 0),
        ('below Stoian Las Vegas base', log_bounds(F('2.9987')-2)-log_bounds(base-2), 0),
        ('below Stoian deterministic base', log_bounds(F('2.9997')-2)-log_bounds(base-2), 0)):
    above(label, x, target)
print('  certified Las Vegas base below', base)
# The rounded witness is strictly below the ratio obtained from these
# three constraint families alone; the other costs are checked above.
g_terms = (G, F(1, 2)-q1, F(1, 2)-q2)
g = Interval(min(term.lo for term in g_terms), min(term.hi for term in g_terms))
den_terms = (T-F(1, 4), Eaug-F(1, 4)+g)
den = Interval(max(term.lo for term in den_terms), max(term.hi for term in den_terms))
above('candidate ratio exceeds rounded certified saving', g/den, delta/lam)
# Comparison only: Stoian's transfer 2 + 2^-delta of the square deterministic
# saving 0.00705208 (Corollary cor:aligned-cache-apsp); its beta-bit extension
# is not certified here.
sq = F('.00705208')
print('Transfer of the square deterministic saving 0.00705208 into base 2 + 2^-delta')
above('transfer base below 2.995124', log_bounds(F('2.995124')-2)+sq*ln2, 0)
above('transfer base above 2.995123', -log_bounds(F('2.995123')-2)-sq*ln2, 0)
above('transfer base below this rectangular base', log_bounds(base-2)+sq*ln2, 0)
print(f'PASS: {v.checked} strict rational interval inequalities.')
# Recorded run: 34 strict rational interval inequalities pass; minimum runtime
# slack above delta is 1.13e-6 (boxes and both query terms), base margin 8.73e-7.
