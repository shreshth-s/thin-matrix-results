#!/usr/bin/env python3
"""Exact rational certificates for integer min-plus convolution through the
five-term fixed-profile data structure (Lemma lem:five-profile) in the
rectangular block reduction r = ceil(n/s), s = n^beta, r = Theta(n^alpha),
alpha = 1 - beta, with D = Theta(r^e) rounded to a power of four.

Las Vegas: Lemma lem:isolation with the two five-term encoder families.
Deterministic: composite incidence certification (Lemma
lem:composite-incidence) generalized to outer parts R = C = r + 1 and middle
part H = s, with the five-term data structure as the counting oracle and
Lambda prime factors per composite, eta = b/Lambda, b = e/2.

This certifies inequalities only, not the asymptotic lemmas.
Intended location: outputs/verify_five_term_convolution.py, recorded output
outputs/five-term-convolution-certificate-results.txt, registered in scripts/verify.py.
"""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_exponents as v
from verify_exponents import F, Interval, entropy, log_bounds, above

ln2, ln4 = map(log_bounds, (F(2), F(4)))


def five_term(c, theta, r, y):
    """Exponent functions of Lemma lem:five-profile, with its hypotheses."""
    CK = c*entropy(1/c)/ln4
    T = CK + c - 1
    G = (c*entropy(1/c) - c*entropy((1-theta)/c) - theta*ln4)/ln2
    Jaug = r*(CK - F('1.5'))
    Eaug, Ebox = T - Jaug, T - G
    q1 = r + ((1-r)*log_bounds((1+3*y)*(1+2*y)) - 2*theta*log_bounds(y))/ln4
    q2 = 2*((1-r)*entropy(theta/(1-r)) + theta*ln4)/ln4
    for label, x in [('c', c), ('theta', theta), ('r', r), ('y', y), ('CK', CK), ('T', T),
                     ('G', G), ('E_aug', Eaug), ('E_box', Ebox), ('q1', q1), ('q2', q2)]:
        print(f'  {label}: {Interval.cast(x).midpoint_display()}')
    for label, x, target in (
            ('compact tail regime', c-5, 0), ('positive prefix', r, 0), ('prefix below one', 1-r, 0),
            ('positive switching fraction', theta, 0), ('switching fits suffix', 1-r-theta, 0),
            ('positive rational coefficient point', y, 0), ('coefficient point below one', 1-y, 0),
            ('stored binomial cutoff increasing', F(4, 5)-theta/(1-r), 0),
            ('prefix projection tail geometric', 1-2/(c-1), 0),
            ('ordinary suffix tail geometric', 1-4/(c-1), 0),
            ('box tail geometric', 1-4*(1-theta)/(c-1+theta), 0),
            ('positive box gain', G, 0), ('box gain below one', 1-G, 0),
            ('positive augmented encoding gain', Jaug, 0),
            ('positive residual query exponent', q1, 0),
            ('positive stored query exponent', q2, 0),
            ('geometry slope above one half', T-F(1, 2), 0)):
        above(label, x, target)
    return T, G, Eaug, Ebox, q1, q2


# Common witness for both guarantees.
c, theta, r, y = map(F, ('11.0588596', '.0563850479', '.0383287249', '.0249694743'))
e, beta, delta = map(F, ('.0814836742', '.03914792', '.006073'))
alpha = 1 - beta
b = e/2
Lam = 100000
eta = b/Lam

print('Rectangular min-plus convolution with the five-term data structure')
print(f'  e: {Interval.cast(e).midpoint_display()}  beta: {Interval.cast(beta).midpoint_display()}'
      f'  alpha: {Interval.cast(alpha).midpoint_display()}  target saving: {Interval.cast(delta).midpoint_display()}')
T, G, Eaug, Ebox, q1, q2 = five_term(c, theta, r, y)

# Block reduction geometry shared by both versions: s = ceil(n^beta) products of
# (r+1) x s by s x r matrices; H = s = n^beta >= sqrt(D) polylog = r^(e/2) polylog.
for label, x, target in (
        ('outer exponent positive', alpha, 0),
        ('block exponent positive', beta, 0),
        ('middle part holds a block, beta > alpha e/2', beta-alpha*e/2, 0),
        ('folded tile fits at the final modulus, 1 > e(T-1/4)', 1-e*(T-F(1, 4)), 0),
        ('folded tile fits at the initial modulus, 1 > bT', 1-b*T, 0),
        ('block exponent below one, 1 > b', 1-b, 0)):
    above(label, x, target)

print('Las Vegas (Lemma lem:isolation with two encoder families, isolated witness recovery)')
lv = (
    ('boxes', alpha*e*G),
    ('residual queries', alpha*e*(F(1, 2)-q1)),
    ('stored queries', alpha*e*(F(1, 2)-q2)),
    ('augmented encodings', alpha*(1-e*(Eaug-F(1, 4)))),
    ('ordinary box encodings', alpha*(1-e*(Ebox-F(1, 4)))),
    ('folded matrix formation', alpha*(1-3*e/4)),
    ('convolution matrix formation', 1-beta),
    ('diagonal extraction', beta),
)
for label, x in lv:
    above(f'Las Vegas {label} saving', x, delta)
tau_lv = 2 - Interval(min(Interval.cast(x).lo for _, x in lv), min(Interval.cast(x).hi for _, x in lv))
print('  unrounded maximal Las Vegas cost exponent: ' + tau_lv.midpoint_display())
above('Las Vegas rounded exponent exceeds the maximal cost exponent', F('1.993927')-tau_lv, 0)

print(f'Deterministic (composite incidence certification, Lambda = {Lam} factors, eta = b/Lambda)')
print(f'  eta: {Interval.cast(eta).midpoint_display()}')
det = (
    ('boxes', alpha*(e*G-eta)),
    ('residual queries', alpha*(e*(F(1, 2)-q1)-eta)),
    ('stored queries', alpha*(e*(F(1, 2)-q2)-eta)),
    ('augmented encodings', alpha*(1-e*(Eaug-F(1, 4))-eta)),
    ('ordinary box encodings', alpha*(1-e*(Ebox-F(1, 4))-eta)),
    ('folded matrix formation', alpha*(1-3*e/4-eta)),
    ('incidence bookkeeping', alpha*(b-eta)),
    ('convolution matrix formation', 1-beta),
    ('diagonal extraction', beta),
)
for label, x in det:
    above(f'deterministic {label} saving', x, delta)
tau_det = 2 - Interval(min(Interval.cast(x).lo for _, x in det), min(Interval.cast(x).hi for _, x in det))
print('  unrounded maximal deterministic cost exponent: ' + tau_det.midpoint_display())
above('deterministic rounded exponent exceeds the maximal cost exponent', F('1.993927')-tau_det, 0)
above('improves the square-block consequence 1.996474', F('1.996474')-F('1.993927'), 0)
above('improves the rectangular Las Vegas bound 1.996057', F('1.996057')-F('1.993927'), 0)
print('Certified exponent for both guarantees:', Interval(2-delta).midpoint_display())
print(f'PASS: {v.checked} strict rational interval inequalities.')
