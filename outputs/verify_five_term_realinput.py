#!/usr/bin/env python3
"""Exact numerical certificates for two black-box uses of the five-term
fixed-profile data structure (Lemma lem:five-profile): the thin-product
regimes N >= D^18 and N >= D^14 of the source, and the real-input Las Vegas
reductions through certified comparison counts (Lemma lem:prefix-count).

Dependencies: the five-term lemma's exponent functions as certified in
verify_five_term_apsp.py. This verifies inequalities, not the lemmas.
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


# Thin products in the source's regimes: N >= D^bound and |W| <= N^2/sqrt(D).
# Costs N^2 D^-G + |W| D^max(q1,q2) + N D^E_aug + N D^E_box.
for bound, c, theta, r, y, gamma, qtarget in (
        (18, '16.2514', '.05033', '.04997', '.02004', '.0991', '.4009'),
        (14, '12.420851', '.05478', '.0150708', '.01', '.0853', '.4147')):
    print(f'Five-term thin product, N >= D^{bound}, |W| <= N^2/sqrt(D)')
    c, theta, r, y, gamma, qtarget = map(F, (c, theta, r, y, gamma, qtarget))
    T, G, Eaug, Ebox, q1, q2 = five_term(c, theta, r, y)
    for label, x, target in (
            ('box saving exceeds gamma', G, gamma),
            ('residual query saving exceeds gamma', F(1, 2)-q1, gamma),
            ('stored query saving exceeds gamma', F(1, 2)-q2, gamma),
            ('residual query exponent below target', qtarget-q1, 0),
            ('stored query exponent below target', qtarget-q2, 0),
            (f'tile fits N >= D^{bound}', F(bound)-T, 0),
            ('augmented encodings below N^2 D^-gamma', F(bound)-Eaug-gamma, 0),
            ('box encodings below N^2 D^-gamma', F(bound)-Ebox-gamma, 0)):
        above(label, x, target)
    print(f'  certified: preprocessing O(N^2/D^{gamma}), query O(D^{qtarget})')

# Real inputs: certified comparison counts with D = Theta(n^e log^5 n), d = n^(e/2).
# Real 3SUM: n D^E_aug + n D^E_box + n^2 D^-G + n^2 D^(q-1/2) + n D + n^2 D^-1/2 + n d.
# Real min-plus/APSP/Exact Triangle: n^2 D^E + n^3 D^-G + n^3 D^(q-1/2) + n^2 D + n^2 d + n^3/d.
print('Real 3SUM and real min-plus/APSP/Exact Triangle with the five-term data structure')
c, theta, r, y, e, delta = map(F, ('10.7769', '.0567', '.03854', '.02511', '.08183', '.006195'))
print(f'  e: {Interval.cast(e).midpoint_display()}  target saving: {Interval.cast(delta).midpoint_display()}')
T, G, Eaug, Ebox, q1, q2 = five_term(c, theta, r, y)
for label, x, target in (
        ('boxes saving', e*G, delta),
        ('residual queries saving', e*(F(1, 2)-q1), delta),
        ('stored queries saving', e*(F(1, 2)-q2), delta),
        ('augmented encodings saving', 1-e*Eaug, delta),
        ('box encodings saving', 1-e*Ebox, delta),
        ('explicit matrices saving', 1-e, delta),
        ('list formation saving', 1-e/2, delta),
        ('counting-call overhead saving', e/2, delta),
        ('bucket term saving', e/2, delta),
        ('unfolded tile condition', 1-e*T, 0)):
    above(label, x, target)
print('  certified exponents:', Interval(2-delta).midpoint_display(), 'and', Interval(3-delta).midpoint_display())
# MonoConvolution through All-Integers 3SUM at the full deterministic saving
# eps = 0.0068945 (Theorem thm:deterministic-cyclic-3sum): exponent (3-2eps)/(2-eps).
print('MonoConvolution through All-Integers 3SUM at the full deterministic saving')
eps = F('.0068945')
split = (1-eps)/(2-eps)
above('large light classes have polynomially bounded indices', 3*split-1, 0)
mono = (3-2*eps)/(2-eps)
print(f'  exponent (3-2eps)/(2-eps): {Interval.cast(mono).midpoint_display()}')
above('MonoConvolution exponent below target', F('1.498271')-mono, 0)
above('improves the half-saving transfer', (F(3, 2)-eps/(8-2*eps))-mono, 0)
# Lopsided five-term clique split: alpha = floor(k/(2+b)) with the aligned-cache
# block exponent b; the block fits when m = k - 2 alpha >= b alpha, and the
# middle part saves mu = m/alpha >= b > delta. Exponent k - delta alpha.
print('Lopsided five-term clique split, aligned-cache parameters')
b_al, delta_al = F('.04604634600'), F('.00705208')
above('middle-part slack exceeds the saving', b_al-delta_al, 0)
for k in range(3, 13):
    alpha = int(k/(2+b_al)); m = k - 2*alpha
    above(f'k={k}: alpha={alpha} block fits (m - b alpha)', F(m)-b_al*alpha, 0)
    above(f'k={k}: exponent {Interval.cast(k-delta_al*alpha).midpoint_display()} below k', F(k)-(k-delta_al*alpha), 0)
print(f'PASS: {v.checked} strict rational interval inequalities.')
