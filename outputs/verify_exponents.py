#!/usr/bin/env python3
"""Exact rational interval certificates for exponent-improvement.tex.

No third-party dependencies. Every asserted inequality uses rational bounds,
not floating point. Decimal displays are informational only. This certifies
the numerical inequalities, not the full asymptotic algorithmic proof.
Run: python3 verify_exponents.py
"""
from fractions import Fraction as F
from functools import lru_cache
from decimal import Decimal, localcontext

if not __debug__:
    raise SystemExit("Numerical certification requires assertions; run Python without -O/-OO or PYTHONOPTIMIZE.")


class Interval:
    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = F(lo if hi is None else hi)
        assert self.lo <= self.hi

    @staticmethod
    def cast(x):
        return x if isinstance(x, Interval) else Interval(x)

    def __add__(self, other):
        b = self.cast(other)
        return Interval(self.lo + b.lo, self.hi + b.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        b = self.cast(other)
        vals = [self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi]
        return Interval(min(vals), max(vals))

    __rmul__ = __mul__

    def __truediv__(self, other):
        b = self.cast(other)
        assert b.lo > 0
        return self * Interval(1/b.hi, 1/b.lo)

    def midpoint_display(self):
        x = (self.lo + self.hi) / 2
        with localcontext() as ctx:
            ctx.prec = 30
            return f'{Decimal(x.numerator)/Decimal(x.denominator):.15f}'


def log_unit(x, terms=64):
    """Bounds log(x) for rational 1 <= x <= 2 using atanh series."""
    x = F(x)
    assert 1 <= x <= 2
    z = (x-1)/(x+1)
    z2 = z*z
    power = z
    total = F(0)
    for j in range(terms):
        total += power / (2*j+1)
        power *= z2
    # All omitted terms are positive; denominators only increase.
    remainder = 2*power / ((2*terms+1)*(1-z2))
    return Interval(2*total, 2*total+remainder)


@lru_cache(None)
def log_bounds(x):
    x = F(x)
    assert x > 0
    k = 0
    while x < 1:
        x *= 2
        k -= 1
    while x >= 2:
        x /= 2
        k += 1
    return log_unit(x) + k*log_unit(F(2))


def entropy(x):
    x = F(x)
    assert 0 < x < 1
    return -x*log_bounds(x) - (1-x)*log_bounds(1-x)


def parameters(c, theta):
    c, theta = F(c), F(theta)
    ln4, ln9 = log_bounds(F(4)), log_bounds(F(9))
    G = (c*entropy(1/c)-c*entropy((1-theta)/c)-theta*ln9)/ln4
    q = (entropy(theta)+theta*ln9)/ln4
    T = (c*entropy(1/c)/2+(c-1)*log_bounds(F(3)))/ln4
    E = T if c >= 10 else c*log_bounds(F(10))/ln4-T
    ratio = 9*(1-theta)/(c-1+theta)
    assert ratio < 1 and 0 < theta < F('0.9')
    assert G.lo > 0
    return G, q, E, T


checked = 0


def above(label, value, target):
    global checked
    value = Interval.cast(value)
    target = F(target)
    assert value.lo > target, (label, value.midpoint_display(), str(target))
    checked += 1
    print(f'  PASS {label}: {value.midpoint_display()} > {target}')


def show_case(label, c, theta):
    vals = parameters(c, theta)
    print(f'\n{label}: c={c}, theta={theta}')
    print('  '+', '.join(f'{k}={v.midpoint_display()}' for k,v in zip(('G','q','E','T'), vals)))
    return vals


def certify():
    # Same input regime as the paper's Corollary 26.
    G,q,E,T = show_case('Thin matrix, N >= D^18', '21.775', '.11121')
    above('boxes', G, '.07195')
    above('queries at density D^-1/2', F('.5')-q, '.07195')
    above('encoding', 18-E, '.07195')
    above('query exponent rounded upward', F('.42805')-q, 0)
    above('tile fits', 18-T, 0)

    # c<10 proof extension. This is only for the specified query density.
    G,q,E,T = show_case('Wider regime, D <= N^.129', '9.33', '.135')
    e=F('.129')
    above('boxes', G, '.0001')
    above('queries', F('.5')-q, '.0001')
    above('encoding', 1/e-E, '.0001')
    above('tile fits', 1/e-T, 0)

    # Deterministic unpadded modulus/block reduction, without residue folding.
    G,q,E,T = show_case('Deterministic integer reduction (unfolded)', '21.915', '.116108')
    e,z,delta = F('.0551975'),F('.0020952'),F('.002095')
    a,b=(e+z)/2,(e-z)/2
    above('boxes saving', e*G-z, delta)
    above('queries saving', e*(F('.5')-q)-z/2, delta)
    above('scans saving', z, delta)
    above('encoding saving', 1-z-e*E, delta)
    above('hash selection saving', 3-log_bounds(F(7))/log_bounds(F(2))-3*a, delta)
    above('matrix writing saving', 1-2*a, delta)
    above('successful scans saving', 1-b, delta)
    above('3SUM rounded exponent saving', delta/2, '.001047')

    # Deterministic reduction with the residue classes folded into the outer
    # dimensions: one instance with N = n*ceil(sqrt p) per block, so the band
    # encodings cost n^2 D^(T-1/4) up to the block/modulus exponents.
    G,q,E,T = show_case('Deterministic integer reduction with residue folding', '21.6844', '.1163026')
    e,z,delta = F('.0565835'),F('.0021252'),F('.002125')
    a,b=(e+z)/2,(e-z)/2
    above('boxes saving', e*G-z, delta)
    above('queries saving', e*(F('.5')-q)-z/2, delta)
    above('scans saving', z, delta)
    above('folded encoding saving', 1-e*(T-F('.25'))-3*z/4, delta)
    above('folded tile fits', 1+a/2-e*T, 0)
    above('hash selection saving', 3-log_bounds(F(7))/log_bounds(F(2))-3*a, delta)
    above('folded matrix writing saving', 1-3*a/2, delta)
    above('successful scans saving', 1-b, delta)
    above('3SUM rounded exponent saving', delta/2, '.001062')

    # Polylogarithmically many independent modular filters, without folding.
    G,q,E,T = show_case('Las Vegas integer amplification (unfolded)', '21.2733', '.111731')
    e,delta=F('.056846'),F('.003999')
    above('boxes saving', e*G, delta)
    above('queries saving', e*(F('.5')-q), delta)
    above('encoding saving', 1-e*E, delta)
    above('matrix writing saving', 1-e, delta)
    above('successful scans saving', 1-e/2, delta)
    above('tile fits', 1-e*T, 0)

    above('oracle preprocessing admissibility', 1-e*(E+G), 0)

    # Independent modular filters with residue folding: per prime and block a
    # single instance with N = n*ceil(sqrt p) replaces the p residue instances,
    # so all band encodings cost O~(n^2 D^(E-1/4)).
    G,q,E,T = show_case('Las Vegas integer amplification with residue folding', '21.0477', '.111971')
    e,delta=F('.05828'),F('.004057')
    above('boxes saving', e*G, delta)
    above('queries saving', e*(F('.5')-q), delta)
    above('folded encoding saving', 1-e*(E-F('.25')), delta)
    above('folded matrix writing saving', 1-3*e/4, delta)
    above('successful scans saving', 1-e/2, delta)
    above('folded tile fits', 1-e*(T-F('.25')), 0)
    tau = 3-min(e*G, e*(F('.5')-q), key=lambda v: v.lo)
    print('  unrounded maximal cost exponent tau = '+tau.midpoint_display())
    above('rounded exponent exceeds tau', F('2.995943')-tau, 0)

    # Direct-sum slot batching of the n/h middle-block products into the K
    # subset slots of one tile (encodings B N N_0, tile N >= N_0, packing B >= K)
    # combined with prefix-contracted queries (exponent q_pc = max(q1, q2)).
    c, th, r = F('20.0337'), F('.11371328'), F('.025732677')
    e, delta = F('.06711237'), F('.004465')
    G, q, E, T = show_case('Las Vegas integer APSP with slot batching and prefix queries', c, th)
    ln4, ln6, ln9 = (log_bounds(F(x)) for x in (4, 6, 9))
    A0 = (c-1)*log_bounds(F(3))/ln4
    CK = c*entropy(1/c)/ln4
    suffix = (1-r)*entropy(th/(1-r))
    q1 = (suffix + (th+r)*ln6)/ln4
    q2 = (suffix + th*ln9)/ln4
    print('  r='+str(r)+', A0='+A0.midpoint_display()+', CK='+CK.midpoint_display()
          +', q1='+q1.midpoint_display()+', q2='+q2.midpoint_display())
    above('prefix fraction below threshold complement', 1-th-r, 0)
    above('residual sum increases to its cutoff', F(6,7)-th/(1-r), 0)
    above('boxes saving', e*G, delta)
    above('residual-query saving', e*(F('.5')-q1), delta)
    above('stored-query saving', e*(F('.5')-q2), delta)
    above('batched encoding saving', 1-e*(A0-F('.25')), delta)
    above('matrix writing saving', 1-3*e/4, delta)
    above('successful scans saving', 1-e/2, delta)
    above('outer bands fit N0', 1-e*(A0-F('.25')), 0)
    above('middle-block count exceeds K', 1-e*(CK+F('.5')), 0)
    batched_savings = tuple(map(Interval.cast, (
        e*G, e*(F('.5')-q1), e*(F('.5')-q2),
        1-e*(A0-F('.25')), 1-3*e/4, 1-e/2,
    )))
    # Include encoding, matrix formation, and scans in the displayed maximum,
    # using the interval minimum rather than selecting one midpoint.
    tau_b = 3-Interval(min(v.lo for v in batched_savings),
                       min(v.hi for v in batched_savings))
    print('  unrounded maximal cost exponent tau = '+tau_b.midpoint_display())
    above('rounded exponent exceeds tau', F('2.995535')-tau_b, 0)

    # Deterministic all-edges Exact Triangle (hence min-plus and APSP) by
    # k-stage conditional modular moments applied to each outer pair on folded
    # instances: stage cost P * n^omega h^(k-1) P^k with the source's
    # omega < 2.372, failed scans n^(3-kz) (the per-pair contraction 2 rho_t
    # costs only the constant 2^k). The same inequalities decide Exact Triangle.
    for label, k, c, th, e, z, mu, delta in (
            ('Deterministic all-edges Exact Triangle by per-pair moments, 11 stages', 11, '21.62', '.11216', F('.05671'), F('.00034'), F(1), F('.003739')),
            ('Deterministic zero-weight 5-Clique, split (2,2,1), 8 stages', 8, '23.04', '.11108', F('.053230'), F('.0004529'), F(1,2), F('.00362'))):
        G, q, E, T = show_case(label, c, th)
        a, b = (e+z)/2, (e-z)/2
        above('boxes saving', e*G-z, delta)
        above('queries saving', e*(F('.5')-q)-z/2, delta)
        above('failed scans saving', k*z, delta)
        above('encoding saving', 1-e*(E-F('.25'))-3*z/4, delta)
        if mu + (k-1)*b <= 1:
            above('selection saving, middle below outer', F('.628')*mu-F('.372')*(k-1)*b-(k+1)*a, delta)
        else:
            above('selection saving, middle above outer', F('.628')-(k-1)*b-(k+1)*a, delta)
        above('matrix writing saving', 1-3*e/4-3*z/4, delta)
        above('residue computation saving', 1-a, delta)
        above('middle part holds a block', mu-b, 0)
        above('folded tile fits', 1+a/2-e*T, 0)
        if mu < 1:
            above('graph construction saving', mu, delta)

    # Lopsided 4-Clique (2,1,1): rows n^2 unfolded, columns n p with the full
    # residue on the small side, middle n; clamped rectangular tiles K x 1.
    c, th, d, delta = F('19.8418'), F('.113322'), F('.06896'), F('.004514')
    G, q, E, T = show_case('Las Vegas integer 4-Clique, split (2,1,1), small-side fold', c, th)
    A0 = (c-1)*log_bounds(F(3))/ln4
    CK = c*entropy(1/c)/ln4
    above('boxes saving', d*G, delta)
    above('queries saving', d*(F('.5')-q), delta)
    above('clamped encoding, large side', 1-d*(A0-F('.5')), delta)
    above('geometric encoding term', F(3,2)-d*(E-F('.25')), delta)
    above('matrix writing, large side', 1-d, delta)
    above('successful scans saving', 1-d/2, delta)
    above('small side holds a tile', 1+d/2-d*A0, 0)
    above('clamp regime: side ratio exceeds K', 1-d/2-d*CK, 0)
    above('middle part holds a block', 1-d/2, 0)

    # Hinted uMv with one clamped rectangular product (source Conjecture 5.12).
    for label, c, th, g, denom_clamp, denom_geo, c10 in (
            ('Hinted uMv, c > 10 parameters', '21.775', '.11121', F('.07195'), F('16.54'), F(36), False),
            ('Hinted uMv, c < 10 parameters', '8.29', '.3385', F('.001'), 1/F('.1726'), F('13.8'), True)):
        G, q, E, T = show_case(label, c, th)
        cc = F(c)
        A0 = (cc-1)*log_bounds(F(3))/ln4
        CK = cc*entropy(1/cc)/ln4
        Aclamp = (cc*log_bounds(F(10))/ln4 - CK - A0) if c10 else A0
        above('phase-2 saving exceeds g', G, g)
        above('phase-3 clamped encoding fits', 1-(Aclamp+g)/denom_clamp, 0)
        above('phase-3 geometric encoding fits', 1-2*(E+g)/denom_geo, 0)
        above('small side holds a tile', 1-A0/denom_clamp, 0)
        above('phase-4 query exponent below one', 1-q, 0)

    # Direct integer 3SUM via bucket-pair folding (one thin product per universe
    # prime, N = O(n log n) rows): costs n D^E, n^2 D^-G, n^2 D^(q-1/2), n D,
    # n^2 D^-1/2 bucket selection, so the unfolded parameter set applies.
    G,q,E,T = show_case('Las Vegas integer 3SUM by bucket-pair folding', '21.2733', '.111731')
    e,delta=F('.056846'),F('.003999')
    above('boxes saving', e*G, delta)
    above('queries saving', e*(F('.5')-q), delta)
    above('encoding saving', 1-e*E, delta)
    above('matrix writing saving', 1-e, delta)
    above('bucket selection saving', e/2, delta)
    above('tile fits', 1-e*T, 0)
    print('  3SUM exponent 2 - delta = '+str(2-delta))

    # Deterministic direct 3SUM: modulus prime chosen by exact cyclic convolution
    # counts, sub-buckets of size n^b with z = e - 2b, failed scans n^(2-z).
    G,q,E,T = show_case('Deterministic integer 3SUM by bucket-pair folding', '21.915', '.116108')
    e,z,delta = F('.055255'),F('.0020975'),F('.002097')
    b = (e-z)/2
    above('boxes saving', e*G-z, delta)
    above('queries saving', e*(F('.5')-q)-z/2, delta)
    above('failed scans saving', z, delta)
    above('encoding saving', 1-e*E-z/2, delta)
    above('modulus selection saving', 1-3*e/2-z/2, delta)
    above('bucket prime selection saving', b, delta)
    above('matrix writing saving', 1-e-z/2, delta)
    above('successful scan saving', 1-b, delta)
    above('tile fits', 1+z/2-e*T, 0)
    print('  3SUM exponent 2 - delta = '+str(2-delta))

    # Deterministic conditional modular moments. At each of k fixed stages,
    # choose the next distinct prime by an exact CRT convolution objective.
    # The scans save k*z; the selector costs n^((1)+(k+1/2)*e+z/2).
    G,q,E,T = show_case('Deterministic integer 3SUM by greedy modular moments', '22.4828', '.111021')
    e,z,delta = F('.0538428'),F('.00021113'),F('.003800')
    k = 18
    above('moment boxes saving', e*G-z, delta)
    above('moment queries saving', e*(F('.5')-q)-z/2, delta)
    above('moment scans saving', k*z, delta)
    above('moment encoding saving', 1-e*E-z/2, delta)
    above('moment selector saving', 1-(F(k)+F('.5'))*e-z/2, delta)
    above('moment bucket selection saving', (e-z)/2, delta)
    above('moment matrix construction saving', 1-e-z/2, delta)
    above('moment tile fits', 1+z/2-e*T, 0)
    print('  deterministic 3SUM exponent 2 - delta = '+str(2-delta))

    # Downstream exponents that are exact rational consequences of the bounds above.
    print('\nDownstream rational consequences')
    tau_lv, tau_det = F('2.995943'), 3-F('.0021252')
    above('min-plus convolution, Las Vegas (1+tau)/2 below bound', F('1.997972')-(1+tau_lv)/2, 0)
    above('min-plus convolution, deterministic (1+tau)/2 below bound', F('1.998938')-(1+tau_det)/2, 0)
    eps_det, eps_lv = F('.002097'), F('.003999')
    above('MonoConvolution deterministic 3/2 - eps/(8-2eps) below bound', F('1.49974')-(F(3,2)-eps_det/(8-2*eps_det)), 0)
    above('MonoConvolution Las Vegas 3/2 - eps/(8-2eps) below bound', F('1.4995')-(F(3,2)-eps_lv/(8-2*eps_lv)), 0)
    eps_moments = F('.003800')
    above('MonoConvolution greedy moments 3/2 - eps/(8-2eps) below bound', F('1.499525')-(F(3,2)-eps_moments/(8-2*eps_moments)), 0)

    # Rectangular digit-block min-plus convolution, with outer exponent alpha
    # and middle/digit exponent beta. Las Vegas singleton isolation removes
    # the successful-scan term; the block-size constraint remains necessary.
    G,q,E,T = show_case('Rectangular isolated Las Vegas min-plus convolution', '21.487', '.111507')
    e,beta,delta = F('.057093'),F('.027755'),F('.003943')
    alpha = 1-beta
    above('rectangular boxes saving', alpha*e*G, delta)
    above('rectangular queries saving', alpha*e*(F('.5')-q), delta)
    above('rectangular encoding saving', alpha*(1-e*(E-F('.25'))), delta)
    above('rectangular thin-matrix construction saving', alpha*(1-F('.75')*e), delta)
    above('rectangular tile fits', alpha*(1-e*(T-F('.25'))), 0)
    above('rectangular middle part exceeds block size', beta-alpha*e/2, 0)
    above('rectangular matrix formation saving', 1-beta, delta)
    above('rectangular diagonal extraction saving', beta, delta)
    print('  Las Vegas min-plus convolution exponent 2 - delta = '+str(2-delta))

    # Deterministic prime selection uses exact quasi-linear cyclic convolution
    # per ring multiplication, hence P^2 across all candidate primes.
    G,q,E,T = show_case('Rectangular deterministic min-plus convolution', '23.1026', '.1151488')
    e,z,beta,delta = F('.053132'),F('.00212056'),F('.083712'),F('.001943')
    alpha = 1-beta
    a,b = (e+z)/2,(e-z)/2
    above('rectangular deterministic boxes saving', alpha*(e*G-z), delta)
    above('rectangular deterministic queries saving', alpha*(e*(F('.5')-q)-z/2), delta)
    above('rectangular deterministic failed scans saving', alpha*z, delta)
    above('rectangular deterministic encoding saving', alpha*(1-e*(E-F('.25'))-3*z/4), delta)
    above('rectangular deterministic thin-matrix construction saving', alpha*(1-3*a/2), delta)
    above('rectangular deterministic tile fits', alpha*(1+a/2-e*T), 0)
    above('rectangular deterministic middle part exceeds block size', beta-alpha*b, 0)
    above('rectangular deterministic successful scans saving', beta-alpha*b, delta)
    above('rectangular deterministic prime selection saving', F('.628')*beta-2*alpha*a, delta)
    above('rectangular deterministic matrix formation saving', 1-beta, delta)
    above('rectangular deterministic diagonal extraction saving', beta, delta)
    print('  deterministic min-plus convolution exponent 2 - delta = '+str(2-delta))

    # Lopsided k-Clique split (a, a, m): every certified gap scales by a; the
    # three range conditions below are the only ones that do not.
    print('\nLopsided k-Clique range conditions')
    e,delta = F('.05828'),F('.004057')
    above('Las Vegas successful scans, a <= 30, m >= 1', 1-30*(e/2+delta), 0)
    e,z,delta = F('.0565835'),F('.0021252'),F('.002125')
    above('deterministic prime selection, a <= 6, omega < 2.372', F('.628')-6*(3*(e+z)/2+delta), 0)
    G,q,E,T = parameters('20.276', '.104566')
    e = F('.059612'); u = e*(1+q)/3
    above('real list length below middle part, a <= 35', 1-35*u, 0)

    # For every fixed k>=3, choose a=floor(k/(2+rho)) and m=k-2a.
    # Then m>=rho*a and min(a,m)>=rho*a because 0<rho<1.
    # With isolation, the Las Vegas block h=R^(e/2)/polylog fits even at
    # equality rho=e/2. All data-structure gaps scale by a.
    print('\nAll-fixed-k lopsided clique geometry')
    e,rho,delta = F('.05828'),F('.02914'),F('.004057')
    assert rho == e/2 and 0 < rho < 1
    above('all-k Las Vegas graph formation saving per outer exponent', rho, delta)
    e,z,rho,delta = F('.0565835'),F('.0021252'),F('.09687'),F('.002125')
    assert 0 < rho < 1
    above('all-k deterministic prime selection saving per outer exponent', F('.628')*rho-e-z, delta)
    above('all-k deterministic successful scans saving per outer exponent', rho-(e-z)/2, delta)
    above('all-k deterministic graph formation saving per outer exponent', rho, delta)
    above('all-k deterministic grouping ratio below one', 1-rho, 0)

    # Hinted OMv (source Corollary 40) only needs query exponent q < 1, so the
    # c < 10 encoding branch reaches larger thinness exponents tau.
    for label, c, th, tau, g, qbound in (
            ('Hinted OMv, tau <= 0.14', '8.58', '.335', F('.14'), F('.0097'), F('.991')),
            ('Hinted OMv, tau <= 0.145', '8.29', '.3385', F('.145'), F('.001'), F('.999'))):
        G,q,E,T = show_case(label, c, th)
        above('phase-2 saving exceeds g', G, g)
        above('encoding fits at thinness tau', 1/tau-E, g)
        above('phase-3 query exponent below bound', qbound-q, 0)
        above('phase-3 query exponent below one', 1-q, 0)
        above('tile fits', 1/tau-T, 0)

    # Comparison-count reductions for real inputs; fixed list-size exponent.
    G,q,E,T = show_case('Las Vegas real-input reduction', '20.276', '.104566')
    e,delta = F('.059612'),F('.003680')
    # u is permitted to be a fixed real constant. Its exact expression is
    # bounded by the same rational interval arithmetic as the other exponents.
    u=e*(1+q)/3
    above('boxes saving', e*G, delta)
    above('queries saving', u-e*q, delta)
    above('same-block comparisons saving', e-2*u, delta)
    above('encoding saving', 1-e*E, delta)
    above('source reduction overhead saving', u, delta)
    above('list exponent less than e', e-u, 0)
    above('matrix construction saving', 1-e, delta)
    above('list construction saving', 1-u, delta)

    # Exact rank-prefix counts remove the old same-block comparisons term.
    # The actual inner dimension is d^2 times a fixed polylogarithm, with
    # d=n^(e/2). Strict gaps absorb this padding and all reduction logarithms.
    G,q,E,T = show_case('Las Vegas real-input rank-prefix comparison counts', '21.2733', '.111731')
    e,delta = F('.056846'),F('.003999')
    u = e/2
    above('rank-prefix boxes saving', e*G, delta)
    above('rank-prefix queries saving', u-e*q, delta)
    above('rank-prefix encoding saving', 1-e*E, delta)
    above('rank-prefix source reduction overhead saving', u, delta)
    above('rank-prefix matrix construction saving', 1-e, delta)
    above('rank-prefix list construction saving', 1-u, delta)
    above('rank-prefix tile fits with polylog padding', 1-e*T, 0)
    above('rank-prefix real clique list length, a <= 35', 1-35*u, 0)
    # All fixed k: a=floor(k/(2+rho)), m=k-2a>=a*rho. The comparison
    # list has length d=floor(n^(a*u)), so rho=u also admits equality.
    rho = F('.028423')
    assert rho == u and 0 < rho < 1
    above('all-k real clique graph formation saving per outer exponent', rho, delta)
    above('all-k real clique list construction saving per outer exponent', 1-rho, delta)
    print(f'\nAll {checked} strict inequalities certified with rational intervals.')


if __name__ == '__main__':
    certify()
