#!/usr/bin/env python3
"""Exact rational certificate for an explicit directed APSP exponent through
Zwick's deterministic reduction (source Theorem 33) and the lopsided
composite-incidence product (cor:aligned-cache-apsp read as in
cor:lopsided-five-clique).

Inputs taken from other certificates / external tables:
  delta = 0.00705208  saving of the aligned-cache oracle below R^2 H for
                      outer parts R = n and middle part H = n^rho, b <= rho
                      (verify_five_term_aligned_apsp.py, 47 inequalities);
  b     = 0.04604634600  block exponent of that certificate;
  mu    = 0.5275      omega(1,mu,1) <= 1+2mu  [ADV+25 Table 1: 2.054999; quoted
                      by the source as mu < 0.5275];
  omega = 2.372       source's square bound (ADV+25: 2.371339).
This certifies the inequalities of the convexity step only; the lopsided
reading of the oracle and Zwick's reduction are proved in the TeX.
"""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_exponents as v
from verify_exponents import F, Interval, above

delta, b = F('.00705208'), F('.04604634600')
mu, omega = F('.5275'), F('2.372')
eps_mm, gamma = F(1, 10**8), F(1, 10**8)   # MM exponent allowance; Zwick level ratio n^gamma


def crossover(slope_w, kappa1, target, label):
    """Fast-MM stage cost g(rho) = 1 - rho + w(rho) + eps_mm + gamma with w the chord of
    slope slope_w from (mu, 1+2mu); lopsided oracle cost 2 + rho - delta.  Returns eps''."""
    c = 1 - slope_w                       # decrease rate of g per unit rho above mu
    above(f'{label}: chord slope below one (g nonincreasing)', c, 0)
    rho_star = mu + (delta + gamma + eps_mm) / (1 + c)
    eps2 = (delta * c - gamma - eps_mm) / (1 + c)
    # identities: both regimes meet at rho_star
    assert 2 + rho_star - delta == 2 + mu - c * (rho_star - mu) + gamma + eps_mm
    above(f'{label}: crossover inside the chord segment', kappa1 - rho_star, 0)
    above(f'{label}: block fits in the middle part at the crossover', rho_star - b, 0)
    above(f'{label}: naive regime rho < b below budget', (2 + mu - eps2) - (2 + b), 0)
    above(f'{label}: tables n^(omega+gamma) below budget', (2 + mu - eps2) - (omega + gamma), 0)
    above(f'{label}: bridges n^(2+gamma) below budget', (2 + mu - eps2) - (2 + gamma), 0)
    above(f'{label}: saving eps\'\' exceeds target', eps2, target)
    print(f'  {label}: rho* = {Interval.cast(rho_star).midpoint_display()}, '
          f'eps\'\' = {Interval.cast(eps2).midpoint_display()}, '
          f'exponent 2+mu-target = {Interval.cast(2 + mu - target).midpoint_display()}')
    return rho_star, eps2


print('Certified point (mu, 1+2mu) and square bound')
above('ADV+25 row kappa=0.5275 is below 1+2mu', 1 + 2 * mu - F('2.054999'), 0)
above('omega below 2+mu', 2 + mu - omega, 0)

print('Main result: chord from (mu, 1+2mu) to (1, omega), source numbers only')
slope_main = (omega - 1 - 2 * mu) / (1 - mu)
c_main = (2 + mu - omega) / (1 - mu)
assert 1 - slope_main == c_main
crossover(slope_main, F(1), F('.001746'), 'chord to kappa=1')
closed = delta * (2 + mu - omega) / (3 - omega)
print(f'  closed form delta(2+mu-omega)/(3-omega) = {Interval.cast(closed).midpoint_display()}')

print('Source-style black-box hypothesis (entries <= n^(1-mu) only, saving eps1 = delta at rho = mu)')
eps_pad = delta * (1 - mu) / (3 - delta)        # padding regime rho < mu binds
above('padding-side saving positive', eps_pad, 0)
above('padding side binds below the fast-MM side', closed - eps_pad, 0)
print(f'  eps\'\'_blackbox = min(eps1(1-mu)/(3-eps1), eps1(2+mu-omega)/(3-omega)) = '
      f'{Interval.cast(eps_pad).midpoint_display()}  (exponent {Interval.cast(2+mu-eps_pad).midpoint_display()})')

print('Refinement A: one more ADV+25 row, omega(1,0.6,1) <= 2.092351, then chord to (1, 2.371339)')
w06, w1 = F('2.092351'), F('2.371339')
slope_a = (w06 - 1 - 2 * mu) / (F('.6') - mu)
rho_a, eps_a = crossover(slope_a, F('.6'), F('.0023025'), 'ADV+25 kappa=0.6')
for kappa, w in ((F('.6'), w06), (F(1), w1)):
    above(f'ADV+25 node kappa={kappa}: 1-kappa+w+allowances below budget',
          (2 + mu - eps_a) - (1 - kappa + w + eps_mm + gamma), 0)

print('Refinement B: SODA 2024 row omega(1,0.55,1) <= 2.066134 with the ADV+25 point at mu')
w055 = F('2.066134')
slope_b = (w055 - 1 - 2 * mu) / (F('.55') - mu)
rho_b, eps_b = crossover(slope_b, F('.55'), F('.0023667'), 'SODA 2024 kappa=0.55')
for kappa, w in ((F('.55'), w055), (F('.6'), F('2.092631')), (F(1), F('2.371552'))):
    above(f'SODA 2024 node kappa={kappa}: 1-kappa+w+allowances below budget',
          (2 + mu - eps_b) - (1 - kappa + w + eps_mm + gamma), 0)

print('Comparison with chunking (saving mu*delta at rho = mu, entries polynomial in n^mu)')
eps_chunk = (mu * delta) * (2 + mu - omega) / (3 - omega)
above('uniform lopsided oracle beats chunked square products', closed - eps_chunk, 0)
print(f'  chunked chord saving = {Interval.cast(eps_chunk).midpoint_display()}')
print(f'PASS: {v.checked} strict rational interval inequalities.')

# Run from the scratchpad: python3 -I verify_directed_apsp.py  -> PASS: 31 strict rational interval inequalities.
# Key outputs: chord to kappa=1: rho* = 0.532805919187898, eps'' = 0.001746160812102 (> 873/500000), exponent 2.525754
#              ADV+25 kappa=0.6: rho* = 0.532249484435527, eps'' = 0.002302595564473, exponent 2.5251975
#              SODA 2024 kappa=0.55: rho* = 0.532185296462529, eps'' = 0.002366783537471, exponent 2.5251333
#              black-box form: 0.001113319673134 (exponent 2.526387); chunked chord saving 0.000921107766083