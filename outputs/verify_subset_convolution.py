#!/usr/bin/env python3
"""Exact inequalities for the rectangular subset-convolution bound.

This certifies numbers, not the accompanying mathematical reduction.
"""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_exponents import F, Interval, parameters, above, log_bounds

G, q, E, T = parameters('21.0477', '.111971')
e, delta = F('.05828'), F('.004057')
lam, kap = F('.916'), F('.034')
A = F('20.0477') * log_bounds(3) / log_bounds(4)
base = F('2.997190')

above('geometric encoding saving', 1 - e*(E-F('.25')), delta)
above('clamped encoding saving', lam - e*(A-F('.25')), delta)
above('boxes saving', e*G, delta)
above('query saving', e*(F('.5')-q), delta)
above('matrix construction saving', lam-F('.75')*e, delta)
above('successful scan saving', kap-e/2, delta)
above('geometric tile fits', 1-e*(T-F('.25')), 0)
above('short side tile fits', lam-e*(A-F('.25')), 0)
above('block fits middle part', kap-e/2, 0)
above('main base below rounded target',
      log_bounds((base-1)/2) + delta*log_bounds(2)/2, 0)
above('outer-boundary base below rounded target',
      log_bounds(base-2) + (delta/lam)*log_bounds(2), 0)
above('middle-boundary base below rounded target',
      log_bounds(base-2) + (delta/kap)*log_bounds(2), 0)
above('new rounded target below simple substitution',
      -delta*log_bounds(2)-log_bounds(base-2), 0)

print('\n13 strict inequalities passed.')
