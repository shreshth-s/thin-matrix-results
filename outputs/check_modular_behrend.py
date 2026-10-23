#!/usr/bin/env python3
"""Exact bounded checks of exhaustive buckets, no-wrap embedding and cleanup.
The analytic Behrend bound is kernel-checked in Lean, not tested by floats.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import isqrt

COLORS = ((0, 1, 1), (1, 0, 1), (1, 1, 0), (0, 0, 2), (0, 2, 0), (2, 0, 0))

@lru_cache(None)
def chosen(N):
    best = ()
    for mask in range(1 << N):
        s = tuple(i for i in range(N) if mask >> i & 1)
        if all((a + c) % 2 or (a + c) // 2 not in s for a, c in combinations(s, 2)):
            if len(s) >= len(best):
                best = s
    # Independent descending-size search and a different progression predicate.
    maximum = next(k for k in range(N, -1, -1)
                   if any(not any(a+d in s and a+2*d in s for a in s for d in range(1, N))
                          for s in combinations(range(N), k)))
    assert len(best) == maximum
    return best

def embedding_checks():
    candidates = 0
    for N in range(13):
        s = chosen(N)
        candidates += 1 << N
        print(f"PASS: interval N={N}: {1 << N} candidates, chosen {s}, maximum size {len(s)}.")
    triples = 0
    for M in range(26):
        N = M // 2
        B = chosen(N)
        assert all(x < M for x in B)
        assert len(set(x % M for x in B)) == len(B)
        assert all(a == b for a, b, c in product(B, repeat=3) if (a+c-2*b) % M == 0)
        for a, b, c in product(range(N), repeat=3):
            assert a+c < M and 2*b < M
            assert ((a+c-2*b) % M == 0) == (a+c == 2*b)
            triples += 1
        if M > 2:
            assert Fraction(N, M) >= Fraction(1, 3)
    assert chosen(0) == () and chosen(1) == (0,)
    assert candidates == 8191 and triples == 12168
    print(f"PASS: {candidates} subset candidates; 26 moduli; {triples} exact no-wrap triples.")

def cleanup(reference):
    n = len(reference)
    E = [w for w in product(range(6), repeat=n) if Counter(w) == Counter(reference)]
    coords = {w: tuple(tuple(COLORS[b][a] for b in w) for a in range(3)) for w in E}
    image_sizes = [len({coords[w][a] for w in E}) for a in range(3)]
    D = sum(len(E) // size for size in image_sizes)
    M = next(m for m in range(2*D+1, 4*D+1) if all(m % d for d in range(2, isqrt(m)+1)))
    B = chosen(M // 2)
    pairs = [(u, v) for u in E for v in E if u != v and any(x == y for x, y in zip(coords[u], coords[v]))]
    inv2 = pow(2, -1, M)
    samples = cand = coll = maximum = 0
    for weights in product(range(M), repeat=n):
        dots = {w: tuple(sum(a*b for a, b in zip(weights, c)) for c in coords[w]) for w in E}
        for b, w0 in product(range(M), repeat=2):
            samples += 1
            filtered = set()
            for w, (x, y, z) in dots.items():
                h = ((b+x) % M, (b+w0+y) % M, (b+inv2*(w0+2*sum(weights)-z)) % M)
                if all(x in B for x in h):
                    assert h[0] == h[1] == h[2]
                    filtered.add(w)
            collisions = [(u, v) for u, v in pairs if u in filtered and v in filtered]
            kept = filtered - {u for u, v in collisions}
            cand += len(filtered)
            coll += len(collisions)
            maximum = max(maximum, len(kept))
    assert samples == M**(n+2)
    assert cand == len(E)*len(B)*M**n
    assert coll == len(pairs)*len(B)*M**max(0, n-1)
    assert maximum >= Fraction(min(image_sizes)*len(B), 24*M)
    print(f"PASS: cleanup n={n}, selected M={M}, constructed |B|={len(B)}: "
          f"{samples} samples, totals {cand}/{coll}, best kept {maximum}.")
    return samples

def main():
    embedding_checks()
    total = sum(cleanup(ref) for ref in ((), (0,), (0, 1)))
    assert total == 15033
    print(f"PASS: {total} exact cleanup samples with constructed buckets and selected primes.")
    print("SCOPE: exhaustive reference construction and finite correctness; no analytic float certificate or generation-cost assertion.")

if __name__ == '__main__':
    main()
