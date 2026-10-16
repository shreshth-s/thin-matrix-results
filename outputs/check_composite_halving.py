#!/usr/bin/env python3
"""Finite audit of composite-modulus all-edges certification.

This uses brute-force modular counts, not the fast thin-product algorithm.
It verifies the finite combinatorial invariant, including false positives
inside true incidences.  It does not prove prime-density estimates or any
asymptotic runtime.  The finite pool need not contain every interval prime:
its exact cardinality is charged in every contraction inequality below.
"""

from fractions import Fraction
from itertools import combinations
from math import isqrt
from random import Random


POOL = (101, 103, 107, 109, 113, 127, 131, 137)


def divisor_bound(bound, minimum_prime):
    result, power = 0, 1
    while power * minimum_prime <= bound:
        power *= minimum_prime
        result += 1
    return result


def count(values, modulus):
    return sum(value % modulus == 0 for value in values)


def stage(sums, active, marked, pool, factors, ell):
    """Keep active fixed throughout one stage; restart its modulus at one."""
    available = list(pool)
    modulus = 1
    zeros = {x: sums[x].count(0) for x in active}
    for _ in range(factors - 1):
        old_false = sum(count(sums[x], modulus) - zeros[x] for x in active)
        candidate = {
            p: {x: count(sums[x], modulus * p) for x in active}
            for p in available
        }
        pstar = min(available, key=lambda p: sum(candidate[p].values()))
        new_false = sum(candidate[pstar][x] - zeros[x] for x in active)
        assert len(available) * new_false <= ell * old_false
        modulus *= pstar
        available.remove(pstar)

    q = len(available)
    assert q > ell
    base = {x: count(sums[x], modulus) for x in active}
    mu = {
        x: min(count(sums[x], modulus * p) for p in available)
        for x in active
    }
    statuses = {}
    for x in active:
        if mu[x] == 0:
            statuses[x] = "false"
            assert zeros[x] == 0
        elif mu[x] * q > ell * base[x]:
            statuses[x] = "true"
            assert zeros[x] > 0
            marked.add(x[:2])
        else:
            statuses[x] = "uncertified"
            assert ell * (base[x] - zeros[x]) >= q - ell

    survivors = {
        x for x in active
        if statuses[x] == "uncertified" and x[:2] not in marked
    }
    for x in active:
        if zeros[x] and x[:2] not in marked:
            assert x in survivors
    total_false = sum(base[x] - zeros[x] for x in active)
    assert (q - ell) * len(survivors) <= ell * total_false
    return survivors, statuses, modulus


def exact_stage_factor(block_size, pool_size, factors, ell):
    result = Fraction(block_size * ell, pool_size - factors + 1 - ell)
    for j in range(factors - 1):
        result *= Fraction(ell, pool_size - j)
    return result


def solve(sums, bound, block_size, stages=4, pool=POOL, factors=3):
    ell = divisor_bound(bound, min(pool))
    assert exact_stage_factor(block_size, len(pool), factors, ell) <= Fraction(1, 2)
    for values in sums.values():
        assert len(values) <= block_size
        for value in values:
            assert abs(value) <= bound
            if value:
                assert sum(value % p == 0 for p in pool) <= ell
    active, marked, records = set(sums), set(), []
    for _ in range(stages):
        if not active:
            break
        previous = active
        active, statuses, modulus = stage(sums, active, marked, pool, factors, ell)
        assert 2 * len(active) <= len(previous)
        records.append((active.copy(), statuses, modulus))
    for x in active:
        if 0 in sums[x]:
            marked.add(x[:2])
    expected = {x[:2] for x in sums if 0 in sums[x]}
    assert marked == expected
    return records, marked


def check_folding():
    rng = Random(20261015)
    cases = 0
    for modulus in (4, 6, 8, 9, 10, 12, 15, 16, 21, 25, 27, 35):
        width = isqrt(modulus - 1) + 1
        na, nb, middle = 4, 5, 6
        ac = [[rng.randint(-50, 50) for _ in range(middle)] for _ in range(na)]
        bc = [[rng.randint(-50, 50) for _ in range(middle)] for _ in range(nb)]
        # Alternating constant residues and arbitrary residues tests imbalance.
        ab = [[-modulus if a % 2 == 0 else rng.randint(-40, 40)
               for _ in range(nb)] for a in range(na)]
        left = {
            (a, r1): {(c, (ac[a][c] + r1) % modulus) for c in range(middle)}
            for a in range(na) for r1 in range(width)
        }
        right = {
            (b, r2): {(c, (-bc[b][c] - width * r2) % modulus)
                      for c in range(middle)}
            for b in range(nb) for r2 in range(width)
        }
        for a in range(na):
            for b in range(nb):
                residue = ab[a][b] % modulus
                r1, r2 = residue % width, residue // width
                got = len(left[a, r1] & right[b, r2])
                want = sum((ab[a][b] + ac[a][c] + bc[b][c]) % modulus == 0
                           for c in range(middle))
                assert got == want
                cases += 1
    return cases


def check_random_graphs():
    rng = Random(718271)
    for _ in range(240):
        na, nb, nc = rng.randint(1, 4), rng.randint(1, 4), rng.randint(1, 18)
        block_size = rng.randint(1, 6)
        ac = [[rng.randint(-1000, 1000) for _ in range(nc)] for _ in range(na)]
        bc = [[rng.randint(-1000, 1000) for _ in range(nc)] for _ in range(nb)]
        ab = [[rng.randint(-1000, 1000) for _ in range(nb)] for _ in range(na)]
        for a in range(na):
            for b in range(nb):
                if rng.randrange(3) == 0:
                    c = rng.randrange(nc)
                    ab[a][b] = -ac[a][c] - bc[b][c]
        sums = {
            (a, b, k): [ab[a][b] + ac[a][c] + bc[b][c]
                        for c in range(k * block_size, min(nc, (k + 1) * block_size))]
            for a in range(na) for b in range(nb)
            for k in range((nc + block_size - 1) // block_size)
        }
        weight_bound = max(1, *(abs(w) for row in ac + bc + ab for w in row))
        solve(sums, 3 * weight_bound, block_size)
    return 240


def check_true_incidence_restarts():
    # Every candidate is equally frequent in the false values.  The first
    # selected pair leaves five false values plus one zero at its incidence.
    # Its zero is NOT enough to certify the incidence in the first stage.
    prime_pairs = list(combinations(POOL, 2))
    sums = {
        (0, 0, k): [p * q] * 5 + [0 if k == 0 else 1]
        for k, (p, q) in enumerate(prime_pairs)
    }
    records, marked = solve(sums, 3 * max(p * q for p, q in prime_pairs), 6)
    assert len(records) == 2
    assert records[0][2] == POOL[0] * POOL[1]
    assert records[0][0] == {(0, 0, 0)}
    assert records[0][1][0, 0, 0] == "uncertified"
    assert records[1][1][0, 0, 0] == "true"
    assert marked == {(0, 0)}
    return 1


def check_boundary_cases():
    # ell=0, signed zeros, no incidences, no exact solution, and a solution
    # found only by the final exact scan (zero preliminary stages).
    solve({(0, 0, 0): [-7, 0, 7]}, 21, 3)
    solve({}, 3, 1)
    solve({(0, 0, 0): [101 * 103, -101 * 107, 1]}, 50000, 3)
    solve({(0, 0, 0): [-1, 0, 1]}, 3, 3, stages=0)
    solve({(0, 0, 0): [101 * 103], (0, 1, 0): [0]}, 50000, 1, factors=1)
    solve({(0, 0, 0): [0, 101 * 103, -101 * 107]}, 50000, 3, factors=2)
    # At equality the true certificate MUST NOT fire.  Each of six primes
    # has a false witness, while three values each cover exactly two primes.
    six = POOL[:6]
    sums = {(0, 0, 0): [six[i] * six[i + 1] for i in (0, 2, 4)]}
    marked = set()
    survivors, status, _ = stage(sums, set(sums), marked, six, 1, 2)
    assert survivors == set(sums) and status[0, 0, 0] == "uncertified"
    assert not marked
    # Different primes can have different witnesses: their product must
    # filter the SAME witness, not multiply unrelated modular counts.
    p, q = POOL[:2]
    values = [p, q]
    assert count(values, p) == count(values, q) == 1
    assert count(values, p * q) == 0
    return 8


def main():
    checks = {
        "composite folded entries": check_folding(),
        "random all-edges graph instances": check_random_graphs(),
        "uncertified true-incidence restart fixture": check_true_incidence_restarts(),
        "boundary/different-witness fixtures": check_boundary_cases(),
    }
    for label, number in checks.items():
        print(f"PASS {label}: {number}")
    print("Finite checks only: no asymptotic exponent or prime-density certification.")


if __name__ == "__main__":
    main()
