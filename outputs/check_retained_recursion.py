#!/usr/bin/env python3
"""Independent exact tests for stored equal-copy recursion and full recovery.

The reference contracts the dense target tensor; it does not expand the
recursive rank coefficients. This fixture does not measure Lean bit costs.
"""
from fractions import Fraction as F
from itertools import product
from math import prod


def execute(base, dims, t, k, x, y):
    left, middle, right = base
    i, j, o = dims
    r = len(left)
    g = (r + t - 1) // t
    if k == 0:
        return [a * b for a, b in zip(x, y)], t, 40 * t + 8
    ni, nj, no = i ** (k - 1), j ** (k - 1), o ** (k - 1)
    lx = [[sum(left[s][c*i+a] * x[c*i*ni+a*ni+p]
               for c in range(t) for a in range(i)) for p in range(ni)] for s in range(r)]
    ry = [[sum(middle[s][c*j+b] * y[c*j*nj+b*nj+q]
               for c in range(t) for b in range(j)) for q in range(nj)] for s in range(r)]
    children, work, control = [], 0, 0
    for group in range(g):
        px = [lx[group*t+c][p] if group*t+c < r else 0 for c in range(t) for p in range(ni)]
        py = [ry[group*t+c][q] if group*t+c < r else 0 for c in range(t) for q in range(nj)]
        value, child_work, child_control = execute(base, dims, t, k-1, px, py)
        children.append(value)
        work += child_work
        control += child_control
    out = [sum(right[s][c*o+a] * children[s//t][(s%t)*no+z] for s in range(r))
           for c in range(t) for a in range(o) for z in range(no)]
    work += 2*r*t*(i**k+j**k+o**k)
    control += (r*ni*(20*t*i+36)+r*nj*(20*t*j+36)
                +g*(40*t*(ni+nj)+56)+t*o**k*(20*r+36)+48)
    return out, work, control


def dense(dims, t, k, tensor, x, y):
    i, j, o = dims
    xs, ys, zs = [list(product(range(d), repeat=k)) for d in dims]
    return [sum(prod(tensor(a, b, c) for a, b, c in zip(ix, iy, iz))
                * x[copy*i**k+p] * y[copy*j**k+q]
                for p, ix in enumerate(xs) for q, iy in enumerate(ys))
            for copy in range(t) for iz in zs]


def check(name, base, dims, tensor, depths, seeds):
    count = 0
    den = prod(v.denominator for side in base for row in side for v in row)
    cleared = [[[int(den*v) for v in row] for row in side] for side in base]
    for k in depths:
        for seed in seeds:
            x = [seed+3*p-4 for p in range(2*dims[0]**k)]
            y = [2*seed-2*p+7 for p in range(2*dims[1]**k)]
            expected = dense(dims, 2, k, tensor, x, y)
            out, work, control = execute(base, dims, 2, k, x, y)
            numerator, int_work, int_control = execute(cleared, dims, 2, k, x, y)
            assert out == expected
            assert numerator == [den**(3*k)*v for v in expected]
            assert all(v % den**(3*k) == 0 for v in numerator)
            assert [v // den**(3*k) for v in numerator] == expected
            assert (work, control) == (int_work, int_control)
            count += len(out)
    print(f"PASS: {name}: {count} complete outputs and their common-denominator recovery.")
    return count


def main():
    weights = [F(2), F(-1, 2), F(1, 2), F(-2)]
    dot = (
        [[weights[s] if p == s else F(0) for p in range(4)] if s < 4 else [F(0)]*4 for s in range(5)],
        [[1/weights[s] if p == s else F(0) for p in range(4)] if s < 4 else [F(0)]*4 for s in range(5)],
        [[F(s < 4 and c == s//2) for c in range(2)] for s in range(5)],
    )
    total = check("signed rational dot / incomplete batch", dot, (2, 2, 1),
                  lambda a, b, _: int(a == b), range(4), (0, 3, -65537))
    rect = ([], [], [])
    for s in range(25):
        copy, row, inner, col = s//12, (s % 12)//6, (s % 6)//3, s % 3
        sign = 1 if s % 2 == 0 else -1
        rect[0].append([F(sign if s < 24 and c == copy and a == 2*row+inner else 0)
                        for c in range(2) for a in range(4)])
        rect[1].append([F(sign if s < 24 and c == copy and b == 3*inner+col else 0)
                        for c in range(2) for b in range(6)])
        rect[2].append([F(s < 24 and c == copy and z == 3*row+col)
                        for c in range(2) for z in range(6)])
    total += check("rectangular / multiple outputs", rect, (4, 6, 6),
                   lambda a, b, z: int(a//2 == z//3 and a % 2 == b//3 and b % 3 == z % 3),
                   range(3), (2, -3))
    total += check("empty rank / zero tensor", ([], [], []), (2, 3, 1),
                   lambda *_: 0, range(3), (0,))
    print(f"PASS: {total} independently checked outputs; no APSP exponent claim from finite tests.")


if __name__ == "__main__":
    main()
