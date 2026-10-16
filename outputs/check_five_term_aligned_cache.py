#!/usr/bin/env python3
"""Exact shared-baseline cache and queries on arbitrary signed source arrays.

The source embedding and its normalization are separate dependencies. This
checker tests raw arrays of local dimensions 4 and 3, with no homogeneity
assumption. Cartesian enumeration is a finite oracle only; asymptotic capped
languages are generated directly. Standard library only.
"""
from functools import lru_cache
from itertools import combinations, product
from math import comb
from random import Random


# Forms are (input coordinate, coefficient, polynomial degree shift).
PHI = (((0, 1, 0), (2, 1, 0), (3, 1, 0)),
       ((0, 1, 0), (2, 1, 0)),
       ((1, 1, 0), (3, -1, 0)), ((1, 1, 0),),
       ((0, -1, 0), (1, -1, 0), (2, 1, 1)), ((3, 1, 0),))
PSI = (((0, 1, 0), (1, 1, 0)), ((0, 1, 0), (1, -1, 0)),
       ((0, 1, 0), (1, 1, 0), (2, -1, 0)),
       ((0, 1, 0), (1, -1, 0), (2, 1, 0)),
       ((0, 2, 0),), ((2, 1, 0),))
PRIVATE, CHANNEL, STAR = 4, 5, 6


def normal(pos, L, side):
    return (pos < L) == (side == 'left')


def new_stats():
    return dict.fromkeys(('encoders', 'stored_entries', 'intermediate_entries',
                         'coefficient_cells', 'encoder_layers', 'residual_keys',
                         'residual_coefficient_checks', 'box_states', 'box_leaves',
                         'box_reads', 'queries', 'asymmetric_queries'), 0)


def encode(array, L, m, t, side, stats):
    """Joint-cap compact encoder, polynomials truncated modulo z**t."""
    assert 1 <= t <= 2*m and side in ('left', 'right')
    assert len(array) == 12**L
    table, volumes = {}, [0]*(2*L+1)
    start = [(value,)+(0,)*(t-1) for value in array]

    def visit(values, pos, word, distinguished, channels):
        volumes[pos] += len(values)
        if pos == 2*L:
            table[word] = values[0]
            return
        is_normal = normal(pos, L, side)
        forms, dim = (PHI, 4) if is_normal else (PSI, 3)
        width = len(values)//dim
        choices = list(range(4))
        if distinguished[pos//L] < m:
            choices.append(PRIVATE)
            if channels < t:
                choices.append(CHANNEL)
        for label in choices:
            child = []
            for j in range(width):
                value = [0]*t
                for index, coefficient, shift in forms[label]:
                    before = values[index*width+j]
                    for degree in range(shift, t):
                        value[degree] += coefficient*before[degree-shift]
                child.append(tuple(value))
            new_distinguished = list(distinguished)
            new_distinguished[pos//L] += label >= PRIVATE
            visit(child, pos+1, word+(label,), new_distinguished,
                  channels+(label == CHANNEL))

    visit(start, 0, (), [0, 0], 0)
    expected = sum(comb(L, j)*comb(L, k)*4**(2*L-j-k)
                   * sum(comb(j+k, h) for h in range(min(t, j+k)+1))
                   for j in range(m+1) for k in range(m+1))
    assert len(table) == expected
    assert all(v <= expected for v in volumes)
    assert sum(volumes) <= (2*L+1)*expected
    stats['encoders'] += 1
    stats['stored_entries'] += len(table)
    stats['intermediate_entries'] += sum(volumes)
    stats['coefficient_cells'] += t*sum(volumes)
    stats['encoder_layers'] += len(volumes)
    return table


def multiply_truncated(left, right, width):
    return tuple(sum(left[a]*right[d-a] for a in range(d+1))
                 for d in range(width))


def residual_coefficients(left, right, fixed, inner, L, m, t, stats):
    """Coefficients <t of the contracted product of (P+z I)."""
    coefficients = [0]*t
    count = 0
    for h in range(t):
        for selected in combinations(inner, h):
            word = list(fixed)
            for pos in inner:
                word[pos] = PRIVATE
            for pos in selected:
                word[pos] = CHANNEL
            word = tuple(word)
            assert word.count(CHANNEL) < t
            assert all(sum(label >= PRIVATE for label in word[half*L:(half+1)*L]) <= m
                       for half in range(2))
            assert word in left and word in right
            value = multiply_truncated(left[word], right[word], t-h)
            for d, coefficient in enumerate(value):
                coefficients[h+d] += coefficient
            count += 1
    assert count == sum(comb(2*m, h) for h in range(t))
    stats['residual_keys'] += count
    return tuple(coefficients)


def valid_box(word, L, m, t):
    special = [x for x in word if x in (PRIVATE, STAR)]
    return (len(special) <= 2*m-t
            and special == sorted(special, reverse=True)
            and all(sum(x in (PRIVATE, STAR) for x in word[h*L:(h+1)*L]) <= m
                    for h in range(2)))


def complete_query(left, right, fixed, inner, L, m, t, stats):
    coefficients = residual_coefficients(left, right, fixed, inner, L, m, t, stats)
    answer = sum((-1)**(t-j-1)*comb(2*m-j-1, t-j-1)*coefficients[j]
                 for j in range(t))

    @lru_cache(None)
    def box(word):
        assert valid_box(word, L, m, t)
        stats['box_states'] += 1
        stars = [pos for pos, label in enumerate(word) if label == STAR]
        if not stars:
            assert word in left and word in right
            stats['box_leaves'] += 1
            # H(0)=Pnormal. A polynomial value itself is not a box base.
            return left[word][0]*right[word][0]
        pos = stars[-1]
        return sum(box(word[:pos]+(label,)+word[pos+1:]) for label in range(5))

    reads = 0
    for marked_tuple in combinations(inner, 2*m-t):
        marked, stars = set(marked_tuple), set()
        for pos in inner:
            if pos not in marked:
                break
            stars.add(pos)
        switched = tuple(pos for pos in inner if pos not in marked)
        for labels in product(range(4), repeat=t):
            word = list(fixed)
            for pos in inner:
                word[pos] = PRIVATE
            for pos in stars:
                word[pos] = STAR
            for pos, label in zip(switched, labels):
                word[pos] = label
            answer += box(tuple(word))
            reads += 1
    assert reads == 4**t*comb(2*m, t)
    stats['box_reads'] += reads
    return answer


def contract(array, forms, dims):
    """Original-array scalar oracle; forms have no polynomial shifts."""
    values = array
    for form, dimension in zip(forms, dims):
        width = len(values)//dimension
        values = [sum(coefficient*values[index*width+j] for index, coefficient in form)
                  for j in range(width)]
    assert len(values) == 1
    return values[0]


def input_scalar(array, fixed, inner, mode, L, side):
    assignment = dict(zip(inner, mode))
    forms, dims = [], []
    for pos, label in enumerate(fixed):
        is_normal = normal(pos, L, side)
        dims.append(4 if is_normal else 3)
        if pos in assignment:
            symbol = assignment[pos]
            if is_normal:
                form = (((0, -1), (1, -1)), ((2, 1),), ((3, 1),))[symbol]
            else:
                form = (((0, 2),), ((0, 2),), ((2, 1),))[symbol]
        else:
            form = tuple((index, coefficient) for index, coefficient, shift
                         in (PHI if is_normal else PSI)[label] if shift == 0)
        forms.append(form)
    return contract(array, forms, dims)


def original_array_oracle(x, y, fixed, inner, L, m, cutoff=None):
    if cutoff is None:
        modes = product((1, 2), repeat=2*m)
        return sum(input_scalar(x, fixed, inner, mode, L, 'left')
                   * input_scalar(y, fixed, inner, mode, L, 'right') for mode in modes)
    coefficients = [0]*cutoff
    for mode in product((0, 1, 2), repeat=2*m):
        degree = sum(symbol != 0 for symbol in mode)
        if degree < cutoff:
            coefficients[degree] += (input_scalar(x, fixed, inner, mode, L, 'left')
                                     * input_scalar(y, fixed, inner, mode, L, 'right'))
    return tuple(coefficients)


def check_local_identity():
    for i, j in product(range(4), range(3)):
        def coefficient(form, index, degree=0):
            return sum(c for k, c, d in form if k == index and d == degree)
        ordinary = sum(coefficient(PHI[label], i)*coefficient(PSI[label], j)
                       for label in range(4))
        private = coefficient(PHI[PRIVATE], i)*coefficient(PSI[PRIVATE], j)
        inner = 2*(i == 2 and j == 0)+(i == 3 and j == 2)
        assert ordinary+private == inner
        baseline_degree0 = coefficient(PHI[PRIVATE], i)*coefficient(PSI[PRIVATE], j)
        baseline_degree1 = (coefficient(PHI[PRIVATE], i, 1)*coefficient(PSI[PRIVATE], j)
                            + coefficient(PHI[CHANNEL], i)*coefficient(PSI[CHANNEL], j))
        assert baseline_degree0 == private and baseline_degree1 == inner


def main():
    check_local_identity()
    rng, stats = Random(2026101703), new_stats()
    for L, m in ((1, 1), (2, 1), (3, 1), (3, 2)):
        x = [rng.randrange(-2, 3) for _ in range(12**L)]
        y = [rng.randrange(-2, 3) for _ in range(12**L)]
        slots = list(combinations(range(L), m))
        pairs = list(product(slots, repeat=2))
        if len(pairs) > 4:
            pairs = [pairs[0], pairs[-1], pairs[1], pairs[-2]]
        for t in range(1, 2*m+1):
            left = encode(x, L, m, t, 'left', stats)
            right = encode(y, L, m, t, 'right', stats)
            for q1, q2 in pairs:
                inner = q1+tuple(L+pos for pos in q2)
                fixed = tuple(PRIVATE if pos in inner else rng.randrange(4) for pos in range(2*L))
                actual_coefficients = residual_coefficients(left, right, fixed, inner, L, m, t, stats)
                expected_coefficients = original_array_oracle(x, y, fixed, inner, L, m, t)
                assert actual_coefficients == expected_coefficients
                stats['residual_coefficient_checks'] += t
                actual = complete_query(left, right, fixed, inner, L, m, t, stats)
                expected = original_array_oracle(x, y, fixed, inner, L, m)
                assert actual == expected, (L, m, t, q1, q2, actual, expected)
                stats['queries'] += 1
                stats['asymmetric_queries'] += q1 != q2
    print('PASS shared-baseline joint cache and arbitrary-original-array queries:', stats)
    print('PASS every residual coefficient, all cache layer volumes, and all high-box base/closure checks.')
    print('Source embedding, its normalization, and numerical exponent certificates are separate obligations.')


if __name__ == '__main__':
    main()
