"""Independent unencoded oracle for the five-term prefix contraction.

Imports the sibling finite query checker, then compares its full answer with
direct contractions of the original input arrays. Also checks the complete
two-frontier box family, rather than only boxes reached by sample queries.
This is finite validation, not an asymptotic proof.
"""
from functools import lru_cache
from itertools import combinations, product
from math import prod
import random

import check_five_term as p


def scalar(values, dimensions, forms):
    """Direct original-array linear form; no encoded-leaf recursion."""
    result = 0
    for choices in product(*forms):
        index, coefficient = 0, 1
        for dimension, (entry, weight) in zip(dimensions, choices):
            index = dimension * index + entry
            coefficient *= weight
        result += coefficient * values[index]
    return result


def original_oracle(a, b, L, fixed, inner):
    result = 0
    for word in product(range(2), repeat=len(inner)):
        choice = dict(zip(inner, word))
        fa, fb = [], []
        for pos in range(2 * L):
            if pos in choice:
                normal_left = ((2 + choice[pos], 1),)
                normal_right = ((0 if choice[pos] == 0 else 2, 1),)
            else:
                normal_left, normal_right = p.X[fixed[pos]], p.Y[fixed[pos]]
            fa.append(normal_left if pos < L else normal_right)
            fb.append(normal_right if pos < L else normal_left)
        result += scalar(a, [4] * L + [3] * L, fa) * scalar(b, [3] * L + [4] * L, fb)
    return result


def full_query(left, right, L, m, fixed, inner, ell, threshold):
    q0, q1 = inner[:m], inner[m:]
    prefix = set(q0[:ell] + q1[:ell])
    suffix = tuple(pos for pos in inner if pos not in prefix)

    @lru_cache(None)
    def box(word):
        assert p.valid_box(word, L, m, threshold)
        if p.STAR not in word:
            return left[word] * right[word]
        last = max(i for i, value in enumerate(word) if value == p.STAR)
        return sum(box(word[:last] + (value,) + word[last + 1:]) for value in range(5))

    result, _, _ = p.sparse_residual(left, right, fixed, inner, prefix, L, threshold)
    for chosen in combinations(suffix, len(suffix) - threshold):
        marked, stars = set(chosen), set(prefix)
        for pos in suffix:
            if pos not in marked:
                break
            stars.add(pos)
        nonprivate = tuple(pos for pos in suffix if pos not in marked)
        for labels in product(range(4), repeat=threshold):
            word = list(fixed)
            for pos in stars:
                word[pos] = p.STAR
            for pos, value in zip(nonprivate, labels):
                word[pos] = value
            result += box(tuple(word))
    return result


def main():
    rng = random.Random(761144)
    query_cases = family_cases = closure_edges = 0
    for L, m in [(1, 1), (2, 1), (2, 2), (3, 2), (3, 3)]:
        a = [rng.randrange(-3, 4) for _ in range(12 ** L)]
        b = [rng.randrange(-3, 4) for _ in range(12 ** L)]
        left = p.encode(a, [p.X] * L + [p.Y] * L)
        right = p.encode(b, [p.Y] * L + [p.X] * L)
        for q0 in combinations(range(L), m):
            for q1 in combinations(range(L, 2 * L), m):
                inner = q0 + q1
                fixed = [p.P if pos in inner else rng.randrange(4) for pos in range(2 * L)]
                expected = original_oracle(a, b, L, fixed, inner)
                for ell in range(m):
                    for threshold in range(max(1, 2 * ell), 2 * (m - ell) + 1):
                        stored_left = p.RetainedEncoding(left, L, m, ell)
                        stored_right = p.RetainedEncoding(right, L, m, ell)
                        assert full_query(stored_left, stored_right, L, m, fixed, inner, ell, threshold) == expected
                        query_cases += 1
    for L in range(1, 4):
        for m in range(1, L + 1):
            for threshold in range(1, 2 * m + 1):
                preimages = {}
                for word in product(range(6), repeat=2 * L):
                    if not p.valid_box(word, L, m, threshold):
                        continue
                    leaf = tuple(p.P if x == p.STAR else x for x in word)
                    preimages[leaf] = preimages.get(leaf, 0) + 1
                    # The source box cutoff also enforces the global pruning
                    # budget for every admissible balanced-prefix length.
                    for ell in range(min(m, threshold // 2) + 1):
                        assert sum(v == p.P for v in leaf) <= 2 * (m - ell)
                    # Expanding the highest star of EITHER half preserves validity.
                    for half in [range(L), range(L, 2 * L)]:
                        stars = [j for j in half if word[j] == p.STAR]
                        if stars:
                            last = stars[-1]
                            for value in range(5):
                                child = word[:last] + (value,) + word[last + 1:]
                                assert p.valid_box(child, L, m, threshold)
                                closure_edges += 1
                    family_cases += 1
                assert max(preimages.values()) <= (m + 1) ** 2
                for leaf, count in preimages.items():
                    zero_counts = [sum(x == p.P for x in leaf[:L]), sum(x == p.P for x in leaf[L:])]
                    assert count == prod(z + 1 for z in zero_counts)
    print(f'PASS: {query_cases} full queries versus an original-array oracle; '
          f'{family_cases} complete box-family states; {closure_edges} DP closure edges.')


if __name__ == '__main__':
    main()
