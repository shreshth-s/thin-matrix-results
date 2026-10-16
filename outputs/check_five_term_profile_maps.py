"""Exact finite audit of good maps restricted to a prescribed profile."""

from fractions import Fraction
from itertools import combinations
from math import comb
import unittest


def rank(columns):
    pivots = {}
    for value in columns:
        while value:
            top = value.bit_length() - 1
            if top in pivots:
                value ^= pivots[top]
            else:
                pivots[top] = value
                break
    return len(pivots)


def mu(dimension):
    result = Fraction(1)
    for i in range(1, dimension + 1):
        result *= 1 - Fraction(1, 2**i)
    return result


def expectation(columns, family, dimension):
    total = Fraction(0)
    for chosen in family:
        fixed = [columns[i] for i in chosen if i < len(columns)]
        if rank(fixed) == len(fixed):
            total += mu(dimension - len(fixed))
    return total


def choose_map(length, dimension, family):
    columns = []
    history = [expectation(columns, family, dimension)]
    for _ in range(length):
        candidates = [
            expectation(columns + [column], family, dimension)
            for column in range(2**dimension)
        ]
        best = max(range(2**dimension), key=candidates.__getitem__)
        # The old expectation is exactly the mean of all possible next columns.
        assert sum(candidates, Fraction(0)) / len(candidates) == history[-1]
        columns.append(best)
        history.append(candidates[best])
        assert history[-1] >= history[-2]
    return columns, history


def subset_images(columns):
    images = {0}
    for column in columns:
        images |= {value ^ column for value in tuple(images)}
    return images


class ProfileMaps(unittest.TestCase):
    def test_exact_conditional_expectations_and_bijections(self):
        total_good = 0
        for length, middle, prefix, ell in (
            (4, 2, 2, 1),
            (5, 2, 2, 1),
            (6, 2, 3, 1),
            (6, 3, 3, 1),
            (7, 3, 3, 1),
        ):
            family = [
                q for q in combinations(range(length), middle)
                if sum(i < prefix for i in q) == ell
            ]
            self.assertEqual(len(family), comb(prefix, ell) * comb(length-prefix, middle-ell))
            gamma, gamma_history = choose_map(length, middle, family)
            gamma_good = [q for q in family if rank([gamma[i] for i in q]) == middle]
            self.assertEqual(gamma_history[-1], len(gamma_good))
            self.assertGreaterEqual(len(gamma_good), mu(middle) * len(family))
            complements = [tuple(i for i in range(length) if i not in q) for q in gamma_good]
            delta, delta_history = choose_map(length, length-middle, complements)
            good = [
                q for q in gamma_good
                if rank([delta[i] for i in range(length) if i not in q]) == length-middle
            ]
            self.assertEqual(delta_history[-1], len(good))
            self.assertGreaterEqual(len(good), mu(middle) * mu(length-middle) * len(family))
            for q in good:
                self.assertEqual(len(subset_images([gamma[i] for i in q])), 2**middle)
                self.assertEqual(
                    len(subset_images([delta[i] for i in range(length) if i not in q])),
                    2**(length-middle),
                )
            total_good += len(good)
        self.assertGreater(total_good, 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
