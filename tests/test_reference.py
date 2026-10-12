import dataclasses
from fractions import Fraction as Q
import itertools
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from reference import Term, load_fixture, numerical_experiment, raw_value, sigma, term_value


class ReferenceTests(unittest.TestCase):
    def setUp(self):
        self.data, self.terms, self.energy, self.static = load_fixture()

    def test_hand_calculated_fixture(self):
        self.assertEqual([term_value(t, self.energy) for t in self.terms], [Q(2, 3), Q(-1), Q(-1)])
        self.assertEqual(sigma(self.terms, self.energy, self.static), Q(-11, 6))

    def test_raw_matches_merged_off_poles(self):
        for coefficient, omega, gap in itertools.product([Q(-4), Q(0), Q(7, 3)], [Q(1), Q(3, 2)], [Q(-3), Q(0), Q(5, 2)]):
            with self.subTest(coefficient=coefficient, omega=omega, gap=gap):
                self.assertEqual(raw_value(coefficient, gap, omega), term_value(Term(coefficient, omega, Q(0), True), gap))

    def test_removable_pole_is_allowed_only_for_occupied(self):
        self.assertEqual(term_value(Term(Q(4), Q(1), Q(0), True), Q(1)), Q(1))
        with self.assertRaises(ValueError):
            raw_value(Q(4), Q(1), Q(1))
        with self.assertRaises(ValueError):
            term_value(Term(Q(4), Q(1), Q(0), False), Q(1))

    def test_invalid_domain_even_with_zero_coefficient(self):
        for coefficient in [Q(0), Q(4)]:
            for omega in [Q(0), Q(-1)]:
                with self.assertRaises(ValueError):
                    term_value(Term(coefficient, omega, Q(0), True), Q(2))
            for occupied, energy in [(True, Q(-1)), (False, Q(1))]:
                with self.assertRaises(ValueError):
                    term_value(Term(coefficient, Q(1), Q(0), occupied), energy)

    def test_empty_order_multiplicity_and_energy_shift(self):
        self.assertEqual(sigma([], self.energy, self.static), self.static)
        target = Q(-11, 6)
        for permutation in itertools.permutations(self.terms):
            self.assertEqual(sigma(permutation, self.energy, self.static), target)
        self.assertEqual(sigma(self.terms + self.terms, self.energy, self.static), Q(-19, 6))
        shifted = [dataclasses.replace(t, epsilon=t.epsilon + 7) for t in self.terms]
        self.assertEqual(sigma(shifted, self.energy + 7, self.static), target)

    def test_fixture_detects_four_mutants(self):
        a, b, c = self.terms
        mutants = {
            "wrong_occupancy": [dataclasses.replace(a, occupied=False), b, c],
            "missing_coefficient": [dataclasses.replace(a, coefficient=Q(1)), b, c],
            "wrong_sign": [dataclasses.replace(a, coefficient=-a.coefficient), b, c],
            "dropped_term": [a, b],
        }
        for name, terms in mutants.items():
            with self.subTest(mutant=name):
                self.assertNotEqual(sigma(terms, self.energy, self.static), Q(-11, 6))

    def test_float_comparison_uses_identical_input(self):
        rows = numerical_experiment()
        for row in rows:
            exact = Q(4) / (2 * (Q.from_float(float.fromhex(row["x_hex"])) + 1))
            self.assertEqual(Q(row["exact_for_binary64_input"]), exact)
        self.assertIsNone(rows[-1]["raw"])
        self.assertTrue(any(r["raw_abs_error"] is not None and r["raw_abs_error"] > 0.1 for r in rows))


if __name__ == "__main__":
    unittest.main()
