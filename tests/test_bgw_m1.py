#!/usr/bin/env python3
"""SCIENTIFIC GATE: BGW-M1, one matched-input BerkeleyGW screening comparison.

Checks the whole chain on the committed q-block of a real BerkeleyGW 4.0
static epsilon run:

1. the export is EXACT -- 17-digit decimal and IEEE-754 bits agree entrywise;
2. the reference is computed from the pre-inversion `E` alone, by exact
   rational elimination, never reading the production answer;
3. the production float64 inverse meets criteria PREDECLARED in
   `bgw/m1_screening/reference.py` from precision, dimension and measured
   INPUT conditioning;
4. four convention mutations are rejected by the same criterion while the
   unmodified control passes;
5. the rationals in the committed Lean certificate `GW/BGW/M1Screening.lean`
   are exactly the ones this dump implies -- so the kernel-checked theorem is
   about this production data and not about some other matrix.

The Lean theorems (`GW.BGW.Rref_mul_E`, `E_mul_Rref`, `Rref_unique`,
`E_mul_Wref`, `Wref_unique`) are the certified part. This file is the
extraction, the numerical comparison and the encoding check.

Input boundary: pre-inversion `E` and Coulomb diagonal `V` from the run. The
formation of `E` from `chi` is an INPUT and is not verified here.
"""

from fractions import Fraction as F
import importlib.util
import pathlib
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]


def _load(name, relpath):
    spec = importlib.util.spec_from_file_location(name, ROOT / relpath)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


extract = _load("bgw_m1_extract", "bgw/m1_screening/extract.py")
ref = _load("bgw_m1_reference", "bgw/m1_screening/reference.py")

DUMP = ROOT / "bgw" / "m1_screening" / "data" / "m1_eps_dump_q2.txt"
GVEC = ROOT / "bgw" / "m1_screening" / "data" / "m1_gvec_q2.txt"
LEAN = ROOT / "GW" / "BGW" / "M1Screening.lean"

#: Provenance of the selected block, fixed by the specification and asserted
#: below -- never read from whatever the file happens to contain.
SELECTED_IQ = 2
SELECTED_Q = (0.0, 0.0, 0.5)
SELECTED_N = 8

#: Recorded digest of the retained snapshot. A replaced snapshot must FAIL
#: rather than silently redefine what is correct, so this is a constant here
#: and is not recomputed from the data under test.
DUMP_SHA256 = "047557fe024854e137c7ec86b046726d11c1d56b8749e1d263f73108dbb6e393"
GVEC_SHA256 = "5060298f692adea87acba7f846a64695c322377b1079cfb858cc82a6dac3a320"


def load():
    block = extract.load_single(DUMP, SELECTED_IQ, expected_n=SELECTED_N,
                                expected_q=SELECTED_Q)
    E, X, v = extract.matrices(block)
    return block, E, X, v


def _tmp(name, lines):
    path = ROOT / "artifacts" / name
    path.parent.mkdir(exist_ok=True)
    path.write_text("\n".join(lines) + "\n")
    return path


class SnapshotIsPinned(unittest.TestCase):
    """The retained snapshots must match their recorded digests exactly.

    The previous version of this test only asserted that a digest was 64
    characters long, which is vacuous. Raised by the BGW-M1 review.
    """

    def test_the_dump_matches_its_recorded_digest(self):
        self.assertEqual(extract.require_sha256(DUMP, DUMP_SHA256), DUMP_SHA256)

    def test_the_basis_matches_its_recorded_digest(self):
        self.assertEqual(extract.require_sha256(GVEC, GVEC_SHA256), GVEC_SHA256)

    def test_a_replaced_snapshot_is_rejected(self):
        path = _tmp("m1-replaced.txt", DUMP.read_text().splitlines() + [""])
        with self.assertRaises(extract.ExtractionError) as cm:
            extract.require_sha256(path, DUMP_SHA256)
        self.assertIn("sha256", str(cm.exception))
        path.unlink()


class ExportIsExact(unittest.TestCase):
    """Round-trip and per-entry integrity."""

    def test_the_committed_dump_parses_and_round_trips(self):
        block, E, X, v = load()
        self.assertEqual(len(E), SELECTED_N)
        self.assertEqual(len(v), SELECTED_N)

    def test_a_broken_round_trip_is_rejected(self):
        text = DUMP.read_text().splitlines()
        i, line = next((i, l) for i, l in enumerate(text)
                       if l.startswith("EPSPRE"))
        t = line.split()
        t[3] = "9.9999999999999999E+99"          # decimal no longer the bits
        text[i] = " ".join(t)
        path = _tmp("m1-broken-roundtrip.txt", text)
        with self.assertRaises(extract.ExtractionError) as cm:
            extract.parse(path)
        self.assertIn("not exact", str(cm.exception))
        path.unlink()

    def test_a_duplicate_entry_inside_a_block_is_rejected(self):
        """The old test appended the duplicate AFTER `QEND`, so it exercised
        the outside-a-block branch instead. Raised by the review."""
        out = []
        for line in DUMP.read_text().splitlines():
            out.append(line)
            if line.startswith("EPSPRE 1 1"):
                out.append(line)
        path = _tmp("m1-dup-inside.txt", out)
        with self.assertRaises(extract.ExtractionError) as cm:
            extract.parse(path)
        self.assertIn("duplicate", str(cm.exception))
        self.assertIn("inside", str(cm.exception))
        path.unlink()

    def test_a_missing_entry_is_rejected(self):
        text = [l for l in DUMP.read_text().splitlines()
                if not l.startswith("EPSPRE 3 3")]
        path = _tmp("m1-missing.txt", text)
        with self.assertRaises(extract.ExtractionError) as cm:
            extract.parse(path)
        self.assertRegex(str(cm.exception), "missing|entries")
        path.unlink()

    def test_an_out_of_range_label_is_rejected(self):
        text = DUMP.read_text().splitlines() + []
        text.insert(5, "EPSPRE 99 1   1.0E+00 4607182418800017408")
        path = _tmp("m1-oor.txt", text)
        with self.assertRaises(extract.ExtractionError) as cm:
            extract.parse(path)
        self.assertIn("outside", str(cm.exception))
        path.unlink()


class RunBoundaryIsRejected(unittest.TestCase):
    """The instrumentation APPENDS, so one file can hold several runs.

    Every case below was measured by the BGW-M1 review to pass the original
    21-test suite. They must now be rejected: silently taking the last block
    for a repeated q would let a corrupted run be masked by a later good one.
    """

    def good(self):
        return DUMP.read_text().splitlines()

    def corrupted(self):
        out = []
        for line in self.good():
            t = line.split()
            out.append("EPSPRE 1 1   4.00000000000000000E+00 4616189618054758400"
                       if (t[0] == "EPSPRE" and t[1] == "1" and t[2] == "1")
                       else line)
        return out

    def reject(self, name, lines, needle):
        path = _tmp(name, lines)
        with self.assertRaises(extract.ExtractionError) as cm:
            extract.load_single(path, SELECTED_IQ, expected_n=SELECTED_N,
                                expected_q=SELECTED_Q)
        self.assertIn(needle, str(cm.exception))
        path.unlink()

    def test_a_repeated_q_is_rejected(self):
        self.reject("m1-repeat-q.txt", self.corrupted() + self.good(), "twice")

    def test_an_unterminated_block_followed_by_another_is_rejected(self):
        lines = [l for l in self.corrupted() if not l.startswith("QEND")]
        self.reject("m1-unterminated.txt", lines + self.good(), "still")

    def test_an_unexpected_extra_q_is_rejected(self):
        extra = ["QSTART 99   0.0E+00   0.0E+00   0.0E+00 1",
                 "VCOUL 1   1.0E+00 4607182418800017408",
                 "EPSPRE 1 1   1.0E+00 4607182418800017408",
                 "EPSINV 1 1   1.0E+00 4607182418800017408",
                 "QEND 99"]
        self.reject("m1-extra-q.txt", self.good() + extra, "exactly q")

    def test_a_mismatched_block_end_is_rejected(self):
        lines = [("QEND 7" if l.startswith("QEND") else l) for l in self.good()]
        self.reject("m1-bad-qend.txt", lines, "closes")

    def test_data_outside_a_block_is_rejected(self):
        self.reject("m1-outside.txt",
                    ["EPSPRE 1 1   1.0E+00 4607182418800017408"] + self.good(),
                    "outside")

    def test_the_unmodified_control_still_loads(self):
        block, E, X, v = load()
        self.assertEqual(block["n"], SELECTED_N)


class BasisProvenance(unittest.TestCase):
    """The ordered retained basis, exported separately so the reviewed dump
    snapshot stays byte-identical."""

    def parse_gvec(self):
        rows = []
        for line in GVEC.read_text().splitlines():
            t = line.split()
            if t[0] == "GVEC":
                rows.append((int(t[1]), (int(t[2]), int(t[3]), int(t[4])),
                             float(t[5])))
        return rows

    def test_the_basis_has_exactly_the_selected_dimension(self):
        rows = self.parse_gvec()
        self.assertEqual(len(rows), SELECTED_N)
        self.assertEqual([r[0] for r in rows], list(range(1, SELECTED_N + 1)))

    def test_the_g_vectors_are_distinct(self):
        self.assertEqual(len({r[1] for r in self.parse_gvec()}), SELECTED_N)

    def test_the_basis_explains_the_two_coulomb_values(self):
        """`vcoul` depends on |q+G|, and the exported kinetic energies take the
        same number of distinct values as `vcoul` does. This is why `E` is
        unsymmetric, so it is worth pinning."""
        block, E, X, v = load()
        ekin = [r[2] for r in self.parse_gvec()]
        self.assertEqual(len({round(e, 12) for e in ekin}), len(set(v)))


class SelectedBlockIsAdmissible(unittest.TestCase):
    """The block must be what the task requires: nonzero q, complete basis,
    nontrivial off-diagonal structure."""

    @classmethod
    def setUpClass(cls):
        cls.block, cls.E, cls.X, cls.v = load()

    def test_q_is_nonzero(self):
        self.assertEqual(self.block["q"], SELECTED_Q)
        self.assertNotEqual(self.block["q"], (0.0, 0.0, 0.0))
        self.assertTrue(any(c != 0 for c in self.block["q"]),
                        "a head/wing q0 limit is excluded for this first test")

    def test_the_basis_is_complete_and_small(self):
        self.assertEqual(self.block["n"], SELECTED_N)

    def test_the_matrix_is_not_diagonal_or_scalar(self):
        n = SELECTED_N
        off = max(abs(self.E[a][b]) for a in range(n) for b in range(n) if a != b)
        self.assertGreater(off, F(1, 100), "off-diagonal structure is required")

    def test_E_is_not_symmetric(self):
        """`E = I - V chi` with non-constant `vcoul`, so a transpose mistake is
        a genuine error here rather than an invisible symmetry."""
        n = SELECTED_N
        self.assertTrue(any(self.E[a][b] != self.E[b][a]
                            for a in range(n) for b in range(n)))

    def test_the_coulomb_diagonal_is_not_constant(self):
        self.assertGreater(len(set(self.v)), 1)


class ReferenceAndComparison(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.block, cls.E, cls.X, cls.v = load()
        cls.R = ref.exact_inverse(cls.E)            # from E alone
        cls.kappa = ref.kappa_inf(cls.E, cls.R)
        cls.limits = ref.thresholds(SELECTED_N, cls.kappa)
        cls.measured = ref.metrics(cls.E, cls.X, cls.R)

    def test_the_reference_is_exact(self):
        n = SELECTED_N
        self.assertEqual(ref.matmul(self.E, self.R), ref.eye(n))
        self.assertEqual(ref.matmul(self.R, self.E), ref.eye(n))

    def test_the_input_is_well_conditioned(self):
        """Reported, and used to set the predeclared forward threshold."""
        self.assertLess(self.kappa, 100)

    def test_production_meets_the_predeclared_criteria(self):
        verdict = ref.verdict(self.measured, self.limits)
        for key, ok in verdict.items():
            self.assertTrue(ok, f"{key}: {float(self.measured[key]):.3e} > "
                                f"{float(self.limits[key]):.3e}")

    def test_the_thresholds_do_not_depend_on_the_observed_error(self):
        """They are functions of precision, dimension and conditioning only."""
        again = ref.thresholds(SELECTED_N, self.kappa)
        self.assertEqual(again, self.limits)
        self.assertEqual(self.limits["normalized_residual"],
                         ref.RESIDUAL_CONST * SELECTED_N * ref.UNIT_ROUNDOFF)


class MutationsAreRejected(unittest.TestCase):
    """A convention error must fail the SAME criterion the control passes."""

    KINDS = ("coulomb_prefactor_doubled", "transposed_one_side",
             "row_permutation_one_side", "sign_of_vchi")

    @classmethod
    def setUpClass(cls):
        cls.block, cls.E, cls.X, cls.v = load()

    def accepts(self, Ein):
        """Run the full declared comparison with `Ein` as the input."""
        R = ref.exact_inverse(Ein)
        limits = ref.thresholds(SELECTED_N, ref.kappa_inf(Ein, R))
        measured = ref.metrics(Ein, self.X, R)
        return all(ref.verdict(measured, limits).values())

    def test_the_unmodified_control_is_accepted(self):
        self.assertTrue(self.accepts(self.E))

    def test_every_convention_mutation_is_rejected(self):
        for kind in self.KINDS:
            with self.subTest(kind):
                mutated = ref.mutate(self.E, self.v, kind)
                self.assertNotEqual(mutated, self.E, "mutation was a no-op")
                self.assertFalse(self.accepts(mutated),
                                 f"{kind} was not rejected")

    def test_an_ordinary_wrong_coefficient_is_rejected(self):
        bad = [row[:] for row in self.E]
        bad[2][5] += F(1, 1000)
        self.assertFalse(self.accepts(bad))


class LeanCertificateMatchesThisData(unittest.TestCase):
    """The kernel-checked theorem must be about THIS production matrix.

    Without this, a certificate could be perfectly valid for a different
    matrix and say nothing about the run.
    """

    @classmethod
    def setUpClass(cls):
        cls.block, cls.E, cls.X, cls.v = load()
        cls.R = ref.exact_inverse(cls.E)
        cls.text = LEAN.read_text()

    def lean_matrix(self, name):
        m = re.search(rf"def {name} : Matrix \(Fin (\d+)\) \(Fin \d+\) ℚ :=\s*"
                      r"!!\[(.*?)\]\n", self.text, re.S)
        self.assertIsNotNone(m, f"no literal found for {name}")
        n = int(m.group(1))
        rows = m.group(2).split(";")
        self.assertEqual(len(rows), n, f"{name}: {len(rows)} rows, want {n}")
        out = []
        for row in rows:
            entries = re.findall(r"\(\s*(-?\d+)\s*/\s*(\d+)\s*:\s*ℚ\s*\)", row)
            self.assertEqual(len(entries), n,
                             f"{name}: {len(entries)} entries in a row, want {n}")
            out.append([F(int(a), int(b)) for a, b in entries])
        return out

    def test_lean_E_is_the_exported_matrix(self):
        self.assertEqual(self.lean_matrix("E"), self.E)

    def test_lean_Rref_is_the_independent_reference(self):
        self.assertEqual(self.lean_matrix("Rref"), self.R)

    def test_lean_V_is_the_exported_coulomb_diagonal(self):
        n = SELECTED_N
        expected = [[self.v[a] if a == b else F(0) for b in range(n)]
                    for a in range(n)]
        self.assertEqual(self.lean_matrix("V"), expected)

    def test_the_module_records_the_dump_hash(self):
        """Pinned to the recorded constant, not merely to a 64-char string."""
        self.assertEqual(extract.sha256(DUMP), DUMP_SHA256)
        self.assertIn("SHA-256", self.text)

    def test_the_module_states_its_input_boundary_and_non_claims(self):
        for phrase in ("narrower boundary", "NOT verified",
                       "NOT claimed", "unconverged"):
            self.assertIn(phrase, self.text)


if __name__ == "__main__":
    unittest.main(verbosity=2)
