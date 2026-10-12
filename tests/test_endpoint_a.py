"""Approximation layer A (docs/ENDPOINT.md): bounds on the GW approximations.
Needs the pristine BerkeleyGW tree (fresh pinned run); skips otherwise."""
import json
import pathlib
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "bgw/endpoint"))
sys.path.insert(0, str(ROOT / "tests"))
import test_endpoint_e1 as e1  # noqa: E402  (shared fresh run)
import qp_cert  # noqa: E402
import qp_unique  # noqa: E402
from iv import I  # noqa: E402


@unittest.skipUnless(e1.HAVE_TREE, "pristine BerkeleyGW tree with epm2bgw.x not built")
class A1Linearisation(unittest.TestCase):
    def test_full_qp_roots_certified(self):
        """A1 gate: certified roots of the full GPP QP equation for both O1
        states (continuity on the bracket + certified endpoint signs); O1 from
        them differs from the linearised O1 by more than 50 meV and keeps its
        sign. Matches the committed evidence."""
        out = pathlib.Path(tempfile.mkdtemp(prefix="a1-")) / "qp.json"
        qp_cert.main([str(e1.fresh()), "--guess-X", "4.19443", "--guess-L", "4.12556",
                      "--out", str(out)])
        r = json.loads(out.read_text())
        for n in "XL":
            lo, hi = r["roots"][n]["root"]
            self.assertLess(hi - lo, 1e-9)
            self.assertTrue(r["roots"][n]["attempts"][-1].get("certified"))
        o1 = r["O1_full_QP"]
        lin = r["O1_linearised_specA"]
        self.assertGreater(o1[0], 0)
        self.assertGreater(o1[0] - lin[1], 0.050)
        committed = json.loads((ROOT / "bgw/endpoint/data/qp_cert.json").read_text())
        self.assertEqual([round(x, 12) for x in committed["O1_full_QP"]], [round(x, 12) for x in o1])


@unittest.skipUnless(e1.HAVE_TREE, "pristine BerkeleyGW tree with epm2bgw.x not built")
class A1Uniqueness(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        sig = qp_unique.build_sigma(str(e1.fresh()))
        cls.qp = qp_cert.QPEquation(sig, sig.run.kpts[1], [5])     # c_L

    def test_derivative_enclosure_matches_finite_difference(self):
        """kernel_d encloses dSigma/dE: the central difference of the interval
        Sigma lies within 1e-7 of the enclosure (the difference's own error)."""
        for E0 in (4.1254, 3.0, -5.0, 20.0):
            d = qp_unique.dsigma(self.qp, I.exact(E0))
            h = 1e-6
            fd = (self.qp.sigma(I.exact(E0 + h)).mid() - self.qp.sigma(I.exact(E0 - h)).mid()) / (2 * h)
            self.assertLess(float(d.hi - d.lo), 1e-8)
            self.assertLess(abs(float(fd) - float(d.mid())), 1e-7)

    def test_cover_excludes_roots_and_cannot_exclude_the_root(self):
        """The cover succeeds on a root-free window (through the TOL_Zero clamp
        of the lowest band at -2.552 eV) and fails on one containing the root
        (control: the cover is not vacuous)."""
        n, _, _ = qp_unique.cover(self.qp, -100.0, 4.12)
        self.assertGreater(n, 1)
        with self.assertRaises(RuntimeError):
            qp_unique.cover(self.qp, 4.12, 4.13)

    def test_committed_certificates_are_convention_free(self):
        """E1 never evaluates the GPP kernel where the source divides by zero
        (wx = w or wx = -w for some mode), so no IEEE NaN convention enters."""
        c = json.loads((ROOT / "bgw/endpoint/data/cert_o1.json").read_text())
        self.assertEqual(c["branch_stats"]["wdiff_zero_possible"], 0)
        self.assertEqual(c["branch_stats"]["source_undefined_possible"], 0)

    def test_committed_root_enumeration(self):
        """data/qp_unique.json: two roots per state in [-1e4, 1e4] eV; the
        principal one (largest Z) is the qp_cert root, the other a low-weight
        solution near 30 eV."""
        r = json.loads((ROOT / "bgw/endpoint/data/qp_unique.json").read_text())
        self.assertEqual(r["window_eV"], [-1e4, 1e4])
        committed = json.loads((ROOT / "bgw/endpoint/data/qp_cert.json").read_text())
        for n in "XL":
            roots = r[n]["roots"]
            self.assertEqual(len(roots), 2)
            for a, b in zip(roots, roots[1:]):
                self.assertLess(a["bracket"][1], b["bracket"][0])
            for x in roots:
                self.assertTrue(x["fprime"][1] < 0 or x["fprime"][0] > 0)
            main = max(roots, key=lambda x: x["Z"][0])
            lo, hi = committed["roots"][n]["root"]
            self.assertTrue(main["root"][0] <= hi and lo <= main["root"][1])
            self.assertGreater(main["Z"][0], 0.8)
            other = [x for x in roots if x is not main][0]
            self.assertLess(other["Z"][1], 0.05)

if __name__ == "__main__":
    unittest.main()
