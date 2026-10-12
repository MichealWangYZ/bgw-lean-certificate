"""E0 gate: the pinned production calculation and its observable (docs/ENDPOINT.md).

The fresh-run tests need the pristine BerkeleyGW tree built by
`bgw/toolchain/setup.sh` (with `epm2bgw.x`); without it they skip, and
`scripts/verify.py` reports them as NOT VERIFIED.
"""
import importlib.util
import json
import pathlib
import re
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


obs = _load("endpoint_observable", "bgw/endpoint/observable.py")
prod = _load("endpoint_run_production", "bgw/endpoint/run_production.py")
ARCHIVE = ROOT / "bgw/export/sigma_hp.log"
HAVE_TREE = all((prod.DEFAULT_TREE / b).is_file() for b in prod.BINARIES)
_RUNS = {}


def fresh(threads):
    """One fresh pinned run per thread setting, shared by the tests."""
    if threads not in _RUNS:
        tmp = tempfile.mkdtemp(prefix="e0-")
        prod.run(pathlib.Path(tmp) / "run", blas_threads=threads)
        _RUNS[threads] = (pathlib.Path(tmp) / "run" / "sigma_hp.log").read_text()
    return _RUNS[threads]


def diagonal_block(text):
    """The per-k diagonal tables, verbatim."""
    return re.findall(r"^ +n +Emf .*?\n(?:.+\n)+", text, re.M)


def offdiag_block(text):
    return re.findall(r"^ +n +m +l .*?\n(?:.+\n)+", text, re.M)


class ArchivedObservable(unittest.TestCase):
    def test_values(self):
        o = obs.observables(ARCHIVE.read_text())
        # printed to 1e-9 eV; a difference of two printed values is exact to 1e-9
        self.assertAlmostEqual(o["O1_Delta_XL"], 4.531684638 - 4.516284091, delta=1e-12)
        self.assertTrue(o["C1_CBM_at_L"])
        self.assertEqual(o["O2_cbm_k"], "L")
        self.assertAlmostEqual(o["O2_gap"], 4.516284091 - 0.163877748, delta=1e-12)
        self.assertLess(o["meanfield_Delta_XL"], -0.6)       # mean field says X
        self.assertEqual(o["max_multiplet_spread"], 0.0)     # symmetrised table
        self.assertEqual(o["states"]["c_X"]["bands"], [5, 6])
        self.assertEqual(o["states"]["c_L"]["bands"], [5])
        self.assertEqual(o["states"]["v_Gamma"]["bands"], [2, 3, 4])

    def test_rejects_window_ending_in_edge_multiplet(self):
        text = ARCHIVE.read_text()
        # drop bands 6..8 at the first k-point: the window now ends at band 5,
        # inside the Gamma conduction triplet
        lines = text.splitlines(keepends=True)
        start = next(i for i, l in enumerate(lines) if l.split()[:2] == ["n", "Emf"])
        cut = "".join(lines[:start + 6] + lines[start + 9:])
        with self.assertRaises(ValueError):
            obs.observables(cut)

    def test_multiplet_spread_detected(self):
        text = ARCHIVE.read_text()
        o = obs.observables(text)
        lines = text.splitlines(keepends=True)
        # perturb Eqp1 of band 6 at X only (third k-point block)
        blocks = [i for i, l in enumerate(lines) if l.split()[:2] == ["n", "Emf"]]
        i6 = blocks[2] + 6
        f = lines[i6].split()
        self.assertEqual(f[0], "6")
        lines[i6] = lines[i6].replace(f[9], f"{float(f[9]) + 0.001:.9f}", 1)
        o2 = obs.observables("".join(lines))
        self.assertAlmostEqual(o2["max_multiplet_spread"], 0.001, delta=1e-9)
        self.assertAlmostEqual(o2["O1_Delta_XL"] - o["O1_Delta_XL"], 0.0005, delta=1e-9)


class Ledger(unittest.TestCase):
    def test_schema(self):
        led = json.loads((ROOT / "bgw/endpoint/ledger.json").read_text())
        ids = [it["id"] for it in led["items"]]
        self.assertEqual(len(ids), len(set(ids)))
        for it in led["items"]:
            self.assertIn(it["status"], {"proved", "certified", "measured", "gap", "unexamined"})
            if it["status"] != "unexamined":
                self.assertTrue(it.get("evidence"), it["id"])


@unittest.skipUnless(HAVE_TREE, "pristine BerkeleyGW tree with epm2bgw.x not built")
class FreshRun(unittest.TestCase):
    def test_fresh_run_reproduces_archive(self):
        self.assertEqual(diagonal_block(fresh(None)), diagonal_block(ARCHIVE.read_text()))
        self.assertEqual(len(diagonal_block(fresh(None))), 3)

    def test_basis_change_invariance(self):
        default, single = fresh(None), fresh(1)
        if offdiag_block(default) == offdiag_block(single):
            self.skipTest("thread setting did not change the degenerate basis here; "
                          "invariance not exercised")
        # the control moved (raw off-diagonal elements depend on the basis) ...
        self.assertNotEqual(offdiag_block(default), offdiag_block(single))
        # ... and the symmetrised diagonal table, hence O1, did not
        self.assertEqual(diagonal_block(default), diagonal_block(single))
        self.assertEqual(obs.observables(default)["O1_Delta_XL"],
                         obs.observables(single)["O1_Delta_XL"])


if __name__ == "__main__":
    unittest.main()
