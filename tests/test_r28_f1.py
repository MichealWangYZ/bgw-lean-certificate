"""R28-F1: are the screening data (WFN, WFNq) and the self-energy data (WFN_inner, RHO)
of the Si-EPM run images of ONE finite mean-field system (GW/Bridge/Common.lean,
`Compat`)? bgw/r28_f1/check.py, committed result bgw/r28_f1/data/check.json.

Three layers:

* the committed measurement: the cell and G-list agree bitwise, the Hamiltonian is the
  same (a local potential fitted to WFN_inner reproduces WFN's and WFNq's eigenpairs),
  the band counts agree, but the eps k-set (32 points of the shifted grid) and the
  Sigma k-set (8 points of the unshifted grid) are DISJOINT, and RHO is not the density
  of either system (it is the unsymmetrised IBZ sum) -- always run;
* an independent toy oracle for the fit/predict and k-closure helpers (a random local
  potential on a toy fcc basis, own diagonalisation) -- always run;
* a fresh pinned production run re-measured against the committed numbers -- needs the
  pristine BerkeleyGW tree, skipped otherwise.
"""
import json
import pathlib
import sys
import tempfile
import unittest

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "bgw/endpoint"))
sys.path.insert(0, str(ROOT / "bgw/r28_f1"))
import check  # noqa: E402
import run_production as prod  # noqa: E402

DATA = json.loads((ROOT / "bgw/r28_f1/data/check.json").read_text())
HAVE_TREE = all((prod.DEFAULT_TREE / b).is_file() for b in prod.BINARIES)


class Committed(unittest.TestCase):
    def test_cell_and_gvec_identical(self):
        for key, v in DATA["F1_headers_equal_vs_WFN"].items():
            if key in ("kshift", "nbands"):
                continue
            self.assertTrue(all(v.values()), key)
        # the k-grid shift is the difference
        self.assertEqual(DATA["F1_headers_equal_vs_WFN"]["kshift"],
                         {"WFNq": False, "WFN_inner": False})

    def test_kgrids_disjoint(self):
        k = DATA["F2_ksets"]
        self.assertEqual(k["eps_kset_size"], 32)
        self.assertEqual(k["sigma_kset_size"], 8)
        self.assertEqual(k["sigma_k_minus_q_size"], 8)
        self.assertTrue(k["sigma_k_minus_q_in_inner_closure"])
        self.assertEqual(k["eps_and_sigma_common_points"], 0)
        self.assertEqual(k["min_distance_eps_to_sigma_crystal"], 0.25)
        self.assertEqual(k["eps_shift"], [0.5, 0.5, 0.5])
        self.assertEqual(k["sigma_shift"], [0.0, 0.0, 0.0])
        # each side is internally consistent: the eps grid is closed under its q != 0
        self.assertTrue(all(DATA["F2_eps_grid_closed_under_q"].values()))
        # the q0 partners are auxiliary WFNq states, not grid states
        self.assertTrue(DATA["F2_q0_partners"]["k_plus_q0_in_WFNq"])
        self.assertFalse(DATA["F2_q0_partners"]["k_plus_q0_in_WFN_grid"])

    def test_hnp_on_sigma_grid(self):
        """The premise hnp of hyps_unsat_of_unpaired at X and L: no Sigma grid point stores
        the negated ordered sphere list (either ordering check.py records)."""
        h = DATA["hnp"]
        self.assertEqual(len(h["grid"]), 8)
        self.assertTrue(h["hnp_holds_X"])
        self.assertTrue(h["hnp_holds_L"])
        # set level: no grid point stores the negated sphere of X (sigma.inp point 2) or
        # L (point 1) even as a set, so hnp there holds for every sphere ordering
        self.assertIs(h["hnp_holds_any_order_X"], True)
        self.assertIs(h["hnp_holds_any_order_L"], True)
        self.assertEqual(h["sigma_kpoints"][2]["negated_sphere_stored_as_a_set_at"], [])
        self.assertEqual(h["sigma_kpoints"][1]["negated_sphere_stored_as_a_set_at"], [])
        for r in h["sigma_kpoints"]:
            self.assertEqual(r["ordered_negated_sphere_stored_at_spec_Wfn_at"], [])
            self.assertEqual(r["ordered_negated_sphere_stored_at_lex_sorted"], [])
            self.assertTrue(r["sphere_has_nonzero_vector"])

    def test_same_hamiltonian(self):
        h = DATA["F3_hamiltonian"]
        self.assertAlmostEqual(h["fit_on_WFN_inner"]["alpha"], 1.0, places=12)
        self.assertLess(h["fit_on_WFN_inner"]["max_residual_Ry"], 1e-13)
        self.assertLess(h["max_abs_V_inner_minus_V_WFN"], 1e-12)
        for f in ("inner_H_predicts_WFN", "inner_H_predicts_WFNq", "inner_H_predicts_WFN_inner"):
            self.assertLess(h[f]["max_dE_meV"], 1e-5, f)
            self.assertGreater(h[f]["min_subspace_overlap"], 1 - 1e-10, f)

    def test_band_counts(self):
        b = DATA["F4_bands"]
        self.assertEqual(b["epsilon_number_bands"], 18)
        self.assertEqual(b["sigma_number_bands"], 18)
        self.assertEqual(b["nocc_WFN"], [4])
        self.assertEqual(b["nocc_WFN_inner"], [4])

    def test_density_hypothesis_fails(self):
        d = DATA["F5_density"]
        for s in ("sigma_system_8pt", "eps_system_32pt", "ibz_replay_no_star"):
            self.assertAlmostEqual(d[s]["rho0"], 8.0, places=10)
        self.assertGreater(d["sigma_system_8pt"]["max_abs_minus_RHO"], 0.3)
        self.assertGreater(d["eps_system_32pt"]["max_abs_minus_RHO"], 0.3)
        self.assertLess(d["ibz_replay_no_star"]["max_abs_minus_RHO"], 1e-12)
        # the Sigma system's density is cubic, RHO is not
        self.assertAlmostEqual(d["sigma_system_8pt"]["rho(b3)"], d["sigma_system_8pt"]["rho(b1)"],
                               places=12)
        self.assertGreater(abs(d["RHO_first_shell"]["rho(b3)"] - d["RHO_first_shell"]["rho(b1)"]),
                           0.19)
        # BRIDGE-Q0's "symmetrized RHO" IS the Sigma system's density
        self.assertLess(d["star_average_RHO_vs_sigma_system"], 1e-12)

    def test_verdict(self):
        v = DATA["verdict"]
        self.assertTrue(v["cell_and_G_list_identical"])
        self.assertTrue(v["kgrids_disjoint"])
        self.assertEqual(v["shared_states"], 0)
        self.assertFalse(v["compat_holds"])


class ToyOracle(unittest.TestCase):
    """The fit/predict helpers on a toy crystal with a known local potential."""

    def make(self, seed, kpts, ecut=6.0):
        rng = np.random.default_rng(seed)
        B = np.array([[3, -1, -1], [-1, 3, -1], [-1, -1, 3]], float) * 0.4
        r = range(-3, 4)
        allG = np.array([(a, b, c) for a in r for b in r for c in r])
        V = {}
        for g in allG:
            c = check.canon(g)
            if c not in V:
                V[c] = 0.0 if not any(c) else rng.uniform(-0.3, 0.3) * (abs(np.array(c)).max() <= 1)
        w = {"bdot": B, "kpt": np.array(kpts), "kg": [], "coef": [], "nbands": 6}
        E = []
        for k in kpts:
            kG = np.array(k)[None, :] + allG
            T = np.einsum("ia,ab,ib->i", kG, B, kG)
            G = allG[T < ecut]
            T = T[T < ecut]
            H = np.diag(T) + np.array([[V.get(check.canon(a - b), 0.0) for b in G] for a in G])
            ev, U = np.linalg.eigh(H)
            w["kg"].append(G)
            w["coef"].append(U[:, :6].T.copy())
            E.append(ev[:6])
        w["energies"] = np.array([E])
        return w, V

    def test_fit_recovers_potential_and_predicts(self):
        w, V = self.make(1, [(0.1, 0.2, 0.0), (0.0, 0.0, 0.5), (0.3, 0.1, 0.2)])
        alpha, Vf, res = check.fit_hamiltonian(w)
        self.assertAlmostEqual(alpha, 1.0, places=10)
        self.assertLess(res, 1e-10)
        w2, _ = self.make(1, [(0.25, 0.25, 0.25), (0.25, 0.25, 0.75)])
        p = check.predict(w2, alpha, Vf)
        self.assertLess(p["max_dE_Ry"], 1e-9)
        self.assertGreater(p["min_subspace_overlap"], 1 - 1e-9)

    def test_predict_detects_a_different_hamiltonian(self):
        w, _ = self.make(1, [(0.1, 0.2, 0.0), (0.0, 0.0, 0.5), (0.3, 0.1, 0.2)])
        alpha, Vf, _ = check.fit_hamiltonian(w)
        w2, _ = self.make(2, [(0.25, 0.25, 0.25)])
        self.assertGreater(check.predict(w2, alpha, Vf)["max_dE_Ry"], 1e-3)

    def test_closure_counts(self):
        # the 48 O_h ops in fcc reciprocal crystal coordinates: use the run's own ops
        if not (pathlib.Path.home() / "bgw-src/runs/eps/WFN").is_file():
            self.skipTest("run files not available")
        import bgwio
        w = bgwio.read_wfn(pathlib.Path.home() / "bgw-src/runs/eps/WFN")
        self.assertEqual(len(check.closure(w["kpt"], w["mtrx"])), 32)
        g = check.closure(np.array([[0, 0, 0], [0, 0, 0.5], [0, 0.5, 0.5]]), w["mtrx"])
        self.assertEqual(len(g), 8)
        self.assertEqual(set(g) & set(check.closure(w["kpt"], w["mtrx"])), set())


@unittest.skipUnless(HAVE_TREE, "pristine BerkeleyGW tree not available")
class FreshRun(unittest.TestCase):
    def test_fresh_run_reproduces(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = pathlib.Path(tmp) / "run"
            prod.run(out, blas_threads=1)
            got = check.main(["--run", str(out), "--out", str(pathlib.Path(tmp) / "c.json")])
        self.assertEqual(got["verdict"]["shared_states"], 0)
        self.assertFalse(got["verdict"]["compat_holds"])
        self.assertEqual(got["F2_ksets"]["eps_ks"], DATA["F2_ksets"]["eps_ks"])
        self.assertEqual(got["F2_ksets"]["sigma_ks"], DATA["F2_ksets"]["sigma_ks"])
        self.assertLess(got["verdict"]["same_hamiltonian_to_meV"], 1e-5)
        for s in ("sigma_system_8pt", "eps_system_32pt", "ibz_replay_no_star"):
            self.assertAlmostEqual(got["F5_density"][s]["max_abs_minus_RHO"],
                                   DATA["F5_density"][s]["max_abs_minus_RHO"], places=10)


if __name__ == "__main__":
    unittest.main()
