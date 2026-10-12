"""E1 gates (docs/ENDPOINT.md section 3): the independent reproducer against a
fresh pinned production run. Needs the pristine tree; skips otherwise."""
import functools
import json
import importlib.util
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "bgw/endpoint"))
import coulomb  # noqa: E402
import observable  # noqa: E402
import run_production as prod  # noqa: E402
import spec  # noqa: E402

HAVE_TREE = all((prod.DEFAULT_TREE / b).is_file() for b in prod.BINARIES)


@functools.lru_cache(maxsize=None)
def fresh():
    d = pathlib.Path(tempfile.mkdtemp(prefix="e1-")) / "run"
    prod.run(d)
    return d


@functools.lru_cache(maxsize=None)
def setup():
    run = spec.Run(fresh())
    mb = coulomb.MiniBZ(run.cr.bdot, run.qgrid, run.cr.celvol)
    return run, mb


@unittest.skipUnless(HAVE_TREE, "pristine BerkeleyGW tree with epm2bgw.x not built")
class E11BareExchange(unittest.TestCase):
    def test_unfolding_little_group(self):
        """Rotated states stay in their multiplet for every little-group op;
        dropping the fractional translations breaks it (control)."""
        run, _ = setup()
        wf = run.wf

        def worst(ops):
            saved, wf.ops = wf.ops, ops
            try:
                w = 0.0
                for ik, k in enumerate(run.wfn["kpt"]):
                    E, c0 = wf.E[ik], run.wfn["coef"][ik]
                    idx = spec.gindex(run.wfn["kg"][ik])
                    for iop, M in enumerate(run.cr.mtrx):
                        d = k - M @ k
                        if not np.allclose(d, np.rint(d)):
                            continue
                        _, G, c = wf.rotate(ik, iop, np.rint(d).astype(int))
                        C = np.zeros(c0.shape, complex)
                        C[:, [idx[tuple(g)] for g in G]] = c
                        ov = np.conj(c0) @ C.T
                        for n in range(run.nbands):     # complete multiplets only
                            deg = np.abs(E - E[n]) < 1e-6
                            w = max(w, abs(1 - np.sum(np.abs(ov[deg, n]) ** 2)))
                return w
            finally:
                wf.ops = saved
        self.assertLess(worst(wf.ops), 1e-8)
        self.assertGreater(worst([(W, 0 * t) for W, t in wf.ops]), 0.5)

    def test_band_window_does_not_cut_multiplets(self):
        run, _ = setup()
        for E in run.wf.E:
            self.assertGreater(abs(E[run.nbands] - E[run.nbands - 1]), 1e-6)

    def test_mc_replica_matches_production_vcoul(self):
        """Our replica of the Monte Carlo estimator reproduces sigma's own
        `write_vcoul` dump (8 significant digits printed)."""
        run, mb = setup()
        d = fresh().parent / "vc"
        d.mkdir(exist_ok=True)
        for f in ("WFN_inner", "RHO", "eps0mat", "epsmat", "VXC", "vxc.dat"):
            if not (d / f).exists():
                (d / f).symlink_to(fresh() / f)
        (d / "sigma.inp").write_text((fresh() / "sigma.inp").read_text() + "write_vcoul\n")
        if not (d / "vcoul").exists():
            with open(d / "sigma.out", "w") as fh:
                subprocess.run([str(prod.DEFAULT_TREE / "Sigma/sigma.real.x")], cwd=d,
                               stdout=fh, stderr=subprocess.STDOUT, check=True)
        rows = [l.split() for l in (d / "vcoul").read_text().splitlines()]
        # one block per (k, q): the dump repeats the q-grid for every k
        self.assertEqual(len(rows), len(run.kpts) *
                         sum(len(run.sphere(q, run.ecutb)[0]) for q in run.qlist))
        worst = 0.0
        for r in rows[::7]:                    # every 7th entry, all q
            qk = np.array([float(x) for x in r[:3]]) + np.array([int(x) for x in r[3:6]])
            v = float(r[6])
            worst = max(worst, abs(mb.production(qk) - v) / v)
        self.assertLess(worst, 1e-7)

    def test_exact_average_is_symmetric(self):
        """The exact cell average is equal on a symmetry star; the MC estimate is not."""
        run, mb = setup()
        star = [np.array(g, float) for g in ([-1, -1, -1], [-1, 0, 0], [0, -1, 0], [0, 0, -1],
                                              [1, 1, 1], [1, 0, 0], [0, 1, 0], [0, 0, 1])]
        ex = [mb.exact(g) for g in star]
        mc = [mb.production(g) for g in star]
        self.assertLess(np.ptp(ex) / np.mean(ex), 1e-8)
        self.assertGreater(np.ptp(mc) / np.mean(mc), 1e-3)

    def test_bare_exchange_matches_production(self):
        """E1.1 gate: X for all 24 states to <= 1e-6 eV (achieved: print precision)."""
        run, mb = setup()
        v = functools.lru_cache(None)(lambda qk: mb.production(np.array(qk)))
        tables = observable.parse((fresh() / "sigma_hp.log").read_text())
        worst = 0.0
        for k in run.kpts:
            X = spec.bare_exchange(run, k, v) * spec.RYD
            for g in observable.multiplets(tables[tuple(k)]):
                idx = [r["n"] - run.bmin for r in g]
                worst = max(worst, abs(X[idx].mean() - g[0]["X"]))
        self.assertLess(worst, 1e-9)




@functools.lru_cache(maxsize=None)
def production_screening():
    run, mb = setup()
    vb = functools.lru_cache(None)(lambda qk: mb.production(np.array(qk)))
    oq = functools.lru_cache(None)(lambda q: mb.oneoverq_production(np.array(q)))
    return vb, oq, spec.Screening(run, vb, oq), spec.bgwio.read_rho(fresh() / "RHO")


@functools.lru_cache(maxsize=None)
def qp_tables():
    run, _ = setup()
    vb, _, scr, rho = production_screening()
    return {tuple(k): spec.quasiparticle(run, k, vb, scr, rho) for k in run.kpts}


@unittest.skipUnless(HAVE_TREE, "pristine BerkeleyGW tree with epm2bgw.x not built")
class E12Correlation(unittest.TestCase):
    def test_irreducible_op_is_last_match(self):
        """irrbz keeps the LAST (iq, op) match; for q = 0 that is op 48 of 48.
        With the first match instead, the q = 0 matrix differs (eps0mat was
        computed at a finite q0 along z and is not cubic-invariant)."""
        run, _ = setup()
        _, _, scr, _ = production_screening()
        Gs, eps, info = scr.at(np.zeros(3))
        self.assertEqual((info["iop"], info["nops"]), (47, 48))
        first = spec.Screening(run, scr.vbar, scr.oneoverq, choose_op="first")
        _, eps1, _ = first.at(np.zeros(3))
        self.assertGreater(np.abs(eps - eps1).max(), 1e-3)

    def test_diagonal_table_matches_production(self):
        """E1.2 gate: X, SX-X, CH, Sig, Eqp0, Eqp1, Z of all 24 states to
        <= 1e-6 eV (achieved: print precision) and O1 reproduced."""
        tables = observable.parse((fresh() / "sigma_hp.log").read_text())
        worst = 0.0
        for k, rows in qp_tables().items():
            prod = {r["n"]: r for r in tables[k]}
            for r in rows:
                p = prod[r["bands"][0]]
                for a, b in [("X", "X"), ("SXX", "SX-X"), ("CH", "CH"), ("CHp", "CH'"),
                             ("Sig", "Sig"), ("Eqp0", "Eqp0"), ("Eqp1", "Eqp1"), ("Z", "Znk")]:
                    worst = max(worst, abs(r[a] - p[b]))
        self.assertLess(worst, 1e-9)
        c = {name: [r for r in qp_tables()[tuple(k)] if 5 in r["bands"]][0]
             for name, k in observable.KPOINTS.items()}
        o1 = c["X"]["Eqp1"] - c["L"]["Eqp1"]
        self.assertAlmostEqual(o1, observable.observables(
            (fresh() / "sigma_hp.log").read_text())["O1_Delta_XL"], delta=2e-9)


@functools.lru_cache(maxsize=None)
def recomputed_blocks():
    run, _ = setup()
    er = spec.EpsilonRun(fresh(), run.nbands, run.ecuts)
    qs = [(run.eps0["q"][0]["q"], True)] + [(b["q"], False) for b in run.eps["q"]]
    return er, [er.epsinv(q, q0) for q, q0 in qs]


@unittest.skipUnless(HAVE_TREE, "pristine BerkeleyGW tree with epm2bgw.x not built")
class E13Epsilon(unittest.TestCase):
    def test_kpoint_closure_is_32(self):
        """Epsilon samples the 48-op closure of the shifted grid (32 points),
        not the nominal 8-point 2x2x2 grid."""
        er, _ = recomputed_blocks()
        self.assertEqual(len(er.kfull), 32)
        self.assertIn("full BZ of WFN: 32", (fresh() / "epsilon.out").read_text())

    def test_epsinv_matches_files(self):
        """E1.3 gate: eps^-1 recomputed from WFN/WFNq equals eps0mat/epsmat."""
        run, _ = setup()
        _, blocks = recomputed_blocks()
        files = [run.eps0["q"][0]] + run.eps["q"]
        for (G, E, _), b in zip(blocks, files):
            Gp = run.eps["gvec"][b["isrtx"][:b["nmtx"]] - 1]
            pos = spec.gindex(Gp)
            self.assertEqual(len(G), b["nmtx"])
            P = b["epsinv"][np.ix_(*(2 * [np.array([pos[tuple(g)] for g in G])]))]
            self.assertLess(np.abs(E - P).max() / np.abs(P).max(), 1e-12)

    def test_o1_from_recomputed_screening(self):
        """O1 from WFN, WFNq, WFN_inner and RHO alone equals production's."""
        run, _ = setup()
        vb, oq, _, rho = production_screening()
        _, blocks = recomputed_blocks()
        scr = spec.Screening(run, vb, oq, blocks=[(G, E.real) for G, E, _ in blocks])
        c = {n: [r for r in spec.quasiparticle(run, k, vb, scr, rho) if 5 in r["bands"]][0]
             for n, k in (("X", run.kpts[2]), ("L", run.kpts[1]))}
        prod = observable.observables((fresh() / "sigma_hp.log").read_text())["O1_Delta_XL"]
        self.assertAlmostEqual(c["X"]["Eqp1"] - c["L"]["Eqp1"], prod, delta=2e-9)


import iv  # noqa: E402
from fractions import Fraction as Fr  # noqa: E402


class IntervalArithmetic(unittest.TestCase):
    """The rules of bgw/endpoint/iv.py against exact rational arithmetic."""

    def operands(self, n=4000, seed=1):
        rng = np.random.default_rng(seed)
        mags = 10.0 ** rng.uniform(-310, 300, n)
        x = rng.choice([-1, 1], n) * mags * rng.uniform(0.5, 1, n)
        x[:20] = [0.0, 5e-324, -5e-324, 1.0, -1.0, 0.1, 1 / 3, 2.0 ** -1074 * 3,
                  1e-12, 1e12, 3.0, 7.0, 1e-300, -1e-300, 2 ** 52 + 1, 0.5, 13.60569253,
                  np.pi, -np.pi, 1e-6]
        return x

    def point(self, a, b):
        return iv.I(np.minimum(a, b), np.maximum(a, b))

    def assert_contains(self, J, exact_vals):
        for lo, hi, e in zip(J.lo.ravel(), J.hi.ravel(), exact_vals):
            self.assertTrue(Fr(lo) <= e <= Fr(hi), (lo, hi, float(e)))

    def test_field_ops(self):
        a, b = self.operands(seed=1), self.operands(seed=2)
        a, b = a[np.abs(a) < 1e150], b[np.abs(b) < 1e150]
        n = min(len(a), len(b))
        a, b = a[:n], b[:n]
        A, B = iv.I(a), iv.I(b)
        self.assert_contains(A + B, [Fr(x) + Fr(y) for x, y in zip(a, b)])
        self.assert_contains(A - B, [Fr(x) - Fr(y) for x, y in zip(a, b)])
        self.assert_contains(A * B, [Fr(x) * Fr(y) for x, y in zip(a, b)])
        nz = np.abs(b) > 1e-150              # keep 1/b finite: iv raises on overflow
        self.assert_contains(A[nz] / B[nz], [Fr(x) / Fr(y) for x, y in zip(a[nz], b[nz])])

    def test_interval_endpoints_all_combinations(self):
        rng = np.random.default_rng(3)
        lo = rng.normal(size=500)
        hi = lo + np.abs(rng.normal(size=500))
        lo2 = rng.normal(size=500)
        hi2 = lo2 + np.abs(rng.normal(size=500))
        A, B = iv.I(lo, hi), iv.I(lo2, hi2)
        P = A * B
        for t in (0, 0.3, 1):
            for s in (0, 0.7, 1):
                xs = [Fr(l) + (Fr(h) - Fr(l)) * Fr(t) for l, h in zip(lo, hi)]
                ys = [Fr(l) + (Fr(h) - Fr(l)) * Fr(s) for l, h in zip(lo2, hi2)]
                self.assert_contains(P, [x * y for x, y in zip(xs, ys)])

    def test_sqrt(self):
        x = np.abs(self.operands(seed=4))
        S = iv.I(x).sqrt()
        for lo, hi, v in zip(S.lo, S.hi, x):
            self.assertTrue(0 <= lo <= hi and Fr(lo) ** 2 <= Fr(v) <= Fr(hi) ** 2)

    def test_sum_and_inverse(self):
        rng = np.random.default_rng(5)
        v = rng.normal(size=(200, 7))
        s = iv.I(v).sum(axis=0)
        exact = [sum(Fr(x) for x in v[:, j]) for j in range(7)]
        self.assert_contains(s, exact)
        A = rng.normal(size=(6, 6)) + 6 * np.eye(6)
        J, beta, delta = iv.inverse(iv.I(A))
        # exact rational inverse by Gauss-Jordan
        n = 6
        M = [[Fr(A[i, j]) for j in range(n)] + [Fr(int(i == j)) for j in range(n)] for i in range(n)]
        for c in range(n):
            p = next(r for r in range(c, n) if M[r][c] != 0)
            M[c], M[p] = M[p], M[c]
            piv = M[c][c]
            M[c] = [x / piv for x in M[c]]
            for r in range(n):
                if r != c and M[r][c] != 0:
                    f = M[r][c]
                    M[r] = [x - f * y for x, y in zip(M[r], M[c])]
        inv = [row[n:] for row in M]
        self.assert_contains(J, [inv[i][j] for i in range(n) for j in range(n)])
        self.assertLess(delta, 1e-13)

    def test_overflow_raises(self):
        with self.assertRaises(FloatingPointError):
            iv.I([1.0]) / iv.I([5e-324])

    def test_select_hulls_undecided(self):
        a, b = iv.I([1.0, 2.0, 3.0]), iv.I([10.0, 20.0, 30.0])
        r = iv.select(np.array([True, False, False]), np.array([False, True, False]), a, b)
        self.assertEqual(list(r.lo), [1.0, 20.0, 3.0])
        self.assertEqual(list(r.hi), [1.0, 20.0, 30.0])


import cert  # noqa: E402

COULOMB_CERT = ROOT / "bgw/endpoint/data/coulomb_cert.json"
PYENV = pathlib.Path.home() / "bgw-src/pyenv-e1/bin/python"


@functools.lru_cache(maxsize=None)
def certified():
    out = pathlib.Path(tempfile.mkdtemp(prefix="e14-")) / "cert.json"
    # cert.STATS is module state shared with every in-process caller (A1's
    # qp_cert.certify_root leaves undecided counts from its rejected brackets).
    # Seed a stale count so this gate checks that cert.main reports its own
    # evaluation only, independent of which tests ran before it.
    cert.STATS["undecided_stale_sentinel"] = 1
    cert.main([str(fresh()), "--coulomb", str(COULOMB_CERT), "--out", str(out)])
    return json.loads(out.read_text())


@unittest.skipUnless(HAVE_TREE, "pristine BerkeleyGW tree with epm2bgw.x not built")
class E14Certified(unittest.TestCase):
    def test_coulomb_certificate_matches_this_run(self):
        """The committed Arb enclosures were made for this run's metric and
        cover every q+G the Sigma sums use; each contains the float estimate."""
        run, mb = setup()
        doc = json.loads(COULOMB_CERT.read_text())
        self.assertEqual(np.array(doc["bdot"]).tolist(), run.cr.bdot.tolist())
        self.assertEqual(doc["n_triangles"], 44)
        cc = cert.CertCoulomb(COULOMB_CERT)
        for q in run.qlist:
            for g in run.sphere(q, run.ecutb)[0][::17]:
                e = cc.vbar(q + g)
                f = mb.exact(q + g)
                self.assertLess(abs(f - e.mid()) / f, 1e-8)   # float quadrature ~4e-9
                self.assertLess(e.hi - e.lo, 1e-9 * abs(e.lo))

    @unittest.skipUnless(PYENV.exists(), "python-flint venv not present")
    def test_coulomb_certificate_regenerates(self):
        out = pathlib.Path(tempfile.mkdtemp(prefix="cc-")) / "c.json"
        subprocess.run([str(PYENV), str(ROOT / "bgw/endpoint/certcoulomb.py"), str(fresh()),
                        str(out)], check=True, capture_output=True)
        a, b = json.loads(out.read_text()), json.loads(COULOMB_CERT.read_text())
        self.assertEqual(a["vbar"], b["vbar"])
        self.assertEqual(a["oneoverq"], b["oneoverq"])

    def test_o1_enclosure_and_layer1_bound(self):
        """E1.4 gate: O1_spec enclosed to < 1e-8 eV with no undecided branch;
        |O1_prod - O1_specA| <= 5.21e-6 eV (exact rationals); C1 holds for spec A, for spec B
        and for every q0 direction choice."""
        c = certified()
        self.assertNotIn("undecided_stale_sentinel", c["branch_stats"])
        self.assertTrue(all(v == 0 for k, v in c["branch_stats"].items() if k.startswith("undecided")))
        self.assertLess(c["O1_width"], 1e-8)
        prod = observable.observables((fresh() / "sigma_hp.log").read_text())["O1_Delta_XL"]
        # the printed production value is exact to 1e-9 eV (two 9-decimal values)
        lo, hi = prod - 1e-9, prod + 1e-9
        bound = max(abs(lo - c["O1_hi"]), abs(hi - c["O1_lo"]))
        self.assertLess(bound, 5.3e-6)
        self.assertGreater(bound, 5.1e-6)            # dominated by the Monte Carlo quadrature
        # The documented 5.21 µeV, in exact rational arithmetic (R28-R2). The endpoints are
        # the kernel-checked dyadics (binary64 values, exact as Fractions); the printed
        # production O1 carries 1 neV of print slack plus 1 feV for its float parse.
        from fractions import Fraction
        self.assertEqual(Fraction(c["O1_lo"]), Fraction(8880811588953599, 2 ** 59))
        self.assertEqual(Fraction(c["O1_hi"]), Fraction(8880812351936001, 2 ** 59))
        slack = Fraction(1, 10 ** 9) + Fraction(1, 10 ** 15)
        plo, phi = Fraction(prod) - slack, Fraction(prod) + slack
        exact = max(abs(plo - Fraction(c["O1_hi"])), abs(phi - Fraction(c["O1_lo"])))
        self.assertLessEqual(exact, Fraction(521, 10 ** 8))
        self.assertGreater(c["O1_lo"], 0)
        self.assertGreater(c["O1_q0_ops_min"], 0)
        self.assertGreater(c["O1_specB_direction_average"][0], 0)
        self.assertEqual(c["O1_per_q0_op"]["47"], [c["O1_lo"], c["O1_hi"]])

    def test_production_conventions_enclose_production(self):
        """With the production Monte Carlo averages in place of the exact ones,
        cert.py encloses production's printed Eqp1 of all four states, O1 and
        O2: the certified evaluator carries the production conventions, and the
        5.2 micro-eV gap to spec A is the quadrature alone."""
        d = pathlib.Path(tempfile.mkdtemp(prefix="e14r-"))
        cj = cert.replica_coulomb_json(fresh(), d / "mc.json")
        cert.main([str(fresh()), "--coulomb", str(cj), "--out", str(d / "c.json")])
        c = json.loads((d / "c.json").read_text())
        tables = observable.parse((fresh() / "sigma_hp.log").read_text())
        run, _ = setup()
        pr = {name: observable.state(tables[tuple(run.kpts[i])], b)["Eqp1"]
              for name, i, b in (("X", 2, 5), ("L", 1, 5), ("Gamma_v", 0, 4), ("Gamma_c", 0, 5))}
        encl = {"X": c["Eqp1_X"], "L": c["Eqp1_L"], "Gamma_v": c["Eqp1_Gamma_v"],
                "Gamma_c": c["Eqp1_Gamma_c"]}
        for k in pr:          # the print is exact to +-5e-10 eV
            self.assertTrue(encl[k][0] - 5e-10 <= pr[k] <= encl[k][1] + 5e-10, (k, pr[k], encl[k]))
        o1 = pr["X"] - pr["L"]
        self.assertTrue(c["O1_lo"] - 1e-9 <= o1 <= c["O1_hi"] + 1e-9)

    def test_o2_enclosure(self):
        """O2 enclosed, CBM certainly at L, |O2_prod - O2_specA| <= 3.4e-5 eV."""
        c = certified()
        self.assertTrue(c["CBM_certainly_at_L"])
        o = observable.observables((fresh() / "sigma_hp.log").read_text())
        lo, hi = c["O2_gap_L_minus_Gamma_v"]
        self.assertLess(hi - lo, 1e-8)
        bound = max(abs(o["O2_gap"] - 1e-9 - hi), abs(o["O2_gap"] + 1e-9 - lo))
        self.assertLess(bound, 3.4e-5)

    def test_near_pole_closed_form_is_the_source_formula(self):
        """cert.py encloses -I w/(2(x+w)); GW/Endpoint/NearPole.lean proves it
        equals the source's -Omega2 delw/(4 w^2 (delw+1/2)); here the float
        source formula (spec.gpp_kernel) agrees with it on random modes."""
        rng = np.random.default_rng(7)
        w = rng.uniform(0.1, 30, 2000)
        x = w + rng.uniform(-0.4, 0.4, 2000)          # inside the near-pole window
        Ie = rng.normal(size=2000)
        ssx, _, br = spec.gpp_kernel(x[:, None], w[:, None], Ie[:, None], True)
        near = br[:, 0] == 1
        self.assertGreater(near.sum(), 1000)
        closed = -Ie * w / (2 * (x + w))
        self.assertLess(np.max(np.abs(ssx[near, 0] - closed[near]) / np.abs(closed[near])), 1e-10)
        import inspect
        src = inspect.getsource(cert.SigmaIV.kernel)
        self.assertIn("den_n = I.exact(2.0) * (wx + wt)", src)
        self.assertIn("-(Ie * wt) / safe_dn", src)          # the near-pole value, inside the sexcut select


@unittest.skipUnless(HAVE_TREE, "pristine BerkeleyGW tree with epm2bgw.x not built")
class E15Mutations(unittest.TestCase):
    LOG = ROOT / "bgw/endpoint/data/mutations_e1.log"

    def test_log_is_current_and_every_mutant_detected(self):
        text = self.LOG.read_text()
        import hashlib
        self.assertIn(hashlib.sha256((ROOT / "bgw/endpoint/spec.py").read_bytes()).hexdigest(), text)
        self.assertIn(hashlib.sha256((ROOT / "bgw/endpoint/mutate_e1.py").read_bytes()).hexdigest(), text)
        rows = [l for l in text.splitlines() if "max table dev" in l]
        self.assertEqual(len(rows), 16)
        self.assertTrue(rows[0].endswith("control-agrees"))
        self.assertTrue(all(r.endswith("DETECTED") and "NOT" not in r for r in rows[1:]))

    def test_rerun_control_and_one_mutant(self):
        import mutate_e1
        import multiprocessing as mpx
        with mpx.get_context("fork").Pool(2) as pool:      # patches stay in the workers
            res = {n: w for n, w, _, _ in pool.map(mutate_e1.evaluate,
                                                   [(str(fresh()), "control"),
                                                    (str(fresh()), "op_first_match")])}
        self.assertLess(res["control"], 1e-9)
        self.assertGreater(res["op_first_match"], 1e-3)


@unittest.skipUnless(HAVE_TREE, "pristine BerkeleyGW tree with epm2bgw.x not built")
class E15SphereMargins(unittest.TestCase):
    def test_no_G_on_a_cutoff_sphere(self):
        import sphere_margins
        m = sphere_margins.margins(fresh())
        self.assertEqual(len(m), 7)
        self.assertGreater(min(m.values()), 1e-2)   # vs ~1e-15 relative rounding
