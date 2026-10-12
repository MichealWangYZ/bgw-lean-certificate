#!/usr/bin/env python3
"""E1.5: would the E1 comparison have caught a production that implemented
something else?  Counterfactual fault classes, run through the reproducer.

    python3 bgw/endpoint/mutate_e1.py RUNDIR [--log FILE] [--only NAME ...]

Each mutant changes ONE convention of spec.py (a plausible way the production
could differ from what we believe it computes). For each we record the largest
deviation from the production diagonal table over all 24 states and columns,
and the shift of O1. DETECTED means the table deviates by more than 1e-8 eV
(20x the print precision the unmutated reproducer achieves). A mutant that is
not detected is reported as such -- it is a blind spot of the comparison, not
a pass -- together with its effect on O1.
"""
import argparse
import functools
import hashlib
import json
import multiprocessing as mp
import os
import pathlib
import sys

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import numpy as np  # noqa: E402

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import coulomb  # noqa: E402
import observable  # noqa: E402
import spec  # noqa: E402

DETECT = 1e-8


def _patch(name):
    """Apply mutant `name` to the spec module (in this worker process)."""
    S = spec
    if name == "control":
        return
    if name == "op_first_match":
        orig = S.Screening.__init__

        def init(self, *a, **k):
            orig(self, *a, **k)
            self.choose_op = "first"
        S.Screening.__init__ = init
    elif name == "static_remainder_factor_1":
        orig_c = S.correlation

        def corr(*a, **k):
            SX, CH, cor, e = orig_c(*a, **k)
            return SX, CH, 2 * cor, e
        S.correlation = corr
    elif name == "no_static_remainder":
        orig_c = S.correlation

        def corr(*a, **k):
            SX, CH, cor, e = orig_c(*a, **k)
            return SX, CH, 0 * cor, e
        S.correlation = corr
    elif name == "unocc_nearpole_ch_kept":
        orig_k = S.gpp_kernel

        def kern(wx, wt, Ie, occupied, gamma=0.5, sexcut=4.0):
            ssx, sch, br = orig_k(wx, wt, Ie, occupied, gamma, sexcut)
            if not occupied:
                with np.errstate(divide="ignore", invalid="ignore"):
                    full = np.where(wt == 0, 0.0, wt / (wx - wt) * Ie)
                sch = np.where(np.isfinite(full), full, 0.0)
            return ssx, sch, br
        S.gpp_kernel = kern
    elif name == "invalid_modes_skipped":
        orig_m = S.gpp_modes

        def modes(*a, **k):
            m = orig_m(*a, **k)
            m["wt"] = np.where(m["wt"] >= 1e11, 0.0, m["wt"])
            return m
        S.gpp_modes = modes
    elif name == "gamma_0.25":
        orig_k = S.gpp_kernel
        S.gpp_kernel = lambda wx, wt, Ie, occ, gamma=0.5, sexcut=4.0: orig_k(wx, wt, Ie, occ, 0.25, sexcut)
    elif name == "sexcut_disabled":
        orig_k = S.gpp_kernel
        S.gpp_kernel = lambda wx, wt, Ie, occ, gamma=0.5, sexcut=4.0: orig_k(wx, wt, Ie, occ, gamma, 1e300)
    elif name == "dw_0.5":
        orig_q = S.quasiparticle
        S.quasiparticle = lambda run, k, vb, scr, rho, dw=1.0: orig_q(run, k, vb, scr, rho, dw=0.5)
    elif name == "q_weight_off_by_one":
        orig_run = S.Run.__init__

        def rinit(self, d, _o=orig_run):
            _o(self, d)
            self.fact = 1.0 / ((len(self.qlist) - 1) * self.cr.celvol)
        S.Run.__init__ = rinit
    elif name == "ryd_codata2018":
        S.RYD = 13.605693122994
    elif name == "tol_small_1e-4":
        S.TOL_SMALL = 1e-4
    elif name == "no_fractional_translations":
        orig_w = S.Wfn.__init__

        def winit(self, w, cr, _o=orig_w):
            _o(self, w, cr)
            self.ops = [(W, 0 * t) for W, t in self.ops]
        S.Wfn.__init__ = winit
    else:
        raise KeyError(name)


# wing mutants need to change arithmetic inside Screening.at; do it by source
# substitution on a private copy of the method, so spec.py stays unmodified.
WING_EDITS = {
    "wing_at_target_G0": [("z = int(np.flatnonzero(np.all(Gs == g0, axis=1))[0])",
                           "z = int(np.flatnonzero(~Gs.any(axis=1))[0])")],
    "wing_v0_is_G0": [("v0 = self.vbar(tuple(q + Gs[0]))", "v0 = self.vbar(tuple(q))")],
    "no_wing_fix_q_nonzero": [("eps[z, others] *= o * qlen / (8 * np.pi)", "pass"),
                              ("eps[others, z] *= o / (v0 * qlen)", "pass")],
}


def _patch_wing(name):
    import inspect
    import textwrap
    src = textwrap.dedent(inspect.getsource(spec.Screening.at))
    for a, b in WING_EDITS[name]:
        if a not in src:
            raise ValueError(f"wing edit anchor missing for {name}")
        src = src.replace(a, b)
    ns = {}
    exec(compile(src, "<mutant>", "exec"), spec.__dict__, ns)
    spec.Screening.at = ns["at"]


def evaluate(args):
    rundir, name = args
    if name in WING_EDITS:
        _patch_wing(name)
    else:
        _patch(name)
    run = spec.Run(rundir)
    mb = coulomb.MiniBZ(run.cr.bdot, run.qgrid, run.cr.celvol)
    vb = functools.lru_cache(None)(lambda qk: mb.production(np.array(qk)))
    oq = functools.lru_cache(None)(lambda q: mb.oneoverq_production(np.array(q)))
    rho = spec.bgwio.read_rho(pathlib.Path(rundir) / "RHO")
    scr = spec.Screening(run, vb, oq)
    tables = observable.parse((pathlib.Path(rundir) / "sigma_hp.log").read_text())
    worst, where, eq = 0.0, None, {}
    for k in run.kpts:
        rows = spec.quasiparticle(run, k, vb, scr, rho)
        prod = {r["n"]: r for r in tables[tuple(k)]}
        for r in rows:
            p = prod[r["bands"][0]]
            for a, b in [("X", "X"), ("SXX", "SX-X"), ("CH", "CH"), ("Sig", "Sig"),
                         ("Eqp1", "Eqp1"), ("Z", "Znk")]:
                d = abs(r[a] - p[b])
                if d > worst:
                    worst, where = d, (tuple(k), r["bands"], b)
            if 5 in r["bands"]:
                eq[tuple(k)] = r["Eqp1"]
    o1 = eq[(0.0, 0.5, 0.5)] - eq[(0.0, 0.0, 0.5)]
    return name, worst, where, o1


MUTANTS = ["control", "op_first_match", "wing_at_target_G0", "wing_v0_is_G0",
           "no_wing_fix_q_nonzero", "static_remainder_factor_1", "no_static_remainder",
           "unocc_nearpole_ch_kept", "invalid_modes_skipped", "gamma_0.25", "sexcut_disabled",
           "dw_0.5", "q_weight_off_by_one", "ryd_codata2018", "tol_small_1e-4",
           "no_fractional_translations"]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("rundir")
    ap.add_argument("--log")
    ap.add_argument("--only", nargs="*")
    a = ap.parse_args(argv)
    names = a.only or MUTANTS
    with mp.get_context("fork").Pool(min(16, len(names))) as pool:
        res = pool.map(evaluate, [(a.rundir, n) for n in names])
    prod_o1 = observable.observables((pathlib.Path(a.rundir) / "sigma_hp.log").read_text())["O1_Delta_XL"]
    lines = ["E1.5 counterfactual fault classes (bgw/endpoint/mutate_e1.py)",
             f"spec.py sha256 {hashlib.sha256((HERE / 'spec.py').read_bytes()).hexdigest()}",
             f"mutate_e1.py sha256 {hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}",
             f"production O1 = {prod_o1 * 1e3:.6f} meV; detection threshold {DETECT:g} eV", ""]
    ok = True
    for name, worst, where, o1 in res:
        det = worst > DETECT
        verdict = "control-agrees" if name == "control" else ("DETECTED" if det else "NOT DETECTED")
        if name == "control" and det:
            ok = False
        lines.append(f"{name:28s} max table dev {worst:.3e} eV at {where}  "
                     f"O1 {o1 * 1e3:+.4f} meV (shift {(o1 - prod_o1) * 1e3:+.4f})  {verdict}")
    txt = "\n".join(lines) + "\n"
    print(txt)
    if a.log:
        pathlib.Path(a.log).write_text(txt)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
