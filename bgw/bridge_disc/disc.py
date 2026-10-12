#!/usr/bin/env python3
"""BRIDGE-DISC D2/D3: the ideal fcc metric on the Si-EPM run.

    python3 bgw/bridge_disc/disc.py RUNDIR [--coulomb-ideal F] [--out F]
    ~/bgw-src/pyenv-e1/bin/python bgw/bridge_disc/disc.py RUNDIR --make-coulomb F [--procs N]

The exported binary64 `bdot` is the ideal fcc metric c[[3,-1,-1],[-1,3,-1],[-1,-1,3]],
c = bdot_11/3 (itself a binary64 number), up to ONE ulp (2^-54) on every off-diagonal
entry (`GW.Bridge.bExp_sub_ideal`). This script

* D2 census (exact rationals): on every eps sphere of Sigma, the pairs (G, G') whose
  ideal-metric dot (q+G').B.(q+G) is exactly 0 (Cartesian orthogonality, `Orth`); the
  gap |ideal dot| >= c/4 on all the others (`ideal_gap`); the Lean bound of
  `om2S_orth_bound` on the rounded Omega^2 of every orthogonal pair, which must be below
  TOL_Small (the hypothesis `hsmall` of `disc_mode`); and that every G-sphere Sigma and
  Epsilon use is the same set under the ideal metric (exact norms);
* `--make-coulomb`: the certified mini-BZ Coulomb averages (bgw/endpoint/certcoulomb.py,
  imported, not modified) recomputed with the ideal metric;
* D3 (rigorous, iv.py): spec A's Sigma, Eqp1 and O1 re-evaluated with the ideal metric
  EVERYWHERE the spec uses bdot (Epsilon's chi -> eps -> eps^-1 enclosure, the spheres,
  Omega^2, |q| in the wing factors, the Coulomb averages), through
  bgw/bridge_measure/measure.py's classifier and switches (imported, not modified).
  The wavefunctions, energies and RHO of the run are inputs and are held fixed.

The metric is substituted by wrapping `bgwio.read_wfn` (every Crystal is built from the
WFN header), after asserting the header holds exactly the exported dyadics.
"""
import argparse
import json
import pathlib
import sys
import time
from fractions import Fraction as Fr

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[2]
EP = ROOT / "bgw/endpoint"
sys.path.insert(0, str(EP))
sys.path.insert(0, str(ROOT / "bgw/bridge_measure"))
import bgwio  # noqa: E402

# the exported bdot (GW.Bridge.bExp) and the ideal one (GW.Bridge.idealB cExp)
DIAG = Fr(5065758257150985, 2 ** 52)
OFF = Fr(-6754344342867979, 2 ** 54)
C = Fr(6754344342867980, 2 ** 54)
TS = Fr(4722366482869645, 2 ** 72)
RYD = Fr(1360569253, 10 ** 8)


def exported_B():
    return [[DIAG if i == j else OFF for j in range(3)] for i in range(3)]


def ideal_B():
    return [[3 * C if i == j else -C for j in range(3)] for i in range(3)]


def ideal_float():
    B = np.array([[float(x) for x in r] for r in ideal_B()])
    assert all(Fr(float(x)) == x for r in ideal_B() for x in r), "ideal metric not binary64"
    return B


_orig_read_wfn = bgwio.read_wfn


def use_ideal_metric():
    """Every WFN header read from now on carries the ideal metric (asserting it held the
    exported dyadics)."""
    Bi = ideal_float()

    def read(path):
        h = _orig_read_wfn(path)
        got = [[Fr(float(x)) for x in r] for r in h["bdot"]]
        if got != exported_B():
            raise ValueError(f"{path}: bdot is not the exported Si-EPM metric")
        h["bdot"] = Bi.copy()
        return h
    bgwio.read_wfn = read


def f_up(x):
    """The least binary64 >= the rational x (upper bounds are reported rounded up)."""
    f = float(x)
    return float(np.nextafter(f, np.inf)) if Fr(f) < x else f


def f_down(x):
    """The greatest binary64 <= the rational x."""
    f = float(x)
    return float(np.nextafter(f, -np.inf)) if Fr(f) > x else f


def dot(u, B, w):
    return sum(u[i] * B[i][j] * w[j] for i in range(3) for j in range(3))


def cart(u):
    return (-u[0] + u[1] + u[2], u[0] - u[1] + u[2], u[0] + u[1] - u[2])


# ------------------------------------------------------------------ D2 census

def census(rundir, coulomb):
    import spec
    import cert
    run = spec.Run(rundir)
    Bx, Bi = exported_B(), ideal_B()
    if [[Fr(float(x)) for x in r] for r in run.cr.bdot] != Bx:
        raise ValueError("WFN_inner bdot is not the exported Si-EPM metric")
    delta = max(abs(Bx[i][j] - Bi[i][j]) for i in range(3) for j in range(3))
    rho = bgwio.read_rho(pathlib.Path(rundir) / "RHO")
    ridx = spec.gindex(rho["gvec"])
    cc = cert.CertCoulomb(coulomb)
    celvol = Fr(float(run.cr.celvol))
    pref = 2 * RYD * RYD / celvol          # factW / (8 pi) = RYD^2 16 pi / celvol / (8 pi)
    out = dict(delta=str(delta), c=str(C), per_q=[], orth_pairs=0, orth_rho_nonzero=0,
               orth_rho_zero=0, pairs=0, min_nonzero_ideal_over_c=None,
               max_bound_over_TS=0.0, max_rounded_residual=0.0)
    mn = None
    for q in run.qlist:
        Gs, _ = run.sphere(q, run.ecuts)
        qF = [Fr(float(x)) for x in q]
        V = [[qF[t] + int(g[t]) for t in range(3)] for g in Gs]
        n = len(Gs)
        q0 = not any(q)
        no = nr = 0
        for i in range(n):
            if q0 and not Gs[i].any():
                continue                       # the q = 0 head row: not a dot (Bloch.OmT)
            vb = cc.vbar(q + Gs[i])
            vhi = Fr(float(vb.hi))
            for j in range(n):
                out["pairs"] += 1
                di = dot(V[j], Bi, V[i])
                if di != 0:
                    m = abs(di) / C
                    mn = m if mn is None else min(mn, m)
                    continue
                assert sum(a * b for a, b in zip(cart(V[j]), cart(V[i]))) == 0
                no += 1
                k = tuple(Gs[i] - Gs[j])
                r = Fr(float(rho["rho"][ridx[k]])) if k in ridx else Fr(0)
                if r == 0:
                    out["orth_rho_zero"] += 1
                    continue
                nr += 1
                dr = dot(V[j], Bx, V[i])
                out["max_rounded_residual"] = max(out["max_rounded_residual"], f_up(abs(dr)))
                s = sum(abs(V[j][a]) * abs(V[i][b]) for a in range(3) for b in range(3))
                bound = abs(pref * r * vhi) * delta * s      # om2S_orth_bound
                out["max_bound_over_TS"] = max(out["max_bound_over_TS"], f_up(bound / TS))
                if not bound < TS:
                    raise AssertionError(f"hsmall fails at q={q}, {Gs[i]}, {Gs[j]}")
        out["per_q"].append(dict(q=[float(x) for x in q], n=n, orth=no, orth_rho_nonzero=nr))
        out["orth_pairs"] += no
        out["orth_rho_nonzero"] += nr
    out["min_nonzero_ideal_over_c"] = str(mn)
    out["spheres"] = spheres_same(run, rundir)
    return out


def spheres_same(run, rundir):
    """Every sphere Sigma (eps, exchange, static CH) and Epsilon (per eps q, incl. q0)
    builds from bdot is the same set with the ideal metric; returns the smallest
    |ideal |q+G|^2 - ecut| over all candidates (exact)."""
    import spec
    Bi = ideal_B()
    er = spec.EpsilonRun(rundir, run.nbands, run.ecuts)
    jobs = [(q, run.ecuts, run.gvec, run.cr) for q in run.qlist]
    jobs += [(q, run.ecutb, run.gvec, run.cr) for q in run.qlist]
    jobs += [(np.zeros(3), max(run.ecuts, run.ecutb), run.gvec, run.cr)]
    qs = [run.eps0["q"][0]["q"]] + [b["q"] for b in run.eps["q"]]
    jobs += [(np.asarray(q, float), er.ecut, er.gvec, er.cr) for q in qs]
    margin = None
    for q, ecut, gvec, cr in jobs:
        n2 = cr.norm2(np.asarray(q)[None, :] + gvec)
        inset = n2 < ecut
        qF = [Fr(float(x)) for x in q]
        E = Fr(float(ecut))
        for g, s in zip(gvec, inset):
            v = [qF[t] + int(g[t]) for t in range(3)]
            ni = dot(v, Bi, v)
            if (ni < E) != bool(s):
                raise AssertionError(f"sphere differs at q={q}, G={g}")
            d = abs(ni - E)
            margin = d if margin is None else min(margin, d)
    return dict(n_spheres=len(jobs), same=True, min_margin=f_down(margin))


# ------------------------------------------------------------------ Coulomb (Arb)

def make_coulomb(rundir, out, procs):
    import multiprocessing as mp
    import certcoulomb
    use_ideal_metric()
    pool0 = mp.Pool

    class Pool:
        """certcoulomb.main's Pool(16) with `procs` workers (sibling jobs share the machine)."""
        def __init__(self, _n, **kw):
            self.p = pool0(procs, **kw)

        def __enter__(self):
            return self.p

        def __exit__(self, *a):
            self.p.__exit__(*a)
    certcoulomb.mp.Pool = Pool
    t0 = time.time()
    try:
        certcoulomb.main(rundir, out)
    finally:
        certcoulomb.mp.Pool = pool0
    d = json.loads(pathlib.Path(out).read_text())
    if [[Fr(x) for x in r] for r in d["bdot"]] != ideal_B():
        raise AssertionError("coulomb file not built on the ideal metric")
    print(f"ideal-metric Coulomb averages: {time.time() - t0:.0f} s")


# ------------------------------------------------------------------ D3 (iv)

def d3(rundir, coulomb_ideal):
    use_ideal_metric()
    import measure as M
    t0 = time.time()
    m = M.Measure(rundir, coulomb_ideal)
    if [[Fr(float(x)) for x in r] for r in m.run.cr.bdot] != ideal_B():
        raise AssertionError("the ideal metric did not reach the run")
    kX, kL = m.run.kpts[2], m.run.kpts[1]
    base = dict(coul="avg", wings="spec", tolzero="spec")
    tX, tL = {}, {}
    rX = m.state(kX, [5, 6], base, tX)
    rL = m.state(kL, [5], base, tL)
    sX, eX, s1X = M.eqp1(rX)
    sL, eL, s1L = M.eqp1(rL)
    o1 = eX - eL
    out = dict(baseline=dict(SigmaX=M.ivl(sX), SigmaL=M.ivl(sL), Eqp1_X=M.ivl(eX), Eqp1_L=M.ivl(eL),
                             O1_meV=M.mev(o1)),
               tally_X=tX, tally_L=tL, rows={})

    def gather(dC, name):
        ex = {}
        for (n, a, iw), v in dC.items():
            if n in (name, name + "_undec") or (name.endswith("_x0") and n == name[:-3] + "_undec_x0"):
                ex[(a, iw)] = ex[(a, iw)] + v if (a, iw) in ex else v
        return ex

    for name in ("drop_O_x0", "drop_O", "drop_I_x0", "drop_I"):
        exX, exL = gather(rX["dC"], name), gather(rL["dC"], name)
        a, b, _ = M.eqp1(rX, 0.5, exX)
        c, d, _ = M.eqp1(rL, 0.5, exL)
        out["rows"][name] = dict(dSigmaX_meV=M.mev(a - sX), dSigmaL_meV=M.mev(c - sL),
                                 dO1_meV=M.mev((b - d) - o1), O1_meV=M.mev(b - d))
    out["seconds"] = time.time() - t0
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("rundir")
    ap.add_argument("--coulomb", default=str(EP / "data/coulomb_cert.json"))
    ap.add_argument("--coulomb-ideal", default=str(ROOT / "bgw/bridge_disc/data/coulomb_ideal.json"))
    ap.add_argument("--make-coulomb", default=None)
    ap.add_argument("--procs", type=int, default=6)
    ap.add_argument("--out", default=str(ROOT / "bgw/bridge_disc/data/disc.json"))
    a = ap.parse_args(argv)
    if a.make_coulomb:
        make_coulomb(a.rundir, a.make_coulomb, a.procs)
        return 0
    t0 = time.time()
    res = dict(census=census(a.rundir, a.coulomb))
    print(json.dumps({k: v for k, v in res["census"].items() if k != "per_q"}), flush=True)
    res["d3"] = d3(a.rundir, a.coulomb_ideal)
    spec_a = json.loads((ROOT / "bgw/bridge_measure/data/measure.json").read_text())
    lo, hi = res["d3"]["baseline"]["O1_meV"]
    slo, shi = spec_a["baseline"]["O1_meV"]
    res["compare"] = dict(O1_ideal_meV=[lo, hi], O1_specA_meV=[slo, shi],
                          overlap=bool(lo <= shi and slo <= hi),
                          # exact differences of the committed endpoints, rounded up
                          max_abs_difference_meV=f_up(max(Fr(hi) - Fr(slo), Fr(shi) - Fr(lo))),
                          width_specA_meV=f_up(Fr(shi) - Fr(slo)), width_ideal_meV=f_up(Fr(hi) - Fr(lo)),
                          switch_drop_O_x0_ideal_meV=res["d3"]["rows"]["drop_O_x0"]["dO1_meV"],
                          switch_drop_O_x0_specA_meV=spec_a["rows"]["drop_O_x0"]["dO1_meV"])
    res["seconds"] = time.time() - t0
    pathlib.Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    pathlib.Path(a.out).write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps(res["compare"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
