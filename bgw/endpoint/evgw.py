#!/usr/bin/env python3
"""A3 starting point: eigenvalue self-consistency in G AND W (evGW), with the
production binaries.

    python3 bgw/endpoint/evgw.py BASE_RUNDIR OUTDIR [--iters 20] [--tol 1e-4]

Each iteration n uses the QP energies of iteration n-1 everywhere:
  1. Epsilon with `eqp_corrections` (Epsilon/input.f90:148-152 reads eqp.dat
     for WFN, input_q.f90:86-90 eqp_q.dat for WFNq) -> eps0mat, epsmat (W_n);
  2. Sigma on WFN_inner (Gamma, L, X), all 18 bands, `eqp_corrections`, with W_n
     -> the O1 states and the inner energies of the next iteration;
  3. Sigma with WFN (the shifted grid Epsilon uses) as WFN_inner, at its two
     irreducible k-points -> the energies of eqp.dat for the next Epsilon.
WFNq (valence only, k + q0 with q0 = 0.001) gets the QP shift of the WFN point
k it is displaced from (the O(q0) difference is neglected: an approximation,
recorded). Iteration 0 is the production (one-shot) chain.
"""
import argparse
import json
import pathlib
import shutil
import subprocess
import sys

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import bgwio  # noqa: E402
import observable  # noqa: E402
import run_production as rp  # noqa: E402
import spec  # noqa: E402

RYD = spec.RYD


def run(binary, d):
    with open(d / (pathlib.Path(binary).stem + ".out"), "w") as fh:
        r = subprocess.run([str(rp.DEFAULT_TREE / binary)], cwd=d, stdout=fh,
                           stderr=subprocess.STDOUT)
    if r.returncode:
        raise RuntimeError(f"{binary} failed in {d}")


def read_eqp(path):
    """{k-tuple: {band: (Emf, Eqp)}} from an eqp*.dat file."""
    out, cur = {}, None
    for l in pathlib.Path(path).read_text().splitlines():
        f = l.split()
        if len(f) == 4 and "." in f[0]:
            cur = tuple(round(float(x), 6) for x in f[:3])
            out[cur] = {}
        elif len(f) == 4:
            out[cur][int(f[1])] = (float(f[2]), float(f[3]))
    return out


def write_eqp(path, table):
    with open(path, "w") as fh:
        for k, bands in table.items():
            fh.write(f"{k[0]:13.9f}{k[1]:13.9f}{k[2]:13.9f}{len(bands):8d}\n")
            for b, (emf, eqp) in sorted(bands.items()):
                fh.write(f"{1:8d}{b:8d}{emf:15.9f}{eqp:15.9f}\n")


def wfnq_table(base, shifted):
    """eqp_q.dat for WFNq: each point k' = k + q0 takes the QP shift of the WFN
    grid point k (found through the symmetry ops of WFN)."""
    wq = bgwio.read_wfn(base / "WFNq")
    w = bgwio.read_wfn(base / "WFN")
    wf = spec.Wfn(w, spec.Crystal(w))
    q0 = np.array([0.0, 0.0, 0.001])
    table = {}
    for ik, kp in enumerate(wq["kpt"]):
        irk, _, _ = wf.find(kp - q0)
        key = tuple(round(float(x), 6) for x in w["kpt"][irk])
        shifts = {b: eqp - emf for b, (emf, eqp) in shifted[key].items()}
        table[tuple(kp)] = {b + 1: (wq["energies"][0, ik, b] * RYD,
                                    wq["energies"][0, ik, b] * RYD + shifts[b + 1])
                            for b in range(4)}
    return table


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("base")
    ap.add_argument("out")
    ap.add_argument("--iters", type=int, default=20)
    ap.add_argument("--tol", type=float, default=1e-4)
    a = ap.parse_args(argv)
    base, out = pathlib.Path(a.base).resolve(), pathlib.Path(a.out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    sig_inp = rp.apply_override((base / "sigma.inp").read_text(), "band_index_max", "18")
    wfn = bgwio.read_wfn(base / "WFN")
    kshift = "\n".join(f"  {k[0]:.9f}  {k[1]:.9f}  {k[2]:.9f}   1.0" for k in wfn["kpt"]) + "\n"
    sig_shift_inp = rp.apply_override(sig_inp, "kpoints", kshift)
    hist, prev = [], None
    for it in range(a.iters + 1):
        d = out / f"it{it:02d}"
        de, dsi, dss = d / "eps", d / "sig", d / "sigshift"
        for x in (de, dsi, dss):
            x.mkdir(parents=True)
        # 1. epsilon
        for f in ("WFN", "WFNq"):
            (de / f).symlink_to(base / f)
        text = (base / "epsilon.inp").read_text()
        if it > 0:
            p = out / f"it{it - 1:02d}"
            shutil.copy2(p / "sigshift" / "eqp1.dat", de / "eqp.dat")
            write_eqp(de / "eqp_q.dat", wfnq_table(base, read_eqp(p / "sigshift" / "eqp1.dat")))
            text = text.rstrip("\n") + "\neqp_corrections\n"
        (de / "epsilon.inp").write_text(text)
        run("Epsilon/epsilon.real.x", de)
        # 2./3. sigma on the inner grid and on the shifted grid
        for dd, wfn_inner, inp, prevdir in ((dsi, base / "WFN_inner", sig_inp, "sig"),
                                            (dss, base / "WFN", sig_shift_inp, "sigshift")):
            (dd / "WFN_inner").symlink_to(wfn_inner)
            for f in ("RHO", "VXC", "vxc.dat"):
                (dd / f).symlink_to(base / f)
            for f in ("eps0mat", "epsmat"):
                (dd / f).symlink_to(de / f)
            t = inp
            if it > 0:
                shutil.copy2(out / f"it{it - 1:02d}" / prevdir / "eqp1.dat", dd / "eqp.dat")
                t = t.rstrip("\n") + "\neqp_corrections\n"
            (dd / "sigma.inp").write_text(t)
            run("Sigma/sigma.real.x", dd)
        o = observable.observables((dsi / "sigma_hp.log").read_text())
        energies = [e for tab in (read_eqp(dsi / "eqp1.dat"), read_eqp(dss / "eqp1.dat"))
                    for k in sorted(tab) for b, (_, e) in sorted(tab[k].items())]
        dmax = max(abs(x - y) for x, y in zip(energies, prev)) if prev else None
        rec = {"iter": it, "O1": o["O1_Delta_XL"], "O2": o["O2_gap"],
               "Eqp1_X": o["states"]["c_X"]["Eqp1"], "Eqp1_L": o["states"]["c_L"]["Eqp1"],
               "max_dE": dmax}
        hist.append(rec)
        print(json.dumps(rec), flush=True)
        prev = energies
        if dmax is not None and dmax < a.tol:
            break
    (out / "evgw.json").write_text(json.dumps(hist, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
