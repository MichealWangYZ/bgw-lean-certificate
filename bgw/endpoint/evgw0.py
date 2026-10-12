#!/usr/bin/env python3
"""A3 starting-point test: eigenvalue self-consistency in G (evGW0), with the
production binaries.

    python3 bgw/endpoint/evgw0.py BASE_RUNDIR OUTDIR [--iters 20] [--tol 1e-4]

BASE_RUNDIR is a finished pinned run (WFN_inner, RHO, VXC, eps0mat, epsmat).
Iteration 0 is the production sigma with band_index_max raised to 18 (all
bands entering G). Each further iteration copies the previous eqp1.dat to
eqp.dat and sets `eqp_corrections` (Sigma/input.f90:279-284 replaces the
energies used in G and the evaluation centres Eo; Emf stays the EPM value),
so Eqp1(n) = Emf + Sigma_n(E_{n-1}) plus one Newton step: at the fixed point
E = Emf + Sigma[G(E)](E). W stays the EPM one (the "0" in evGW0).
Records O1 (multiplet averages, as observable.py) per iteration.
"""
import argparse
import json
import pathlib
import shutil
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import observable  # noqa: E402
import run_production as rp  # noqa: E402


def run_sigma(d):
    with open(d / "sigma.out", "w") as fh:
        r = subprocess.run([str(rp.DEFAULT_TREE / "Sigma/sigma.real.x")], cwd=d,
                           stdout=fh, stderr=subprocess.STDOUT)
    if r.returncode:
        raise RuntimeError(f"sigma failed in {d}")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("base")
    ap.add_argument("out")
    ap.add_argument("--iters", type=int, default=20)
    ap.add_argument("--tol", type=float, default=1e-4, help="eV, max |dE| over all states")
    a = ap.parse_args(argv)
    base, out = pathlib.Path(a.base).resolve(), pathlib.Path(a.out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    inp = rp.apply_override((base / "sigma.inp").read_text(), "band_index_max", "18")
    hist = []
    prev = None
    for it in range(a.iters + 1):
        d = out / f"it{it:02d}"
        d.mkdir()
        for f in ("WFN_inner", "RHO", "VXC", "vxc.dat", "eps0mat", "epsmat"):
            (d / f).symlink_to(base / f)
        text = inp
        if it > 0:
            shutil.copy2(out / f"it{it - 1:02d}" / "eqp1.dat", d / "eqp.dat")
            text = text.rstrip("\n") + "\neqp_corrections\n"
        (d / "sigma.inp").write_text(text)
        run_sigma(d)
        o = observable.observables((d / "sigma_hp.log").read_text())
        eq = [l.split() for l in (d / "eqp1.dat").read_text().splitlines()]
        energies = [float(x[3]) for x in eq if len(x) == 4 and x[0] == "1"]
        dmax = max(abs(p - q) for p, q in zip(energies, prev)) if prev else None
        rec = {"iter": it, "O1": o["O1_Delta_XL"], "O2": o["O2_gap"],
               "Eqp1_X": o["states"]["c_X"]["Eqp1"], "Eqp1_L": o["states"]["c_L"]["Eqp1"],
               "max_dE": dmax}
        hist.append(rec)
        print(json.dumps(rec), flush=True)
        prev = energies
        if dmax is not None and dmax < a.tol:
            break
    (out / "evgw0.json").write_text(json.dumps(hist, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
