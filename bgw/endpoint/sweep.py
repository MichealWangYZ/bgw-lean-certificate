#!/usr/bin/env python3
"""ARCHIVED (2026-10-02): E2 convergence layer, withdrawn from scope by owner decision 2026-09-23 (docs/ENDPOINT.md); kept with data/e2_results.jsonl, not extended. See docs/CODEMAP.md. -- E2: convergence sweeps of O1 over the numerical controls (empirical).

    python3 bgw/endpoint/sweep.py OUTROOT --grid 2 --nb 18 30 60 --ecuts 7 10 \
        [--ecutwfc 11] [--jobs 16] [--results results.jsonl]

One point = (N, nb, ecuts, ecutwfc, ecutb): an N x N x N k/q grid (N even,
so that L and X are grid points), nb bands in Epsilon and Sigma,
epsilon_cutoff ecuts (Sigma's screened cutoff follows it), wavefunction
cutoff ecutwfc, and Sigma's bare_coulomb_cutoff ecutb (default: the larger of
ecutwfc and ecuts, since Sigma requires screened <= bare). Everything else is
the pinned testsuite input.

Band window: nb is raised to the first value that does not end inside a
degenerate multiplet in WFN or WFN_inner (|E_nb+1 - E_nb| > 1e-5 Ry at every
k); the requested and the used nb are both recorded. Each point records O1
with and without the static remainder (BerkeleyGW prints both: CH and CH`),
every constituent of the two conduction states, input/binary hashes and the
wall time. Results append to a JSONL file; points already present are skipped.
"""
import argparse
import hashlib
import json
import multiprocessing as mp
import os
import pathlib
import re
import shutil
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import bgwio  # noqa: E402
import observable  # noqa: E402
import run_production as rp  # noqa: E402

TREE = rp.DEFAULT_TREE
KGRID = TREE / "MeanField/ESPRESSO/kgrid.x"
LATTICE = "0.0 0.5 0.5\n0.5 0.0 0.5\n0.5 0.5 0.0\n2\n1 -0.125 -0.125 -0.125\n1  0.125  0.125  0.125\n16 16 16\n.false.\n"


def kgrid(workdir, n, shift, qshift):
    d = pathlib.Path(workdir)
    (d / "kg.in").write_text(f"{n} {n} {n}\n{shift} {shift} {shift}\n{qshift[0]} {qshift[1]} {qshift[2]}\n\n" + LATTICE)
    subprocess.run([str(KGRID), "kg.in", "kg.out", "kg.log"], cwd=d, check=True,
                   capture_output=True)
    lines = (d / "kg.out").read_text().splitlines()
    nk = int(lines[1])
    return [l.split() for l in lines[2:2 + nk]]


def klist(rows):
    return "\n".join("  " + "  ".join(r) for r in rows)


def with_list(text, n, offsets, rows):
    text = rp.apply_override(text, "KPointNumbers", f"{n} {n} {n}")
    text = rp.apply_override(text, "KPointOffsets", " ".join(str(o) for o in offsets))
    head, _ = text.split("KPointsList", 1)
    return head + f"KPointsList {len(rows)}\n" + klist(rows) + "\n"


def set_key(text, key, value):
    return rp.apply_override(text, key, str(value))


def safe_nb(files, nb, tol=1e-5):
    """Smallest nb' >= nb that no WFN file cuts inside a multiplet."""
    Es = []
    for f in files:
        w = bgwio.read_wfn(f)
        Es.append(w["energies"][0])
    top = min(E.shape[1] for E in Es)
    for cand in range(nb, top):
        if all(abs(E[k, cand] - E[k, cand - 1]) > tol for E in Es for k in range(E.shape[0])):
            return cand
    raise ValueError(f"no safe band window >= {nb} below {top}")


def execute(d, binary, log, stdin=None, env=None):
    with open(d / log, "w") as fh:
        sin = open(d / stdin) if stdin else None
        try:
            r = subprocess.run([str(TREE / binary)], cwd=d, stdin=sin, stdout=fh,
                               stderr=subprocess.STDOUT, env=env)
        finally:
            if sin:
                sin.close()
    if r.returncode:
        raise RuntimeError(f"{binary} failed in {d}")


def point_id(p):
    return f"N{p['N']}_nb{p['nb']}_ec{p['ecuts']:g}_ew{p['ecutwfc']:g}_eb{p['ecutb']:g}"


def run_point(args):
    try:
        return _run_point(args)
    except Exception as e:          # recorded, not hidden: the point is reported as failed
        return dict(args[1], id=point_id(args[1]), error=f"{type(e).__name__}: {e}")


def _run_point(args):
    root, p = args
    d = pathlib.Path(root) / point_id(p)
    if d.exists():
        shutil.rmtree(d)
    d.mkdir(parents=True)
    env = dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1")
    t0 = time.time()
    n, nb, ecuts, ecw = p["N"], p["nb"], p["ecuts"], p["ecutwfc"]
    src = {f: (rp.ROOT / "bgw/export" / f).read_text() for f in rp.INPUTS}
    q0 = 0.001
    sh = kgrid(d, n, 0.5, (0, 0, 0))
    shq = kgrid(d, n, 0.5, (0, 0, q0))
    un = kgrid(d, n, 0.0, (0, 0, 0))
    # the smallest EPM Hamiltonian at ecutwfc = 11 Ry is 162 plane waves; the
    # count grows as ecutwfc^1.5 -- stay 3% below the estimate
    extra = min(nb + 40, int(0.97 * 162 * (ecw / 11.0) ** 1.5))
    wfn = with_list(set_key(set_key(src["WFN.in"], "NumberOfBands", extra), "EnergyCutoff", ecw),
                    n, (0.5, 0.5, 0.5), sh)
    wfnq = with_list(set_key(src["WFNq.in"], "EnergyCutoff", ecw), n, (0.5, 0.5, 0.5 + q0 * n), shq)
    wco = with_list(set_key(set_key(src["WFN_co.in"], "NumberOfBands", extra), "EnergyCutoff", ecw),
                    n, (0.0, 0.0, 0.0), un)
    for name, text in (("WFN.in", wfn), ("WFNq.in", wfnq), ("WFN_co.in", wco)):
        (d / name).write_text(text)
    for name in ("WFN", "WFNq", "WFN_co"):
        execute(d, "MeanField/EPM/epm2bgw.x", name + ".out", name + ".in", env)
    nbu = safe_nb([d / "WFN", d / "WFN_inner"], nb)
    qrows = [["0.000000000", "0.000000000", f"{q0:.9f}", "1.0", "1"]] + \
            [r[:3] + ["1.0", "0"] for r in un if any(float(x) != 0 for x in r[:3])]
    eps = src["epsilon.inp"]
    eps = set_key(set_key(eps, "epsilon_cutoff", ecuts), "number_bands", nbu)
    eps = rp.apply_override(eps, "qpoints", "\n".join("  " + "  ".join(r) for r in qrows) + "\n")
    (d / "epsilon.inp").write_text(eps)
    execute(d, "Epsilon/epsilon.real.x", "epsilon.out", None, env)
    sig = set_key(src["sig_GPP.inp"], "number_bands", nbu)
    if p["ecutb"] != ecw:
        sig = set_key(sig, "bare_coulomb_cutoff", p["ecutb"])
    (d / "sigma.inp").write_text(sig)
    execute(d, "Sigma/sigma.real.x", "sigma.out", None, env)
    text = (d / "sigma_hp.log").read_text()
    o = observable.observables(text)
    tabs = observable.parse(text)
    def state(k, band):
        s = observable.state(tabs[observable.KPOINTS[k]], band)
        return {c: s[c] for c in ("Emf", "X", "SX-X", "CH", "CH'", "Sig", "Eqp1", "Eqp1'", "Znk")}
    cX, cL = state("X", 5), state("L", 5)
    rec = dict(p, id=point_id(p), nb_used=nbu, seconds=time.time() - t0,
               O1=cX["Eqp1"] - cL["Eqp1"], O1_noremainder=cX["Eqp1'"] - cL["Eqp1'"],
               O2=o["O2_gap"], cbm_k=o["O2_cbm_k"], X=cX, L=cL,
               meanfield_O1=cX["Emf"] - cL["Emf"],
               nk_inner=len(un), nq=len(qrows),
               hashes={f: hashlib.sha256((d / f).read_bytes()).hexdigest()
                       for f in ("WFN", "WFNq", "WFN_inner", "eps0mat", "epsmat", "sigma_hp.log")})
    return rec


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("outroot")
    ap.add_argument("--grid", type=int, nargs="+", default=[2])
    ap.add_argument("--nb", type=int, nargs="+", default=[18])
    ap.add_argument("--ecuts", type=float, nargs="+", default=[7.0])
    ap.add_argument("--ecutwfc", type=float, nargs="+", default=[11.0])
    ap.add_argument("--ecutb", type=float, nargs="+", default=[None],
                    help="bare_coulomb_cutoff; default max(ecutwfc, ecuts)")
    ap.add_argument("--jobs", type=int, default=16)
    ap.add_argument("--results", default=str(HERE / "data/e2_results.jsonl"))
    a = ap.parse_args(argv)
    res = pathlib.Path(a.results)
    done = set()
    if res.exists():
        done = {json.loads(l)["id"] for l in res.read_text().splitlines() if l.strip()}
    pts = [dict(N=N, nb=nb, ecuts=ec, ecutwfc=ew, ecutb=eb if eb is not None else max(ew, ec))
           for N in a.grid for nb in a.nb for ec in a.ecuts for ew in a.ecutwfc for eb in a.ecutb]
    pts = [p for p in pts if point_id(p) not in done]
    print(f"{len(pts)} points to run", flush=True)
    with mp.Pool(a.jobs) as pool:
        for rec in pool.imap_unordered(run_point, [(a.outroot, p) for p in pts]):
            if "error" in rec:
                print(f"{rec['id']:28s} FAILED {rec['error']}", flush=True)
                with res.with_suffix(".errors.jsonl").open("a") as fh:
                    fh.write(json.dumps(rec) + "\n")
                continue
            with res.open("a") as fh:
                fh.write(json.dumps(rec) + "\n")
            print(f"{rec['id']:28s} nb_used {rec['nb_used']:3d}  O1 {rec['O1']*1e3:+9.3f} meV  "
                  f"O1' {rec['O1_noremainder']*1e3:+9.3f}  {rec['seconds']:.0f}s", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
