#!/usr/bin/env python3
"""A2 Step 1: layer-1 reproduction of production CD sigma_hp.log columns.

    python3 bgw/endpoint/a2_repro.py [--out bgw/endpoint/data/a2_repro.json]

(1) the full diagonal table (3 k-points x bands 1-8) of ~/bgw-e-runs/a2-cd;
(2) the X and L states of the variant runs a2-cd-brd0.1 (eta 0.1),
    a2-cd-fine (eta 0.02, real step 0.05 eV, 60 imaginary frequencies) and
    a2-cd-nimag15 (15 imaginary frequencies), each against its own eps files;
(3) counterfactual conventions on a2-cd X and L: each changes one transcribed
    convention and must move some printed column by more than print precision
    (otherwise the gate cannot tell that convention apart and we say so).
Print precision: 1e-6 eV (unprimed columns), 1e-5 eV (primed columns, f11.5).
"""
import argparse
import contextlib
import json
import pathlib
import sys

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import spec  # noqa: E402
import spec_cd as S  # noqa: E402

RUNS = pathlib.Path.home() / "bgw-e-runs"
COLS = ("X", "ReRes", "ImRes", "ReInt", "ReCor", "ReSig", "ReIntp", "ReCorp", "ReSigp")
HALF_ULP = {c: (5e-6 if c.endswith("p") else 5e-7) for c in COLS}


def compare(cd, rundir, ik, bands):
    prod = S.read_hp(pathlib.Path(rundir) / "sigma_hp.log", ik + 1)
    rows = S.table(cd, cd.run.kpts[ik], bands)
    out = []
    for r in rows:
        p = prod[r["bands"][0]]
        out.append(dict(bands=r["bands"], ours={c: r[c] for c in COLS},
                        prod={c: p[c] for c in COLS},
                        diff={c: r[c] - p[c] for c in COLS}))
    return out


def worst(rows):
    return {c: max(abs(r["diff"][c]) for r in rows) for c in COLS}


# ------------------------------------------------------- counterfactuals

@contextlib.contextmanager
def patched(name, fn):
    old = getattr(S, name)
    setattr(S, name, fn(old))
    try:
        yield
    finally:
        setattr(S, name, old)


def m_nearest(old):
    def f(grid, w):
        i, f1, f2 = old(grid, w)
        return (i, 1.0, 0.0) if f1 >= f2 else (i, 0.0, 1.0)
    return f


def m_no_tolsmall(old):
    """TOL_SMALL = 1e-6 replaced by 1e-12: wx = 0 terms stay on the wx >= 0
    side (without any shift wx is exactly 0.0 here and atan(x/0) = pi/2 in
    Fortran, i.e. the same selection); tests the 1e-6 eV offset itself."""
    def f(cd, e_lk):
        freq0, iw = old(cd, e_lk)
        return freq0 - spec.TOL_SMALL + 1e-12, iw
    return f


def m_tol_negative(old):
    def f(cd, e_lk):
        freq0, iw = old(cd, e_lk)
        return freq0 - 2 * spec.TOL_SMALL, iw        # E = Eo - 1e-6: wx = 0 terms leave
    return f


def m_last_not_mirrored(old):
    def f(imag_freqs, wx):
        w = old(imag_freqs, wx)
        fl = imag_freqs
        start = (fl[-2] + fl[-1]) * 0.5
        w[-1] = np.arctan(fl[-1] / wx) - np.arctan(start / wx)
        return w
    return f


def m_trapezoid(old):
    """piecewise-linear sW with the same atan kernel replaced by trapezoid in w."""
    def f(imag_freqs, wx):
        fl = imag_freqs
        k = wx / (wx * wx + fl * fl)
        h = np.diff(fl)
        w = np.zeros(len(fl))
        w[:-1] += 0.5 * h
        w[1:] += 0.5 * h
        return w * k
    return f


def m_nowings(old):
    def f(cd, q, blocks=None):
        # undo the q != 0 wing scalings by recomputing without them
        Gs, eps, info = old(cd, q, blocks)
        if not info["is0"]:
            run = cd.run
            z = int(np.flatnonzero(np.all(Gs == S.spec.Screening.mapping(cd.scr, q)[4], axis=1))[0])
            others = np.arange(len(Gs)) != z
            qlen = np.sqrt(run.cr.norm2(q))
            o, v0 = cd.oq(tuple(q)), cd.vb(tuple(q + Gs[0]))
            eps[:, z, others] /= o * qlen / (8 * np.pi)
            eps[:, others, z] /= o / (v0 * qlen)
        return Gs, eps, info
    return f


def m_first_op(cd):
    return spec.Screening(cd.run, cd.vb, cd.oq, choose_op="first")


COUNTERFACTUALS = {
    "residue: nearest grid point instead of linear interpolation": ("interp_index", m_nearest),
    "eval point: +1e-12 instead of +TOL_SMALL in freq0": ("eval_energy", m_no_tolsmall),
    "eval point: E = Eo - 1e-6 (wx = 0 residues dropped)": ("eval_energy", m_tol_negative),
    "cd_int_method 0: last interval not mirrored": ("cd_int0_weights", m_last_not_mirrored),
    "imaginary integral: trapezoid in w on the file frequencies instead of atan weights": ("cd_int0_weights", m_trapezoid),
    "wings: no q != 0 scaling": ("ff_at", m_nowings),
}


def counterfactuals(cd, rundir):
    res = {}
    base = {n: compare(cd, rundir, ik, b) for n, (ik, b) in S.STATES.items()}
    for label, (name, fn) in COUNTERFACTUALS.items():
        with patched(name, fn):
            rows = {n: compare(cd, rundir, ik, b) for n, (ik, b) in S.STATES.items()}
        res[label] = _moved(rows)
    saved = cd.scr
    cd.scr = m_first_op(cd)
    try:
        rows = {n: compare(cd, rundir, ik, b) for n, (ik, b) in S.STATES.items()}
    finally:
        cd.scr = saved
    res["symmetry: first-match op instead of last"] = _moved(rows)
    return res, {n: worst(v) for n, v in base.items()}


def _moved(rows):
    w = {n: worst(v) for n, v in rows.items()}
    ratio = max(w[n][c] / HALF_ULP[c] for n in w for c in COLS)
    o1 = (rows["X"][0]["ours"]["ReCor"] - rows["L"][0]["ours"]["ReCor"]) * 1e3
    return dict(worst=w, max_ratio_to_half_print_unit=ratio, detected=bool(ratio > 1.0),
                O1_cor_meV=o1)


def main(out=None):
    result = {}
    cd = S.CDSetup(RUNS / "a2-cd")
    full = [compare(cd, RUNS / "a2-cd", ik, list(range(1, 9))) for ik in range(3)]
    result["a2-cd_full_table"] = {"rows": full, "worst": worst([r for f in full for r in f])}
    print("a2-cd full table worst |diff| (eV):", result["a2-cd_full_table"]["worst"], flush=True)
    result["counterfactuals"], result["baseline_worst"] = counterfactuals(cd, RUNS / "a2-cd")
    for k, v in result["counterfactuals"].items():
        print(f"  {k}: detected={v['detected']} ratio={v['max_ratio_to_half_print_unit']:.3g}"
              f" O1_cor={v['O1_cor_meV']:.4f} meV", flush=True)
    result["variants"] = {}
    for var in ("a2-cd-brd0.1", "a2-cd-fine", "a2-cd-nimag15"):
        c2 = S.CDSetup(RUNS / var)
        rows = {n: compare(c2, RUNS / var, ik, b) for n, (ik, b) in S.STATES.items()}
        result["variants"][var] = dict(
            eta=c2.eta, nreal=c2.nreal, nimag=c2.nimag, step=float(c2.grid[1] - c2.grid[0]),
            rows=rows, worst=worst([r for v in rows.values() for r in v]),
            O1_cor_prod_meV=(rows["X"][0]["prod"]["ReCor"] - rows["L"][0]["prod"]["ReCor"]) * 1e3,
            O1_cor_ours_meV=(rows["X"][0]["ours"]["ReCor"] - rows["L"][0]["ours"]["ReCor"]) * 1e3)
        print(var, result["variants"][var]["worst"], flush=True)
    if out:
        pathlib.Path(out).write_text(json.dumps(result, indent=1, default=float) + "\n")
    return result


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out")
    main(ap.parse_args().out)
