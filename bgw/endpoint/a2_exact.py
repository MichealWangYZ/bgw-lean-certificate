#!/usr/bin/env python3
"""A2 Step 2: the CD formula of spec_cd.py without BerkeleyGW's numerical
shortcuts, on the same mean-field files, symmetry map, Coulomb averages and
wing conventions.

    python3 bgw/endpoint/a2_exact.py [RUNDIR] [--out data/a2_exact.json]

What is replaced (and nothing else):
  * residue: W at the exact real frequency |E - e_n1| + i eta, eps^-1 there
    computed directly (spec_cd.epsinv_ff, chi0 from WFN/WFNq; reproduces the
    file's eps^-1 to <= 4e-11), instead of linear interpolation on the 0.1 eV
    grid; eta = BerkeleyGW's broadening unless varied.
  * imaginary-axis integral: (1/pi) int_0^inf sW(i w) wx/(wx^2 + w^2) dw with
    sW(i w) computed directly at every node, instead of 30 file frequencies
    with piecewise-constant sW. Quadrature: subtract sW(0),
        I = sW(0) sgn(wx)/2 + (1/pi) int_0^inf [sW(iw) - sW(0)] wx/(wx^2+w^2) dw,
    the remaining integral by Gauss-Legendre panels in u = ln w on
    [w_lo, w_hi] (log variable change for the infinite range), plus the two
    end pieces in closed form assuming sW(iw) - sW(0) = 0 below w_lo and
    = -sW(0) above w_hi (sW -> 0 as w -> inf since eps^-1 -> 1). Convergence
    is shown by refinement (panels, nodes, w_lo, w_hi).
  * static remainder: Re eps^-1(0 + i eta) computed directly (identical to the
    file's grid point 1 at the production eta; varied with eta otherwise).
Float evidence throughout.
"""
import argparse
import json
import pathlib
import sys

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import spec  # noqa: E402
import spec_cd as S  # noqa: E402
from spec import RYD  # noqa: E402

DEFAULT_RUN = pathlib.Path.home() / "bgw-e-runs/a2-cd"


class DirectEps:
    """eps^-1 on the target sphere at q for arbitrary complex frequencies,
    computed from WFN/WFNq and carried through spec_cd.ff_at (same symmetry
    map, phases and fixwings_dyn as the file matrices)."""

    def __init__(self, cd, rundir):
        self.cd = cd
        self.er = spec.EpsilonRun(rundir, cd.run.nbands, cd.run.ecuts)
        self._cache = {}

    def block(self, j, W):
        key = (j, tuple(np.round(np.asarray(W, complex), 14)))
        if key not in self._cache:
            qi, b, is0 = self.cd.scr.irr[j]
            self._cache[key] = S.epsinv_ff(self.er, b["q"], np.asarray(W, complex), q0=is0)
        return self._cache[key]

    def at(self, q, W, j):
        Gs, eps, info = S.ff_at(self.cd, q, blocks={j: self.block(j, W)})
        return Gs, eps


def log_nodes(w_lo, w_hi, panels_per_decade, order):
    """Gauss-Legendre nodes/weights in u = ln w, returned as (w, weight dw)."""
    t, wt = np.polynomial.legendre.leggauss(order)
    a, b = np.log(w_lo), np.log(w_hi)
    npan = max(1, int(np.ceil((b - a) / np.log(10) * panels_per_decade)))
    edges = np.linspace(a, b, npan + 1)
    us, ws = [], []
    for lo, hi in zip(edges[:-1], edges[1:]):
        us.append(0.5 * (hi - lo) * t + 0.5 * (hi + lo))
        ws.append(0.5 * (hi - lo) * wt)
    u, wu = np.concatenate(us), np.concatenate(ws)
    w = np.exp(u)
    return w, wu * w                                   # dw = w du


def lorentz_integral(sW0, D, wx, w, dw, w_lo, w_hi):
    """(1/pi) int_0^inf sW(iw) wx/(wx^2+w^2) dw with sW = sW0 + D (D on nodes)."""
    body = np.sum(D * dw * wx / (wx * wx + w * w)) / np.pi
    tail = -sW0 * (0.5 * np.sign(wx) - np.arctan(w_hi / wx) / np.pi)   # D = -sW0 above w_hi
    return 0.5 * np.sign(wx) * sW0 + body + tail                        # D = 0 below w_lo


class Exact:
    def __init__(self, cd, direct, eta=None, quad=(1e-4, 1e5, 4, 12)):
        self.cd, self.de = cd, direct
        self.eta = cd.eta if eta is None else eta
        self.w_lo, self.w_hi, ppd, order = quad
        self.w, self.dw = log_nodes(self.w_lo, self.w_hi, ppd, order)
        self.stats = {"n_res": 0, "max_im_sW": 0.0, "res_interp_minus_exact": []}

    def residue(self, q, Gs, eps_file, pairs, info):
        """Exact-frequency residue for every pair (0 where production has none)."""
        out = np.zeros(len(pairs), complex)
        sel = [(i, p) for i, p in enumerate(pairs) if (p[2] >= 0.0) != p[5]]
        if not sel:
            return out
        W = np.array([abs(p[2]) + 1j * self.eta for _, p in sel])
        _, epsW = self.de.at(q, W, info["j"])
        eye = np.eye(len(Gs))
        for m, (i, (a, n1, wx, x, xc, occ)) in enumerate(sel):
            sgn = 1.0 if wx >= 0 else -1.0
            out[i] = -sgn * np.sum((x @ (eye - epsW[m])) * xc)
            self.stats["n_res"] += 1
        return out

    def integral(self, q, Gs, eps_file, pairs, info):
        W = np.concatenate([[0.0], self.w]) * 1j
        _, epsI = self.de.at(q, W, info["j"])
        II = (np.eye(len(Gs))[None] - epsI).real
        out = np.zeros(len(pairs))
        for i, (a, n1, wx, x, xc, occ) in enumerate(pairs):
            sW = np.einsum("g,wgh,h->w", x, II, xc)
            self.stats["max_im_sW"] = max(self.stats["max_im_sW"], float(np.abs(sW.imag).max()))
            sW = sW.real
            out[i] = lorentz_integral(sW[0], sW[1:] - sW[0], wx, self.w, self.dw,
                                      self.w_lo, self.w_hi)
        return out

    def static(self, q, info):
        """Target-sphere eps^-1(0 + i eta) for the static remainder."""
        return self.de.at(q, np.array([1j * self.eta]), info["j"])[1][0]


def terms(cd, k, bands, residue=None, integral=None, static=None):
    """spec_cd.cd_terms with an optional replacement of the remainder's
    eps^-1(0 + i eta); returns multiplet-averaged (Res, Int, achcor) in eV."""
    nb = np.array(bands) - 1
    if static is None:
        RES, INT, cor, e = S.cd_terms(cd, k, nb, residue=residue, integral=integral)
    else:
        orig = S.ff_at

        def patched(cd_, q, blocks=None):
            Gs, eps, info = orig(cd_, q, blocks)
            if blocks is None:
                eps = eps.copy()
                eps[0] = static(q, info)
            return Gs, eps, info
        S.ff_at = patched
        try:
            RES, INT, cor, e = S.cd_terms(cd, k, nb, residue=residue, integral=integral)
        finally:
            S.ff_at = orig
    grp = spec.multiplets_from_energies(e)
    assert len(grp) == 1, "bands must form one multiplet"
    return dict(Res=complex(np.mean(RES)) * RYD, Int=float(np.mean(INT)) * RYD,
                achcor=float(np.mean(cor)) * RYD)


def summary(t):
    return dict(ReRes=t["Res"].real, ImRes=t["Res"].imag, Int=t["Int"], achcor=t["achcor"],
                Cor=t["Res"].real + t["Int"] + t["achcor"])


def study(rundir=DEFAULT_RUN, etas=(0.1, 0.05, 0.02, 0.01),
          quads=((1e-4, 1e5, 2, 8), (1e-4, 1e5, 4, 12), (1e-6, 1e6, 6, 16))):
    cd = S.CDSetup(rundir)
    de = DirectEps(cd, rundir)
    out = {"run": str(rundir), "eta_production": cd.eta, "states": {}}
    for name, (ik, bands) in S.STATES.items():
        k = cd.run.kpts[ik]
        st = {"bands": bands}
        st["production_repro"] = summary(terms(cd, k, bands))
        # (a) exact residue only, production integral
        ex = Exact(cd, de, quad=quads[1])
        st["exact_residue_only"] = summary(terms(cd, k, bands, residue=ex.residue))
        # (b) production residue, exact integral at each quadrature (refinement)
        st["exact_integral_only"] = {}
        for qd in quads:
            ex = Exact(cd, de, quad=qd)
            st["exact_integral_only"][str(qd)] = summary(terms(cd, k, bands, integral=ex.integral))
        # (c) both, at production eta and the eta scan (remainder at the same eta)
        st["exact"] = {}
        for eta in sorted(set(etas) | {cd.eta}, reverse=True):
            ex = Exact(cd, de, eta=eta, quad=quads[1])
            st["exact"][f"{eta:g}"] = summary(terms(cd, k, bands, residue=ex.residue,
                                                    integral=ex.integral, static=ex.static))
            st["exact"][f"{eta:g}"]["n_residue_terms"] = ex.stats["n_res"]
            st["exact"][f"{eta:g}"]["max_im_sW"] = ex.stats["max_im_sW"]
        out["states"][name] = st
        print(name, json.dumps(st, indent=1), flush=True)
    X, L = out["states"]["X"], out["states"]["L"]
    diff = lambda a, b: {kk: a[kk] - b[kk] for kk in ("ReRes", "Int", "achcor", "Cor")}
    out["O1_correlation"] = {
        "production_repro": diff(X["production_repro"], L["production_repro"]),
        "exact_residue_only": diff(X["exact_residue_only"], L["exact_residue_only"]),
        "exact_integral_only": {qd: diff(X["exact_integral_only"][qd], L["exact_integral_only"][qd])
                                for qd in X["exact_integral_only"]},
        "exact": {e: diff(X["exact"][e], L["exact"][e]) for e in X["exact"]},
    }
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("rundir", nargs="?", default=str(DEFAULT_RUN))
    ap.add_argument("--out")
    a = ap.parse_args()
    r = study(pathlib.Path(a.rundir))
    print(json.dumps(r["O1_correlation"], indent=1))
    if a.out:
        pathlib.Path(a.out).write_text(json.dumps(r, indent=1) + "\n")
