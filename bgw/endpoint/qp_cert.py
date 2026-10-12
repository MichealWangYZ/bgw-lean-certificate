#!/usr/bin/env python3
"""Approximation layer A1, certified: roots of the full GPP quasiparticle
equation for the two O1 states, versus BerkeleyGW's linearised Eqp1.

    python3 bgw/endpoint/qp_cert.py RUNDIR --guess-X 4.1944 --guess-L 4.1256 [--out F]

Specification: spec A of cert.py (production conventions, exact mini-BZ
Coulomb averages), evaluated in rigorous interval arithmetic on WFN, WFNq,
WFN_inner, RHO. With Vxc = 0 (asserted by spec.Run) the QP equation of a
degenerate multiplet is

    f(E) = Emf + Sigma(E) - E = 0,   Sigma(E) = X + SX(E) + CH(E) + achcor,

multiplet-averaged exactly as in the diagonal table.

A root is certified on a bracket B = [a, b] when
  (i)  the interval evaluation of Sigma over the whole of B decides every GPP
       branch condition (no undecided generic / near-pole / sexcut / |wx|
       threshold) and meets no possibly-zero denominator -- then every mode
       takes one fixed branch on B, Sigma is a rational function of E without
       poles there, so f is continuous on B; and
  (ii) f(a) > 0 > f(b) certainly (point evaluations).
The intermediate value theorem then gives a root in B. The bracket is then
shrunk by bisection with certified endpoint signs (continuity on the original
bracket covers every sub-bracket).

Uniqueness in the whole energy window is NOT certified: qp_full.py scans
[Emf-12, Emf+2] eV on a 0.1 eV grid and finds one sign change per state.
"""
import argparse
import json
import pathlib
import sys
import time

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import bgwio  # noqa: E402
import cert  # noqa: E402
import iv  # noqa: E402
import spec  # noqa: E402
from iv import I  # noqa: E402


class QPEquation:
    def __init__(self, sig, k, bands):
        self.sig, self.k, self.bands = sig, k, bands
        self.pre = sig.prepare(k, bands)
        run = sig.run
        # E-independent parts: X and the static remainder, and per-q modes
        self.static = I.exact(0.0)
        self.qdata = []
        nb = len(bands)
        for q in run.qlist:
            Gk, ck = self.pre["Gk"], self.pre["ck"]
            Gb, _ = run.sphere(q, run.ecutb)
            Gq, cq, Eq = cert.real_coeffs(run.wf, tuple(k - q))
            Mb = cert.mtxel_iv(Gk, ck, Gq, cq[:run.nocc], Gb)
            vbx = I(np.array([sig.coul.vbar(q + g).lo for g in Gb]),
                    np.array([sig.coul.vbar(q + g).hi for g in Gb])) * sig.fact
            X = -(Mb.sqr() * vbx.reshape(1, 1, -1)).sum(axis=2).sum(axis=1)
            Gs, eps = sig.eps_at(q)
            m = sig.modes(q, Gs, eps)
            v, Ie = m["v"], m["Ie"]
            n = len(Gs)
            Iex = eps - I.exact(np.eye(n))
            pos = np.array([[self.pre["chidx"].get(tuple(g - gp), -1) for gp in Gs] for g in Gs])
            okt = Iex.abs().certainly_ge(cert.TOL_SMALL) & (pos >= 0)
            okf = Iex.abs().certainly_lt(cert.TOL_SMALL) | (pos < 0)
            if np.any(~okt & ~okf):
                raise NotImplementedError("undecided static-CH threshold")
            COR = I.exact(np.zeros(nb))
            rho_n = self.pre["rho_n"]
            for a in range(nb):
                A = I(np.where(pos >= 0, rho_n.lo[a][np.where(pos >= 0, pos, 0)], 0.0),
                      np.where(pos >= 0, rho_n.hi[a][np.where(pos >= 0, pos, 0)], 0.0))
                COR[a] = COR[a] + I.exact(0.25) * (iv.select(okt, okf, A * Iex, 0.0).sum(axis=0) * v).sum(axis=0)
            M = cert.mtxel_iv(Gk, ck, Gq, cq[:run.nbands], Gs)
            for n1 in range(run.nbands):
                for a in range(nb):
                    x = M[a, n1]
                    achs = I.exact(0.5) * ((x * v) * iv.matvec(-Ie.T, x)).sum()
                    COR[a] = COR[a] - I.exact(0.5) * achs
            self.static = self.static + (X + COR).sum() / I.exact(float(nb))
            self.qdata.append((m, M, Eq))
        self.emf = self.pre["e_lk"].sum() / I.exact(float(nb))

    def sigma(self, E, strict=True):
        """Interval Sigma(E) (eV) for an energy interval E (eV). strict: refuse an
        undecided |wx| < TOL_Zero clamp (needed for continuity); otherwise the
        hull of both branch values is taken (sound, no continuity)."""
        run = self.sig.run
        nb = len(self.bands)
        dyn = I.exact(0.0)
        for m, M, Eq in self.qdata:
            v = m["v"]
            for n1 in range(run.nbands):
                e1 = I.exact(Eq[n1]) * cert.RYD
                occ = n1 < run.nocc
                wx = E - e1
                tz = wx.abs().certainly_lt(cert.TOL_ZERO)
                if strict and np.any(~tz & ~wx.abs().certainly_ge(cert.TOL_ZERO)):
                    raise NotImplementedError("undecided |wx| < TOL_Zero")
                wx = iv.select(tz, ~tz, cert.TOL_ZERO, wx)
                ssx, sch = self.sig.kernel(wx, m, occ)
                for a in range(nb):
                    x = M[a, n1]
                    xv = x * v
                    dyn = dyn + I.exact(0.5) * (xv * iv.matvec(sch.T, x)).sum()
                    if occ:
                        dyn = dyn - (xv * iv.matvec(ssx.T, x)).sum()
        return (self.static + dyn / I.exact(float(nb))) * cert.RYD

    def f(self, E, strict=True):
        return self.emf + self.sigma(E, strict) - E


def undecided():
    return sum(v for k, v in cert.STATS.items() if k.startswith("undecided"))


def certify_root(qp, guess, halves=(1e-3, 3e-4, 1e-4, 3e-5, 1e-5, 3e-6), steps=30):
    """Try brackets of decreasing half-width around `guess` until one has a
    fixed branch structure (continuity) and certified endpoint signs; then
    bisect. Returns (a, b, info) with a record of every attempt."""
    attempts = []
    for half in halves:
        a, b = guess - half, guess + half
        snap = dict(cert.STATS)
        Fb = qp.f(I(a, b))
        und = {k: cert.STATS.get(k, 0) - snap.get(k, 0) for k in cert.STATS
               if k.startswith("undecided") and cert.STATS.get(k, 0) != snap.get(k, 0)}
        if und:
            attempts.append(dict(half=half, continuity=False, undecided=und))
            continue
        fa, fb = qp.f(I.exact(a)), qp.f(I.exact(b))
        if not (fa.lo > 0 and fb.hi < 0):
            attempts.append(dict(half=half, continuity=True, signs=[[float(fa.lo), float(fa.hi)],
                                                                    [float(fb.lo), float(fb.hi)]]))
            continue
        attempts.append(dict(half=half, continuity=True, certified=True))
        for _ in range(steps):
            c = 0.5 * (a + b)
            fc = qp.f(I.exact(c))
            if fc.lo > 0:
                a = c
            elif fc.hi < 0:
                b = c
            else:
                break                        # the enclosure of f(c) contains 0: stop
        return a, b, dict(attempts=attempts, bracket_used=[guess - half, guess + half],
                          f_on_bracket=[float(Fb.lo), float(Fb.hi)])
    raise ValueError(f"no certifiable bracket around {guess}: {attempts}")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("rundir")
    ap.add_argument("--coulomb", default=str(HERE / "data/coulomb_cert.json"))
    ap.add_argument("--guess-X", type=float, required=True)
    ap.add_argument("--guess-L", type=float, required=True)
    ap.add_argument("--out")
    a = ap.parse_args(argv)
    t0 = time.time()
    cert.STATS.clear()                   # report this invocation's counts only
    run = spec.Run(a.rundir)
    rho = bgwio.read_rho(pathlib.Path(a.rundir) / "RHO")
    coul = cert.CertCoulomb(a.coulomb)
    qs = [(run.eps0["q"][0]["q"], True)] + [(b["q"], False) for b in run.eps["q"]]
    blocks = []
    for q, q0 in qs:
        Gs, E, beta, delta = cert.epsinv_iv(a.rundir, run.nbands, run.ecuts, q, q0)
        blocks.append((Gs, E))
    sig = cert.SigmaIV(run, coul, blocks, rho)
    out = {}
    for name, k, bands, g in (("X", run.kpts[2], [5, 6], a.guess_X), ("L", run.kpts[1], [5], a.guess_L)):
        qp = QPEquation(sig, k, bands)
        lo, hi, info = certify_root(qp, g)
        out[name] = dict(root=[lo, hi], **info)
        print(f"{name}: certified root of the GPP QP equation in [{lo:.12f}, {hi:.12f}] eV", flush=True)
    o1 = (out["X"]["root"][0] - out["L"]["root"][1], out["X"]["root"][1] - out["L"]["root"][0])
    lin = json.loads((HERE / "data/cert_o1.json").read_text())
    res = {"roots": out, "O1_full_QP": list(o1),
           "O1_linearised_specA": [lin["O1_lo"], lin["O1_hi"]],
           "Eqp1_linearised_specA": {"X": lin["Eqp1_X"], "L": lin["Eqp1_L"]},
           "branch_stats": dict(cert.STATS), "seconds": time.time() - t0,
           "uniqueness": "not certified; one sign change per state on a 0.1 eV grid over [Emf-12, Emf+2] (qp_full.py)"}
    print(f"O1 full QP equation in [{o1[0]*1e3:.6f}, {o1[1]*1e3:.6f}] meV "
          f"(linearised Eqp1: {lin['O1_lo']*1e3:.6f} meV)")
    if a.out:
        pathlib.Path(a.out).write_text(json.dumps(res, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
