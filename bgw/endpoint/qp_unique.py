#!/usr/bin/env python3
"""Approximation layer A1, root enumeration: ALL roots of the full GPP
quasiparticle equation of each O1 state in an energy window W, each certified
isolated.

    python3 bgw/endpoint/qp_unique.py RUNDIR [--window -10000 10000] [--out F]

f(E) = Emf + Sigma(E) - E as in qp_cert.py (spec A, rigorous intervals).
W is bisected adaptively into closed boxes J, each of one of three kinds:

 (a) f has no zero on J: the interval evaluation f(J) excludes 0 (undecided
     branches take the hull of both branch values, so this needs no
     continuity and is valid for the discontinuous f);
 (b) f has no zero on J, at a jump of f across 0 where one GPP branch
     switches: exactly one branch condition is undecided on J, and f with
     that condition forced true, and forced false, both exclude 0 on J
     (split_excludes_zero);
 (c) where neither works on a box of width < 1e-9 eV, an isolating bracket
     B around it (isolate_root): every GPP branch condition decided on B (f
     continuous there), f'(B) excludes 0 by an enclosure of the E-derivative
     of the branch values (kernel_d), and f has certainly opposite signs at
     the ends of B. Then B holds exactly one root.
No bracket contains a point where the source's formula divides by zero
(wx = w or wx = -w for some mode), so no IEEE NaN convention enters (a) or
(c); the convention-free kernel takes the hull of both conventions at
wx = w. The brackets come out ordered and disjoint; GW/Endpoint/QPUnique.lean
(qp_roots_enumerated) turns (a)-(c) into: the zeros of f in W are exactly one
point per bracket. The quasiparticle weight of each root is enclosed as
Z = -1/f'(B).

The window is a stated hypothesis, not all of R: the spec's convention for
invalid GPP modes (wtilde = 1e12 eV, mtxel_cor.f90 static limit) places
artificial structure near |E| ~ 1e12 eV, about which nothing is claimed.
"""
import argparse
import contextlib
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
import qp_cert  # noqa: E402
import spec  # noqa: E402
from iv import I  # noqa: E402


class Undecided(Exception):
    pass


def kernel_d(wx, dwx, m, occupied):
    """E-derivatives (dssx, dsch) of the kernel values cert.SigmaIV.kernel
    selects, on an interval where EVERY branch condition is decided (raises
    Undecided otherwise). dwx is 1 or 0 per (the |wx| < TOL_Zero clamp makes
    wx constant). Branch values (mtxel_cor.f90:1766-1850, real flavor):
      generic  sch = wt I/(wx - wt)          ssx = wt^2 I/(wx^2 - wt^2)
      near     sch = 0                       ssx = -I wt/(2 (wx + wt))
      clamped / zero branch: 0."""
    wt, Ie, keep = m["wt"], m["Ie"], m["keep"]
    G2, lim = cert.GAMMA ** 2, 1.0 / (cert.TOL_SMALL * 4.0)
    wdiff = wx - wt
    wdiffr = wdiff.sqr()
    wt2 = wt.sqr()
    gen_t = keep & wdiffr.certainly_gt(G2) & wt2.certainly_lt(wdiffr * I.exact(lim))
    gen_f = ~keep | wdiffr.certainly_le(G2) | wt2.certainly_ge(wdiffr * I.exact(lim))
    if np.any(~gen_t & ~gen_f):
        raise Undecided("generic")
    one = I.exact(1.0)
    safe_wd = iv.select(gen_t, gen_f, wdiff, one)
    dsch = iv.select(gen_t, gen_f, -(wt * Ie) / safe_wd.sqr(), 0.0) * I.exact(dwx)
    if not occupied:
        return None, dsch
    neg_t, neg_f = wx.certainly_lt(0.0), wx.certainly_ge(0.0)
    den = wx.sqr() - wt2
    lim_g = wt2 * I.exact(1.0 / cert.SEXCUT)
    cg_t, cg_f = den.abs().certainly_lt(lim_g), den.abs().certainly_ge(lim_g)
    clampg_t, clampg_f = cg_t & neg_t, cg_f | neg_f
    if np.any(gen_t & ~clampg_t & ~clampg_f):
        raise Undecided("sexcut generic")
    safe_den = iv.select(gen_t & clampg_f, ~(gen_t & clampg_f), den, one)
    dssx_g = iv.select(clampg_t, clampg_f,
                       0.0, -(I.exact(2.0) * wx * wt2 * Ie) / safe_den.sqr())
    wd0 = wdiff.contains_zero()                  # as cert.kernel: undecided at wdiff = 0
    near_t = keep & wt2.certainly_gt(wdiffr * I.exact(cert.TOL_ZERO)) & ~wd0
    near_f = ~keep | wt2.certainly_le(wdiffr * I.exact(cert.TOL_ZERO))
    if np.any(gen_f & ~near_t & ~near_f):
        raise Undecided("near zero")
    den_n = I.exact(2.0) * (wx + wt)
    lim_n = wt * I.exact(1.0 / cert.SEXCUT)
    cn_t, cn_f = den_n.abs().certainly_lt(lim_n), den_n.abs().certainly_ge(lim_n)
    clampn_t, clampn_f = cn_t & neg_t, cn_f | neg_f
    if np.any(gen_f & near_t & ~clampn_t & ~clampn_f):
        raise Undecided("sexcut near")
    need_n = gen_f & near_t & clampn_f
    safe_dn = iv.select(need_n, ~need_n, wx + wt, one)
    if np.any(need_n & safe_dn.contains_zero()):
        raise ZeroDivisionError("near-pole derivative denominator")
    dssx_n = iv.select(clampn_t, clampn_f, 0.0, (Ie * wt) / (I.exact(2.0) * safe_dn.sqr()))
    dssx_nb = iv.select(near_t, near_f, dssx_n, 0.0)
    dssx = iv.select(gen_t, gen_f, dssx_g, dssx_nb) * I.exact(dwx)
    return dssx, dsch


def dsigma(qp, E):
    """Enclosure of dSigma/dE (dimensionless) on the energy interval E (eV)."""
    run = qp.sig.run
    nb = len(qp.bands)
    d = I.exact(0.0)
    for m, M, Eq in qp.qdata:
        v = m["v"]
        for n1 in range(run.nbands):
            e1 = I.exact(Eq[n1]) * cert.RYD
            occ = n1 < run.nocc
            wx = E - e1
            tz = wx.abs().certainly_lt(cert.TOL_ZERO)
            if np.any(~tz & ~wx.abs().certainly_ge(cert.TOL_ZERO)):
                raise Undecided("|wx| < TOL_Zero")
            dwx = np.where(tz, 0.0, 1.0)
            wx = iv.select(tz, ~tz, cert.TOL_ZERO, wx)
            dssx, dsch = kernel_d(wx, dwx, m, occ)
            for a in range(nb):
                x = M[a, n1]
                xv = x * v
                d = d + I.exact(0.5) * (xv * iv.matvec(dsch.T, x)).sum()
                if occ:
                    d = d - (xv * iv.matvec(dssx.T, x)).sum()
    # sigma() is in Ry (times RYD at the end) as a function of E in eV, with the
    # kernel's wx in eV: the RYD factor carries over unchanged
    return d / I.exact(float(nb)) * cert.RYD


def f_safe(qp, J):
    try:
        return qp.f(J, strict=False)
    except (ZeroDivisionError, NotImplementedError, FloatingPointError):
        return None


@contextlib.contextmanager
def forced(value):
    """Within the block, iv.select takes branch a (value True) or b (False)
    wherever its condition is undecided, instead of the hull."""
    orig = iv.select

    def sel(cond_true, cond_false, a, b):
        if value:
            return orig(~np.asarray(cond_false), np.asarray(cond_false), a, b)
        return orig(np.asarray(cond_true), ~np.asarray(cond_true), a, b)

    iv.select = sel
    try:
        yield
    finally:
        iv.select = orig


def _undecided():
    return sum(v for k, v in cert.STATS.items() if k.startswith("undecided"))


def split_excludes_zero(qp, J):
    """Branch split at a discontinuity. Suppose that on J exactly one branch
    condition of one mode is undecided per kernel call, that every kernel
    call with an undecided condition has IDENTICAL inputs (same mode set m,
    bit-identical wx interval, same occupation -- e.g. the two bands of a
    degenerate multiplet with equal float energies), and that the
    |wx| < TOL_Zero clamp is decided. Identical inputs give the identical
    condition, one predicate P(E). At every E in J, f(E) is then f_true(E) or
    f_false(E), f with P forced true / false on all of J (every other
    condition is decided on J, so forcing touches only P). If both interval
    values exclude 0, f has no zero in J; no continuity is needed, which is
    how a jump of f across 0 at a branch switch is certified root-free."""
    calls = []
    orig = cert.SigmaIV.kernel

    def rec(self, wx, m, occupied):
        before = _undecided()
        out = orig(self, wx, m, occupied)
        d = _undecided() - before
        if d:
            calls.append((d, id(m), wx.lo.tobytes(), wx.hi.tobytes(), occupied))
        return out

    cert.SigmaIV.kernel = rec
    try:
        qp.f(J, strict=True)
    except (ZeroDivisionError, NotImplementedError, FloatingPointError):
        return False
    finally:
        cert.SigmaIV.kernel = orig
    if not calls or any(c[0] != 1 for c in calls) or len({c[1:] for c in calls}) != 1:
        return False
    for value in (True, False):
        with forced(value):
            try:
                F = qp.f(J, strict=True)
            except (ZeroDivisionError, NotImplementedError, FloatingPointError):
                return False
        if F.contains_zero():
            return False
    return True


def isolate_root(qp, c, halves=(1e-4, 3e-5, 1e-5, 3e-6, 1e-6, 3e-7, 1e-7), steps=40):
    """Certify exactly one root of f near c. On a bracket B = [c-h, c+h]: every
    branch condition decided (f continuous), f'(B) excludes 0 (f strictly
    monotone), and f(c-h), f(c+h) have certainly opposite signs (IVT). Then
    bisect the root enclosure. Returns dict or None."""
    for h in halves:
        a, b = c - h, c + h
        before = _undecided()
        undef0 = cert.STATS.get("source_undefined_possible", 0)
        try:
            qp.f(I(a, b), strict=True)
            # every branch decided, and no point of B where the source's
            # formula divides by zero (so the claim needs no NaN convention)
            if _undecided() != before or cert.STATS.get("source_undefined_possible", 0) != undef0:
                continue
            fp = dsigma(qp, I(a, b)) - I.exact(1.0)
            fa, fb = qp.f(I.exact(a)), qp.f(I.exact(b))
        except (Undecided, ZeroDivisionError, NotImplementedError, FloatingPointError):
            continue
        if fp.contains_zero():
            continue
        sa = 1 if fa.lo > 0 else (-1 if fa.hi < 0 else 0)
        sb = 1 if fb.lo > 0 else (-1 if fb.hi < 0 else 0)
        if sa == 0 or sb == 0 or sa == sb:
            continue
        lo, hi = a, b
        for _ in range(steps):
            m = 0.5 * (lo + hi)
            fm = qp.f(I.exact(m))
            if (fm.lo > 0 and sa > 0) or (fm.hi < 0 and sa < 0):
                lo = m
            elif (fm.lo > 0 and sb > 0) or (fm.hi < 0 and sb < 0):
                hi = m
            else:
                break
        return dict(bracket=[a, b], root=[lo, hi], fprime=[float(fp.lo), float(fp.hi)],
                    sign_left=sa)
    return None


def cover(qp, lo, hi, min_width=1e-9, max_boxes=2_000_000, split_width=1e-6, roots=None):
    """Cover [lo, hi] by intervals on which f certainly has no zero. Returns
    (number of boxes, smallest width used, number of branch-split boxes) or
    raises if it cannot."""
    stack, n, wmin, nsplit = [(lo, hi)], 0, np.inf, 0
    while stack:
        a, b = stack.pop()
        # boxes may contain the finitely many points where the source divides
        # by zero (wx = -w; IEEE NaN, not a root under any convention): there
        # the enclosure uses the clamp value 0, the limit from both sides
        F = f_safe(qp, I(a, b))
        ok = F is not None and not F.contains_zero()
        if not ok and b - a < split_width and split_excludes_zero(qp, I(a, b)):
            ok, nsplit = True, nsplit + 1
        if ok:
            n += 1
            wmin = min(wmin, b - a)
            if n > max_boxes:
                raise RuntimeError("too many boxes")
            continue
        if b - a < min_width:
            r = isolate_root(qp, 0.5 * (a + b)) if roots is not None else None
            if r is None:
                raise RuntimeError(f"cannot exclude a root in [{a!r}, {b!r}]: f = {F}")
            roots.append(r)
            ra, rb = r["bracket"]
            # the bracket is certified; cover what is left of [a, b] and of the
            # pending boxes that overlap it
            pending = [(x, y) for x, y in stack]
            stack = []
            for x, y in pending + [(a, b)]:
                if x < ra:
                    stack.append((x, min(y, ra)))
                if y > rb:
                    stack.append((max(x, rb), y))
            continue
        c = 0.5 * (a + b)
        stack.append((c, b))
        stack.append((a, c))
    return n, wmin, nsplit


def build_sigma(rundir, coulomb=str(HERE / "data/coulomb_cert.json")):
    run = spec.Run(rundir)
    rho = bgwio.read_rho(pathlib.Path(rundir) / "RHO")
    coul = cert.CertCoulomb(coulomb)
    qs = [(run.eps0["q"][0]["q"], True)] + [(b["q"], False) for b in run.eps["q"]]
    blocks = [cert.epsinv_iv(rundir, run.nbands, run.ecuts, q, q0)[:2] for q, q0 in qs]
    return cert.SigmaIV(run, coul, blocks, rho)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("rundir")
    ap.add_argument("--coulomb", default=str(HERE / "data/coulomb_cert.json"))
    ap.add_argument("--window", type=float, nargs=2, default=[-1e4, 1e4])
    ap.add_argument("--out")
    a = ap.parse_args(argv)
    t0 = time.time()
    sig = build_sigma(a.rundir, a.coulomb)
    run = sig.run
    W = tuple(a.window)
    out = {"window_eV": list(W)}
    for name, k, bands in (("X", run.kpts[2], [5, 6]), ("L", run.kpts[1], [5])):
        qp = qp_cert.QPEquation(sig, k, bands)
        roots = []
        n, wmin, nsplit = cover(qp, W[0], W[1], roots=roots)
        roots.sort(key=lambda r: r["bracket"][0])
        for r0, r1 in zip(roots, roots[1:]):          # ordered, disjoint brackets
            if not r0["bracket"][1] < r1["bracket"][0]:
                raise RuntimeError(f"{name}: overlapping root brackets {r0} {r1}")
        for r in roots:
            if not (W[0] <= r["bracket"][0] and r["bracket"][1] <= W[1]):
                raise RuntimeError(f"{name}: bracket outside the window: {r}")
            lo, hi = r["fprime"]
            # quasiparticle weight Z = 1 / (1 - dSigma/dE) = -1 / f'
            z = I.exact(-1.0) / I(lo, hi)
            r["Z"] = [float(z.lo), float(z.hi)]
        out[name] = dict(roots=roots, boxes=n, branch_split_boxes=nsplit,
                         smallest_box=float(wmin))
        print(name, json.dumps(out[name]), flush=True)
    out["claim"] = ("for each state, the zeros of f(E) = Emf + Sigma(E) - E in the window "
                    "are exactly one point per listed bracket (qp_roots_enumerated)")
    out["seconds"] = time.time() - t0
    if a.out:
        pathlib.Path(a.out).write_text(json.dumps(out, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
