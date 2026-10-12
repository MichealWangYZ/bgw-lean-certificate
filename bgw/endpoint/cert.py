#!/usr/bin/env python3
"""E1.4: certified enclosure of O1 = Eqp1(X,c) - Eqp1(L,c) for the SPECIFICATION
evaluated in exact real arithmetic on the production mean-field files.

    python3 bgw/endpoint/cert.py RUNDIR [--coulomb data/coulomb_cert.json]
                                        [--out cert.json]

Specification (docs/ENDPOINT.md section 4) = the finite calculation BerkeleyGW
defines, with every production convention reproduced in spec.py (op choice,
wing placement, GPP branch rules, thresholds, static remainder, forward
difference), EXCEPT that the mini-BZ Coulomb averages are the exact integrals
the Monte Carlo estimates (enclosed by certcoulomb.py): spec A. Also enclosed:
O1 for each of the 48 symmetry ops Sigma could have used for the q = 0 cell,
and spec B, which averages the q = 0 cell over those 48 rotations of eps0mat
(the angular average of the q -> 0 limit for a cubic crystal) instead of the
single direction BerkeleyGW's irrbz picks.

Inputs are taken as exact reals: WFN, WFNq, WFN_inner, RHO (floats in the
files), bdot/celvol, and the decimal constants of the source (enclosed).
Global phases of unfolded states are dropped: every quantity used is
M(G) S conj(M(G')) or |M|^2 for one band pair, in which they cancel; the
remaining per-G phases are exactly +-1 (asserted).

Arithmetic: iv.py (rigorous outward-rounded intervals). A branch condition that
the enclosure cannot decide takes the hull of both branches and is counted;
a denominator whose enclosure contains 0 raises. The result states the
enclosure [lo, hi] of O1_spec, its width, and every undecided-branch count.
"""
import argparse
import functools
import json
import pathlib
import sys
import time

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import bgwio  # noqa: E402
import iv  # noqa: E402
import spec  # noqa: E402
from iv import I  # noqa: E402

RYD = I.around(13.60569253)           # Common/nrtype.f90:155 (decimal constant)
TOL_SMALL = 1e-6                      # thresholds are the source's doubles: taken
TOL_ZERO = 1e-12                      # as exactly those doubles (they define the rule)
GAMMA, SEXCUT, DW = 0.5, 4.0, 1.0     # exact in binary
# Branch-decision counters of the current main() (or qp_cert.main()) call. They
# are module state because SigmaIV.kernel increments them; each main() clears
# them first, so a report never carries counts from earlier in-process
# evaluations (e.g. qp_cert.certify_root's deliberately undecided brackets).
STATS = {}


def count(name, n):
    STATS[name] = STATS.get(name, 0) + int(n)


# ------------------------------------------------------------ exact inputs

def real_coeffs(wf, kp):
    """(G, real coefficient matrix) at kp with the global phase removed; the
    per-G phase exp(-2 pi i (M G).t) is asserted to be exactly +-1."""
    ik, iop, kg0 = wf.find(np.array(kp))
    M = wf.cr.mtrx[iop]
    W, t = wf.ops[iop]
    G = wf.w["kg"][ik]
    arg = 2 * ((M @ G.T).T @ t)                 # (M G).t in units of 1/2
    if not np.allclose(arg, np.rint(arg), atol=1e-9):
        raise ValueError("per-G phase is not +-1")
    sign = np.where(np.rint(arg).astype(int) % 2 == 0, 1.0, -1.0)
    Gnew = (M @ G.T).T - kg0
    return Gnew, wf.w["coef"][ik] * sign[None, :], wf.E[ik]


def norm2(bdot, v, shift=None):
    """Interval |v + shift|^2_B for float vectors v (rows) and an optional
    float vector `shift`, the sum formed in interval arithmetic (q0 + G is
    not exact in binary64)."""
    v = np.atleast_2d(v)
    comps = [I.exact(v[:, i]) + (I.exact(np.full(len(v), shift[i])) if shift is not None else 0.0)
             for i in range(3)]
    out = None
    for i in range(3):
        for j in range(3):
            term = comps[i] * I.exact(np.full(len(v), bdot[i, j])) * comps[j]
            out = term if out is None else out + term
    return out


def mtxel_iv(Gk, ck, Gq, cq, Gout):
    """M(n, n1, G) = sum_G2 ck(n, G2+G) cq(n1, G2), rigorous (real)."""
    idx = spec.gindex(Gk)
    pos = np.array([[idx.get(tuple(g2 + g), -1) for g in Gout] for g2 in Gq])  # (G2, G)
    acc = None
    for j in range(len(Gq)):
        p = pos[j]
        a = np.where(p[None, :] >= 0, ck[:, np.where(p >= 0, p, 0)], 0.0)       # (n, G)
        term = I.exact(a[:, None, :]) * I.exact(cq[None, :, j, None])          # (n, n1, G)
        acc = term if acc is None else acc + term
    return acc


# ------------------------------------------------------------ epsilon

def epsinv_iv(rundir, nbands, ecut, q, q0):
    er = spec.EpsilonRun(rundir, nbands, ecut)
    Gs, _ = spec.sphere_of(er.cr, er.gvec, q, ecut)
    n, nv = len(Gs), 4
    chi = I.exact(np.zeros((n, n)))
    for k in er.kfull:
        Gc, cc, Ec = real_coeffs(er.wf, tuple(k))
        src = er.wfq if q0 else er.wf
        Gv, cv, Ev = real_coeffs(src, tuple(np.round(k + q, 12)))
        M = mtxel_iv(Gv, cv[:nv], Gc, cc[nv:nbands], Gs)             # (v, c, G)
        for v in range(nv):
            for c in range(nbands - nv):
                eden = I.exact(1.0) / (I.exact(Ev[v]) - I.exact(Ec[nv + c]))
                x = M[v, c]
                chi = chi + (x.reshape(n, 1) * x.reshape(1, n)) * eden
    fact = I.exact(4.0) / (I.exact(float(len(er.kfull))) * I.exact(er.cr.celvol))
    chi = chi * fact
    vq = I.exact(8.0) * iv.PI / norm2(er.cr.bdot, Gs.astype(float), q)
    eps = I.exact(np.eye(n)) - chi * vq.reshape(n, 1)
    # exact power-of-two balancing eps' = S^-1 eps S, s_i ~ sqrt(v_i): the q0
    # head row carries 8 pi/|q0|^2 ~ 3e7 and would dominate any norm bound
    s = 2.0 ** np.rint(0.5 * np.log2(vq.mid()))
    scale = s[None, :] / s[:, None]                   # exact (powers of two)
    epsb = eps * I.exact(scale)                      # outward: exact unless subnormal
    invb, beta, delta = iv.inverse_cw(epsb)
    back = s[:, None] / s[None, :]
    inv = invb * I.exact(back)
    return Gs, inv, beta, delta


# ---------------------------------------------------------- Coulomb input

class CertCoulomb:
    def __init__(self, path):
        d = json.loads(pathlib.Path(path).read_text())
        self.v = {self._key(k): I(lo, hi) for k, (lo, hi, _) in d["vbar"].items()}
        self.o = {self._key(k): I(lo, hi) for k, (lo, hi, _) in d["oneoverq"].items()}

    @staticmethod
    def _key(s):
        from fractions import Fraction as Fr
        return tuple(Fr(x) for x in s.split(","))

    @staticmethod
    def key(Q):
        from fractions import Fraction as Fr
        return tuple(Fr(float(x)).limit_denominator(1000) for x in Q)

    def vbar(self, Q):
        return self.v[self.key(Q)]

    def oneoverq(self, q):
        return self.o[self.key(q)]


# ------------------------------------------------------------ Sigma side

class SigmaIV:
    def __init__(self, run, coul, blocks, rho):
        self.run, self.coul, self.rho = run, coul, rho
        self.scr = spec.Screening(run, None, None, blocks=blocks)
        self.blocks = blocks
        self.fact = I.exact(1.0) / (I.exact(float(len(run.qlist))) * I.exact(run.cr.celvol))
        g0 = spec.gindex(rho["gvec"])[(0, 0, 0)]
        self.nelec = rho["rho"][g0]
        self.wpsq = RYD * RYD * I.exact(16.0) * iv.PI * I.exact(self.nelec) / I.exact(run.cr.celvol)
        self.rho_idx = spec.gindex(rho["gvec"])

    def eps_at(self, q, choose=None):
        """Interval eps^-1 on the sphere at q with the production op rule and
        the wing factors (spec.Screening.at, in intervals)."""
        run, cr = self.run, self.run.cr
        if choose is not None:
            self.scr.choose_op = choose
        Gs, b, is0, iop, g0, Gi, phase, nops, qi = self.scr.mapping(q)
        self.scr.choose_op = "last"
        Gb, E = b["G"], b["E"]
        pos = spec.gindex(Gb)
        idx = np.array([pos[tuple(g)] for g in Gi])
        # eps transforms with phase(G) conj(phase(G')): the common factor
        # exp(-2 pi i (M qi).t) cancels; the relative phases must be +-1
        rel = phase / phase[0]
        ph = np.rint(rel.real)
        if not np.allclose(rel, ph, atol=1e-12):
            raise ValueError("relative eps phase not +-1")
        sgn = ph[:, None] * ph[None, :]
        eps = I(np.where(sgn > 0, E.lo[np.ix_(idx, idx)], -E.hi[np.ix_(idx, idx)]),
                np.where(sgn > 0, E.hi[np.ix_(idx, idx)], -E.lo[np.ix_(idx, idx)]))
        z = int(np.flatnonzero(np.all(Gs == g0, axis=1))[0])
        others = np.arange(len(Gs)) != z
        if is0:
            eps.lo[others, z] = eps.hi[others, z] = 0.0
            eps.lo[z, others] = eps.hi[z, others] = 0.0
        else:
            qlen = norm2(cr.bdot, np.zeros((1, 3)), q).sqrt()[0]
            o = self.coul.oneoverq(q)
            v0 = self.coul.vbar(q + Gs[0])
            f_row = o * qlen / (I.exact(8.0) * iv.PI)
            f_col = o / (v0 * qlen)
            row = eps[z, others] * f_row
            col = eps[others, z] * f_col
            eps.lo[z, others], eps.hi[z, others] = row.lo, row.hi
            eps.lo[others, z], eps.hi[others, z] = col.lo, col.hi
        return Gs, eps

    def modes(self, q, Gs, eps):
        """I_eps, wtilde (eV) and v (with fact), mtxel_cor.f90:690-735, wpeff.f90."""
        cr = self.run.cr
        n = len(Gs)
        Ie = I.exact(np.eye(n)) - eps
        v = I(np.array([self.coul.vbar(q + g).lo for g in Gs]),
              np.array([self.coul.vbar(q + g).hi for g in Gs])) * self.fact
        vb = I(np.array([self.coul.vbar(q + g).lo for g in Gs]),
               np.array([self.coul.vbar(q + g).hi for g in Gs]))
        qG = q[None, :] + Gs
        q_nonzero = np.any(q != 0)
        fact = self.wpsq / I.exact(self.nelec)
        # Omega2(G,G') = fact * vbar(G)/(8 pi) * (q+G').B.(q+G) * rho(G-G')
        dotm = None
        for i in range(3):
            for j in range(3):
                term = I.exact(qG[None, :, i]) * I.exact(np.full((1, 1), cr.bdot[i, j])) * I.exact(qG[:, None, j])
                dotm = term if dotm is None else dotm + term        # dotm[g, g'] = (q+G').B.(q+G)
        r = np.zeros((n, n))
        has = np.zeros((n, n), bool)
        for i in range(n):
            for jp in range(n):
                gg = tuple(Gs[i] - Gs[jp])
                if gg in self.rho_idx:
                    r[i, jp] = self.rho["rho"][self.rho_idx[gg]]
                    has[i, jp] = True
        pre = fact * vb / (I.exact(8.0) * iv.PI)                      # per row G
        Om2 = pre.reshape(n, 1) * dotm * I.exact(r)
        g0row = ~Gs.any(axis=1)
        if not q_nonzero:
            # G = 0 row at q = 0 (wpeff.f90: igadd == 1 and q = 0):
            # Omega2(0, G') = fact * rho(0) if G' = 0, else 0
            zi = int(np.flatnonzero(g0row)[0])
            row = I.exact(np.zeros(n))
            row[zi] = fact * I.exact(r[zi, zi])
            Om2[zi] = row
        Om2 = iv.select(has, ~has, Om2, 0.0)
        # thresholds: keep iff |I| >= TOL_SMALL and |Om2| >= TOL_SMALL
        Ia, Oa = Ie.abs(), Om2.abs()
        keepI_t, keepI_f = Ia.certainly_ge(TOL_SMALL), Ia.certainly_lt(TOL_SMALL)
        keepO_t, keepO_f = Oa.certainly_ge(TOL_SMALL), Oa.certainly_lt(TOL_SMALL)
        count("undecided_TOL_SMALL_I", np.sum(~keepI_t & ~keepI_f))
        count("undecided_TOL_SMALL_Om2", np.sum(keepI_t & ~keepO_t & ~keepO_f))
        keep = keepI_t & keepO_t
        und = (~keepI_t & ~keepI_f) | (keepI_t & ~keepO_t & ~keepO_f)
        if np.any(und):
            for i, j in np.argwhere(und)[:5]:
                print("UNDECIDED", q, Gs[i], Gs[j], "I", Ie.lo[i, j], Ie.hi[i, j],
                      "Om2", Om2.lo[i, j], Om2.hi[i, j], file=sys.stderr)
            raise NotImplementedError("undecided GPP drop threshold")
        Ie_used = iv.select(keepI_t, keepI_f, Ie, 0.0)
        safeI = iv.select(keep, ~keep, Ie, 1.0)
        wt2 = iv.select(keep, ~keep, Om2 / safeI, 0.0)
        pos, neg = wt2.certainly_gt(0.0), wt2.certainly_lt(0.0)
        count("undecided_wt2_sign", np.sum(keep & ~pos & ~neg))
        if np.any(keep & ~pos & ~neg):
            raise NotImplementedError("undecided GPP mode validity")
        small_t, small_f = wt2.abs().certainly_lt(TOL_SMALL), wt2.abs().certainly_ge(TOL_SMALL)
        if np.any(keep & ~small_t & ~small_f):
            raise NotImplementedError("undecided |wtilde2| threshold")
        keep &= small_f
        count("invalid_modes", np.sum(keep & neg))
        wt = iv.select(keep & pos, ~(keep & pos), iv.select(pos, ~pos, wt2, 1.0).abs().sqrt(), 0.0)
        wt = iv.select(keep & neg, ~(keep & neg), 1.0 / TOL_ZERO, wt)
        return dict(Ie=Ie_used, wt=wt, keep=keep, v=v)

    def kernel(self, wx, m, occupied):
        """(ssx, sch) intervals for energy wx (eV interval), mtxel_cor.f90:1766-1850.
        Near-pole (occupied): ssx = -I w/(2 (wx + w)), the exact value of the
        source's -Omega2 delw / (4 w^2 (delw + 1/2)) wherever that is defined."""
        wt, Ie, keep = m["wt"], m["Ie"], m["keep"]
        wdiff = wx - wt
        wdiffr = wdiff.sqr()
        gen_a_t, gen_a_f = wdiffr.certainly_gt(GAMMA ** 2), wdiffr.certainly_le(GAMMA ** 2)
        # delwr = wt^2 / wdiff^2 < limitone  <=>  wt^2 < limitone * wdiff^2
        lim = 1.0 / (TOL_SMALL * 4.0)
        rhs = wdiffr * I.exact(lim)
        wt2 = wt.sqr()
        gen_b_t, gen_b_f = wt2.certainly_lt(rhs), wt2.certainly_ge(rhs)
        gen_t = keep & gen_a_t & gen_b_t
        gen_f = ~keep | gen_a_f | gen_b_f
        count("undecided_generic", np.sum(~gen_t & ~gen_f))
        # generic values, only where generic is possible (wdiff bounded away from 0)
        safe_wdiff = iv.select(~gen_f, gen_f, wdiff, 1.0)
        if np.any((~gen_f) & safe_wdiff.contains_zero()):
            raise ZeroDivisionError("generic branch possible with wdiff ~ 0")
        sch_g = wt * Ie / safe_wdiff
        if not occupied:
            sch = iv.select(gen_t, gen_f, sch_g, 0.0)
            return None, sch
        # sexcut (mtxel_cor.f90:1847-1848): ssx = 0 when |ssx| > sexcut |I| and
        # wx < 0, applied to whichever branch value was taken. It is decided
        # here WITHOUT dividing, by the exactly equivalent (for |I| > 0)
        #   generic:   |wx^2 - w^2| < w^2 / sexcut
        #   near-pole: |2 (wx + w)| < w / sexcut       (|ssx_n| = |I| w / |2(wx+w)|)
        # so that the hole-branch poles of SX (wx = -w), which production
        # clamps to 0, need no division.
        neg_t, neg_f = wx.certainly_lt(0.0), wx.certainly_ge(0.0)
        den = wx.sqr() - wt2
        lim_g = wt2 * I.exact(1.0 / SEXCUT)
        cg_t, cg_f = den.abs().certainly_lt(lim_g), den.abs().certainly_ge(lim_g)
        clampg_t, clampg_f = cg_t & neg_t, cg_f | neg_f
        need_g = ~gen_f & ~clampg_t
        safe_den = iv.select(need_g, ~need_g, den, 1.0)
        if np.any(need_g & safe_den.contains_zero()):
            raise ZeroDivisionError("generic ssx denominator ~ 0 outside the sexcut clamp")
        ssx_g = iv.select(clampg_t, clampg_f, 0.0, wt2 * Ie / safe_den)
        # near-pole: delwr > TOL_Zero decides between the combined term and 0;
        # in the near region wdiff is tiny, so delwr = wt^2/wdiff^2 is huge
        # at wdiff = 0 exactly the source divides by zero: under IEEE its delw is
        # 0 * Inf = NaN, both branch tests fail and ssx = 0; the closed form's
        # continuous value is -I/4. The spec does not choose: wherever wdiff may
        # be 0 the condition is left undecided, so the enclosure is the hull of
        # both (convention-free) and continuity is not claimed there.
        wd0 = wdiff.contains_zero()
        near_cond_t = keep & (wt2.certainly_gt(wdiffr * I.exact(TOL_ZERO))) & ~wd0
        near_cond_f = ~keep | wt2.certainly_le(wdiffr * I.exact(TOL_ZERO))
        count("wdiff_zero_possible", np.sum(keep & ~gen_t & wd0))
        count("undecided_near_zero", np.sum(~gen_t & ~near_cond_t & ~near_cond_f))
        den_n = I.exact(2.0) * (wx + wt)
        lim_n = wt * I.exact(1.0 / SEXCUT)
        cn_t, cn_f = den_n.abs().certainly_lt(lim_n), den_n.abs().certainly_ge(lim_n)
        clampn_t, clampn_f = cn_t & neg_t, cn_f | neg_f
        need_n = keep & ~gen_t & ~near_cond_f & ~clampn_t
        safe_dn = iv.select(need_n, ~need_n, den_n, 1.0)
        if np.any(need_n & safe_dn.contains_zero()):
            raise ZeroDivisionError("near-pole denominator ~ 0")
        ssx_n = iv.select(clampn_t, clampn_f, 0.0, -(Ie * wt) / safe_dn)
        # wx = -w exactly: the source's SX denominator is 0 (IEEE: NaN, Sigma
        # undefined); the clamp above assigns 0, the limit from either side.
        # Counted so that a certificate can state it never evaluates there.
        count("source_undefined_possible",
              np.sum((~gen_f & den.contains_zero()) | (keep & ~gen_t & ~near_cond_f & den_n.contains_zero())))
        ssx_nb = iv.select(near_cond_t, near_cond_f, ssx_n, 0.0)
        ssx = iv.select(gen_t, gen_f, ssx_g, ssx_nb)
        sch = iv.select(gen_t, gen_f, sch_g, 0.0)
        und_g = ~gen_f & ~clampg_t & ~clampg_f
        und_n = ~gen_t & keep & ~near_cond_f & ~clampn_t & ~clampn_f
        count("undecided_sexcut", np.sum(und_g | und_n))
        count("sexcut_clamped", np.sum((gen_t & clampg_t) | (gen_f & near_cond_t & clampn_t)))
        count("near_pole_modes", np.sum(keep & gen_f & near_cond_t))
        return ssx, sch

    def prepare(self, k, bands):
        run = self.run
        Gk, ck, Ek = real_coeffs(run.wf, tuple(k))
        nb = np.array(bands) - 1
        Gch, _ = run.sphere(np.zeros(3), max(run.ecuts, run.ecutb))
        rho_n = mtxel_iv(Gk, ck[nb], Gk, ck[nb], Gch)
        rho_n = I(np.array([rho_n.lo[a, a] for a in range(len(nb))]),
                  np.array([rho_n.hi[a, a] for a in range(len(nb))]))  # (n, G)
        return dict(Gk=Gk, ck=ck[nb], e_lk=I.exact(Ek[nb]) * RYD, rho_n=rho_n,
                    chidx=spec.gindex(Gch), n=len(nb))

    def qpart(self, pre, k, q, choose=None):
        """Contributions of one q to X, SX(iw), CH(iw), cor (Ry), per band."""
        run = self.run
        Gk, ck, e_lk, n_b = pre["Gk"], pre["ck"], pre["e_lk"], pre["n"]
        X, SX0, SX1, CH0, CH1, COR = (I.exact(np.zeros(n_b)) for _ in range(6))
        Gb, _ = run.sphere(q, run.ecutb)
        Gq, cq, Eq = real_coeffs(run.wf, tuple(k - q))
        Mb = mtxel_iv(Gk, ck, Gq, cq[:run.nocc], Gb)
        vbx = I(np.array([self.coul.vbar(q + g).lo for g in Gb]),
                np.array([self.coul.vbar(q + g).hi for g in Gb])) * self.fact
        X = X - (Mb.sqr() * vbx.reshape(1, 1, -1)).sum(axis=2).sum(axis=1)
        Gs, eps = self.eps_at(q, choose)
        m = self.modes(q, Gs, eps)
        v, Ie = m["v"], m["Ie"]
        n = len(Gs)
        Iex = eps - I.exact(np.eye(n))
        pos = np.array([[pre["chidx"].get(tuple(g - gp), -1) for gp in Gs] for g in Gs])
        okt = Iex.abs().certainly_ge(TOL_SMALL) & (pos >= 0)
        okf = Iex.abs().certainly_lt(TOL_SMALL) | (pos < 0)
        if np.any(~okt & ~okf):
            raise NotImplementedError("undecided static-CH threshold")
        rho_n = pre["rho_n"]
        for a in range(n_b):
            A = I(np.where(pos >= 0, rho_n.lo[a][np.where(pos >= 0, pos, 0)], 0.0),
                  np.where(pos >= 0, rho_n.hi[a][np.where(pos >= 0, pos, 0)], 0.0))
            term = iv.select(okt, okf, A * Iex, 0.0).sum(axis=0) * v
            COR[a] = COR[a] + I.exact(0.25) * term.sum(axis=0)
        M = mtxel_iv(Gk, ck, Gq, cq[:run.nbands], Gs)
        for n1 in range(run.nbands):
            e1 = I.exact(Eq[n1]) * RYD
            occ = n1 < run.nocc
            ks = []
            for iw in range(2):
                wx = e_lk + I.exact(DW * iw) - e1
                tz = wx.abs().certainly_lt(TOL_ZERO)
                if np.any(~tz & ~wx.abs().certainly_ge(TOL_ZERO)):
                    raise NotImplementedError("undecided |wx| < TOL_Zero")
                wx = iv.select(tz, ~tz, TOL_ZERO, wx)
                ks.append([self.kernel(wx[a], m, occ) for a in range(n_b)])
            for a in range(n_b):
                x = M[a, n1]
                xv = x * v
                achs = I.exact(0.5) * (xv * iv.matvec(-Ie.T, x)).sum()
                COR[a] = COR[a] - I.exact(0.5) * achs
                for iw, (SXa, CHa) in enumerate(((SX0, CH0), (SX1, CH1))):
                    ssx, sch = ks[iw][a]
                    CHa[a] = CHa[a] + I.exact(0.5) * (xv * iv.matvec(sch.T, x)).sum()
                    if occ:
                        SXa[a] = SXa[a] - (xv * iv.matvec(ssx.T, x)).sum()
        return [X, SX0, SX1, CH0, CH1, COR]

    def parts(self, k, bands, all_q0_ops=True):
        """{q-tuple: parts} for the production op rule, plus (optionally) the
        q=0 parts for every op matching q=0 (for the direction study)."""
        pre = self.prepare(k, bands)
        out = {tuple(q): self.qpart(pre, k, q) for q in self.run.qlist}
        q0 = np.zeros(3)
        per_op = {iop: self.qpart(pre, k, q0, {(0.0, 0.0, 0.0): iop})
                  for iop in range(48)} if all_q0_ops else None
        return pre, out, per_op

    def eqp1(self, pre, parts):
        """Multiplet-averaged Eqp1 (eV) from summed parts over one multiplet."""
        X, SX0, SX1, CH0, CH1, COR = parts
        nb = I.exact(float(pre["n"]))
        avg = lambda a: a.sum() / nb
        x, cor = avg(X) * RYD, avg(COR) * RYD
        s0 = x + avg(SX0) * RYD + avg(CH0) * RYD + cor
        s1 = x + avg(SX1) * RYD + avg(CH1) * RYD + cor
        eo = avg(pre["e_lk"])
        d = (s1 - s0) / I.exact(DW)
        eqp0 = eo + s0
        return eqp0 + d / (I.exact(1.0) - d) * (eqp0 - eo), dict(
            X=x, SXX=avg(SX0) * RYD, CH=avg(CH0) * RYD + cor, Z=I.exact(1.0) / (I.exact(1.0) - d))


def total(parts_by_q, q0_override=None):
    keys = list(parts_by_q)
    acc = None
    for key in keys:
        p = parts_by_q[key]
        if q0_override is not None and not any(key):
            p = q0_override
        acc = p if acc is None else [a + b for a, b in zip(acc, p)]
    return acc


def average_parts(plist):
    n = I.exact(float(len(plist)))
    acc = None
    for p in plist:
        acc = p if acc is None else [a + b for a, b in zip(acc, p)]
    return [a / n for a in acc]


def replica_coulomb_json(rundir, out, rel=1e-12):
    """Coulomb 'certificate' built from the production Monte Carlo replica
    (coulomb.MiniBZ.production / oneoverq_production), widened by `rel`.
    With it, cert.py must enclose production's own printed values: that checks
    that cert.py carries the production conventions and that the gap to spec A
    is the quadrature alone (E1 review finding 1)."""
    import coulomb
    run = spec.Run(rundir)
    mb = coulomb.MiniBZ(run.cr.bdot, run.qgrid, run.cr.celvol)
    from fractions import Fraction as Fr
    doc = {"vbar": {}, "oneoverq": {}}
    for q in run.qlist:
        for g in run.sphere(q, run.ecutb)[0]:
            Q = q + g
            v = mb.production(Q)
            key = ",".join(str(Fr(float(x)).limit_denominator(1000)) for x in Q)
            doc["vbar"][key] = [v * (1 - rel), v * (1 + rel), ""]
        if q.any():
            o = mb.oneoverq_production(q)
            key = ",".join(str(Fr(float(x)).limit_denominator(1000)) for x in q)
            doc["oneoverq"][key] = [o * (1 - rel), o * (1 + rel), ""]
    pathlib.Path(out).write_text(json.dumps(doc))
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("rundir")
    ap.add_argument("--coulomb", default=str(HERE / "data/coulomb_cert.json"))
    ap.add_argument("--out")
    a = ap.parse_args(argv)
    t0 = time.time()
    STATS.clear()
    run = spec.Run(a.rundir)
    rho = bgwio.read_rho(pathlib.Path(a.rundir) / "RHO")
    coul = CertCoulomb(a.coulomb)
    qs = [(run.eps0["q"][0]["q"], True)] + [(b["q"], False) for b in run.eps["q"]]
    blocks, inv_info = [], []
    for q, q0 in qs:
        Gs, E, beta, delta = epsinv_iv(a.rundir, run.nbands, run.ecuts, q, q0)
        blocks.append((Gs, E))
        inv_info.append(dict(q=q.tolist(), n=len(Gs), beta=beta, delta=delta,
                             max_width=float(np.max(E.hi - E.lo))))
    sig = SigmaIV(run, coul, blocks, rho)
    kX, kL = run.kpts[2], run.kpts[1]
    preX, pX, opX = sig.parts(kX, [5, 6])
    preL, pL, opL = sig.parts(kL, [5])
    # spec A: BerkeleyGW's op rule for q = 0 (the last match, op 48)
    eX, cX = sig.eqp1(preX, total(pX))
    eL, cL = sig.eqp1(preL, total(pL))
    # every q = 0 direction choice, and spec B: the direction-averaged q = 0 cell
    per_op = {}
    for iop in range(48):
        o = sig.eqp1(preX, total(pX, opX[iop]))[0] - sig.eqp1(preL, total(pL, opL[iop]))[0]
        per_op[iop] = [float(o.lo), float(o.hi)]
    avgX = average_parts([opX[i] for i in range(48)])
    avgL = average_parts([opL[i] for i in range(48)])
    oB = sig.eqp1(preX, total(pX, avgX))[0] - sig.eqp1(preL, total(pL, avgL))[0]
    # O2 = min_k Eqp1(c) - Eqp1(Gamma, v): enclose Gamma v (2,3,4) and Gamma c (5,6,7)
    kG = run.kpts[0]
    preGv, pGv, _ = sig.parts(kG, [2, 3, 4], all_q0_ops=False)
    preGc, pGc, _ = sig.parts(kG, [5, 6, 7], all_q0_ops=False)
    eGv, cGv = sig.eqp1(preGv, total(pGv))
    eGc, cGc = sig.eqp1(preGc, total(pGc))
    cbm_at_L = bool(eL.hi < eX.lo and eL.hi < eGc.lo)
    o2 = eL - eGv
    o1 = eX - eL
    res = {"O1_lo": float(o1.lo), "O1_hi": float(o1.hi),
           "O1_width": float(o1.hi - o1.lo),
           "Eqp1_X": [float(eX.lo), float(eX.hi)], "Eqp1_L": [float(eL.lo), float(eL.hi)],
           "constituents_X": {k: [float(v.lo), float(v.hi)] for k, v in cX.items()},
           "constituents_L": {k: [float(v.lo), float(v.hi)] for k, v in cL.items()},
           "epsilon_inverse": inv_info, "branch_stats": dict(STATS),
           "O1_per_q0_op": per_op,
           "O1_q0_ops_min": min(v[0] for v in per_op.values()),
           "O1_q0_ops_max": max(v[1] for v in per_op.values()),
           "O1_specB_direction_average": [float(oB.lo), float(oB.hi)],
           "Eqp1_Gamma_v": [float(eGv.lo), float(eGv.hi)],
           "Eqp1_Gamma_c": [float(eGc.lo), float(eGc.hi)],
           "CBM_certainly_at_L": cbm_at_L,
           "O2_gap_L_minus_Gamma_v": [float(o2.lo), float(o2.hi)],
           "seconds": time.time() - t0}
    if a.out:
        pathlib.Path(a.out).write_text(json.dumps(res, indent=1) + "\n")
        print(f"O1_spec in [{res['O1_lo']:.12f}, {res['O1_hi']:.12f}] eV -> {a.out}")
    else:
        print(json.dumps(res, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
