#!/usr/bin/env python3
"""BRIDGE-MEASURE: how large are the named departures of `GW.Bridge.sigA_eq_theory`
on the Si-EPM O1 run?

    python3 bgw/bridge_measure/measure.py RUNDIR [--coulomb F] [--out F]

`GW/Bridge/Compare.lean` proves  SigA = SigT + COR  under hypotheses
hC (Coulomb averages = point values), hW (WingFree), hX (no TOL_Zero replacement
of x), hM (every mode ModeOK). This script evaluates, on the spec-A inputs that
`bgw/endpoint/cert.py` loads (its loaders and `iv.py` are imported, not modified),

* a per-mode classification written from the Compare.lean / SigmaSpec.lean
  definitions (keepM, wt2, Generic, ClampG, ClampN, ModeOK), NOT from cert.py's
  kernel; Omega^2 is recomputed from `OmT` (Bloch.lean), not taken from cert.py;
* for each class, Sigma(X), Sigma(L), Eqp1 and O1 with that class switched from the
  BerkeleyGW rule to the theory value (where one exists), in rigorous interval
  arithmetic (iv.py): every branch condition is asserted decided and every
  denominator certainly nonzero;
* a plain-float second classifier over cert.py's exact accumulation scope, whose
  counts are cross-checked against `cert_o1.json` branch_stats.

Units: energies in eV. Sigma is multiplet averaged (X: bands 5,6; L: band 5).
"""
import argparse
import json
import pathlib
import sys
import time

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[2]
EP = ROOT / "bgw/endpoint"
sys.path.insert(0, str(EP))
import bgwio  # noqa: E402
import cert  # noqa: E402
import iv  # noqa: E402
import spec  # noqa: E402
from iv import I  # noqa: E402

# SigmaSpec.lean constants (binary64 values of the source's decimals)
TS = 4722366482869645 / 2 ** 72        # TOL_Small = 1e-6
TZ = 4951760157141521 / 2 ** 92        # TOL_Zero = 1e-12
LIM1 = 250000.0
GAM2 = 0.25
SEXC = 4.0
WINV = 1e12
RYD = cert.RYD
RYD_F = 13.60569253
W2RY_F = 2.0 * RYD_F                   # invalid_gpp_mode = 2: wtilde = 2 Ry (in eV)

CLASSES = (
    "generic_ok",          # ModeOK case 1
    "occ_near_ok",         # ModeOK case 2
    "zero_mode",           # ModeOK case 3: I = Omega2 = 0 exactly
    "drop_I_O0",           # |I| < TS, Omega2 = 0 exactly (theory value 0: agrees)
    "drop_I",              # |I| < TS, Omega2 != 0
    "drop_O_O0",           # |I| >= TS, Omega2 = 0 exactly (theory value 0: agrees)
    "drop_O",              # |I| >= TS, 0 < |Omega2| < TS
    "drop_wt2",            # both kept, |wt2| < TS
    "invalid",             # kept, wt2 < 0
    "emp_near",            # empty band, valid, not Generic
    "occ_clampG",          # occupied, generic, sexcut clamp
    "occ_clampN",          # occupied, near-pole, sexcut clamp
    "occ_other",           # occupied, valid, not generic, not near (incl. x = w exactly)
)


def dec(t, f, what, scope=True):
    """The true-mask of a real condition that must be decided on `scope`; raise if
    it is undecided anywhere there."""
    und = ~t & ~f & scope
    if np.any(und):
        raise NotImplementedError(f"undecided: {what} ({int(np.sum(und))} entries)")
    return t & scope


def isexact0(a):
    return (a.lo == 0) & (a.hi == 0)


# ----------------------------------------------------------------- Coulomb

class Coul:
    """spec A averages (`avg`) or the bare point value 8 pi/|q+G|^2 (`bare`) at
    every q+G != 0; at q+G = 0 the point value does not exist and the average is
    kept (the only regularisation available; see docs/BRIDGE.md)."""

    def __init__(self, base, bdot, bare, head_zero=False):
        self.base, self.bdot, self.bare, self.head_zero = base, bdot, bare, head_zero

    def vbar(self, Q):
        Q = np.asarray(Q, float)
        if self.head_zero and not np.any(Q != 0):
            return I.exact(0.0)
        if self.bare and np.any(Q != 0):
            return I.exact(8.0) * iv.PI / cert.norm2(self.bdot, Q[None, :])[0]
        return self.base.vbar(Q)

    def oneoverq(self, q):
        return self.base.oneoverq(q)

    def vvec(self, q, Gs):
        vs = [self.vbar(q + g) for g in Gs]
        return I(np.array([float(v.lo) for v in vs]), np.array([float(v.hi) for v in vs]))


# ----------------------------------------------------------------- the measurement

class Measure:
    def __init__(self, rundir, coulomb):
        self.run = run = spec.Run(rundir)
        self.rho = bgwio.read_rho(pathlib.Path(rundir) / "RHO")
        self.base = cert.CertCoulomb(coulomb)
        qs = [(run.eps0["q"][0]["q"], True)] + [(b["q"], False) for b in run.eps["q"]]
        blocks = []
        for q, q0 in qs:
            Gs, E, _, _ = cert.epsinv_iv(rundir, run.nbands, run.ecuts, q, q0)
            blocks.append((Gs, E))
        # SigmaIV is used only for its loaders: prepare() (states, pair densities),
        # scr.mapping() (the symmetry map) and `fact`. Its eps_at/modes/kernel are not used.
        self.sig = cert.SigmaIV(run, self.base, blocks, self.rho)
        self.rho_idx = spec.gindex(self.rho["gvec"])
        cr = run.cr
        # factW = wpsq / nelec = RYD^2 16 pi / celvol (SigmaSpec.factW, exactly)
        self.factW = RYD * RYD * I.exact(16.0) * iv.PI / I.exact(cr.celvol)
        self.factW_f = RYD_F ** 2 * 16 * np.pi / cr.celvol
        self.coul = {"avg": Coul(self.base, cr.bdot, False), "bare": Coul(self.base, cr.bdot, True),
                     "head_zero": Coul(self.base, cr.bdot, False, head_zero=True)}
        self._dz = {}

    # ---------------------------------------------------------- eps and Omega2
    def eps_raw(self, q, choose=None):
        """The symmetry-mapped eps^-1 WITHOUT the wing rule (Bloch.epsT)."""
        scr = self.sig.scr
        if choose is not None:
            scr.choose_op = choose
        try:
            Gs, b, is0, iop, g0, Gi, phase, nops, qi = scr.mapping(q)
        finally:
            scr.choose_op = "last"
        pos = spec.gindex(b["G"])
        E = b["E"]
        idx = np.array([pos[tuple(g)] for g in Gi])
        rel = phase / phase[0]
        ph = np.rint(rel.real)
        if not np.allclose(rel, ph, atol=1e-12):
            raise ValueError("relative eps phase not +-1")
        sgn = ph[:, None] * ph[None, :]
        eps = I(np.where(sgn > 0, E.lo[np.ix_(idx, idx)], -E.hi[np.ix_(idx, idx)]),
                np.where(sgn > 0, E.hi[np.ix_(idx, idx)], -E.lo[np.ix_(idx, idx)]))
        z = int(np.flatnonzero(np.all(Gs == g0, axis=1))[0])
        return Gs, eps, z, bool(is0)

    def wing_mask(self, n, z):
        m = np.zeros((n, n), bool)
        m[z, :] = True
        m[:, z] = True
        m[z, z] = False
        return m

    def eps_spec(self, q, Gs, eps, z, is0, coul, wings):
        """SigmaSpec.epsS: q = 0 wings zeroed; q != 0 row x oq|q|/(8 pi), col x
        oq/(vb(q+Gs[0])|q|). `wings` in {'spec', 'theory', 'q0theory', 'qntheory'}."""
        out = eps.copy()
        n = len(Gs)
        others = np.arange(n) != z
        if is0:
            if wings in ("spec", "qntheory"):
                out.lo[others, z] = out.hi[others, z] = 0.0
                out.lo[z, others] = out.hi[z, others] = 0.0
        else:
            if wings in ("spec", "q0theory"):
                qlen = cert.norm2(self.run.cr.bdot, np.zeros((1, 3)), q).sqrt()[0]
                o = coul.oneoverq(q)
                v0 = coul.vbar(q + Gs[0])
                row = eps[z, others] * (o * qlen / (I.exact(8.0) * iv.PI))
                col = eps[others, z] * (o / (v0 * qlen))
                out.lo[z, others], out.hi[z, others] = row.lo, row.hi
                out.lo[others, z], out.hi[others, z] = col.lo, col.hi
        return out

    def dot_exact(self, q, Gs):
        """(q+G_c).B.(q+G_r) evaluated EXACTLY in rational arithmetic on the binary64
        B and the half-integer q + G, returned as a one-ulp enclosure (exactly 0
        where it vanishes, e.g. orthogonal fcc G pairs). A rounded interval product
        would enclose 0 at many entries whose real value is ~1e-14 away from it and
        leave sign(Omega2) undecided there."""
        from fractions import Fraction as Fr
        key = (tuple(q), Gs.tobytes())
        if key not in self._dz:
            B = [[Fr(float(b)) for b in row] for row in self.run.cr.bdot]
            qG = [[Fr(float(q[i])) + int(g[i]) for i in range(3)] for g in Gs]
            Bv = [[sum(B[i][j] * v[j] for j in range(3)) for i in range(3)] for v in qG]
            n = len(Gs)
            val = [[sum(qG[a][i] * Bv[c][i] for i in range(3)) for c in range(n)] for a in range(n)]
            f = np.array([[float(x) for x in row] for row in val])
            zero = np.array([[x == 0 for x in row] for row in val])
            lo = np.where(zero, 0.0, np.nextafter(f, -np.inf))
            hi = np.where(zero, 0.0, np.nextafter(f, np.inf))
            # the same dot in the IDEAL fcc metric B ~ [[3,-1,-1],[-1,3,-1],[-1,-1,3]]
            # (binary64 cannot hold -1/3): diagnostic only, never used in a value
            pat = [[Fr(float(b) / float(self.run.cr.bdot[0][0])).limit_denominator(100) for b in row]
                   for row in self.run.cr.bdot]
            Bi = [[sum(pat[i][j] * v[j] for j in range(3)) for i in range(3)] for v in qG]
            izero = np.array([[sum(qG[a][i] * Bi[c][i] for i in range(3)) == 0 for c in range(n)]
                              for a in range(n)])
            self._dz[key] = (I(lo, hi), zero, izero)
        return self._dz[key]

    def omega2(self, q, Gs, coul):
        """Bloch.OmT: factW rho(G_r - G_c) * (q = 0 and G_r = 0 ? [G_c = 0]
        : vc(q+G_r)/(8 pi) (q+G_c).B.(q+G_r)); rho absent -> 0."""
        n = len(Gs)
        qG = q[None, :] + Gs  # noqa: F841
        dot, dzero, izero = self.dot_exact(q, Gs)
        r = np.zeros((n, n))
        for a in range(n):
            for c in range(n):
                k = tuple(Gs[a] - Gs[c])
                if k in self.rho_idx:
                    r[a, c] = self.rho["rho"][self.rho_idx[k]]
        v = coul.vvec(q, Gs)
        pre = self.factW * v / (I.exact(8.0) * iv.PI)
        O = pre.reshape(n, 1) * dot * I.exact(r)
        # structural zeros are EXACT zeros of the real Omega2 (outward rounding of a
        # product with an exact 0 would otherwise give [-5e-324, 5e-324]):
        # rho(G_r - G_c) absent or 0, q + G_r = 0 or q + G_c = 0 (dot = 0)
        zero = (r == 0) | dzero
        if not np.any(q != 0):
            zr = int(np.flatnonzero(~Gs.any(axis=1))[0])
            row = I.exact(np.zeros(n))
            row[zr] = self.factW * I.exact(r[zr, zr])
            O[zr] = row
            zero[zr] = True
            zero[zr, zr] = r[zr, zr] == 0
        O.lo[zero] = 0.0
        O.hi[zero] = 0.0
        return O, r, izero & ~zero

    # ---------------------------------------------------------- one-mode rules
    @staticmethod
    def bgw_value(Ie, w, x, occ, keep):
        """SigmaSpec specMode = CH/2 - [occ] SX for a given wtilde array `w` (BGW rules).
        Returns (value, gen, clampG, near, clampN) with decided masks."""
        d = x - w
        d2 = d.sqr()
        w2 = w.sqr()
        gen = dec(d2.certainly_gt(GAM2), d2.certainly_le(GAM2), "gen a", keep) & \
            dec(w2.certainly_lt(d2 * I.exact(LIM1)), w2.certainly_ge(d2 * I.exact(LIM1)), "gen b", keep)
        safe_d = iv.select(gen, ~gen, d, 1.0)
        if np.any(gen & safe_d.contains_zero()):
            raise ZeroDivisionError("generic x - w")
        sch = iv.select(gen, ~gen, w * Ie / safe_d, 0.0)
        z = np.zeros(gen.shape, bool)
        if not occ:
            return sch * I.exact(0.5), gen, z, z, z
        xneg = dec(x.certainly_lt(0.0), x.certainly_ge(0.0), "x < 0", keep)
        den = x.sqr() - w2
        cg = den.abs()
        cG = xneg & dec(cg.certainly_lt(w2 * I.exact(1.0 / SEXC)),
                        cg.certainly_ge(w2 * I.exact(1.0 / SEXC)), "clampG", gen & xneg)
        need = gen & ~cG
        safe_den = iv.select(need, ~need, den, 1.0)
        if np.any(need & safe_den.contains_zero()):
            raise ZeroDivisionError("generic x^2 - w^2")
        ssx_g = iv.select(need, ~need, w2 * Ie / safe_den, 0.0)
        ng = keep & ~gen
        nc_t = w2.certainly_gt(d2 * I.exact(TZ)) & ~d.contains_zero()
        nc_f = w2.certainly_le(d2 * I.exact(TZ)) | isexact0(d)
        near = dec(nc_t, nc_f, "near cond", ng)
        dn = I.exact(2.0) * (x + w)
        cN = xneg & dec(dn.abs().certainly_lt(w * I.exact(1.0 / SEXC)),
                        dn.abs().certainly_ge(w * I.exact(1.0 / SEXC)), "clampN", near & xneg)
        needn = near & ~cN
        safe_dn = iv.select(needn, ~needn, dn, 1.0)
        if np.any(needn & safe_dn.contains_zero()):
            raise ZeroDivisionError("near 2(x + w)")
        ssx_n = iv.select(needn, ~needn, -(Ie * w) / safe_dn, 0.0)
        ssx = iv.select(gen, ~gen, ssx_g, ssx_n)
        return sch * I.exact(0.5) - ssx, gen, cG, near, cN

    @staticmethod
    def theory_value(O, w, x, occ, mask):
        """Bloch.thK: occupiedTerm O/(2 w (x + w)), emptyTerm O/(2 w (x - w)) on `mask`
        (w = sqrt(O/I) > 0). Entries of `mask` with a possibly-zero denominator
        are returned in `sing` and valued 0 (they must be reported)."""
        den = I.exact(2.0) * w * ((x + w) if occ else (x - w))
        sing = mask & den.contains_zero()
        ok = mask & ~sing
        safe = iv.select(ok, ~ok, den, 1.0)
        return iv.select(ok, ~ok, O / safe, 0.0), sing

    def classify(self, Ie, O, x, occ):
        """Masks and wtilde per SigmaSpec (keepM, wt2, wtM) and Compare.ModeOK."""
        aI, aO = Ie.abs(), O.abs()
        kI = dec(aI.certainly_ge(TS), aI.certainly_lt(TS), "|I| >= TS")
        kO = dec(aO.certainly_ge(TS), aO.certainly_lt(TS), "|O| >= TS")
        kIO = kI & kO
        safeI = iv.select(kIO, ~kIO, Ie, 1.0)
        wt2 = iv.select(kIO, ~kIO, O / safeI, 0.0)
        aw = wt2.abs()
        kw = dec(aw.certainly_ge(TS), aw.certainly_lt(TS), "|wt2| >= TS", kIO)
        keep = kIO & kw
        pos = dec(wt2.certainly_gt(0.0), wt2.certainly_lt(0.0), "wt2 sign", keep)
        valid, inval = keep & pos, keep & ~pos
        w = iv.select(valid, ~valid, iv.select(valid, ~valid, wt2, 1.0).sqrt(), 0.0)
        w = iv.select(inval, ~inval, WINV, w)
        val, gen, cG, near, cN = self.bgw_value(Ie, w, x, occ, keep)
        O0, I0 = isexact0(O), isexact0(Ie)
        c = {k: np.zeros(keep.shape, bool) for k in CLASSES}
        c["zero_mode"] = I0 & O0
        c["drop_I_O0"] = ~kI & O0 & ~I0
        c["drop_I"] = ~kI & ~O0
        c["drop_O_O0"] = kI & O0
        c["drop_O"] = kI & ~kO & ~O0
        c["drop_wt2"] = kIO & ~kw
        c["invalid"] = inval
        if occ:
            c["generic_ok"] = valid & gen & ~cG
            c["occ_clampG"] = valid & gen & cG
            c["occ_near_ok"] = valid & near & ~cN
            c["occ_clampN"] = valid & near & cN
            c["occ_other"] = valid & ~gen & ~near
        else:
            c["generic_ok"] = valid & gen
            c["emp_near"] = valid & ~gen
        tot = sum(m.astype(int) for m in c.values())
        if not np.all(tot == 1):
            raise AssertionError("classes do not partition the modes")
        return dict(c=c, val=val, w=w, wt2=wt2, keep=keep, valid=valid, gen=gen, near=near)

    # ---------------------------------------------------------- one state, one variant
    def state(self, k, bands, cfg, tally=None):
        """Per band a and iw: X, C (= SX + CH, GPP part), COR (Ry), and per-class
        Delta C for the class switches (Ry). cfg keys: coul ('avg'|'bare'), wings,
        tolzero ('spec'|'exact'), switch (set of class switches applied in the value)."""
        run, sig = self.run, self.sig
        coul = self.coul[cfg["coul"]]
        pre = sig.prepare(k, bands)
        Gk, ck, e_lk, nb = pre["Gk"], pre["ck"], pre["e_lk"], pre["n"]
        Z = lambda: I.exact(np.zeros(nb))  # noqa: E731
        X, COR = Z(), Z()
        C = [Z(), Z()]
        dC = {}
        for q in run.qlist:
            Gb, _ = run.sphere(q, run.ecutb)
            Gq, cq, Eq = cert.real_coeffs(run.wf, tuple(k - q))
            Mb = cert.mtxel_iv(Gk, ck, Gq, cq[:run.nocc], Gb)
            vbx = coul.vvec(q, Gb) * sig.fact
            X = X - (Mb.sqr() * vbx.reshape(1, 1, -1)).sum(axis=2).sum(axis=1)
            Gs, eraw, z, is0 = self.eps_raw(q)
            eps = self.eps_spec(q, Gs, eraw, z, is0, coul, cfg["wings"])
            n = len(Gs)
            Ie = I.exact(np.eye(n)) - eps
            ez = (eps.lo == 0) & (eps.hi == 0) & ~np.eye(n, dtype=bool)   # I = 0 exactly there
            Ie.lo[ez] = 0.0
            Ie.hi[ez] = 0.0
            O, _, izero = self.omega2(q, Gs, coul)
            v = coul.vvec(q, Gs) * sig.fact
            # static remainder (SigmaSpec CSq + ACq), same thresholds as the spec
            Iex = eps - I.exact(np.eye(n))
            pos = np.array([[pre["chidx"].get(tuple(g - gp), -1) for gp in Gs] for g in Gs])
            okt = Iex.abs().certainly_ge(TS) & (pos >= 0)
            okf = Iex.abs().certainly_lt(TS) | (pos < 0)
            dec(okt, okf, "static CH threshold")
            kI = dec(Ie.abs().certainly_ge(TS), Ie.abs().certainly_lt(TS), "IeU")
            IeU = iv.select(kI, ~kI, Ie, 0.0)
            M = cert.mtxel_iv(Gk, ck, Gq, cq[:run.nbands], Gs)
            wing = self.wing_mask(n, z)
            for a in range(nb):
                rn = pre["rho_n"]
                A = I(np.where(pos >= 0, rn.lo[a][np.where(pos >= 0, pos, 0)], 0.0),
                      np.where(pos >= 0, rn.hi[a][np.where(pos >= 0, pos, 0)], 0.0))
                COR[a] = COR[a] + I.exact(0.25) * (iv.select(okt, okf, A * Iex, 0.0).sum(axis=0) * v).sum(axis=0)
            for n1 in range(run.nbands):
                occ = n1 < run.nocc
                e1 = I.exact(Eq[n1]) * RYD
                for a in range(nb):
                    xm = M[a, n1]
                    W = xm.reshape(n, 1) * xm.reshape(1, n) * v.reshape(1, n)   # W[r,c] = M_r M_c v_c
                    # static COH of band n1 (ACq): -1/2 * 1/2 * sum W (-IeU)
                    COR[a] = COR[a] - I.exact(0.25) * (W * (-IeU)).sum(axis=0).sum(axis=0)
                    for iw in range(2):
                        x = e_lk[a] + I.exact(float(iw)) - e1
                        tz_t, tz_f = x.abs().certainly_lt(TZ), x.abs().certainly_ge(TZ)
                        dec(tz_t, tz_f, "|x| < TZ")  # noqa
                        tzhit = bool(tz_t)
                        if tzhit and cfg["tolzero"] == "spec":
                            x = I.exact(TZ)
                        xs = I(np.full((n, n), float(x.lo)), np.full((n, n), float(x.hi)))
                        cl = self.classify(Ie, O, xs, occ)
                        val = cl["val"]
                        # class switches: values replacing the BGW rule on a class
                        alts = self.alternatives(Ie, O, xs, occ, cl)
                        if tzhit:
                            # x within TOL_Zero of 0 (n1 = a at q = 0 and its degenerate or
                            # symmetry-equivalent partners): the dropped-mode theory value is
                            # discontinuous in Omega2 there (-I/2 for Omega2 -> 0, see docs), so
                            # those switches are kept apart as `<class>_x0`
                            alts = {(k_ + "_x0" if k_.startswith("drop_") and not k_.endswith("_sing")
                                     else k_): v_ for k_, v_ in alts.items()}
                        for name, (mask, alt) in alts.items():
                            d = ((alt - val) * W)
                            d = iv.select(mask, ~mask, d, 0.0).sum(axis=0).sum(axis=0)
                            key = (name, a, iw)
                            dC[key] = dC.get(key, I.exact(0.0)) + d
                            if name in cfg.get("switch", ()):
                                val = iv.select(mask, ~mask, alt, val)
                        C[iw][a] = C[iw][a] + (W * val).sum(axis=0).sum(axis=0)
                        if tally is not None:
                            Wm = np.abs(W.mid())
                            for cname, m in cl["c"].items():
                                t = tally.setdefault(cname, {"count": 0, "absW_eV": 0.0})
                                t["count"] += int(m.sum())
                                t["absW_eV"] += float((Wm * m).sum()) * RYD_F
                            t = tally.setdefault("wing_entries", {"count": 0, "absW_eV": 0.0})
                            t["count"] += int(wing.sum())
                            t["absW_eV"] += float((Wm * wing).sum()) * RYD_F
                            t = tally.setdefault("tolzero_x", {"count": 0, "modes": 0})
                            if tzhit:
                                t["count"] += 1
                                t["modes"] += n * n
                            s = tally.setdefault("_singular", {})
                            for name, (mask, alt) in alts.items():
                                if name.endswith("_sing") or "_undec" in name:
                                    s[name] = s.get(name, 0) + int(mask.sum())
                            for name, (mask, alt) in alts.items():
                                if name.endswith("_unbounded_sing") and mask.any():
                                    kk = name + "_absWI_eV"
                                    s[kk] = s.get(kk, 0.0) + float((Wm * Ie.mag() * mask).sum()) * RYD_F
                                    kk = name + "_max_abs_x"
                                    s[kk] = max(s.get(kk, 0.0), float(xs.mag().max()))
                            for kk_ in ("drop_O", "drop_I"):
                                mm = cl["c"][kk_]
                                t = tally.setdefault(kk_ + "_ideal_metric_Omega2_zero",
                                                     {"count": 0, "count_x0": 0, "count_x0_total": 0})
                                t["count"] += int((mm & izero).sum())
                                if tzhit:
                                    t["count_x0"] += int((mm & izero).sum())
                                    t["count_x0_total"] += int(mm.sum())
                            if "emp_near" in alts:
                                mk, al = alts["emp_near"]
                                dm = np.abs(((al - val) * W).mid()) * mk * RYD_F
                                kk = "emp_near_max_single_mode_abs_dSigma_eV"
                                s[kk] = max(s.get(kk, 0.0), float(dm.max()))
                            en = cl["c"]["emp_near"]
                            if en.any():
                                dmin = float((xs - cl["w"]).abs().lo[en].min())
                                s["emp_near_min_abs_x_minus_w"] = min(s.get("emp_near_min_abs_x_minus_w", 9e9), dmin)
                            if cl["c"]["occ_other"].any():
                                dd = (xs - cl["w"]).contains_zero() & cl["c"]["occ_other"]
                                s["x_eq_w_possible"] = s.get("x_eq_w_possible", 0) + int(dd.sum())
        return dict(pre=pre, X=X, C=C, COR=COR, dC={k_: v_ for k_, v_ in dC.items()
                                                    if not k_[0].endswith("_sing")})

    def alternatives(self, Ie, O, xs, occ, cl):
        """{switch: (mask, value)}: the value a class takes when switched to the
        theory (or to another BerkeleyGW option where the theory has none)."""
        c, w = cl["c"], cl["w"]
        out = {}
        valid = cl["valid"]
        # ModeOK classes: theory value (Delta must be ~0 by mode_eq)
        for name in ("generic_ok", "occ_near_ok", "emp_near", "occ_clampG", "occ_clampN", "occ_other"):
            m = c[name] & valid
            if m.any():
                t, sing = self.theory_value(O, w, xs, occ, m)
                out[name] = (m & ~sing, t)
                out[name + "_sing"] = (sing, t)
        # dropped with Omega2 != 0. Theory: w = sqrt(O/I) (Bloch.thK) where O/I > 0.
        #  * sign(O/I) certain and > 0: exact enclosure of thK;
        #  * certain < 0: no single pole exists (single_pole_exists_iff), no theory value;
        #  * undecided (O or I encloses 0, e.g. symmetry zeros carried as ~1e-14 noise):
        #    whenever thK exists, |thK| = |w I / (2 (x +- w))| <= b (monotone bounds
        #    below), so the switch is enclosed by [-b, b].
        xa = xs.abs()
        for name in ("drop_I", "drop_O", "drop_wt2"):
            m = c[name]
            if not m.any():
                continue
            Ip, In = Ie.certainly_gt(0.0), Ie.certainly_lt(0.0)
            Op, On = O.certainly_gt(0.0), O.certainly_lt(0.0)
            ex = m & ((Ip & Op) | (In & On))
            nopole = m & ((Ip & On) | (In & Op))
            und = m & ~ex & ~nopole
            safeI = iv.select(ex, ~ex, Ie, 1.0)
            r = iv.select(ex, ~ex, O / safeI, 1.0)
            wt = r.sqrt()
            t, sing = self.theory_value(O, wt, xs, occ, ex)
            out[name] = (ex & ~sing, t)
            # bounds for `und`
            b = np.full(m.shape, np.inf)
            Imag, Imin = Ie.mag(), Ie.abs().lo
            Omag, Omin = O.mag(), O.abs().lo
            one = np.ones(m.shape)
            cO = und & (Imin > 0)                     # w in [0, wmax]
            if cO.any():
                wmax = (I(np.where(cO, Omag, 1.0)) / I(np.where(cO, Imin, 1.0))).sqrt().hi
                okO = cO & (xa.lo > wmax)
                den = I.exact(2.0) * (I(np.where(okO, xa.lo, 2.0)) - I(np.where(okO, wmax, 1.0)))
                bo = (I(np.where(okO, wmax, 1.0)) * I(np.where(okO, Imag, 1.0)) / den).hi
                b = np.where(okO, np.minimum(b, bo), b)
            cI = und & (Omin > 0)                     # w in [wmin, inf)
            if cI.any():
                wmin = (I(np.where(cI, Omin, 1.0)) / I(np.where(cI, Imag, 1.0))).sqrt().lo
                okI = cI & (wmin > xa.hi)
                den = I.exact(2.0) * I(np.where(okI, wmin, 2.0)) * \
                    (I(np.where(okI, wmin, 2.0)) - I(np.where(okI, xa.hi, 1.0)))
                bi = (I(np.where(okI, Omag, 1.0)) / den).hi
                b = np.where(okI, np.minimum(b, bi), b)
            bnd = und & np.isfinite(b)
            bb = np.where(bnd, b, 0.0)
            out[name + "_undec"] = (bnd, I(-bb, bb))
            out[name + "_nopole_sing"] = (nopole, I.exact(0.0 * one))
            out[name + "_unbounded_sing"] = (sing | (und & ~bnd), I.exact(0.0 * one))
        # invalid: no theory pole exists (single_pole_exists_iff); BGW's other options
        m = c["invalid"]
        if m.any():
            out["invalid_skip"] = (m, I.exact(np.zeros(m.shape)))      # invalid_gpp_mode = 0
            w2 = I.exact(np.full(m.shape, 2.0)) * RYD
            v2 = self.bgw_value(Ie, w2, xs, occ, m)[0]                 # invalid_gpp_mode = 2
            out["invalid_2Ry"] = (m, v2)
        return out


# ------------------------------------------------------------------ Eqp1

def eqp1(res, cor_factor=0.5, extra=None):
    """Multiplet-averaged Sigma(Eo) (eV) and linearised Eqp1 (eV). `cor_factor`
    multiplies (CH_exact - sum_n CH_static) (spec: 1/2). `extra`: {(a, iw): dRy}."""
    pre = res["pre"]
    nb = I.exact(float(pre["n"]))
    s = []
    for iw in range(2):
        tot = res["X"] + res["C"][iw] + res["COR"] * I.exact(2.0 * cor_factor)
        if extra:
            for a in range(pre["n"]):
                if (a, iw) in extra:
                    tot[a] = tot[a] + extra[(a, iw)]
        s.append(tot.sum() / nb * RYD)
    eo = pre["e_lk"].sum() / nb
    d = s[1] - s[0]
    return s[0], eo + s[0] + d / (I.exact(1.0) - d) * s[0], s[1]


def ivl(x):
    return [float(x.lo), float(x.hi)]


def mev(x):
    """Convert an eV interval to meV without narrowing it in binary64."""
    y = x * I.exact(1000.0)
    return [float(y.lo), float(y.hi)]


# ------------------------------------------------------------------ float cross-check

def float_counts(m):
    """cert.py's accumulation scope, plain float64: invalid_modes (per modes() call),
    near_pole_modes and sexcut_clamped (per occupied kernel call) and x = w hits."""
    run = m.run
    coul = m.coul["avg"]
    B = run.cr.bdot

    def modes(q, choose=None):
        Gs, eraw, z, is0 = m.eps_raw(q, choose)
        e = m.eps_spec(q, Gs, eraw, z, is0, coul, "spec").mid()
        n = len(Gs)
        Ie = np.eye(n) - e
        qG = q[None, :] + Gs
        dot = qG @ B @ qG.T
        r = np.zeros((n, n))
        for a in range(n):
            for c in range(n):
                kk = tuple(Gs[a] - Gs[c])
                r[a, c] = m.rho["rho"][m.rho_idx[kk]] if kk in m.rho_idx else 0.0
        v = np.array([coul.vbar(q + g).mid() for g in Gs], float)
        O = (m.factW_f * v / (8 * np.pi))[:, None] * dot * r
        if not q.any():
            zr = int(np.flatnonzero(~Gs.any(axis=1))[0])
            O[zr] = 0.0
            O[zr, zr] = m.factW_f * r[zr, zr]
        kIO = (np.abs(Ie) >= TS) & (np.abs(O) >= TS)
        wt2 = np.where(kIO, O / np.where(kIO, Ie, 1.0), 0.0)
        keep = kIO & (np.abs(wt2) >= TS)
        w = np.where(keep & (wt2 > 0), np.sqrt(np.abs(wt2)), 0.0)
        w = np.where(keep & (wt2 < 0), WINV, w)
        return Gs, keep, w, int((keep & (wt2 < 0)).sum())

    def occ_counts(k, bands, q, keep, w, Gs):
        Gq, cq, Eq = cert.real_coeffs(run.wf, tuple(k - q))
        Gk, ck, Ek = cert.real_coeffs(run.wf, tuple(k))
        near_n = clamp_n = xw = 0
        for a in np.array(bands) - 1:
            for n1 in range(run.nocc):
                for iw in range(2):
                    x = Ek[a] * RYD_F + iw - Eq[n1] * RYD_F
                    if abs(x) < TZ:
                        x = TZ
                    d = x - w
                    gen = keep & (d * d > GAM2) & (w * w < d * d * LIM1)
                    cG = gen & (np.abs(x * x - w * w) < w * w / SEXC) & (x < 0)
                    near = keep & ~gen & (w * w > d * d * TZ) & (d != 0)
                    cN = near & (np.abs(2 * (x + w)) < w / SEXC) & (x < 0)
                    near_n += int(near.sum())
                    clamp_n += int((cG | cN).sum())
                    xw += int((keep & (d == 0)).sum())
        return near_n, clamp_n, xw

    kG, kL, kX = run.kpts[0], run.kpts[1], run.kpts[2]
    states = [(kX, [5, 6], True), (kL, [5], True), (kG, [2, 3, 4], False), (kG, [5, 6, 7], False)]
    tot = dict(invalid_modes=0, near_pole_modes=0, sexcut_clamped=0, wdiff_zero_exact=0)
    cache = {}
    for q in run.qlist:
        cache[tuple(q), None] = modes(q)
    q0 = np.zeros(3)
    for iop in range(48):
        cache[(0.0, 0.0, 0.0), iop] = modes(q0, {(0.0, 0.0, 0.0): iop})
    for k, bands, ops in states:
        calls = [(q, None) for q in run.qlist] + ([(q0, iop) for iop in range(48)] if ops else [])
        for q, iop in calls:
            Gs, keep, w, ninv = cache[tuple(q), iop]
            tot["invalid_modes"] += ninv
            a, b, c = occ_counts(k, bands, q, keep, w, Gs)
            tot["near_pole_modes"] += a
            tot["sexcut_clamped"] += b
            tot["wdiff_zero_exact"] += c
    # the O1 scope of the interval pass (X bands 5,6 and L band 5, production op,
    # E in {Eo, Eo + 1 eV}, every n1): for cross-checking the interval classifier
    o1 = {}
    for lab, k, bands in (("X", kX, [5, 6]), ("L", kL, [5])):
        inv = near = 0
        for q in run.qlist:
            Gs, keep, w, ninv = cache[tuple(q), None]
            inv += ninv * run.nbands * 2 * len(bands)
            near += occ_counts(k, bands, q, keep, w, Gs)[0]
        o1[lab] = dict(invalid=inv, occ_near=near)
    tot["O1_scope"] = o1
    return tot


# ------------------------------------------------------------------ main

SWITCHES = ("generic_ok", "occ_near_ok", "occ_clampG", "occ_clampN", "occ_other", "emp_near",
            "drop_I", "drop_O", "drop_wt2", "drop_I_x0", "drop_O_x0", "drop_wt2_x0",
            "invalid_skip", "invalid_2Ry")


def run_all(rundir, coulomb):
    t0 = time.time()
    m = Measure(rundir, coulomb)
    run = m.run
    kX, kL = run.kpts[2], run.kpts[1]
    base = dict(coul="avg", wings="spec", tolzero="spec")
    out = {"inputs": {"rundir_files": ["WFN_inner", "RHO", "eps0mat", "epsmat", "sigma.inp"],
                      "coulomb": str(pathlib.Path(coulomb).name)}}

    def variant(cfg, tallyX=None, tallyL=None):
        rX = m.state(kX, [5, 6], cfg, tallyX)
        rL = m.state(kL, [5], cfg, tallyL)
        return rX, rL

    tX, tL = {}, {}
    rX, rL = variant(base, tX, tL)
    sX, eX, s1X = eqp1(rX)
    sL, eL, s1L = eqp1(rL)
    o1 = eX - eL
    out["baseline"] = dict(SigmaX=ivl(sX), SigmaL=ivl(sL), SigmaX_Eo_plus_1eV=ivl(s1X),
                           SigmaL_Eo_plus_1eV=ivl(s1L), Eqp1_X=ivl(eX), Eqp1_L=ivl(eL), O1_meV=mev(o1))
    out["tally_X"], out["tally_L"] = tX, tL

    def delta(vX, vL, cfX=0.5, cfL=0.5, exX=None, exL=None):
        a, b, a1 = eqp1(vX, cfX, exX)
        c, d, c1 = eqp1(vL, cfL, exL)
        return dict(dSigmaX_meV=mev(a - sX), dSigmaL_meV=mev(c - sL),
                    dSigmaX_Eo_plus_1eV_meV=mev(a1 - s1X), dSigmaL_Eo_plus_1eV_meV=mev(c1 - s1L),
                    dEqp1X_meV=mev(b - eX), dEqp1L_meV=mev(d - eL), dO1_meV=mev((b - d) - o1),
                    O1_meV=mev(b - d))

    rows = {}
    # per-class switches (mode masks fixed; exact because only that class's values change)
    def gather(dC, name):
        ex = {}
        for (n, a, iw), v in dC.items():
            if n in (name, name + "_undec") or (name.endswith("_x0") and n == name[:-3] + "_undec_x0"):
                ex[(a, iw)] = ex[(a, iw)] + v if (a, iw) in ex else v
        return ex

    for name in SWITCHES:
        exX, exL = gather(rX["dC"], name), gather(rL["dC"], name)
        rows[name] = delta(rX, rL, exX=exX, exL=exL)
    # COR factor 1/2 -> 0 (theory, finite bands) and -> 1
    rows["COR_off"] = delta(rX, rL, 0.0, 0.0)
    rows["COR_factor_1"] = delta(rX, rL, 1.0, 1.0)
    # global input switches, recomputed from scratch (mode classes may move)
    for label, cfg in (("wings_theory", dict(base, wings="theory")),
                       ("wings_q0_theory", dict(base, wings="q0theory")),
                       ("wings_qn_theory", dict(base, wings="qntheory")),
                       ("coulomb_bare", dict(base, coul="bare")),
                       ("tolzero_exact", dict(base, tolzero="exact")),
                       ("coulomb_head_zero", dict(base, coul="head_zero")),
                       ("all_theory_but_emp_near", dict(coul="bare", wings="theory", tolzero="exact",
                                                        switch=("drop_I", "drop_O", "drop_wt2", "drop_I_undec",
                                                                "drop_O_undec", "drop_wt2_undec"))),
                       ("all_theory_COR_on", dict(coul="bare", wings="theory", tolzero="exact",
                                                  switch=("drop_I", "drop_O", "drop_wt2", "drop_I_undec",
                                                          "drop_O_undec", "drop_wt2_undec", "emp_near")))):
        vX, vL = variant(cfg)
        rows[label] = delta(vX, vL)
        if label == "all_theory_COR_on":
            rows["all_theory_COR_off"] = delta(vX, vL, 0.0, 0.0)
    out["rows"] = rows
    out["float_cross_check"] = float_counts(m)
    out["seconds"] = time.time() - t0
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("rundir")
    ap.add_argument("--coulomb", default=str(EP / "data/coulomb_cert.json"))
    ap.add_argument("--out", default=str(ROOT / "bgw/bridge_measure/data/measure.json"))
    a = ap.parse_args(argv)
    res = run_all(a.rundir, a.coulomb)
    pathlib.Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    pathlib.Path(a.out).write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps(res["baseline"]), res["seconds"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
