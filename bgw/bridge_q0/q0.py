#!/usr/bin/env python3
"""BRIDGE-Q0 Q3: the q -> 0 screening of the Si-EPM run, the q0-direction spread of
O1 and the theory's angular average.

    python3 bgw/bridge_q0/q0.py RUNDIR [--coulomb F] [--ndir N] [--workers W] [--out F]

RUNDIR is a fresh pinned run (bgw/endpoint/run_production.py). Everything is built
from the mean-field files with bgw/endpoint/cert.py's loaders and its interval
arithmetic (iv.py); cert.py, iv.py and spec.py are imported, not modified.

What is computed (all intervals unless marked "float" / "quadrature"):

1. RHO: its space-group star asymmetry, and the reconstruction
   rho = 2 sum_{k in IBZ} w_k sum_v |psi_vk|^2 over the three IBZ points of
   WFN_co (Gamma, one L, one X; weights 1/8, 4/8, 3/8), i.e. WITHOUT the star average
   (float). Plus the star-symmetrized RHO (float, exact up to rounding).
2. The k.p limit of the Epsilon q0 block on the ray q = t u, u = (0,0,1) crystal,
   t0 = 0.001 (the input q0 is exactly t0 u): the scaled limit
   E~0(u) = 1 - diag(v~0) chi0s(u) of GW/Bridge/EpsQ0.lean, with
     head  u^T H u,  H_ab = C sum_x P_xa P_xb / dE_x,
     wing  A_G . u,  A_Gb = C sum_x P_xb M_x(0, G) / dE_x,
     body  C sum_x M_x(0,G) M_x(0,G') / dE_x,
     p_x = P_x . u = <c|dH/dt|v> / (E_v - E_c),  dH/dt = 2 (k+G).B.u (local EPM),
   valence AND conduction from WFN at k (the q = 0 states); v~0_z = 8 pi/|u|^2,
   v~0_G = 8 pi/|G|^2. Against it the scaled eps at t0 from WFNq (what Epsilon uses):
   delta = ||E~(t0) - E~0||_inf, beta = ||E~0^-1||_inf, the q0_error bound
   beta^2 delta/(1 - beta delta), and the actual entry differences.
3. Isotropy: eps_M(u) = 1/(E~0(u)^-1)_zz for the four <111> axes and random u, and
   the direction dependence of the body limit.
4. O1 = Eqp1(X, 5-6) - Eqp1(L, 5) of spec A with the q = 0 block replaced, for the
   production RHO and the symmetrized RHO:
   (a) the q0 block under each of the 48 ops (reproduces cert_o1.json O1_per_q0_op);
   (b) the k.p limit block (direction u0) under each op;
   (c) the angular average of the q = 0 cell contribution with the limit block at
       direction u, weighted by the q = 0 mini-BZ cell's solid-angle measure r(u)^3
       (Wigner-Seitz cell of the Sigma q-grid) -- a quadrature estimate over a
       Fibonacci set of directions, reported at two resolutions.
"""
import argparse
import json
import multiprocessing as mp
import pathlib
import sys
import time

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "bgw/endpoint"))
import bgwio  # noqa: E402
import cert  # noqa: E402
import iv  # noqa: E402
import spec  # noqa: E402
from iv import I  # noqa: E402

T0 = 0.001                     # q0 = T0 * (0,0,1) crystal, exactly (the double 0.001)
U0 = np.array([0.0, 0.0, 1.0])


def iv_row_norm_up(A):
    """Upper bound of the l-inf operator norm (max absolute row sum) of an interval matrix."""
    return float(iv._row_sum_up(A.mag()).max())


# ----------------------------------------------------------------- RHO

def rho_star(rho, cr):
    """Star asymmetry max |rho(hG) e^{-i hG.t} - rho(G)| and the star average."""
    g = np.asarray(rho["gvec"])
    r = np.asarray(rho["rho"], float)
    idx = spec.gindex(g)
    acc = np.zeros_like(r)
    worst = 0.0
    for M, t in zip(cr.mtrx, cr.tnp):
        M, t = np.asarray(M), np.asarray(t)
        hg = g @ M.T
        j = np.array([idx[tuple(x)] for x in hg])
        ph = np.cos(hg @ t)                      # tnp in radians; phases are exactly +-1
        if not np.allclose(np.abs(ph), 1.0, atol=1e-12):
            raise ValueError("non +-1 RHO phase")
        img = r[j] * np.rint(ph)
        worst = max(worst, float(np.abs(img - r).max()))
        acc += img
    rs = dict(rho)
    rs["rho"] = acc / len(cr.mtrx)
    return worst, rs


def rho_ibz_reconstruction(run, rho):
    """max |RHO - 2 sum_{k in IBZ} w_k sum_{v<=4} |psi_vk|^2| over WFN_inner (float)."""
    w = run.wf.w
    g = np.asarray(rho["gvec"])
    r = np.asarray(rho["rho"], float)
    acc = np.zeros(len(g))
    for ik in range(len(w["kpt"])):
        G = np.asarray(w["kg"][ik])
        C = np.asarray(w["coef"][ik])[:run.nocc].real
        idx = spec.gindex(G)
        for gi, gg in enumerate(g):
            s = 0.0
            for j, g2 in enumerate(G):
                p = idx.get(tuple(g2 + gg))
                if p is not None:
                    s += float(np.dot(C[:, p], C[:, j]))
            acc[gi] += w["kw"][ik] * s
    return float(np.abs(r - 2.0 * acc).max()), [list(map(float, k)) for k in w["kpt"]], \
        [float(x) for x in w["kw"]]


# --------------------------------------------------------- the k.p limit

class Limit:
    """The scaled q -> 0 limit E~0(u) of the Epsilon q0 block and E~(t0)."""

    def __init__(self, rundir, run):
        self.er = er = spec.EpsilonRun(rundir, run.nbands, run.ecuts)
        self.run = run
        cr = er.cr
        self.B = cr.bdot
        q0 = np.asarray(run.eps0["q"][0]["q"], float)
        if not np.array_equal(q0, T0 * U0):
            raise ValueError(f"q0 = {q0} is not {T0} * {U0}")
        self.q0 = q0
        self.Gs, _ = spec.sphere_of(cr, er.gvec, q0, run.ecuts)
        Gs = self.Gs
        n = len(Gs)
        self.n = n
        self.z = int(np.flatnonzero(~Gs.any(axis=1))[0])
        nv, nb = 4, run.nbands
        fact = I.exact(4.0) / (I.exact(float(len(er.kfull))) * I.exact(cr.celvol))
        self.fact = fact
        Bm = I.exact(self.B)
        H = I.exact(np.zeros((3, 3)))
        A = I.exact(np.zeros((n, 3)))
        body = I.exact(np.zeros((n, n)))
        chi_t0 = I.exact(np.zeros((n, n)))
        for k in er.kfull:
            Gk, ck, Ek = cert.real_coeffs(er.wf, tuple(k))
            M0 = cert.mtxel_iv(Gk, ck[:nv], Gk, ck[nv:nb], Gs)              # (v, c, G) at q = 0
            # P_x,b = sum_G c_c(G) c_v(G) 2 ((k+G).B)_b / (E_v - E_c)
            kG = I.exact(Gk.astype(float)) + I.exact(np.broadcast_to(k, Gk.shape).copy())
            kGB = [None] * 3
            for b in range(3):
                acc = None
                for a in range(3):
                    term = kG[:, a] * I.exact(np.full(len(Gk), self.B[a, b]))
                    acc = term if acc is None else acc + term
                kGB[b] = acc * I.exact(2.0)                                   # (G,)
            dE = I.exact(Ek[:nv, None]) - I.exact(Ek[None, nv:nb])            # (v, c)
            P = []
            for b in range(3):
                prod = I.exact(ck[:nv, None, :]) * I.exact(ck[None, nv:nb, :]) * \
                    I(kGB[b].lo[None, None, :], kGB[b].hi[None, None, :])
                P.append(prod.sum(axis=2) / dE)                              # (v, c)
            # Epsilon at q0: valence at k + q0 from WFNq
            Gv, cv, Ev = cert.real_coeffs(er.wfq, tuple(np.round(k + q0, 12)))
            Mq = cert.mtxel_iv(Gv, cv[:nv], Gk, ck[nv:nb], Gs)
            for v in range(nv):
                for c in range(nb - nv):
                    ed = I.exact(1.0) / dE[v, c]
                    p = [P[b][v, c] for b in range(3)]
                    for a in range(3):
                        for b in range(3):
                            H[a, b] = H[a, b] + p[a] * p[b] * ed
                    x0 = M0[v, c]
                    for b in range(3):
                        col = x0 * p[b] * ed
                        A.lo[:, b], A.hi[:, b] = (A[:, b] + col).lo, (A[:, b] + col).hi
                    body = body + (x0.reshape(n, 1) * x0.reshape(1, n)) * ed
                    xq = Mq[v, c]
                    edq = I.exact(1.0) / (I.exact(Ev[v]) - I.exact(Ek[nv + c]))
                    chi_t0 = chi_t0 + (xq.reshape(n, 1) * xq.reshape(1, n)) * edq
        self.H = H * fact
        self.A = A * fact
        self.body = body * fact
        self.chi_t0 = chi_t0 * fact
        n2 = cert.norm2(self.B, Gs.astype(float))
        n2.lo[self.z] = n2.hi[self.z] = 1.0                                   # z entry unused
        self.vG = I.exact(8.0) * iv.PI / n2
        self.vq0 = I.exact(8.0) * iv.PI / cert.norm2(self.B, Gs.astype(float), q0)

    def unorm2(self, u):
        return cert.norm2(self.B, np.atleast_2d(u))[0]

    def chi0s(self, u):
        """The scaled chi limit at direction u (crystal coordinates)."""
        n, z = self.n, self.z
        U = [I.exact(float(u[b])) for b in range(3)]
        X = self.body.copy()
        h = None
        for a in range(3):
            for b in range(3):
                t = self.H[a, b] * U[a] * U[b]
                h = t if h is None else h + t
        w = None
        for b in range(3):
            t = self.A[:, b] * U[b]
            w = t if w is None else w + t
        X.lo[z, :], X.hi[z, :] = w.lo, w.hi
        X.lo[:, z], X.hi[:, z] = w.lo, w.hi
        X.lo[z, z], X.hi[z, z] = h.lo, h.hi
        return X

    def E0(self, u):
        n, z = self.n, self.z
        others = np.arange(n) != z
        vt = I(np.where(others, self.vG.lo, 0.0), np.where(others, self.vG.hi, 0.0))
        vz = I.exact(8.0) * iv.PI / self.unorm2(u)
        vt.lo[z], vt.hi[z] = vz.lo, vz.hi
        return I.exact(np.eye(n)) - self.chi0s(u) * vt.reshape(n, 1)

    def Et0(self):
        """E~(t0) = diag(s) eps(q0) diag(s)^-1, s = (t0 at z, 1 elsewhere)."""
        n, z = self.n, self.z
        eps = I.exact(np.eye(n)) - self.chi_t0 * self.vq0.reshape(n, 1)
        s = np.ones(n)
        s[z] = T0
        sc = I.exact(s)
        return eps * sc.reshape(n, 1) / sc.reshape(1, n)

    def inv(self, M):
        """Componentwise inverse enclosure with the q0 balancing of cert.epsinv_iv."""
        return iv.inverse_cw(M)[0]

    def unscaled_inverse(self, X):
        """eps^-1 entries on the ray at t0 would be X_ij s_j / s_i; for the q = 0 block
        Sigma uses only head and body (wings are zeroed), so the block injected is X
        with its wings set to 0 (they never enter; see EpsQ0Sigma.sigA_eq_theory_q0)."""
        z = self.z
        Y = X.copy()
        others = np.arange(self.n) != z
        Y.lo[z, others] = Y.hi[z, others] = 0.0
        Y.lo[others, z] = Y.hi[others, z] = 0.0
        return Y


# ----------------------------------------------------------- the q = 0 cell

def cell_radius(B, u):
    """r(u) of the Wigner-Seitz cell of the Sigma q-grid lattice {n/2} (crystal)."""
    ns = np.array([(a, b, c) for a in range(-3, 4) for b in range(-3, 4) for c in range(-3, 4)
                   if (a, b, c) != (0, 0, 0)], float) / 2.0
    ub = ns @ B @ u
    g2 = np.einsum("ij,jk,ik->i", ns, B, ns)
    pos = ub > 1e-14
    return float(np.min(g2[pos] / (2.0 * ub[pos])))


def fibonacci_dirs(n, B):
    """n Cartesian unit vectors on a Fibonacci sphere, returned in crystal coordinates
    with |u|_B = 1 (B = bvec bvec^T; u = bvec^-T c)."""
    L = np.linalg.cholesky(B)             # B = L L^T: u^T B u = |L^T u|^2
    Linv_T = np.linalg.inv(L.T)
    out = []
    g = (1 + 5 ** 0.5) / 2
    for i in range(n):
        zc = 1 - (2 * i + 1) / n
        r = np.sqrt(1 - zc * zc)
        ph = 2 * np.pi * i / g
        c = np.array([r * np.cos(ph), r * np.sin(ph), zc])
        out.append(Linv_T @ c)
    return out


# ------------------------------------------------------------- Sigma side

class Sig:
    def __init__(self, rundir, run, coul, blocks, rho):
        self.run = run
        self.sig = cert.SigmaIV(run, coul, blocks, rho)
        self.orig0 = self.sig.scr.irr[0]
        kX, kL = run.kpts[2], run.kpts[1]
        self.kX, self.kL = kX, kL
        self.preX, self.pX, _ = self.sig.parts(kX, [5, 6], all_q0_ops=False)
        self.preL, self.pL, _ = self.sig.parts(kL, [5], all_q0_ops=False)

    def set_block0(self, G, E):
        qi, _, is0 = self.orig0
        self.sig.scr.irr[0] = (qi, {"G": G, "E": E}, is0)

    def reset_block0(self):
        self.sig.scr.irr[0] = self.orig0

    def q0parts(self, iop):
        z = np.zeros(3)
        return (self.sig.qpart(self.preX, self.kX, z, {(0.0, 0.0, 0.0): iop}),
                self.sig.qpart(self.preL, self.kL, z, {(0.0, 0.0, 0.0): iop}))

    def o1(self, pxq0, plq0):
        eX = self.sig.eqp1(self.preX, cert.total(self.pX, pxq0))[0]
        eL = self.sig.eqp1(self.preL, cert.total(self.pL, plq0))[0]
        return eX, eL, eX - eL


def iv2(x):
    return [float(x.lo), float(x.hi)]


def per_op(S, label):
    out = {}
    for iop in range(48):
        px, pl = S.q0parts(iop)
        eX, eL, o = S.o1(px, pl)
        out[iop] = dict(eX=iv2(eX), eL=iv2(eL), O1=iv2(o))
    print(f"  {label}: O1 classes (meV)",
          sorted({round(v["O1"][0] * 1e3, 4) for v in out.values()}), flush=True)
    return out


_W = {}


def _dir_worker(args):
    i, u = args
    S, L = _W["S"], _W["L"]
    X = L.inv(L.E0(u))
    S.set_block0(L.Gs, L.unscaled_inverse(X))
    px, pl = S.q0parts(0)                     # op 0 is the identity
    return i, [[a.lo.tolist(), a.hi.tolist()] for a in px], [[a.lo.tolist(), a.hi.tolist()] for a in pl]


def angular(S, L, dirs, weights, workers):
    """Weighted average of the q = 0 parts over directions, then O1 (quadrature)."""
    _W["S"], _W["L"] = S, L
    jobs = list(enumerate(dirs))
    if workers > 1:
        with mp.get_context("fork").Pool(workers) as pool:
            res = pool.map(_dir_worker, jobs, chunksize=4)
    else:
        res = [_dir_worker(j) for j in jobs]
    res.sort()
    W = np.asarray(weights, float) / np.sum(weights)
    accX = accL = None
    per = []
    for (i, px, pl), w in zip(res, W):
        PX = [I(np.array(a[0]), np.array(a[1])) for a in px]
        PL = [I(np.array(a[0]), np.array(a[1])) for a in pl]
        eX, eL, o = S.o1(PX, PL)
        per.append(float(o.mid()))
        wX = [p * I.exact(w) for p in PX]
        wL = [p * I.exact(w) for p in PL]
        accX = wX if accX is None else [a + b for a, b in zip(accX, wX)]
        accL = wL if accL is None else [a + b for a, b in zip(accL, wL)]
    eX, eL, o = S.o1(accX, accL)
    return dict(O1=iv2(o), per_direction_min=min(per), per_direction_max=max(per),
                per_direction_unweighted_mean=float(np.mean(per)))


# ------------------------------------------------------------------ main

def run_all(rundir, coulomb, ndir, workers):
    t_start = time.time()
    run = spec.Run(rundir)
    rho = bgwio.read_rho(pathlib.Path(rundir) / "RHO")
    coul = cert.CertCoulomb(coulomb)
    out = {"q0": [0.0, 0.0, T0]}

    # 1. RHO
    asym, rho_sym = rho_star(rho, run.cr)
    rec, kpts, kw = rho_ibz_reconstruction(run, rho)
    asym_sym, _ = rho_star(rho_sym, run.cr)
    out["rho"] = dict(star_asymmetry_max=asym, symmetrized_star_asymmetry_max=asym_sym,
                      ibz_reconstruction_max_dev=rec, ibz_kpts=kpts, ibz_weights=kw)
    print("RHO star asymmetry", asym, "IBZ reconstruction dev", rec, flush=True)

    # 2. the k.p limit
    t = time.time()
    L = Limit(rundir, run)
    X0 = L.inv(L.E0(U0))
    Et = L.Et0()
    D = Et - L.E0(U0)
    delta = iv_row_norm_up(D)
    beta = iv_row_norm_up(X0)
    # beta, delta are upper bounds and beta^2 delta/(1 - beta delta) is increasing in both
    # (beta delta < 1), so the bound is evaluated in iv.py and its upper end reported
    bI, dI = I.exact(beta), I.exact(delta)
    bdI = bI * dI
    bd_up = float(bdI.hi)
    bnd = float((bI * bI * dI / (I.exact(1.0) - bdI)).hi) if bd_up < 1 else None
    qs = [(run.eps0["q"][0]["q"], True)] + [(b["q"], False) for b in run.eps["q"]]
    blocks = []
    for q, isq0 in qs:
        Gs, E, _, _ = cert.epsinv_iv(rundir, run.nbands, run.ecuts, q, isq0)
        blocks.append((Gs, E))
    Gq0, Eq0 = blocks[0]
    if not np.array_equal(Gq0, L.Gs):
        raise ValueError("sphere order differs")
    z, n = L.z, L.n
    oth = np.arange(n) != z
    Ez = Eq0
    diff_head = (Ez[z, z] - X0[z, z]).mag()
    diff_body = float((Ez - X0).mag()[np.ix_(oth, oth)].max())
    row = Ez[z, :] * I.exact(T0) - X0[z, :]
    col = Ez[:, z] / I.exact(T0) - X0[:, z]
    out["limit"] = dict(
        t0=T0, u0=U0.tolist(), n=n, z=z,
        head_chi_coef=iv2(L.H[2, 2]),
        head_eps_inv_limit=iv2(X0[z, z]), head_eps_inv_q0=iv2(Ez[z, z]),
        eps_M_limit=iv2(X0[z, z].recip()),
        delta_linf=delta, beta_linf=beta, beta_delta=bd_up, q0_error_bound=bnd,
        K_empirical=delta / T0,
        actual_head_diff=float(diff_head), actual_body_diff_max=diff_body,
        actual_rowwing_scaled_diff_max=float(row.mag()[oth].max()),
        actual_colwing_scaled_diff_max=float(col.mag()[oth].max()),
        raw_row_wing_max=float(Ez[z, :].mag()[oth].max()),
        raw_col_wing_max=float(Ez[:, z].mag()[oth].max()),
        head_chi_q0_over_t0sq=iv2(L.chi_t0[z, z] / (I.exact(T0) * I.exact(T0))),
        wing_chi_q0_over_t0_max_diff=float((L.chi_t0[z, :] / I.exact(T0) - L.A[:, 2]).mag()[oth].max()),
        body_chi_q0_max_diff=float((L.chi_t0 - L.body).mag()[np.ix_(oth, oth)].max()),
        seconds=time.time() - t)
    print("limit", json.dumps(out["limit"], indent=1), flush=True)

    # 3. isotropy and body direction dependence
    axes = {"b1": [1, 0, 0], "b2": [0, 1, 0], "b3": [0, 0, 1], "b1+b2+b3": [1, 1, 1]}
    rng = np.random.default_rng(1)
    dirs = {k: np.array(v, float) for k, v in axes.items()}
    for i in range(4):
        dirs[f"random{i}"] = rng.normal(size=3)
    epsM, bodies = {}, {}
    for k, u in dirs.items():
        u = u / np.sqrt(u @ L.B @ u)
        dirs[k] = u
        X = L.inv(L.E0(u))
        epsM[k] = iv2(X[z, z].recip())
        bodies[k] = X
    lo = min(v[0] for v in epsM.values())
    hi = max(v[1] for v in epsM.values())
    bd = max(float((bodies[a] - bodies[b]).mag()[np.ix_(oth, oth)].max())
             for a in bodies for b in bodies)
    spread = float((I.exact(hi) - I.exact(lo)).hi)      # upper bound
    out["isotropy"] = dict(eps_M=epsM, eps_M_spread=spread,
                           head_tensor=[[iv2(L.H[a, b]) for b in range(3)] for a in range(3)],
                           body_limit_max_direction_dependence=bd)
    print("isotropy spread", spread, "body dir dependence", bd, flush=True)

    # 4. O1
    res = {}
    for label, rr in (("production_rho", rho), ("symmetrized_rho", rho_sym)):
        t = time.time()
        S = Sig(rundir, run, coul, blocks, rr)
        r = {}
        S.reset_block0()
        r["q0_block_per_op"] = per_op(S, label + " q0 block")
        S.set_block0(L.Gs, L.unscaled_inverse(X0))
        r["limit_block_per_op"] = per_op(S, label + " limit block")
        for key in ("q0_block_per_op", "limit_block_per_op"):
            ops = r[key]
            r[key.replace("per_op", "op_average_48")] = [
                float(np.mean([ops[i]["O1"][0] for i in range(48)])),
                float(np.mean([ops[i]["O1"][1] for i in range(48)]))]
        r["op_average_48_note"] = (
            "float: the plain-float mean of the 48 lower and of the 48 upper endpoints of the "
            "per-op O1 intervals (eV), i.e. a mean of O1 over the ops. Not an enclosure, and "
            "not spec B (cert.py's O1_specB_direction_average averages the q = 0 parts before "
            "the linearised Eqp1)")
        # angular average of the q -> 0 limit over the q = 0 cell
        ang = {}
        for nd in (ndir // 2, ndir):
            ds = fibonacci_dirs(nd, L.B)
            ws = [cell_radius(L.B, u) ** 3 for u in ds]
            ang[str(nd)] = angular(S, L, ds, ws, workers)
            print(f"  {label} angular average N={nd}:", ang[str(nd)], flush=True)
        r["angular_average"] = ang
        S.reset_block0()
        r["seconds"] = time.time() - t
        res[label] = r
    out["O1"] = res
    out["seconds"] = time.time() - t_start
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("rundir")
    ap.add_argument("--coulomb", default=str(ROOT / "bgw/endpoint/data/coulomb_cert.json"))
    ap.add_argument("--ndir", type=int, default=400)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--out", default=str(ROOT / "bgw/bridge_q0/data/q0.json"))
    a = ap.parse_args(argv)
    res = run_all(a.rundir, a.coulomb, a.ndir, a.workers)
    pathlib.Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    pathlib.Path(a.out).write_text(json.dumps(res, indent=1) + "\n")
    print("->", a.out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
