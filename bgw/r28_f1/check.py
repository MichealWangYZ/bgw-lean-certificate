#!/usr/bin/env python3
"""R28-F1 target 2: are BerkeleyGW's screening data (WFN, WFNq) and self-energy data
(WFN_inner, RHO) images of ONE finite mean-field system (GW/Bridge/Common.lean, `Compat`)?

    python3 bgw/r28_f1/check.py [--eps DIR] [--sig DIR] [--run DIR] [--out FILE]

`--run DIR` is a single fresh pinned run (bgw/endpoint/run_production.py, all files in
one directory); otherwise `--eps` holds WFN, WFNq, epsilon.inp and `--sig` holds
WFN_inner, RHO, sigma.inp (defaults: ~/bgw-src/runs/eps and ~/bgw-src/runs/sig-pristine).

The fields `Compat` needs to agree on (GW/Bridge/Common.lean, `MF`, `MF.inp`, `MF.gl`,
`MF.st`):

  (F1) the cell: bdot (`B`), celvol (`Om`) -- shared by the eps Input and Sigma's Gl;
  (F2) the k-grid: the eps k-sum runs over EVERY grid point and Sigma's k0 - q_t are grid
       points of the SAME grid;
  (F3) per grid point: the G-sphere, the coefficient rows and the energies of every band
       (eps: valence at k+q, conduction at k; Sigma: all bands at k0 - q_t);
  (F4) nocc and the band count nb (all bands of the system on both sides);
  (F5) the density: RHO is the density of the system's occupied orbitals (`DensOK`).

What is computed (float64; independent of Lean, reads only the BerkeleyGW files through
bgw/endpoint/bgwio.py, and spec.py's `Wfn` for the space-group unfolding used in F5):

  1. header equality WFN / WFNq / WFN_inner (bitwise), F1;
  2. the k-sets: the 48-op closure of WFN's k-points (what Epsilon sums), of WFNq's, of
     WFN_inner's, and the k0 - q points Sigma uses; their intersection (mod G), F2;
  3. "same Hamiltonian, different sampling": a local potential V(g) (V(g) = V(-g)) and a
     kinetic scale alpha fitted by least squares to WFN_inner's eigenpairs
     (sum_G' [alpha |k+G|^2 delta + V(G-G')] c(G') = E c(G)); the fitted H re-diagonalised
     at WFN's and WFNq's k-points against their stored energies and eigenvectors;
  4. the band counts, nocc and number_bands of epsilon.inp / sigma.inp, F4;
  5. RHO against the density of the Sigma system (WFN_inner unfolded to the 8-point
     2x2x2 grid), of the eps system (WFN, 32 points), and the BRIDGE-FIX replay
     (3 IBZ points, weights 1/8, 4/8, 3/8, no star sum), F5;
  6. the premise `hnp` of `hyps_unsat_of_unpaired` on the Sigma grid: for each Sigma
     k-point, whether any of the 8 grid points stores, as an ORDERED list, the negated
     ordered sphere list of that k-point.
"""
import argparse
import json
import pathlib
import sys

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "bgw/endpoint"))
import bgwio  # noqa: E402
import spec  # noqa: E402

RYD_MEV = 13605.69253
HEADER = ["nspin", "ng", "ntran", "nat", "ecutrho", "ecutwfc", "FFTgrid", "celvol", "alat",
          "avec", "adot", "recvol", "blat", "bvec", "bdot", "mtrx", "tnp", "apos", "atyp",
          "gvec", "kgrid"]


def parse_kv(text):
    kv = {}
    for line in text.splitlines():
        s = line.split()
        if s and not s[0].startswith("#"):
            kv.setdefault(s[0], s[1:])
    return kv


# ---------------------------------------------------------------- 1. headers

def headers(files):
    names = list(files)
    ref = files[names[0]]
    out = {}
    for key in HEADER + ["kshift", "nbands"]:
        out[key] = {n: bool(np.array_equal(np.asarray(ref[key]), np.asarray(files[n][key])))
                    for n in names[1:]}
    return out


# ---------------------------------------------------------------- 2. k-sets

def closure(kpts, mtrx):
    pts = {}
    for k in kpts:
        for M in mtrx:
            p = M @ k
            p = p - np.floor(p + 1e-9)
            pts.setdefault(tuple(np.round(p, 9)), p)
    return pts


def kkey(p):
    p = np.asarray(p, float)
    p = p - np.floor(p + 1e-9)
    return tuple(np.round(p, 9))


def dist_mod(a, b):
    d = np.asarray(a) - np.asarray(b)
    return float(np.max(np.abs(d - np.rint(d))))


def ksets(w, wq, wi, sig_kpts, qgrid):
    mt = w["mtrx"]
    eps = closure(w["kpt"], mt)
    epsq = closure(wq["kpt"], mt)
    inner = closure(wi["kpt"], mt)
    g = qgrid
    qs = [np.array([i / g[0], j / g[1], l / g[2]])
          for i in range(g[0]) for j in range(g[1]) for l in range(g[2])]
    used = {kkey(k0 - q) for k0 in sig_kpts for q in qs}
    common = set(eps) & (set(inner) | used)
    mind = min(dist_mod(a, b) for a in eps.values() for b in inner.values())
    # eps grid closed under +q for the eps q != 0 points; q0 partners in WFNq's closure
    return {
        "eps_kset_size": len(eps), "epsq_kset_size": len(epsq),
        "sigma_kset_size": len(inner), "sigma_k_minus_q_size": len(used),
        "sigma_k_minus_q_in_inner_closure": all(k in inner for k in used),
        "eps_and_sigma_common_points": len(common),
        "min_distance_eps_to_sigma_crystal": mind,
        "eps_shift": w["kshift"].tolist(), "sigma_shift": wi["kshift"].tolist(),
        "eps_ibz": w["kpt"].tolist(), "sigma_ibz": wi["kpt"].tolist(),
        "eps_ks": [list(k) for k in eps], "sigma_ks": [list(k) for k in inner],
    }


def eps_plus_closed(w, qlist):
    eps = closure(w["kpt"], w["mtrx"])
    return {str([float(x) for x in q]): all(kkey(k + q) in eps for k in eps.values())
            for q in qlist}


def q0_partners(w, wq, q0):
    """Epsilon's q0 block pairs (k + q0 from WFNq, k from WFN): k + q0 in WFNq's closure,
    and not a WFN grid point (the partners are auxiliary states, not grid states)."""
    eps = closure(w["kpt"], w["mtrx"])
    epsq = closure(wq["kpt"], wq["mtrx"])
    return {"q0": [float(x) for x in q0],
            "k_plus_q0_in_WFNq": all(kkey(k + q0) in epsq for k in eps.values()),
            "k_plus_q0_in_WFN_grid": any(kkey(k + q0) in eps for k in eps.values())}


# ---------------------------------------------------------------- 3. Hamiltonian

def canon(g):
    g = tuple(int(x) for x in g)
    m = tuple(-x for x in g)
    return max(g, m)


def fit_hamiltonian(w, nbands=None):
    """Least squares for (alpha, V) on all eigenpairs of the file."""
    cols, rows_A, rows_b = {}, [], []
    B = w["bdot"]
    nb = nbands or w["nbands"]
    for ik, k in enumerate(w["kpt"]):
        G = w["kg"][ik]
        C = w["coef"][ik][:nb]
        E = w["energies"][0, ik][:nb]
        kG = k[None, :] + G
        T = np.einsum("ia,ab,ib->i", kG, B, kG)
        n = len(G)
        D = G[:, None, :] - G[None, :, :]
        idx = np.empty((n, n), int)
        for i in range(n):
            for j in range(n):
                idx[i, j] = cols.setdefault(canon(D[i, j]), len(cols))
        rows_A.append((idx, C, T))
        rows_b.append((C, E))
    ncol = len(cols) + 1
    blocks, rhs = [], []
    for (idx, C, T), (_, E) in zip(rows_A, rows_b):
        nbk, n = C.shape
        A = np.zeros((nbk * n, ncol))
        for b in range(nbk):
            r0 = b * n
            for i in range(n):
                np.add.at(A[r0 + i], 1 + idx[i], C[b])
            A[r0:r0 + n, 0] = T * C[b]
        blocks.append(A)
        rhs.append((E[:, None] * C).ravel())
    A = np.vstack(blocks)
    b = np.concatenate(rhs)
    x, *_ = np.linalg.lstsq(A, b, rcond=None)
    res = A @ x - b
    V = {g: x[1 + i] for g, i in cols.items()}
    return float(x[0]), V, float(np.max(np.abs(res)))


def predict(w, alpha, V, nbands=None):
    """Re-diagonalise the fitted H at the file's k-points; max |dE| and min overlap."""
    B = w["bdot"]
    nb = nbands or w["nbands"]
    dE, ov, missing = 0.0, 1.0, 0
    for ik, k in enumerate(w["kpt"]):
        G = w["kg"][ik]
        kG = k[None, :] + G
        T = np.einsum("ia,ab,ib->i", kG, B, kG)
        n = len(G)
        H = np.diag(alpha * T)
        for i in range(n):
            for j in range(n):
                g = canon(G[i] - G[j])
                if g in V:
                    H[i, j] += V[g]
                elif any(G[i] - G[j]):
                    missing += 1
        ev, U = np.linalg.eigh(H)
        E = w["energies"][0, ik][:nb]
        C = w["coef"][ik][:nb]
        dE = max(dE, float(np.max(np.abs(ev[:nb] - E))))
        # overlaps by degenerate subspace of the fitted H (a group may extend past nb)
        i = 0
        while i < nb:
            j = i + 1
            while j < len(ev) and abs(ev[j] - ev[i]) < 1e-8:
                j += 1
            P = np.abs(C[i:min(j, nb)] @ U[:, i:j]) ** 2
            ov = min(ov, float(np.min(P.sum(axis=1))))
            i = j
    return {"max_dE_Ry": dE, "max_dE_meV": dE * RYD_MEV, "min_subspace_overlap": ov,
            "unfitted_offdiag_entries": missing}


# ---------------------------------------------------------------- 5. density

def density(wf, kpts, weights, nocc, gkeys):
    """rho(g) = 2 sum_k w_k sum_{n<nocc} sum_{G1-G2=g} c(G1) conj c(G2)."""
    rho = dict.fromkeys(gkeys, 0j)
    for k, wk in zip(kpts, weights):
        G, c, _ = wf.at(tuple(k))
        n = len(G)
        D = (G[:, None, :] - G[None, :, :]).reshape(-1, 3)
        Pm = np.einsum("ni,nj->ij", c[:nocc], np.conj(c[:nocc])).ravel()
        for d, p in zip(map(tuple, D), Pm):
            if d in rho:
                rho[d] += 2 * wk * p
            elif abs(p) > 1e-12:
                raise ValueError(f"density component outside RHO's list: {d}")
        del n
    return rho


def density_compare(rhofile, wi, w, nocc):
    gv = [tuple(int(x) for x in g) for g in rhofile["gvec"]]
    R = dict(zip(gv, rhofile["rho"]))
    cri, cre = spec.Crystal(wi), spec.Crystal(w)
    wfi, wfe = spec.Wfn(wi, cri), spec.Wfn(w, cre)
    grid = list(closure(wi["kpt"], wi["mtrx"]).values())
    egrid = list(closure(w["kpt"], w["mtrx"]).values())
    out = {}
    for name, wf, pts, wts in [
            ("sigma_system_8pt", wfi, grid, [1 / len(grid)] * len(grid)),
            ("eps_system_32pt", wfe, egrid, [1 / len(egrid)] * len(egrid)),
            ("ibz_replay_no_star", wfi, list(wi["kpt"]), list(wi["kw"]))]:
        rho = density(wf, pts, wts, nocc, gv)
        d = np.array([rho[g] - R[g] for g in gv])
        imag = max(abs(v.imag) for v in rho.values())
        worst = int(np.argmax(np.abs(d)))
        out[name] = {"rho0": float(rho[(0, 0, 0)].real),
                     "max_abs_minus_RHO": float(np.max(np.abs(d))),
                     "worst_g": list(gv[worst]),
                     "worst_values": [float(rho[gv[worst]].real), float(R[gv[worst]])],
                     "max_imag": float(imag),
                     "rho(b3)": float(rho[(0, 0, 1)].real), "rho(b1)": float(rho[(1, 0, 0)].real),
                     "rho(-2,-1,-1)": float(rho[(-2, -1, -1)].real)}
    # the 48-op star average of RHO (the "symmetrized RHO" of BRIDGE-Q0, row Q-6) against
    # the Sigma system's own density: equal => Q-6's O1 shift is the size of DensOK's failure
    g = np.array(gv)
    r = np.array([R[x] for x in gv], float)
    pos = {x: i for i, x in enumerate(gv)}
    acc = np.zeros_like(r)
    for Mx, t in zip(wi["mtrx"], wi["tnp"]):
        hg = g @ np.asarray(Mx).T
        ph = np.rint(np.cos(hg @ np.asarray(t)))
        acc += r[[pos[tuple(int(y) for y in x)] for x in hg]] * ph
    acc /= len(wi["mtrx"])
    rho8 = density(wfi, grid, [1 / len(grid)] * len(grid), nocc, gv)
    out["star_average_RHO_vs_sigma_system"] = float(
        np.max(np.abs(acc - np.array([rho8[x].real for x in gv]))))
    out["RHO_first_shell"] = {"rho(b3)": float(R[(0, 0, 1)]), "rho(-b3)": float(R[(0, 0, -1)]),
                              "rho(b1)": float(R[(1, 0, 0)]),
                              "rho(-2,-1,-1)": float(R[(-2, -1, -1)])}
    return out


# ---------------------------------------------------------------- 6. hnp

def hnp_check(wi, sig_kpts):
    """`hnp` of GW/Bridge/Common.lean `hyps_unsat_of_unpaired` at k: no grid index j has
    G j = (G k).map (-), as ordered lists. Grid: the 48-op closure of WFN_inner (the
    Sigma grid). Two orderings of the sphere at each grid point: the one Sigma reads
    (spec.Wfn.at, rotated from the IBZ, as in F5) and the lexicographically sorted one
    (WFN_inner's own order at its IBZ points). Exact integer comparisons."""
    wf = spec.Wfn(wi, spec.Crystal(wi))
    grid = list(closure(wi["kpt"], wi["mtrx"]).values())
    rot = [np.asarray(wf.at(tuple(k))[0]).astype(int) for k in grid]
    orders = {"spec_Wfn_at": rot, "lex_sorted": [np.array(sorted(map(tuple, g))) for g in rot]}
    keys = [kkey(k) for k in grid]
    out = {"grid": [[float(x) for x in k] for k in grid],
           "sphere_sizes": [len(g) for g in rot]}
    per = []
    for k in sig_kpts:
        i = keys.index(kkey(k))
        row = {"k": [float(x) for x in k], "grid_index": i,
               "sphere_has_nonzero_vector": bool(np.any(rot[i] != 0))}
        for name, S in orders.items():
            neg = -S[i]
            row[f"ordered_negated_sphere_stored_at_{name}"] = [
                j for j, g in enumerate(S) if g.shape == neg.shape and np.array_equal(g, neg)]
        row["negated_sphere_stored_as_a_set_at"] = [
            j for j, g in enumerate(rot) if set(map(tuple, g)) == set(map(tuple, -rot[i]))]
        row["hnp_holds"] = all(not row[f"ordered_negated_sphere_stored_at_{n}"] for n in orders)
        per.append(row)
    out["sigma_kpoints"] = per
    # residual.py / cert.py: X = sigma.inp k-point 2, L = k-point 1
    out["hnp_holds_X"] = per[2]["hnp_holds"] if len(per) > 2 else None
    out["hnp_holds_L"] = per[1]["hnp_holds"] if len(per) > 1 else None
    # equal ordered lists have equal sets, so an empty set-level match list gives hnp at k
    # for every ordering of every stored sphere
    out["hnp_holds_any_order_X"] = (not per[2]["negated_sphere_stored_as_a_set_at"]
                                    if len(per) > 2 else None)
    out["hnp_holds_any_order_L"] = (not per[1]["negated_sphere_stored_as_a_set_at"]
                                    if len(per) > 1 else None)
    out["note"] = ("hnp_holds_X / hnp_holds_L = true supports the premise hnp of "
                   "hyps_unsat_of_unpaired (GW/Bridge/Common.lean) for X and L on this grid: "
                   "no grid point stores the negated ordered sphere list of X or of L, for the "
                   "two sphere orderings listed. A data check, not a Lean proof. The lex_sorted "
                   "comparison holds by construction (a negated increasing list is decreasing). "
                   "hnp_holds_any_order_X / hnp_holds_any_order_L = true says more: no grid "
                   "point stores the negated sphere of X or of L even as a set, and equal "
                   "ordered lists have equal sets, so for X and L the result does not depend "
                   "on how the spheres are ordered. At Gamma the negated sphere equals its own "
                   "sphere as a set, so the set test cannot decide hnp there and only the "
                   "ordered tests apply")
    return out


# ---------------------------------------------------------------- main

def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--run")
    ap.add_argument("--eps", default=str(pathlib.Path.home() / "bgw-src/runs/eps"))
    ap.add_argument("--sig", default=str(pathlib.Path.home() / "bgw-src/runs/sig-pristine"))
    ap.add_argument("--out")
    ap.add_argument("--no-density", action="store_true")
    a = ap.parse_args(argv)
    ed = pathlib.Path(a.run or a.eps)
    sd = pathlib.Path(a.run or a.sig)
    w = bgwio.read_wfn(ed / "WFN")
    wq = bgwio.read_wfn(ed / "WFNq")
    wi = bgwio.read_wfn(sd / "WFN_inner")
    rho = bgwio.read_rho(sd / "RHO")
    epsin = parse_kv((ed / "epsilon.inp").read_text())
    sigtext = (sd / "sigma.inp").read_text()
    kv, sig_kpts = spec.parse_sigma_inp(sigtext)
    qgrid = bgwio.read_eps(sd / "epsmat")["qgrid"]

    out = {"files": {"eps": str(ed), "sig": str(sd)}}
    out["F1_headers_equal_vs_WFN"] = headers({"WFN": w, "WFNq": wq, "WFN_inner": wi})
    out["F2_ksets"] = ksets(w, wq, wi, sig_kpts, qgrid)
    out["F2_eps_grid_closed_under_q"] = eps_plus_closed(
        w, [np.array([0, 0, 0.5]), np.array([0, 0.5, 0.5])])
    out["F2_q0_partners"] = q0_partners(w, wq, np.array([0.0, 0.0, 0.001]))
    nb_eps = int(epsin["number_bands"][0])
    nb_sig = int(kv["number_bands"][0])
    out["F4_bands"] = {"WFN_nbands": int(w["nbands"]), "WFN_inner_nbands": int(wi["nbands"]),
                       "WFNq_nbands": int(wq["nbands"]),
                       "epsilon_number_bands": nb_eps, "sigma_number_bands": nb_sig,
                       "nocc_WFN": sorted(set(int(x) for x in w["ifmax"])),
                       "nocc_WFN_inner": sorted(set(int(x) for x in wi["ifmax"]))}
    alpha, V, res = fit_hamiltonian(wi)
    alpha_e, Ve, res_e = fit_hamiltonian(w)
    common = [g for g in V if g in Ve and (abs(V[g]) > 1e-6 or abs(Ve[g]) > 1e-6)]
    big = sorted({g for g in V if abs(V[g]) > 1e-6}, key=lambda g: -abs(V[g]))
    out["F3_hamiltonian"] = {
        "fit_on_WFN_inner": {"alpha": alpha, "max_residual_Ry": res,
                             "largest_V": {str(g): V[g] for g in big[:8]}},
        "fit_on_WFN": {"alpha": alpha_e, "max_residual_Ry": res_e},
        "max_abs_V_inner_minus_V_WFN": max(abs(V[g] - Ve[g]) for g in common),
        "inner_H_predicts_WFN": predict(w, alpha, V),
        "inner_H_predicts_WFNq": predict(wq, alpha, V),
        "inner_H_predicts_WFN_inner": predict(wi, alpha, V),
    }
    if not a.no_density:
        out["F5_density"] = density_compare(rho, wi, w, 4)
    out["hnp"] = hnp_check(wi, sig_kpts)
    k = out["F2_ksets"]
    out["verdict"] = {
        "cell_and_G_list_identical": all(all(v.values()) for key, v in
                                         out["F1_headers_equal_vs_WFN"].items()
                                         if key not in ("kshift", "nbands")),
        "same_hamiltonian_to_meV": max(out["F3_hamiltonian"][x]["max_dE_meV"] for x in
                                       ("inner_H_predicts_WFN", "inner_H_predicts_WFNq")),
        "kgrids_disjoint": k["eps_and_sigma_common_points"] == 0,
        "shared_states": k["eps_and_sigma_common_points"],
        "band_counts_agree": nb_eps == nb_sig,
        "compat_holds": False if k["eps_and_sigma_common_points"] == 0 else None,
    }
    txt = json.dumps(out, indent=1, default=float)
    if a.out:
        pathlib.Path(a.out).write_text(txt + "\n")
    else:
        print(txt)
    return out


if __name__ == "__main__":
    main()
