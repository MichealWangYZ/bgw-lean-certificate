"""Independent float64 reproducer of the Si-EPM GPP self-energy (E1).

This module evaluates the SPECIFICATION (docs/ENDPOINT.md section 4) on the
production inputs. It shares no code with BerkeleyGW: wavefunctions are unfolded
with the textbook space-group formula (conventions fixed by the atom-mapping
test, not by BerkeleyGW's gmap), matrix elements are direct plane-wave
convolutions (no FFT), and every production convention it follows is cited.

Units: Rydberg atomic units throughout; eV only at the very end via
RYD = 13.60569253 (Common/nrtype.f90:155).
"""
import functools
import pathlib

import numpy as np

import bgwio

RYD = 13.60569253
TWO_PI = 2.0 * np.pi


# ----------------------------------------------------------------- geometry

class Crystal:
    def __init__(self, wfn):
        self.bdot = wfn["bdot"]
        self.celvol = wfn["celvol"]
        self.avec = wfn["avec"] * wfn["alat"]        # rows: direct vectors (bohr)
        self.bvec = wfn["bvec"] * wfn["blat"]        # rows: reciprocal vectors (1/bohr)
        self.alat = wfn["alat"]
        # atoms: BerkeleyGW stores apos in Cartesian units of alat
        self.apos_frac = np.linalg.solve(self.avec.T, (wfn["apos"] * wfn["alat"]).T).T
        self.mtrx = wfn["mtrx"]                      # action on reciprocal crystal coords
        self.tnp = wfn["tnp"]

    def norm2(self, v):
        """|v|^2 for v in reciprocal crystal coordinates (last axis)."""
        v = np.asarray(v, float)
        return np.einsum("...i,ij,...j->...", v, self.bdot, v)


def real_space_ops(cr, tsign):
    """(W, t) with x -> W x + t on direct crystal coordinates for each op.

    mtrx acts on reciprocal crystal coordinates, so W = mtrx^{-T}. The
    fractional translation is t = tsign * tnp / 2pi; `tsign` is fixed by
    requiring every op to map the atoms onto themselves (atom_mapping_sign)."""
    ops = []
    for M, tau in zip(cr.mtrx, cr.tnp):
        W = np.rint(np.linalg.inv(M).T).astype(int)
        ops.append((W, tsign * tau / TWO_PI))
    return ops


def maps_atoms(cr, W, t):
    x = cr.apos_frac
    y = (W @ x.T).T + t
    for yi in y:
        d = x - yi
        if not np.any(np.all(np.abs(d - np.rint(d)) < 1e-8, axis=1)):
            return False
    return True


def atom_mapping_sign(cr):
    ok = {s: all(maps_atoms(cr, W, t) for W, t in real_space_ops(cr, s)) for s in (+1, -1)}
    good = [s for s, v in ok.items() if v]
    if not good:
        raise ValueError("no translation sign maps the atoms onto themselves")
    if len(good) == 2:
        # both work only if every 2t is a lattice vector, and then +t and -t
        # are the same operation modulo the lattice
        if not all(np.allclose(2 * t, np.rint(2 * t)) for _, t in real_space_ops(cr, +1)):
            raise ValueError("translation sign ambiguous")
    return good[0]


# ------------------------------------------------------------ wavefunctions

class Wfn:
    """Wavefunctions of WFN_inner, unfolded to any k of the full grid."""

    def __init__(self, wfn, cr):
        self.w, self.cr = wfn, cr
        self.tsign = atom_mapping_sign(cr)
        self.ops = real_space_ops(cr, self.tsign)
        self.E = wfn["energies"][0]                   # (nk, nb) Ry
        self.nb = wfn["nbands"]

    def rotate(self, ik, iop, kg0):
        """Coefficients of O psi_{k_ik}, re-expressed at k' = M k + kg0.

        (O psi)(x) = psi(g^{-1} x) with g: x -> W x + t. For psi = sum_G c(G)
        exp(2 pi i (k+G).x): new component at k'+G'' with G'' = M G - kg0 is
        c(G) exp(-2 pi i (M(k+G)).t)."""
        M = self.cr.mtrx[iop]
        W, t = self.ops[iop]
        k = self.w["kpt"][ik]
        G = self.w["kg"][ik]
        MkG = (M @ (k[None, :] + G).T).T
        phase = np.exp(-2j * np.pi * (MkG @ t))
        Gnew = (M @ G.T).T - kg0
        coef = self.w["coef"][ik] * phase[None, :]
        kp = M @ k + kg0
        return kp, Gnew, coef

    def find(self, kp):
        """(ik, iop, kg0) with kp = M k + kg0, first match in (ik, op) order."""
        for ik, k in enumerate(self.w["kpt"]):
            for iop, M in enumerate(self.cr.mtrx):
                d = kp - M @ k
                if np.all(np.abs(d - np.rint(d)) < 1e-9):
                    return ik, iop, np.rint(d).astype(int)
        raise KeyError(kp)

    @functools.lru_cache(maxsize=None)
    def at(self, kp):
        """(G list, coefficient matrix (nb, nG) complex, energies) at kp (tuple)."""
        kp = np.array(kp)
        ik, iop, kg0 = self.find(kp)
        kk, G, c = self.rotate(ik, iop, kg0)
        assert np.allclose(kk, kp)
        return G, c, self.E[ik]


def gindex(G):
    return {tuple(g): i for i, g in enumerate(G)}


def mtxel(Gk, ck, Gq, cq, Gout):
    """M_{n n'}(G) = <n k| e^{i(q+G).r} |n' k-q> = sum_{G2} ck*(G2+G) cq(G2).

    ck: (nk_bands, NGk) at k; cq: (nq_bands, NGq) at k-q, where k-q is carried
    with the same G-origin convention (k-q = kfull + kg0 already absorbed).
    Returns array (nk_bands, nq_bands, len(Gout))."""
    idx = gindex(Gk)
    out = np.zeros((ck.shape[0], cq.shape[0], len(Gout)), complex)
    for j, g in enumerate(Gout):
        pos = np.array([idx.get(tuple(g2 + g), -1) for g2 in Gq])
        m = pos >= 0
        out[:, :, j] = np.conj(ck[:, pos[m]]) @ cq[:, m].T
    return out


# ----------------------------------------------------------------- the run

def parse_sigma_inp(text):
    kv, kpts, lines = {}, [], text.splitlines()
    i = 0
    while i < len(lines):
        s = lines[i].split()
        if not s or s[0].startswith("#"):
            i += 1
            continue
        if s[:2] == ["begin", "kpoints"]:
            i += 1
            while lines[i].split()[0] != "end":
                kpts.append([float(x) for x in lines[i].split()[:3]])
                i += 1
        elif s[0] == "begin":
            while lines[i].split()[0] != "end":
                i += 1
        else:
            kv[s[0]] = s[1:]
        i += 1
    return kv, np.array(kpts)


class Run:
    """Production inputs of one run directory, plus the grids Sigma uses."""

    def __init__(self, rundir):
        d = pathlib.Path(rundir)
        self.dir = d
        self.wfn = bgwio.read_wfn(d / "WFN_inner")
        self.cr = Crystal(self.wfn)
        self.wf = Wfn(self.wfn, self.cr)
        kv, self.kpts = parse_sigma_inp((d / "sigma.inp").read_text())
        self.nbands = int(kv["number_bands"][0])
        self.bmin, self.bmax = int(kv["band_index_min"][0]), int(kv["band_index_max"][0])
        self.eps0 = bgwio.read_eps(d / "eps0mat")
        self.eps = bgwio.read_eps(d / "epsmat")
        self.qgrid = self.eps["qgrid"]
        self.ecuts = self.eps["ecuts"]
        # bare_coulomb_cutoff defaults to the wavefunction cutoff (sigma.out:95)
        self.ecutb = float(kv["bare_coulomb_cutoff"][0]) if "bare_coulomb_cutoff" in kv \
            else self.wfn["ecutwfc"]
        self.nocc = 4
        self.gvec = self.wfn["gvec"]
        # the q-grid of Sigma: full grid, no q-symmetry (no_symmetries_q_grid),
        # the q0 point enters as q = 0 exactly (vcoul dump; genwf_mpi needs it)
        g = self.qgrid
        self.qlist = [np.array([i / g[0], j / g[1], l / g[2]])
                      for i in range(g[0]) for j in range(g[1]) for l in range(g[2])]
        self.fact = 1.0 / (len(self.qlist) * self.cr.celvol)   # sigma_main.f90:1129
        self.check_preconditions(d, kv)

    def check_preconditions(self, d, kv):
        """Run-specific facts under which this transcription equals BerkeleyGW
        4.0 (found by the E1 review). Asserted, so a sweep point outside the
        spec's domain fails loudly instead of being silently misread.

        (a) isotropic q-grid: vcoul_generator folds MC points in dd-scaled
            coordinates, which is the Wigner-Seitz cell only when dd is equal;
        (b,c) q = 0 is the first q of the grid: the exact static CH range
            (isrtrqi/ncoulch from irq_min) and the q0 head (wcoul0 scaled by
            fact only at ika=1, irq_=irq_min) are taken from it;
        (d) wpeff tests gvec index 1 for G = 0: Sigma sorts gvec by |G|^2
            (input.f90:386-433), so index 1 is G = 0 -- nothing to check here
            beyond G = 0 being in the list;
        (e) avgcut: semiconductor screening, no truncation, cell_average_cutoff
            not set -> 1e12 Ry (inread.f90:871-875), wings fixed at every q;
        (f) Vxc = 0 (EPM): VXC and vxc.dat identically zero."""
        g = self.qgrid
        assert g[0] == g[1] == g[2], "(a) anisotropic q-grid"
        assert not self.qlist[0].any(), "(b,c) q = 0 is not the first q"
        assert any(not x.any() for x in self.gvec), "(d) G = 0 missing"
        inp = (d / "sigma.inp").read_text()
        for key in ("cell_average_cutoff", "cell_slab_truncation", "cell_wire_truncation",
                    "cell_box_truncation", "screening_metal", "screening_graphene",
                    "invalid_gpp_mode", "gpp_broadening", "gpp_sexcutoff", "finite_difference_form",
                    "finite_difference_spacing"):
            assert not any(l.split()[:1] == [key] for l in inp.splitlines()), f"(e) {key} set"
        assert "screening_semiconductor" in inp, "(e) not semiconductor screening"
        # dont_use_vxcdat: Sigma takes Vxc from the VXC file
        assert "dont_use_vxcdat" in inp, "(f) Vxc source is not the VXC file"
        v = bgwio.read_rho(d / "VXC", kind="VXC")
        assert not np.any(v["rho"]), "(f) Vxc != 0"

    def sphere(self, q, ecut):
        """G in the global list with |q+G|^2 < ecut (gcutoff, strict)."""
        n2 = self.cr.norm2(q[None, :] + self.gvec)
        return self.gvec[n2 < ecut], n2[n2 < ecut]


def bgw_order(run, q, G):
    """Order of sortrx with its gvec tie-break (Common/sort_inc.f90:15-18,
    sort.F90:204-217): ascending |q+G|^2, values within TOL_Zero = 1e-12 tied,
    ties broken by GK = g3 + E3*(g2 + E2*g1), E = extent of the global list."""
    ext = run.gvec.max(axis=0) - run.gvec.min(axis=0) + 1
    GK = G[:, 2] + ext[2] * (G[:, 1] + ext[1] * G[:, 0])
    ek = run.cr.norm2(q[None, :] + G)
    order = np.argsort(ek, kind="stable")
    out, i = [], 0
    while i < len(order):
        j = i + 1
        while j < len(order) and ek[order[j]] - ek[order[j - 1]] <= 1e-12:
            j += 1
        grp = order[i:j]
        out.extend(grp[np.argsort(GK[grp], kind="stable")])
        i = j
    return np.array(out)


def bare_exchange(run, k, vbar):
    """Sigma_x for bands bmin..bmax at k (Ry), before multiplet averaging.

    Sigma_x,nn(k) = - fact * sum_q sum_{n' occ} sum_{|q+G|^2<ecutb}
                    |M_nn'(k,q,G)|^2 vbar(q+G)       (sigma_main.f90:1614-1639)
    `vbar(qk)` returns the (unscaled) Coulomb average at qk = q+G."""
    Gk, ck, Ek = run.wf.at(tuple(k))
    nb = np.arange(run.bmin - 1, run.bmax)
    X = np.zeros(len(nb))
    for q in run.qlist:
        Gs, _ = run.sphere(q, run.ecutb)
        Gq, cq, Eq = run.wf.at(tuple(k - q))
        M = mtxel(Gk, ck[nb], Gq, cq[:run.nocc], Gs)
        v = np.array([vbar(tuple(q + g)) for g in Gs])
        X -= run.fact * np.einsum("nmg,g->n", np.abs(M) ** 2, v)
    return X


# -------------------------------------------------------------- screening

TOL_SMALL, TOL_ZERO = 1e-6, 1e-12            # Common/nrtype.f90:161-162


class Screening:
    """eps^-1 on the sphere |q+G|^2 < ecuts at every q of the grid, by the
    space-group formula from the irreducible q of eps0mat/epsmat, with
    BerkeleyGW's semiconductor wing treatment applied (Common/fixwings.f90,
    called for the q0 point with q0flag and, since avgcut = 1e12 Ry, for every
    other q with q0flag = false: sigma_main.f90:1250-1290)."""

    def __init__(self, run, vbar, oneoverq, choose_op="last", blocks=None):
        """`blocks`: optional [(G list, eps^-1)] replacing eps0mat then epsmat
        in file order (E1.3: the recomputed screening)."""
        self.run, self.vbar, self.oneoverq = run, vbar, oneoverq
        cr = run.cr
        self.irr = [(np.zeros(3), run.eps0["q"][0], True)] + \
                   [(b["q"], b, False) for b in run.eps["q"]]
        if blocks is not None:
            self.irr = [(qi, {"G": G, "E": E}, is0)
                        for (qi, _, is0), (G, E) in zip(self.irr, blocks)]
        self.gidx = gindex(run.eps["gvec"])
        self.choose_op = choose_op

    def block_matrix(self, b):
        """eps^-1 of one irreducible block keyed by G (crystal integer tuples)."""
        if "G" in b:
            return b["G"], b["E"]
        G = self.run.eps["gvec"][b["isrtx"][:b["nmtx"]] - 1]
        return G, b["epsinv"]

    def mapping(self, q):
        """Index/phase map from the irreducible block to the sphere at q
        (no arithmetic on eps values): (Gs, b, is0, iop, g0, Gi, phase, nops)."""
        run, cr = self.run, self.run.cr
        Gs, n2 = run.sphere(q, run.ecuts)
        Gs = Gs[bgw_order(run, q, Gs)]
        # irrbz.f90:153-166 scans every irreducible q and every op WITHOUT an
        # exit: the LAST match (iq, it) is the one used. k_range folds M qi into
        # [0,1), so the match is modulo reciprocal lattice vectors.
        matches = [(qi, b, is0, iop, M) for qi, b, is0 in self.irr
                   for iop, M in enumerate(cr.mtrx)
                   if np.allclose((M @ qi - q) - np.rint(M @ qi - q), 0, atol=1e-6)]
        if not matches:
            raise KeyError(q)
        if self.choose_op == "last":
            qi, b, is0, iop, M = matches[-1]
        elif self.choose_op == "first":
            qi, b, is0, iop, M = matches[0]
        else:                                     # {q: op} overrides (diagnostics)
            want = self.choose_op.get(tuple(np.round(q, 6)))
            sel = [m for m in matches if m[3] == want] or [matches[-1]]
            qi, b, is0, iop, M = sel[0]
        g0 = np.rint(M @ qi - q).astype(int)          # M qi = q + g0
        W, t = run.wf.ops[iop]
        Minv = np.rint(np.linalg.inv(M)).astype(int)
        Gi = (Minv @ (Gs - g0).T).T                   # q+G = M(qi+Gi), q = M qi - g0
        phase = np.exp(-2j * np.pi * ((M @ (qi[None, :] + Gi).T).T @ t))
        return Gs, b, is0, iop, g0, Gi, phase, len(matches), qi

    def at(self, q):
        """(G sphere at q, eps^-1 matrix on it after wing fix, source info)."""
        run, cr = self.run, self.run.cr
        Gs, b, is0, iop, g0, Gi, phase, nops, qi = self.mapping(q)
        ops = [None] * nops
        Geps, E = self.block_matrix(b)
        pos = gindex(Geps)
        idx = np.array([pos.get(tuple(g), -1) for g in Gi])
        if (idx < 0).any():
            raise ValueError(f"q={q}: {np.sum(idx < 0)} sphere G outside the eps basis")
        eps = (phase[:, None] * np.conj(phase[None, :])) * E[np.ix_(idx, idx)]
        # wings (fixwings.f90:18-44) are applied to the IRREDUCIBLE matrix at
        # irow_G0 = isrtqi(G_i = 0) (sigma_main.f90:1192-1193, 1256), i.e. to the
        # target row/column G = g0; the kernel value is vcoul(1), the first
        # element of the target sphere in sortrx order.
        z = int(np.flatnonzero(np.all(Gs == g0, axis=1))[0])
        others = np.arange(len(Gs)) != z
        qlen = np.sqrt(cr.norm2(q))
        eps = eps.astype(complex)
        if is0:
            eps[others, z] = 0.0
            eps[z, others] = 0.0
            # head: averagew => wcoul0/vcoul(1) = epshead (unchanged)
        else:
            o = self.oneoverq(tuple(q))
            v0 = self.vbar(tuple(q + Gs[0]))
            eps[z, others] *= o * qlen / (8 * np.pi)             # wing' (row G=0)
            eps[others, z] *= o / (v0 * qlen)                    # wing (col G'=0)
        return Gs, eps, dict(iop=iop, g0=g0, nops=len(ops), qi=qi)


def gpp_modes(run, q, Gs, eps, vbar, rho, wpsq_ev2, nelec):
    """I_eps = delta - eps^-1 and wtilde (eV) per (G, G'), mtxel_cor.f90:690-735
    with Omega2 from wpeff.f90. Entries dropped by the source's thresholds are
    zero in both arrays (arrays are zeroed per call, mtxel_cor.f90:418-421)."""
    cr = run.cr
    n = len(Gs)
    Ieps = np.eye(n) - eps
    v = np.array([vbar(tuple(q + g)) for g in Gs]) * run.fact     # vcoul(ig)
    coulfact = 8 * np.pi * run.fact
    qG = q[None, :] + Gs
    fact = wpsq_ev2 / nelec
    q_nonzero = cr.norm2(q) > 1e-12
    rho_idx = gindex(rho["gvec"])
    Om2 = np.zeros((n, n))
    for jp in range(n):                    # column G'
        for i in range(n):                 # row G
            gg = tuple(Gs[i] - Gs[jp])
            if gg not in rho_idx:
                continue
            r = rho["rho"][rho_idx[gg]]
            if Gs[i].any() or q_nonzero:
                pre = fact * v[i] * qG[i] / coulfact
                Om2[i, jp] = (qG[jp] @ cr.bdot @ pre) * r
            else:
                Om2[i, jp] = fact * r if not Gs[jp].any() else 0.0
    keep = (np.abs(Ieps) >= TOL_SMALL) & (np.abs(Om2) >= TOL_SMALL)
    Ie = np.where(np.abs(Ieps) >= TOL_SMALL, Ieps, 0.0)
    wt2 = np.where(keep, Om2 / np.where(keep, Ieps, 1.0), 0.0).real
    keep &= np.abs(wt2) >= TOL_SMALL
    wt = np.zeros((n, n))
    wt[keep & (wt2 > 0)] = np.sqrt(wt2[keep & (wt2 > 0)])
    wt[keep & (wt2 <= 0)] = 1.0 / TOL_ZERO     # invalid_gpp_mode default: static limit
    Om2_used = np.where(keep, wt ** 2 * Ie.real, 0.0)
    return dict(Ieps=Ie.real, wt=wt, v=v, Om2=Om2, keep=keep,
                n_invalid=int(np.sum(keep & (wt2 <= 0))))


def gpp_kernel(wx, wt, Ie, occupied, gamma=0.5, sexcut=4.0):
    """(ssx, sch, branch) arrays for one energy wx (eV), mtxel_cor.f90:1766-1850.
    branch: 0 generic, 1 near-pole (occupied: combined SX+CH), 2 dropped."""
    limitone, limittwo = 1.0 / (TOL_SMALL * 4.0), gamma ** 2
    with np.errstate(divide="ignore", invalid="ignore"):
        wdiff = wx - wt
        delw = wt / wdiff
        delwr = delw * delw
        wdiffr = wdiff * wdiff
        generic = (wdiffr > limittwo) & (delwr < limitone)
        sch = np.where(generic, delw * Ie, 0.0)
        if not occupied:
            return None, sch, np.where(generic, 0, 2)
        Om2 = wt * wt * Ie
        ssx_g = Om2 / (wx * wx - wt * wt)
        near = ~generic & (delwr > TOL_ZERO)
        ssx_n = -Om2 * delw / (4.0 * wt * wt * (delw + 0.5))
        ssx = np.where(generic, ssx_g, np.where(near, ssx_n, 0.0))
        ssx = np.where((np.abs(ssx) > sexcut * np.abs(Ie)) & (wx < 0), 0.0, ssx)
        branch = np.where(generic, 0, np.where(near, 1, 2))
        ssx = np.where(wt == 0, 0.0, ssx)
        sch = np.where(wt == 0, 0.0, sch)
        return ssx, sch, branch


def correlation(run, k, scr, rho, gamma=0.5, sexcut=4.0, dw=1.0, record=None):
    """GPP correlation for bands bmin..bmax at k, all in Ry:
    SX[iw], CH[iw] (iw = 0,1 for E = Eo, Eo+dw) and the static remainder
    achcor, as accumulated in mtxel_cor.f90 and sigma_main.f90:1570-1580."""
    Gk, ck, Ek = run.wf.at(tuple(k))
    nb = np.arange(run.bmin - 1, run.bmax)
    e_lk = Ek[nb] * RYD
    nelec = rho["rho"][gindex(rho["gvec"])[(0, 0, 0)]]
    wpsq = RYD * RYD * 16.0 * np.pi * nelec / run.cr.celvol   # read_rho_vxc.f90:192-193
    SX = np.zeros((2, len(nb)))
    CH = np.zeros((2, len(nb)))
    cor = np.zeros(len(nb))
    # exact static CH needs <n|e^{iG.r}|n> on the q=0 sphere of max(ecuts, ecutb)
    Gch, _ = run.sphere(np.zeros(3), max(run.ecuts, run.ecutb))
    rho_n = mtxel(Gk, ck[nb], Gk, ck[nb], Gch)                      # (n, n, G)
    rho_n = np.array([rho_n[i, i] for i in range(len(nb))])        # (n, G)
    chidx = gindex(Gch)
    for q in run.qlist:
        Gs, eps, info = scr.at(q)
        m = gpp_modes(run, q, Gs, eps, scr.vbar, rho, wpsq, nelec)
        v, Ie, wt = m["v"], m["Ieps"], m["wt"]
        # exact static CH for this q (mtxel_cor.f90:600-649), per band n
        Iex = eps.real - np.eye(len(Gs))
        pos = np.full((len(Gs), len(Gs)), -1)
        for i, g in enumerate(Gs):
            for j, gp in enumerate(Gs):
                pos[i, j] = chidx.get(tuple(g - gp), -1)
        ok = (np.abs(Iex) >= TOL_SMALL) & (pos >= 0)
        for a in range(len(nb)):
            A = np.where(ok, rho_n[a][np.where(pos >= 0, pos, 0)], 0.0)
            cor[a] += 0.5 * (0.5 * np.real(np.sum((A * Iex).sum(axis=0) * v)))
        Gq, cq, Eq = run.wf.at(tuple(k - q))
        # complex: an unfolded state may carry a global phase (e.g. +-i);
        # every form below is M(G) S(G,G') conj(M(G')), as in mtxel_cor.f90
        M = mtxel(Gk, ck[nb], Gq, cq[:run.nbands], Gs)             # (n, n1, G)
        for n1 in range(run.nbands):
            e1 = Eq[n1] * RYD
            occ = n1 < run.nocc
            for a in range(len(nb)):
                x = M[a, n1]
                xc = np.conj(x) * v
                achs = 0.5 * np.real(np.sum(xc * (-(x @ Ie))))     # acc_static_ch
                cor[a] -= 0.5 * achs
                for iw in range(2):
                    wx = e_lk[a] + dw * iw - e1
                    if abs(wx) < TOL_ZERO:
                        wx = TOL_ZERO
                    ssx, sch, br = gpp_kernel(wx, wt, Ie, occ, gamma, sexcut)
                    if occ:
                        SX[iw, a] -= np.real(np.sum((x @ ssx) * xc))
                    CH[iw, a] += 0.5 * np.real(np.sum((x @ sch) * xc))
                    if record is not None and iw == 0:
                        for b in (1, 2):
                            sel = br == b
                            if sel.any():
                                key = ("near" if b == 1 else "dropped", a)
                                ssxb = 0 if ssx is None else -np.real(np.sum((x @ np.where(sel, ssx, 0)) * xc))
                                schb = 0.5 * np.real(np.sum((x @ np.where(sel, sch, 0)) * xc))
                                record[key] = record.get(key, 0) + ssxb + schb
    return SX, CH, cor, e_lk


# ------------------------------------------------------------- QP energies

def quasiparticle(run, k, vbar, scr, rho, dw=1.0):
    """Diagonal table for bands bmin..bmax at k, multiplet-averaged, in eV.

    Sig(E) = X + SX(E) + CH(E) + achcor; Eqp0 = Emf - Vxc + Sig(Eo) with
    Vxc = 0 here; forward difference dSig/dE = (Sig(Eo+dw) - Sig(Eo))/dw
    (finite_difference_form 2 = forward for diagonal, sigma.out notes); Z =
    1/(1 - dSig/dE); Eqp1 = Eqp0 + dSig/dE/(1 - dSig/dE) (Eqp0 - Eo)."""
    X = bare_exchange(run, k, vbar)
    SX, CH, cor, e_lk = correlation(run, k, scr, rho, dw=dw)
    E = run.wf.at(tuple(k))[2][run.bmin - 1:run.bmax] * RYD
    rows = []
    for grp in multiplets_from_energies(E):
        m = lambda a: float(np.mean(a[grp]))
        x, sx0, sx1 = m(X) * RYD, m(SX[0]) * RYD, m(SX[1]) * RYD
        ch0, ch1, c = m(CH[0]) * RYD, m(CH[1]) * RYD, m(cor) * RYD
        eo = float(np.mean(E[grp]))
        sig0, sig1 = x + sx0 + ch0 + c, x + sx1 + ch1 + c
        d = (sig1 - sig0) / dw
        eqp0 = eo + sig0
        rows.append(dict(bands=[run.bmin + i for i in grp], Emf=eo, X=x, SXX=sx0,
                         CH=ch0 + c, CHp=ch0, cor=c, Sig=sig0, Eqp0=eqp0,
                         Eqp1=eqp0 + d / (1 - d) * (eqp0 - eo), Z=1 / (1 - d)))
    return rows


def multiplets_from_energies(E, tol_ev=1.0e-6 * RYD):
    groups = []
    for i, e in enumerate(E):
        if groups and abs(e - E[groups[-1][-1]]) <= tol_ev:
            groups[-1].append(i)
        else:
            groups.append([i])
    return groups


# ------------------------------------------------------------ epsilon stage

class EpsilonRun:
    """Independent chi0 -> eps -> eps^-1 from WFN (shifted grid) and WFNq.

    chi(G,G') = fact sum_{k in full grid} sum_{v<=4<c<=nbands}
                M(G) conj(M(G')) / (E_v(k+q) - E_c(k)),  fact = 4/(N_k celvol)
    (epsilon_main.f90:657; mtxel.f90:13 eden = 1/(e_val-e_cond);
     mtxelmultiply.f90:64,95 chi = -fact * gr . gc^T with gr = gme*sqrt(-eden)),
    M(G) = <v, k+q| e^{i(q+G).r} |c, k>, valence at k+q from WFNq for q0 and
    from WFN otherwise. eps = 1 - v(q+G) chi (row scaling, epsinv.f90:225-241),
    v = 8 pi/|q+G|^2 without cell averaging in Epsilon (avgcut = 0)."""

    def __init__(self, rundir, nbands, ecut, nv=4):
        d = pathlib.Path(rundir)
        self.w = bgwio.read_wfn(d / "WFN")
        self.wq = bgwio.read_wfn(d / "WFNq")
        self.cr = Crystal(self.w)
        self.crq = Crystal(self.wq)
        self.wf = Wfn(self.w, self.cr)
        self.wfq = Wfn(self.wq, self.crq)
        self.nbands, self.ecut, self.nv = nbands, ecut, nv
        self.gvec = self.w["gvec"]
        # fullbz unfolds the irreducible k-points with ALL ops (epsilon_main.f90:
        # 268-278). For this shifted fcc grid that closure has 32 points, not
        # the 8 of the nominal 2x2x2 grid; fact uses gr%nf (epsilon_main.f90:659).
        pts = {}
        for k in self.w["kpt"]:
            for M in self.cr.mtrx:
                p = M @ k
                p = p - np.floor(p + 1e-9)
                pts.setdefault(tuple(np.round(p, 9)), p)
        self.kfull = list(pts.values())
        self.fact = 4.0 / (len(self.kfull) * self.cr.celvol)

    def chi(self, q, Gs, q0=False):
        n = len(Gs)
        chi = np.zeros((n, n), complex)
        for k in self.kfull:
            Gc, cc, Ec = self.wf.at(tuple(k))
            src = self.wfq if q0 else self.wf
            Gv, cv, Ev = src.at(tuple(np.round(k + q, 12)))
            # M_vc(G) = <v,k+q| e^{i(q+G).r} |c,k> = sum_G2 cv*(G2+G) cc(G2)
            M = mtxel(Gv, cv[:self.nv], Gc, cc[self.nv:self.nbands], Gs)   # (v, c, G)
            eden = 1.0 / (Ev[:self.nv, None] - Ec[None, self.nv:self.nbands])
            chi += np.einsum("vcg,vc,vch->gh", M, eden, np.conj(M))
        return self.fact * chi

    def epsinv(self, q, q0=False):
        Gs, _ = sphere_of(self.cr, self.gvec, q, self.ecut)
        chi = self.chi(q, Gs, q0)
        v = 8 * np.pi / self.cr.norm2(q[None, :] + Gs)
        eps = np.eye(len(Gs)) - v[:, None] * chi
        return Gs, np.linalg.inv(eps), chi


def sphere_of(cr, gvec, q, ecut):
    n2 = cr.norm2(q[None, :] + gvec)
    return gvec[n2 < ecut], n2[n2 < ecut]


def epsinv_ff(er, q, W_ev, q0=False):
    """Full-frequency retarded eps^-1 at complex energies W_ev (eV):
    chi(W) = fact sum_t M M* (1/2)[1/(z - W) + 1/(z + W)], z = E_v - E_c
    (Epsilon/chi_summation.f90:812-817, applied with negfact = -fact to
    edenDRtemp = -1/2 occ_diff (...)); eps = 1 - v chi; returns (Gs, [eps^-1])."""
    Gs, _ = sphere_of(er.cr, er.gvec, q, er.ecut)
    n = len(Gs)
    W = np.asarray(W_ev, complex) / RYD
    chi = np.zeros((len(W), n, n), complex)
    for k in er.kfull:
        Gc, cc, Ec = er.wf.at(tuple(k))
        src = er.wfq if q0 else er.wf
        Gv, cv, Ev = src.at(tuple(np.round(k + q, 12)))
        M = mtxel(Gv, cv[:er.nv], Gc, cc[er.nv:er.nbands], Gs)       # (v, c, G)
        z = Ev[:er.nv, None] - Ec[None, er.nv:er.nbands]              # (v, c)
        P = np.einsum("vcg,vch->vcgh", M, np.conj(M))
        den = 0.5 * (1.0 / (z[None] - W[:, None, None]) + 1.0 / (z[None] + W[:, None, None]))
        chi += np.einsum("wvc,vcgh->wgh", den, P)
    chi *= er.fact
    v = 8 * np.pi / er.cr.norm2(q[None, :] + Gs)
    eps = np.eye(n)[None] - v[None, :, None] * chi
    return Gs, np.linalg.inv(eps)
