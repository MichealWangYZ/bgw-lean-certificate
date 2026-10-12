"""Independent float64 reproducer of BerkeleyGW 4.0's contour-deformation (CD)
full-frequency correlation self-energy, and the same CD formula evaluated
without BerkeleyGW's numerical shortcuts (task A2).

Layer 1 (`cd_terms`, `table`): the printed "Res", "Int", "Cor", "Sig" columns of
sigma_hp.log for frequency_dependence 2, frequency_dependence_method 2,
cd_int_method 0, exact_static_ch 1, at E = Eo. Everything below the eps^-1
matrices (wavefunction unfolding, matrix elements, symmetry mapping with the
last-match op, Monte Carlo Coulomb averages, wing scalings) is spec.py's,
unchanged; this module adds only the frequency-dependent parts, each with its
source line in Sigma/mtxel_cor.f90 (BerkeleyGW 4.0, pristine).

Conventions (mtxel_cor.f90 unless stated):
  * eval grid: freq0 = e_lk - step (nfreqeval-1)/2 + TOL_SMALL (471-477), so
    the CD "E = Eo" point is Eo + 1e-6 eV; nfreqeval = 2 int((max+TOL_ZERO)/
    step) + 1 (inread.f90:1003); E = Eo is iw = iwlda, the grid point closest
    to e_lk (3091-3099; write_result_dyn_hp.f90:66-79).
  * wx = freq0 - e_n1(k-q) + (iw-1) step (3101-3104).
  * residue (3120-3196): taken only if (wx >= 0) differs from flag_occ, i.e.
    empty n1 with wx >= 0 and occupied n1 with wx < 0 (3125-3127);
    occ_sign = sign(1, wx) (3128); eps^-1 is interpolated LINEARLY on the
    real grid at |wx|: ifreq = the last ijk with grid(ijk) <= |wx| <
    grid(ijk+1) (3134-3139), fact1/fact2 (3151-3154);
    sres = - occ_sign sum_{G G'} M(G) I_epsR(G,G';|wx|) M*(G') v(G') (3163-3183),
    I_epsR = delta - ph ph* eps^-1_R (984-987), complex.
  * integral (3199-3246): sW(i w_j) = sum M(G) I_eps_imag(G,G') M*(G') v(G'),
    I_eps_imag = SCALARIFY(delta - ph ph* eps^-1(i w_j)) (1011-1016) -- real
    part in the real flavour; imag_freqs = Im(dFreqGrid + dFreqBrd) of the
    imaginary block (3212); cd_int_method 0: piecewise constant sW on
    intervals bounded by midpoints, the last one mirrored, with weights
    atan(end/wx) - atan(start/wx) (3216-3244); Int = sint / pi (3338).
  * imaginary block of the eps file: every frequency with |dFreqGrid| <
    TOL_ZERO except the first (Sigma/epscopy.f90:192-194).
  * wings: fixwings_dyn at every frequency (sigma_main.f90:1255-1286 with
    nfreq_fixwings = nFreq, sigma_main.f90:614; Common/fixwings.f90:190-216):
    q0 wings zeroed, head UNCHANGED (no W averaging in the FF branch);
    q != 0 the same row/column scalings as the static fixwings.
  * static remainder (exact_static_ch 1): exact static CH from
    Re eps^-1(grid point 1) (596, 609-651), partial static CH from
    acc_static_ch with eps_cplx = I_epsR(:,:,1) (3107-3110, 3924-3965),
    achtcor_n1(1) = achxtemp/2 (1208-1213), -achstemp/2 per band (1428-1432);
    printed Int = achDyn + achcor, Int` = achDyn (write_result_dyn_hp.f90).
  * accumulation: Res = asxDyn, Int = achDyn (1557-1560), neq = 1 per q
    (no_symmetries_q_grid), multiplied by ryd at print (sigma_main.f90:2061).

`read_eps_ff` and `epsinv_ff` are also present, uncommitted, in the bgw-e
worktree's spec.py/bgwio.py; they are reproduced here (einsum replaced by the equivalent
tensordot for speed) so that this branch does not depend on uncommitted work
(task rule: spec.py is not modified).
"""
import functools
import pathlib
import unittest.mock

import numpy as np

import bgwio
import coulomb
import spec
from spec import RYD, TOL_SMALL, TOL_ZERO, gindex, mtxel, sphere_of

HERE = pathlib.Path(__file__).resolve().parent


# ------------------------------------------------------------------ readers

def read_eps_ff(path):
    """Full-frequency real-flavour epsmat/eps0mat: the frequency record
    (dFreqGrid real, dFreqBrd complex; Epsilon/inread.f90:565-605), then per q
    the index maps, kinetic energies, q, and for every column jj and row ii one
    record of nfreq complex retarded eps^-1 values (Common/write_matrix.f90:
    363-368)."""
    Records, Reader = bgwio.Records, bgwio.Reader
    rec = Records(path)
    h = {}
    r = Reader(rec.next())
    h["ajname"], h["adate"] = r.s(6), r.s(11)
    r = Reader(rec.next())
    (h["freq_dep"], h["nFreq"], h["subspace"], h["matrix_in_subspace_basis"],
     h["keep_full_eps_static"]) = r.i(5)
    if h["freq_dep"] != 2 or h["subspace"] != 0:
        raise ValueError("expected a full-frequency, full-basis epsmat")
    nf = h["nFreq"]
    h["qgrid"] = Reader(rec.next()).i(3)
    r = Reader(rec.next())
    h["freq_grid"] = r.d(nf)
    h["freq_brd"] = r.take("<c16", nf).copy()
    r.end()
    for _ in range(2):
        if rec.next():
            raise ValueError("expected an empty record")
    h["ecuts"] = Reader(rec.next()).d()
    r = Reader(rec.next())
    nq = r.i()
    h["qpts_header"] = r.d(3 * nq).reshape(nq, 3)
    r = Reader(rec.next())
    ng = h["ng"] = r.i()
    h["gvec"] = r.i(3 * ng).reshape(ng, 3)
    h["q"] = []
    while not rec.done():
        r = Reader(rec.next())
        ngq, nmtx = r.i(2)
        pairs = r.i(2 * ngq).reshape(ngq, 2)
        ekin = Reader(rec.next()).d(ngq)
        q0 = Reader(rec.next()).d(3)
        E = np.zeros((nf, nmtx, nmtx), complex)
        for jj in range(nmtx):
            for ii in range(nmtx):
                E[:, ii, jj] = Reader(rec.next()).take("<c16", nf)
        h["q"].append({"nmtx": nmtx, "isrtx": pairs[:, 0], "isorti": pairs[:, 1],
                       "ekin": ekin, "q": q0, "epsinv": E})
    if len(h["q"]) != nq:
        raise ValueError("q-block count differs from header")
    return h


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
        chi += np.tensordot(den, P, axes=([1, 2], [0, 1]))     # = einsum wvc,vcgh->wgh
    chi *= er.fact
    v = 8 * np.pi / er.cr.norm2(q[None, :] + Gs)
    eps = np.eye(n)[None] - v[None, :, None] * chi
    return Gs, np.linalg.inv(eps)


# ------------------------------------------------------------------ the run

class CDSetup:
    """A CD run directory: spec.Run with the FF eps files, production Coulomb
    averages, spec.Screening for the symmetry map, the frequency grids."""

    def __init__(self, rundir):
        d = pathlib.Path(rundir)
        # spec.Run reads eps0mat/epsmat with the static reader; substitute the
        # FF reader for the duration of construction only (spec.py unchanged).
        with unittest.mock.patch.object(spec.bgwio, "read_eps", read_eps_ff):
            self.run = spec.Run(d)
        run = self.run
        kv, _ = spec.parse_sigma_inp((d / "sigma.inp").read_text())
        assert kv["frequency_dependence"] == ["2"] and kv["frequency_dependence_method"] == ["2"]
        assert "cd_integration_method" not in kv, "cd_int_method must be the default 0"
        assert kv.get("exact_static_ch") == ["1"]
        self.step = float(kv["delta_frequency_eval"][0])
        maxf = float(kv["max_frequency_eval"][0])
        self.nfreqeval = 2 * int((maxf + TOL_ZERO) / self.step) + 1     # inread.f90:1003
        e0, e1 = run.eps0, run.eps
        assert np.array_equal(e0["freq_grid"], e1["freq_grid"])
        assert np.array_equal(e0["freq_brd"], e1["freq_brd"])
        is_imag = np.abs(e0["freq_grid"]) < TOL_ZERO
        is_imag[0] = False                                               # epscopy.f90:192-194
        self.nimag = int(is_imag.sum())
        self.nreal = int(e0["nFreq"]) - self.nimag
        assert not is_imag[:self.nreal].any() and is_imag[self.nreal:].all()
        self.grid = e0["freq_grid"][:self.nreal]                         # eV
        self.brd = e0["freq_brd"][:self.nreal]
        self.eta = float(self.brd[0].imag)
        assert np.allclose(self.brd.imag, self.eta) and np.allclose(self.brd.real, 0)
        self.imag_freqs = (e0["freq_grid"][self.nreal:] + e0["freq_brd"][self.nreal:]).imag
        self.mb = coulomb.MiniBZ(run.cr.bdot, run.qgrid, run.cr.celvol)
        self.vb = functools.lru_cache(None)(lambda qk: self.mb.production(np.array(qk)))
        self.oq = functools.lru_cache(None)(lambda q: self.mb.oneoverq_production(np.array(q)))
        self.rho = bgwio.read_rho(d / "RHO")
        self.scr = spec.Screening(run, self.vb, self.oq)


def ff_at(cd, q, blocks=None):
    """eps^-1(G,G'; w_j) on the target sphere at q for every frequency of the
    irreducible block, after the symmetry map and fixwings_dyn.

    `blocks`: optional list, aligned with cd.scr.irr, of (G list, E[nf, n, n])
    replacing the file's matrices (used for directly computed frequencies).
    Returns (Gs, eps[nf, n, n] complex, info)."""
    scr, run = cd.scr, cd.run
    Gs, b, is0, iop, g0, Gi, phase, nops, qi = scr.mapping(q)
    if blocks is None:
        Geps = run.eps["gvec"][b["isrtx"][:b["nmtx"]] - 1]
        E = b["epsinv"]
    else:
        Geps, E = blocks[block_index(scr, b)]
    pos = gindex(Geps)
    idx = np.array([pos.get(tuple(g), -1) for g in Gi])
    if (idx < 0).any():
        raise ValueError(f"q={q}: sphere G outside the eps basis")
    pp = phase[:, None] * np.conj(phase[None, :])
    eps = pp[None] * E[:, idx][:, :, idx]
    z = int(np.flatnonzero(np.all(Gs == g0, axis=1))[0])
    others = np.arange(len(Gs)) != z
    qlen = np.sqrt(run.cr.norm2(q))
    if is0:                                   # fixwings.f90:190-201, 203-214
        eps[:, others, z] = 0.0
        eps[:, z, others] = 0.0
    else:
        o = cd.oq(tuple(q))
        v0 = cd.vb(tuple(q + Gs[0]))
        eps[:, z, others] *= o * qlen / (8 * np.pi)
        eps[:, others, z] *= o / (v0 * qlen)
    return Gs, eps, dict(iop=iop, qi=qi, is0=is0, max_im_phase=float(np.abs(pp.imag).max()),
                         j=block_index(scr, b))


def block_index(scr, b):
    return next(i for i, (_, bb, _) in enumerate(scr.irr) if bb is b)


def cd_int0_weights(imag_freqs, wx):
    """cd_int_method 0 weights (mtxel_cor.f90:3216-3244), per imaginary
    frequency, for one wx (eV): atan(end/wx) - atan(start/wx)."""
    f = imag_freqs
    n = len(f)
    start = np.empty(n)
    end = np.empty(n)
    start[0] = f[0]
    end[0] = (f[0] + f[1]) * 0.5
    for j in range(1, n - 1):
        start[j] = (f[j - 1] + f[j]) * 0.5
        end[j] = (f[j] + f[j + 1]) * 0.5
    start[n - 1] = (f[n - 2] + f[n - 1]) * 0.5
    end[n - 1] = (-f[n - 2] + 3.0 * f[n - 1]) * 0.5
    return np.arctan(end / wx) - np.arctan(start / wx)


def interp_index(grid, w):
    """ifreq (0-based) and weights of the residue interpolation
    (mtxel_cor.f90:3131-3154), including the out-of-range clamp."""
    nr = len(grid)
    ifreq = -1
    for ijk in range(nr - 1):
        if grid[ijk] <= w < grid[ijk + 1]:
            ifreq = ijk
    if ifreq < 0 or ifreq >= nr - 1:
        ifreq = nr - 2
    f1 = (grid[ifreq + 1] - w) / (grid[ifreq + 1] - grid[ifreq])
    f2 = (w - grid[ifreq]) / (grid[ifreq + 1] - grid[ifreq])
    return ifreq, f1, f2


def eval_energy(cd, e_lk):
    """(freq0, iwlda, E) of the CD evaluation point E = Eo (mtxel_cor.f90:471-477,
    3091-3099). All in eV, same operation order as the Fortran."""
    s, n = cd.step, cd.nfreqeval
    freq0 = e_lk - s * (n - 1) / 2
    freq0 = freq0 + TOL_SMALL
    diffs = [abs(freq0 + (iw - 1) * s - e_lk) for iw in range(1, n + 1)]
    iwlda = int(np.argmin(diffs)) + 1        # first minimum (strict <)
    return freq0, iwlda


# --------------------------------------------------------- the self-energy

def cd_terms(cd, k, bands, residue=None, integral=None, record=None):
    """Per band (0-based `bands`) at k: Res (complex), Int (real), achcor
    (real), all in Ry, before multiplet averaging.

    `residue(q, Gs, eps_ff, pairs)` and `integral(q, Gs, eps_ff, pairs)`
    override the production residue and integral (Step 2): `pairs` is a list
    of (a, n1, wx, x, xc) and each returns an array over pairs of the
    contribution in Ry (residue: complex, already signed; integral: real,
    already divided by pi). Default: production conventions."""
    run = cd.run
    Gk, ck, Ek = run.wf.at(tuple(k))
    nb = np.asarray(bands)
    e_lk = Ek[nb] * RYD
    RES = np.zeros(len(nb), complex)
    INT = np.zeros(len(nb))
    cor = np.zeros(len(nb))
    Gch, _ = run.sphere(np.zeros(3), max(run.ecuts, run.ecutb))
    rho_n = mtxel(Gk, ck[nb], Gk, ck[nb], Gch)
    rho_n = np.array([rho_n[i, i] for i in range(len(nb))])
    chidx = gindex(Gch)
    ev = [eval_energy(cd, e) for e in e_lk]
    for q in run.qlist:
        Gs, eps, info = ff_at(cd, q)
        n = len(Gs)
        v = np.array([cd.vb(tuple(q + g)) for g in Gs]) * run.fact
        eye = np.eye(n)
        IR = eye[None] - eps[:cd.nreal]                            # I_epsR, complex
        II = (eye[None] - eps[cd.nreal:]).real                     # I_eps_imag, SCALARIFY
        # exact static CH from Re eps^-1 at grid point 1 (mtxel_cor.f90:596, 609-651)
        Iex = eps[0].real - eye
        posm = np.array([[chidx.get(tuple(g - gp), -1) for gp in Gs] for g in Gs])
        ok = (np.abs(Iex) >= TOL_SMALL) & (posm >= 0)
        for a in range(len(nb)):
            A = np.where(ok, rho_n[a][np.where(posm >= 0, posm, 0)], 0.0)
            cor[a] += 0.5 * (0.5 * np.real(np.sum((A * Iex).sum(axis=0) * v)))
        Gq, cq, Eq = run.wf.at(tuple(k - q))
        M = mtxel(Gk, ck[nb], Gq, cq[:run.nbands], Gs)             # (a, n1, G)
        pairs = []
        for n1 in range(run.nbands):
            e1 = Eq[n1] * RYD
            occ = n1 < run.nocc
            for a in range(len(nb)):
                x = M[a, n1]
                xc = np.conj(x) * v
                achs = 0.5 * np.real(np.sum(xc * (-(x @ IR[0].real))))   # acc_static_ch
                cor[a] -= 0.5 * achs
                freq0, iwlda = ev[a]
                wx = freq0 - e1 + (iwlda - 1) * cd.step
                pairs.append((a, n1, wx, x, xc, occ))
        # residue
        if residue is None:
            for (a, n1, wx, x, xc, occ) in pairs:
                if (wx >= 0.0) == occ:
                    continue
                sgn = 1.0 if wx >= 0 else -1.0
                w = abs(wx)
                i, f1, f2 = interp_index(cd.grid, w)
                S = IR[i] * f1 + IR[i + 1] * f2
                val = -sgn * np.sum((x @ S) * xc)
                RES[a] += val
                if record is not None:
                    record.setdefault("res", []).append((tuple(q), a, n1, wx, val))
        else:
            for (a, *_), val in zip(pairs, residue(q, Gs, eps, pairs, info)):
                RES[a] += val
        # integral
        if integral is None:
            for (a, n1, wx, x, xc, occ) in pairs:
                sW = np.einsum("g,wgh,h->w", x, II, xc)
                if record is not None:
                    record["max_im_sW"] = max(record.get("max_im_sW", 0.0),
                                              float(np.abs(sW.imag).max()))
                wts = cd_int0_weights(cd.imag_freqs, wx)
                INT[a] += float(np.sum(sW.real * wts)) / np.pi
        else:
            for (a, *_), val in zip(pairs, integral(q, Gs, eps, pairs, info)):
                INT[a] += val
        if record is not None:
            record["max_im_phase"] = max(record.get("max_im_phase", 0.0), info["max_im_phase"])
    return RES, INT, cor, e_lk


def table(cd, k, bands, X=None, **kw):
    """Multiplet-averaged sigma_hp.log columns (eV) for `bands` (1-based) at k."""
    nb = np.array(bands) - 1
    RES, INT, cor, e_lk = cd_terms(cd, k, nb, **kw)
    if X is None:
        X = bare_x(cd, k, nb)
    rows = []
    for grp in spec.multiplets_from_energies(e_lk):
        m = lambda arr: np.mean(arr[grp])
        res, it, c, x = m(RES) * RYD, m(INT) * RYD, m(cor) * RYD, m(X) * RYD
        rows.append(dict(bands=[int(bands[i]) for i in grp], Emf=float(np.mean(e_lk[grp])),
                         X=float(x), ReRes=float(res.real), ImRes=float(res.imag),
                         ReInt=float(it + c), ReIntp=float(it), achcor=float(c),
                         ReCor=float(res.real + it + c), ReCorp=float(res.real + it),
                         ReSig=float(x + res.real + it + c), ReSigp=float(x + res.real + it)))
    return rows


def bare_x(cd, k, nb):
    run = cd.run
    Gk, ck, Ek = run.wf.at(tuple(k))
    X = np.zeros(len(nb))
    for q in run.qlist:
        Gb, _ = run.sphere(q, run.ecutb)
        Gq, cq, _ = run.wf.at(tuple(k - q))
        Mb = mtxel(Gk, ck[nb], Gq, cq[:run.nocc], Gb)
        vv = np.array([cd.vb(tuple(q + g)) for g in Gb])
        X -= run.fact * np.einsum("nmg,g->n", np.abs(Mb) ** 2, vv)
    return X


# ------------------------------------------------------ production output

def read_hp(path, ik):
    """Diagonal rows of the ik-th k block of a CD sigma_hp.log (exact_ch 1):
    {band: dict(Emf, Eo, X, ReRes, ReInt, ReSig, ReCor, ImRes, ImInt, ImSig,
    ImCor, ReIntp, ReSigp, ReCorp)}."""
    lines = pathlib.Path(path).read_bytes().decode("latin1").splitlines()
    out, blk, i = {}, 0, 0
    while i < len(lines):
        if lines[i].strip().startswith("k =") and f"ik = {ik:3d}" in lines[i]:
            blk = 1
        elif blk and lines[i].split()[:1] == ["n"] and "Re Res" in lines[i]:
            i += 2
            while i < len(lines) and lines[i].strip():
                a = lines[i].split()
                b = lines[i + 1].split()
                out[int(a[0])] = dict(Emf=float(a[1]), Eo=float(a[2]), X=float(a[3]),
                                      ReRes=float(a[4]), ReInt=float(a[5]), ReSig=float(a[6]),
                                      ReCor=float(a[7]), ReIntp=float(a[12]),
                                      ReSigp=float(a[13]), ReCorp=float(a[14]),
                                      ImRes=float(b[0]), ImInt=float(b[1]), ImSig=float(b[2]),
                                      ImCor=float(b[3]))
                i += 2
            return out
        i += 1
    raise KeyError(ik)


STATES = {"X": (2, [5, 6]), "L": (1, [5])}     # index into sigma.inp kpoints, bands
