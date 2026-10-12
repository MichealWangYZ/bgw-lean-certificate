#!/usr/bin/env python3
"""A3(c): size of the leading term GW leaves out -- second-order exchange.

    python3 bgw/endpoint/second_order.py RUNDIR [--at emf|g0w0]

Second-order self-energy of a closed-shell system in spatial orbitals (bare
Coulomb, G0 from the EPM energies; a, b occupied, r, s empty):

  Sigma2_pp(E) = sum_{a r s} <pa|rs> (2 <rs|pa> - <rs|ap>) / (E + e_a - e_r - e_s)
               + sum_{a b r} <pr|ab> (2 <ab|pr> - <ab|rp>) / (E + e_r - e_a - e_b)

The "2" terms (direct, the second-order ring) are contained in GW; the "-1"
terms (second-order exchange, SOX) are not: SOX is the leading vertex
correction. Both are evaluated with the same integrals, so their ratio on O1
is the estimate reported. It is an ESTIMATE: bare second order is not GW's
screened expansion, the band sum stops at number_bands, and the q = 0
divergence is handled with the same mini-BZ averaged v as Sigma.

Integrals. With phi_nk = (N_k Omega)^-1/2 sum_G c_nk(G) e^{i(k+G).r} and
A_mn(Q) = sum_G2 c_m*(G2) c_n(G2 + Q - k_n + k_m) (the pair-density Fourier
coefficient of phi_m* phi_n at Q = k_n - k_m + G),
  <pq|rs> = (1 / (N_k Omega)) sum_Q vbar(Q) A_pr(Q) A_qs(-Q).
Check: the same routine gives the HF exchange -sum_a <pa|ap>, which must
reproduce the production X column.
"""
import argparse
import functools
import json
import pathlib
import sys

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import coulomb  # noqa: E402
import observable  # noqa: E402
import spec  # noqa: E402

RYD = spec.RYD


class Orbitals:
    def __init__(self, run, eqp=None):
        """eqp: optional {k-tuple: {band: Eqp}} (an eqp1.dat of the irreducible
        k-points) replacing the mean-field energies in G0 by QP energies."""
        self.run, self.eqp = run, eqp
        g = run.qgrid
        self.kfull = [np.array([i / g[0], j / g[1], l / g[2]]) for i in range(g[0])
                      for j in range(g[1]) for l in range(g[2])]

    def at(self, k):
        G, c, E = self.run.wf.at(tuple(np.round(k, 12)))
        E = E[:self.run.nbands] * RYD
        if self.eqp is not None:
            ik, _, _ = self.run.wf.find(np.round(k, 12))
            key = tuple(round(float(x), 6) for x in self.run.wfn["kpt"][ik])
            E = np.array([self.eqp[key][b + 1] for b in range(self.run.nbands)])
        return G, c[:self.run.nbands], E

    @staticmethod
    def pair(km, Gm, cm, kn, Gn, cn, Qs):
        """A_mn(Q) for every Q in Qs (rows: crystal coords), shape (m, n, len(Qs))."""
        idx = spec.gindex(Gn)
        out = np.zeros((cm.shape[0], cn.shape[0], len(Qs)), complex)
        for j, Q in enumerate(Qs):
            shift = np.rint(Q - kn + km).astype(int)
            assert np.allclose(Q - kn + km, shift)
            pos = np.array([idx.get(tuple(g2 + shift), -1) for g2 in Gm])
            ok = pos >= 0
            out[:, :, j] = np.conj(cm[:, ok]) @ cn[:, pos[ok]].T
        return out


def qlist_for(run, dk):
    """Q = dk + G over the bare-exchange sphere |Q|^2 < ecutb."""
    Gs, _ = run.sphere(dk, run.ecutb)
    return dk[None, :] + Gs


def exchange_check(run, orb, vbar, k, bands):
    """HF exchange -sum_a <pa|ap> for bands at k, multiplet-averaged (eV)."""
    Gp, cp, _ = orb.at(k)
    V = len(orb.kfull) * run.cr.celvol
    tot = np.zeros(len(bands))
    for q in run.qlist:
        ka = k - q
        Ga, ca, _ = orb.at(ka)
        Qs = qlist_for(run, ka - k)
        A = orb.pair(k, Gp, cp[np.array(bands) - 1], ka, Ga, ca[:run.nocc], Qs)
        v = np.array([vbar(tuple(Q)) for Q in Qs])
        tot -= np.einsum("pag,g->p", np.abs(A) ** 2, v) / V
    return tot.mean() * RYD


def sigma2(run, orb, vbar, k, bands, E):
    """(direct, exchange) second-order self-energy (eV) at energy E (eV) for
    the multiplet `bands` at k, averaged over the multiplet."""
    nocc, nb = run.nocc, run.nbands
    V = len(orb.kfull) * run.cr.celvol
    Gp, cp, _ = orb.at(k)
    cp = cp[np.array(bands) - 1]
    D = X = 0.0
    for ka in orb.kfull:
        Ga, ca, ea = orb.at(ka)
        for q in run.qlist:
            kr = k - q                        # k_p + k_a = k_r + k_s
            ks = ka + q
            Gr, cr_, er = orb.at(kr)
            Gs, cs, es = orb.at(ks)
            # <p a | r s>: rho_pr at Q = kr - k (+G), rho_as at -Q = ks - ka (+G)
            Q1 = qlist_for(run, kr - k)
            v1 = np.array([vbar(tuple(Q)) for Q in Q1])
            Apr = orb.pair(k, Gp, cp, kr, Gr, cr_, Q1)            # (p, r, Q)
            Aas = orb.pair(ka, Ga, ca, ks, Gs, cs, -Q1)           # (a, s, Q)
            I_parS = np.einsum("prg,asg,g->pars", Apr, Aas, v1) / V   # <pa|rs>
            # <a p | r s> for the exchange partner <rs|ap> = conj(<ap|rs>):
            # rho_ar at Q = kr - ka (+G), rho_ps at -Q = ks - k (+G)
            Q2 = qlist_for(run, kr - ka)
            v2 = np.array([vbar(tuple(Q)) for Q in Q2])
            Aar = orb.pair(ka, Ga, ca, kr, Gr, cr_, Q2)           # (a, r, Q)
            Aps = orb.pair(k, Gp, cp, ks, Gs, cs, -Q2)            # (p, s, Q)
            I_aprs = np.einsum("arg,psg,g->pars", Aar, Aps, v2) / V   # <ap|rs>
            occ_a, vir_r, vir_s = slice(0, nocc), slice(nocc, nb), slice(nocc, nb)
            vir_a, occ_r, occ_s = slice(nocc, nb), slice(0, nocc), slice(0, nocc)
            # first sum: a occupied, r, s empty
            den1 = E + ea[occ_a, None, None] - er[None, vir_r, None] - es[None, None, vir_s]
            T = I_parS[:, occ_a, vir_r, vir_s]
            U = I_aprs[:, occ_a, vir_r, vir_s]
            D += np.real(np.sum(2 * np.abs(T) ** 2 / den1[None])) / len(bands)
            X += np.real(np.sum(-T * np.conj(U) / den1[None])) / len(bands)
            # second sum (hole part): here the roles are <p r | a b> with r empty,
            # a, b occupied. With the loop variables renamed (ka -> k_r, kr -> k_a,
            # ks -> k_b) it is the same integrals with occupations swapped.
            den2 = E + ea[vir_a, None, None] - er[None, occ_r, None] - es[None, None, occ_s]
            T2 = I_parS[:, vir_a, occ_r, occ_s]
            U2 = I_aprs[:, vir_a, occ_r, occ_s]
            D += np.real(np.sum(2 * np.abs(T2) ** 2 / den2[None])) / len(bands)
            X += np.real(np.sum(-T2 * np.conj(U2) / den2[None])) / len(bands)
    return D * RYD, X * RYD


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("rundir")
    ap.add_argument("--out")
    ap.add_argument("--eqp", help="eqp1.dat with QP energies for G0 and for E (e.g. converged evGW0)")
    a = ap.parse_args(argv)
    run = spec.Run(a.rundir)
    mb = coulomb.MiniBZ(run.cr.bdot, run.qgrid, run.cr.celvol)
    vbar = functools.lru_cache(None)(lambda Q: mb.production(np.array(Q)))
    eqp = None
    if a.eqp:
        import evgw
        eqp = {k: {b: e for b, (_, e) in v.items()} for k, v in evgw.read_eqp(a.eqp).items()}
    orb = Orbitals(run, eqp)
    tables = observable.parse((pathlib.Path(a.rundir) / "sigma_hp.log").read_text())
    res = {}
    for name, k, bands in (("X", run.kpts[2], [5, 6]), ("L", run.kpts[1], [5])):
        xh = exchange_check(run, orb, vbar, k, bands)
        prod = observable.state(tables[tuple(k)], bands[0])
        emf = prod["Emf"]
        out = {"X_check": xh, "X_production": prod["X"], "Emf": emf, "Eqp1": prod["Eqp1"]}
        points = (("at_Emf", emf), ("at_Eqp1", prod["Eqp1"]))
        if eqp is not None:
            ik = next(i for i, kk in enumerate(run.wfn["kpt"]) if np.allclose(kk, k))
            key = tuple(round(float(x), 6) for x in run.wfn["kpt"][ik])
            points = (("at_own_QP", float(np.mean([eqp[key][b] for b in bands]))),)
        for label, E in points:
            d, x = sigma2(run, orb, vbar, k, bands, E)
            out[label] = {"direct": d, "exchange": x}
        res[name] = out
        print(name, json.dumps(out), flush=True)
    for label in res["X"]:
        if not label.startswith("at_"):
            continue
        dd = res["X"][label]["direct"] - res["L"][label]["direct"]
        dx = res["X"][label]["exchange"] - res["L"][label]["exchange"]
        print(f"{label}: O1 contribution of second-order direct {dd*1e3:+.2f} meV, "
              f"of second-order exchange (not in GW) {dx*1e3:+.2f} meV")
    if a.out:
        pathlib.Path(a.out).write_text(json.dumps(res, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
