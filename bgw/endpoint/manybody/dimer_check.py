#!/usr/bin/env python3
"""G4 cross-check against the Hubbard dimer (GW/Endpoint/HubbardDimerSecondOrder.lean).

    python3 bgw/endpoint/manybody/dimer_check.py [--t T] [--U U]

The half-filled two-site Hubbard model in the spin-orbital basis of the bare
bonding/antibonding orbitals: modes 0 = B up, 1 = B down, 2 = A up, 3 = A down,
eps = (-t, -t, t, t), O = {0, 1}, and v[p,q,r,s] = <pq|rs> of the contact
interaction (spin-conserving on each electron line; spatial part U/2 if the number
of A labels is even, else 0, as in `eri_eq`).

Checks:
1. v has the two symmetries hv1, hv2 assumed by the general theorem.
2. The Brillouin condition Sigma1_ra = 0 holds (parity), so the general theorem
   gives Sigma2 = dir2 + sox2 (relax = 0).
3. Exact Sigma2 of the dimer (exact diagonalization, finite differences in U) equals
   dir2 + sox2 of the general formula.
4. The gap combinations at the orbital energies reproduce the dimer file:
   dir-gap = U^2/(4t), sox-gap = -U^2/(8t) (gap = Sigma_AA(eps_A) - Sigma_BB(eps_B)),
   so GW (HF + dir) misses exactly the SOX -U^2/(8t) at order U^2, as proved there.
   (The dimer file evaluates with HF energies; the difference is O(U^3).)
"""
import argparse
import itertools
import pathlib
import sys

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_sigma2 as cs  # noqa: E402


def dimer(t, U):
    eps = np.array([-t, -t, t, t])
    spin = [0, 1, 0, 1]
    kind = [0, 0, 1, 1]  # 0 = B, 1 = A
    v = np.zeros((4, 4, 4, 4))
    for p, q, r, s in itertools.product(range(4), repeat=4):
        if spin[p] == spin[r] and spin[q] == spin[s]:
            if (kind[p] + kind[q] + kind[r] + kind[s]) % 2 == 0:
                v[p, q, r, s] = U / 2
    return eps, v


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--t", type=float, default=1.0)
    ap.add_argument("--U", type=float, default=1.0)
    a = ap.parse_args()
    t, U = a.t, a.U
    eps, v = dimer(t, U)
    print("hv1:", np.abs(v - v.transpose(1, 0, 3, 2)).max(), " hv2:", np.abs(v - v.transpose(2, 3, 0, 1)).max())
    c = cs.ops(4)
    nocc = 2
    for w in (eps[2] + 0.1, eps[0] - 0.1, 0.33):
        # exact Sigma2 by finite differences in the coupling lambda (v -> lambda v)
        h = 1e-3
        f = {k: cs.exact_sigma(eps, v, nocc, c, k * h, w)[0] for k in (-2, -1, 0, 1, 2)}
        c2 = (-f[2] + 16 * f[1] - 30 * f[0] + 16 * f[-1] - f[-2]) / (24 * h * h)
        S1, dr, sx, rl, _ = cs.formulas(eps, v, nocc, w)
        print(f"w={w:+.3f}  max|S1 occ-emp|={np.abs(S1[2:, :2]).max():.1e}  max|relax|={np.abs(rl).max():.1e}"
              f"  max|Sigma2 - (dir+sox)|={np.abs(c2 - dr - sx).max():.2e}  (scale {np.abs(c2).max():.3f})")
    _, drA, sxA, _, _ = cs.formulas(eps, v, nocc, eps[2])
    _, drB, sxB, _, _ = cs.formulas(eps, v, nocc, eps[0])
    gd = drA[2, 2] - drB[0, 0]
    gx = sxA[2, 2] - sxB[0, 0]
    print(f"dir gap  = {gd:.12f}   U^2/(4t)  = {U * U / (4 * t):.12f}")
    print(f"sox gap  = {gx:.12f}   -U^2/(8t) = {-U * U / (8 * t):.12f}")


if __name__ == "__main__":
    main()
