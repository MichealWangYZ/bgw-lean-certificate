/-
G2 stage 2: the static RPA dielectric matrix of one q-point, as a real-number
definition over the exact input data (`Input`, file `EpsCheck.lean`).

This is spec A's eps for q ≠ 0 exactly as `bgw/endpoint/cert.py` (`epsinv_iv`,
`mtxel_iv`) and `bgw/endpoint/spec.py` (`EpsilonRun.chi`, `epsinv`) define it,
real flavor, on the symmetry-unfolded full k-grid:

  M_vc(k, G)  = Σ_{G', G2 : G' - G2 = G} c_v(k+q, G') c_c(k, G2)
  chi(G, G')  = 4 / (N_k Ω) Σ_k Σ_v Σ_c M_vc(k, G) M_vc(k, G') / (E_v(k+q) - E_c(k))
  v(G)        = 8π / |q + G|²_B
  eps(G, G')  = δ_GG' - v(G) chi(G, G')

(`epsilon_main.f90:657`, `mtxel.f90:13` eden = 1/(e_val - e_cond),
`epsinv.f90:225-241` row scaling; no cell averaging in Epsilon.) `|x|²_B` is the
quadratic form of the metric `bdot` on reciprocal crystal coordinates. Every
input — the coefficients `c`, the energies (Ry), `bdot`, `celvol`, `q` — is the
exact dyadic rational of the float cert.py uses.

For the certified run, the lists `ks` are computed in Lean from the irreducible
WFN/WFNq coefficients by the symmetry unfolding and checked against the exported
literals (`U.*`, `Unfold.lean`). Trusted (not formalized): the decoding/export of the run
files, and that this formula is BerkeleyGW's (a modeling claim, checked by source reading
and numerical agreement on one run).
-/
import GW.Endpoint.Kernel.EpsCheck
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace GW.Endpoint.Kernel.Eps

open Finset

variable (inp : Input)

/-- The dyadic `x / 2^S` as a real number. -/
noncomputable def dy (S : ℕ) (x : ℤ) : ℝ := (x : ℝ) / 2 ^ S

/-- The pair density `M_vc(k, G) = Σ_{Gv_i - Gc_j = G} c_v(Gv_i) c_c(Gc_j)` of
valence band `v` (at `k + q`) and conduction band `c` (at `k`). -/
noncomputable def M (kp : KPair) (v c : ℕ) (G : V3) : ℝ :=
  ∑ i ∈ range kp.Gv.length, ∑ j ∈ range kp.Gc.length,
    if kp.Gv.getD i 0 - kp.Gc.getD j 0 = G then
      dy inp.SC ((kp.cv.getD v []).getD i 0) * dy inp.SC ((kp.cc.getD c []).getD j 0)
    else 0

/-- The independent-particle polarizability
`chi(G, G') = 4/(N_k Ω) Σ_k Σ_v Σ_c M_vc(G) M_vc(G') / (E_v - E_c)`. -/
noncomputable def chi (G G' : V3) : ℝ :=
  4 / (inp.ks.length * dy inp.SOm inp.Om) *
    ∑ t ∈ range inp.ks.length,
      ∑ v ∈ range (inp.ks.getD t default).cv.length,
        ∑ c ∈ range (inp.ks.getD t default).cc.length,
          M inp (inp.ks.getD t default) v c G * M inp (inp.ks.getD t default) v c G' /
            (dy inp.SEn ((inp.ks.getD t default).Ev.getD v 0) -
              dy inp.SEn ((inp.ks.getD t default).Ec.getD c 0))

/-- `|q + G|²_B = Σ_ab (q + G)_a B_ab (q + G)_b`. -/
noncomputable def qG2 (G : V3) : ℝ :=
  let w : Fin 3 → ℝ := ![G.1 + dy inp.SQ inp.qn.1, G.2.1 + dy inp.SQ inp.qn.2.1,
    G.2.2 + dy inp.SQ inp.qn.2.2]
  ∑ a : Fin 3, ∑ b : Fin 3, w a * dy inp.SB ((inp.B.getD a []).getD b 0) * w b

/-- The bare Coulomb interaction `v(q + G) = 8π / |q + G|²` (Rydberg units). -/
noncomputable def vC (G : V3) : ℝ := 8 * Real.pi / qG2 inp G

/-- The static RPA dielectric matrix `eps_ij = δ_ij - v(q + G_i) chi(G_i, G_j)` on the
sphere `Gs` (row/column `i` is `Gs[i]`). -/
noncomputable def epsR (i j : ℕ) : ℝ :=
  (if i = j then 1 else 0) - vC inp (inp.Gs.getD i 0) * chi inp (inp.Gs.getD i 0) (inp.Gs.getD j 0)

end GW.Endpoint.Kernel.Eps
