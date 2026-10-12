/-
BRIDGE-EPS E3: the RPA dielectric matrix `eps = 1 - diag(v) χ0` and the screened
interaction `W = eps⁻¹ diag(v)`.

On a finite channel basis (`Fin N`; in E4 the eps sphere `G_i`) with the diagonal bare
interaction `v_i` (in E4: `v(q + G_i) = 8π/|q + G_i|²`, Rydberg) and a static
polarisability matrix `χ`:

* `epsM v χ = 1 - diag(v) χ`, row-scaled ("unsymmetrised") as in EpsSpec's
  `eps_ij = δ_ij - v(q+G_i) χ(G_i, G_j)`; `WM v χ = eps⁻¹ diag(v)`, the convention of
  BRIDGE (`W_ji = eps⁻¹_ji v_i`, `screened_entry`) and SigmaSpec.

Proved (all exact algebra; no series convergence is claimed):

* `epsM_chi0_eq_dielectric`, `chiMat_eq_chi0`, `theory_eps_eq_dielectric`: the theory
  `χ0` of E1 on the channels IS `GW.LL.chi0` of an explicit transition list (two
  transitions per occupied/empty pair, weight `1`: the two time orderings), so the theory
  eps is `GW.LL.dielectric`, the object whose formal geometric resummation is
  `GW.LL.electronicW = geoW (-(v χ0)) v`.
* `rpa_solve`, `rpa_unique`, `rpa_dyson`: when `det eps ≠ 0`, `W = eps⁻¹ v` is the unique
  solution of `eps W = v`, i.e. of the RPA Dyson equation `W = v + v χ0 W`.
* `rpa_neumann`, `partialScreened_eq_coeff_sum`: for every `K`, when `det eps ≠ 0`,
  `eps⁻¹ v = Σ_{k ≤ K} coeff_k(electronicW) + eps⁻¹ (v χ0)^{K+1} v` exactly: the
  coefficients of the formal RPA series are the Neumann terms of `eps⁻¹ v`, with an
  explicit remainder and no convergence claim.
* `chiMatW_zero`, `wDyn_tendsto`: the dynamic RPA `W(ω) = (1 - v χ0(ω))⁻¹ v` built from
  E1's `χ0(ω)` tends to `eps⁻¹ v` as `ω → 0` (gapped, `det eps ≠ 0`): `eps` is the static
  limit of the RPA.
* `sym_W`, `det_epsSym`, `WM_symm`: with `v > 0`, the symmetrised
  `eps~ = 1 - v^{1/2} χ v^{1/2}` has the same determinant and
  `v^{1/2} eps~⁻¹ v^{1/2} = eps⁻¹ v`; so the symmetrised and unsymmetrised forms give the
  same `W`, which is symmetric when `χ` is. `WM_entry`: `W_ji = eps⁻¹_ji v_i`.
-/
import GW.Bridge.EpsBloch
import GW.LL.Electronic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Ring.Units

set_option linter.unusedSectionVars false

namespace GW.Bridge

open Matrix Finset Filter Topology PowerSeries

variable {N : ℕ}

/-- The RPA dielectric matrix `eps = 1 - diag(v) χ`. -/
def epsM (v : Fin N → ℝ) (χ : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  1 - diagonal v * χ

/-- The RPA screened interaction `W = eps⁻¹ diag(v)`. -/
noncomputable def WM (v : Fin N → ℝ) (χ : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (epsM v χ)⁻¹ * diagonal v

theorem epsM_chi0_eq_dielectric (v : Fin N → ℝ) (ts : List (GW.LL.Transition ℝ N)) :
    epsM v (GW.LL.chi0 ts) = GW.LL.dielectric (diagonal v) ts := rfl

theorem WM_entry (v : Fin N → ℝ) (χ : Matrix (Fin N) (Fin N) ℝ) (j i : Fin N) :
    WM v χ j i = (epsM v χ)⁻¹ j i * v i := mul_diagonal _ _ _ _

/-! ### `W = eps⁻¹ v` solves the RPA equation -/

section solve

variable {v : Fin N → ℝ} {χ : Matrix (Fin N) (Fin N) ℝ}

theorem rpa_solve (h : IsUnit (epsM v χ).det) : epsM v χ * WM v χ = diagonal v := by
  rw [WM, ← Matrix.mul_assoc, mul_nonsing_inv _ h, Matrix.one_mul]

theorem rpa_unique (h : IsUnit (epsM v χ).det) {W : Matrix (Fin N) (Fin N) ℝ}
    (hW : epsM v χ * W = diagonal v) : W = WM v χ := by
  rw [WM, ← hW, ← Matrix.mul_assoc, nonsing_inv_mul _ h, Matrix.one_mul]

/-- The RPA Dyson equation `W = v + v χ W`, when `det eps ≠ 0`. -/
theorem rpa_dyson (h : IsUnit (epsM v χ).det) :
    WM v χ = diagonal v + diagonal v * χ * WM v χ := by
  have := rpa_solve h
  rw [epsM, Matrix.sub_mul, Matrix.one_mul] at this
  exact sub_eq_iff_eq_add.mp this

end solve

/-! ### The formal RPA series, with an exact remainder -/

theorem partialScreened_eq_coeff_sum (v : Matrix (Fin N) (Fin N) ℝ)
    (ts : List (GW.LL.Transition ℝ N)) (K : ℕ) :
    GW.LL.partialScreened v ts K =
      ∑ k ∈ range (K + 1), coeff _ k (GW.LL.electronicW v ts) := by
  induction K with
  | zero => simp [GW.LL.partialScreened, GW.LL.coeff_electronicW]
  | succ K ih =>
      rw [GW.LL.partialScreened, ih, sum_range_succ _ (K + 1), GW.LL.coeff_electronicW]

/-- **`eps⁻¹ v` and the RPA series.** When `det eps ≠ 0`, for every `K`, `eps⁻¹ v` is the
sum of the first `K + 1` coefficients of `GW.LL.electronicW` plus the exact remainder
`eps⁻¹ (v χ0)^{K+1} v`. (Lean's inverse is totalized: without `det eps ≠ 0` the identity
can fail.) -/
theorem rpa_neumann (v : Fin N → ℝ) (ts : List (GW.LL.Transition ℝ N))
    (h : IsUnit (epsM v (GW.LL.chi0 ts)).det) (K : ℕ) :
    WM v (GW.LL.chi0 ts) =
      ∑ k ∈ range (K + 1), coeff _ k (GW.LL.electronicW (diagonal v) ts) +
        (epsM v (GW.LL.chi0 ts))⁻¹ * ((diagonal v * GW.LL.chi0 ts) ^ (K + 1) * diagonal v) := by
  have hd := GW.LL.dielectric_mul_partialScreened (diagonal v) ts K
  rw [← epsM_chi0_eq_dielectric] at hd
  have : GW.LL.partialScreened (diagonal v) ts K =
      (epsM v (GW.LL.chi0 ts))⁻¹ * (diagonal v - (diagonal v * GW.LL.chi0 ts) ^ (K + 1) * diagonal v) := by
    rw [← hd, ← Matrix.mul_assoc, nonsing_inv_mul _ h, Matrix.one_mul]
  rw [← partialScreened_eq_coeff_sum, this, Matrix.mul_sub, WM]
  abel

/-! ### The theory `χ0` of E1 is a `GW.LL.chi0` -/

section theory

variable {ι γ : Type*} [Fintype ι] [DecidableEq ι] (S : FSys ι γ) (gs : Fin N → γ)

/-- The theory static `χ0` on the channels `gs`. -/
noncomputable def chiMat : Matrix (Fin N) (Fin N) ℝ := of fun i j => chiS S (gs i) (gs j)

/-- The dynamic `χ0(ω)` on the channels `gs`. -/
noncomputable def chiMatW (ω : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  of fun i j => chiW S (gs i) (gs j) ω

/-- Two transitions per occupied/empty pair `(v, c)`, weight `1`: the particle-first
ordering (amplitude `P_cv`) and the hole-first ordering (amplitude `P_vc`). -/
noncomputable def tsOf : List (GW.LL.Transition ℝ N) :=
  ((S.O ×ˢ S.Oᶜ).toList.map fun p => ⟨S.ε p.1, S.ε p.2, 1, fun i => S.P p.2 p.1 (gs i)⟩) ++
    ((S.O ×ˢ S.Oᶜ).toList.map fun p => ⟨S.ε p.1, S.ε p.2, 1, fun i => S.P p.1 p.2 (gs i)⟩)

theorem chiMat_eq_chi0 : chiMat S gs = GW.LL.chi0 (tsOf S gs) := by
  ext i j
  rw [GW.LL.chi0_apply, tsOf, List.map_append, List.sum_append, List.map_map, List.map_map,
    Finset.sum_map_toList, Finset.sum_map_toList, ← sum_add_distrib, chiMat, of_apply, chiS,
    sum_product]
  refine sum_congr rfl fun v _ => sum_congr rfl fun c _ => ?_
  simp only [Function.comp]
  ring

theorem theory_eps_eq_dielectric (v : Fin N → ℝ) :
    epsM v (chiMat S gs) = GW.LL.dielectric (diagonal v) (tsOf S gs) := by
  rw [chiMat_eq_chi0]; rfl

theorem chiMatW_zero : chiMatW S gs 0 = chiMat S gs := by
  ext i j; simp only [chiMatW, chiMat, of_apply, chiW_zero]

/-- **Static limit of the RPA.** Off the excitations at `ω = 0` (`ExcOff S 0`, e.g.
gapped) and when `det eps ≠ 0`, the dynamic `W(ω) = (1 - v χ0(ω))⁻¹ v` tends to
`eps⁻¹ v` as `ω → 0`. -/
theorem wDyn_tendsto (v : Fin N → ℝ) (h0 : ExcOff S 0)
    (h : IsUnit (epsM v (chiMat S gs)).det) :
    Tendsto (fun ω => (epsM v (chiMatW S gs ω))⁻¹ * diagonal v) (𝓝 0)
      (𝓝 (WM v (chiMat S gs))) := by
  have hchi : Tendsto (chiMatW S gs) (𝓝 0) (𝓝 (chiMat S gs)) := by
    rw [← chiMatW_zero]
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    simp only [chiMatW, of_apply]
    exact chiW_continuousAt S (gs i) (gs j) h0
  have heps : Tendsto (fun ω => epsM v (chiMatW S gs ω)) (𝓝 0) (𝓝 (epsM v (chiMat S gs))) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hchi)
  have hinv : ContinuousAt Inv.inv (epsM v (chiMat S gs)) :=
    continuousAt_matrix_inv _ (by
      have := NormedRing.inverse_continuousAt h.unit
      simpa using this)
  exact (hinv.tendsto.comp heps).mul tendsto_const_nhds

end theory

/-! ### Symmetrised and unsymmetrised forms -/

section sym

variable (v : Fin N → ℝ) (χ : Matrix (Fin N) (Fin N) ℝ)

/-- `v^{1/2}`. -/
noncomputable def sqD : Matrix (Fin N) (Fin N) ℝ := diagonal fun i => √(v i)

/-- The symmetrised dielectric matrix `eps~ = 1 - v^{1/2} χ v^{1/2}`. -/
noncomputable def epsSym : Matrix (Fin N) (Fin N) ℝ := 1 - sqD v * χ * sqD v

variable {v χ}

theorem sqD_mul_sqD (hv : ∀ i, 0 ≤ v i) : sqD v * sqD v = diagonal v := by
  have e : (fun i => √(v i) * √(v i)) = v := funext fun i => Real.mul_self_sqrt (hv i)
  rw [sqD, diagonal_mul_diagonal, e]

theorem epsM_mul_sq (hv : ∀ i, 0 ≤ v i) : epsM v χ * sqD v = sqD v * epsSym v χ := by
  rw [epsM, epsSym, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    ← sqD_mul_sqD hv, Matrix.mul_assoc (sqD v), Matrix.mul_assoc (sqD v), Matrix.mul_assoc]

theorem det_sqD_ne (hv : ∀ i, 0 < v i) : (sqD v).det ≠ 0 := by
  rw [sqD, det_diagonal]
  exact prod_ne_zero_iff.mpr fun i _ => (Real.sqrt_pos.mpr (hv i)).ne'

theorem det_epsSym (hv : ∀ i, 0 < v i) : (epsSym v χ).det = (epsM v χ).det := by
  have h := congrArg det (epsM_mul_sq (χ := χ) fun i => (hv i).le)
  rw [det_mul, det_mul, mul_comm] at h
  exact (mul_left_cancel₀ (det_sqD_ne hv) h).symm

/-- **Symmetrised = unsymmetrised.** For `v > 0` and `det eps ≠ 0`,
`v^{1/2} eps~⁻¹ v^{1/2} = eps⁻¹ v`. -/
theorem sym_W (hv : ∀ i, 0 < v i) (h : IsUnit (epsM v χ).det) :
    sqD v * (epsSym v χ)⁻¹ * sqD v = WM v χ := by
  have hs : IsUnit (epsSym v χ).det := by rw [det_epsSym hv]; exact h
  apply rpa_unique h
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, epsM_mul_sq fun i => (hv i).le, Matrix.mul_assoc (sqD v),
    mul_nonsing_inv _ hs, Matrix.mul_one, sqD_mul_sqD fun i => (hv i).le]

/-- `W` is symmetric when `χ` is. -/
theorem WM_symm (hv : ∀ i, 0 < v i) (h : IsUnit (epsM v χ).det) (hχ : χᵀ = χ) :
    (WM v χ)ᵀ = WM v χ := by
  rw [← sym_W hv h, transpose_mul, transpose_mul, transpose_nonsing_inv]
  have hS : (sqD v)ᵀ = sqD v := diagonal_transpose _
  have hE : (epsSym v χ)ᵀ = epsSym v χ := by
    rw [epsSym, transpose_sub, transpose_one, transpose_mul, transpose_mul, hS, hχ,
      Matrix.mul_assoc]
  rw [hS, hE, Matrix.mul_assoc]

end sym

end GW.Bridge
