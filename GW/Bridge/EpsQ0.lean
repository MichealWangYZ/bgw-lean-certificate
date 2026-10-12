/-
BRIDGE-Q0 Q1: the `q → 0` limit of the finite-k-grid RPA screening.

BRIDGE-EPS derived `eps` for `q ≠ 0`; BerkeleyGW's `q = 0` block is EpsSpec at a small
finite `q0` (here `(0,0,0.001)` crystal). This file states what the theory at `q = 0` is
(the `q → 0` limit along a direction `u`) and what EpsSpec at a finite `q0 = t0 u` is
relative to it.

**χ0 near `q = 0`** (`KPRay`, one ray `q = t u` of the finite transition set: the
k-grid, valence/conduction pairs, the Epsilon band set). EpsSpec's
`χ(q; G, G') = C Σ_x M_x(q, G) M_x(q, G') / (E_v(k+q) - E_c(k))` (`C = 4/(N_k Ω)`).

* `KPRay.head_tendsto`, `wing_tendsto`, `wing'_tendsto`, `body_tendsto`: if
  `M_x(0, G = 0) = 0` (orthogonality of distinct Bloch bands at the same `k`), the map
  `t ↦ M_x(t u, 0)` has derivative `p_x` at `0` (the k·p / commutator slope
  `p_x = ⟨v|∂_t H|c⟩ / (E_v - E_c)`, `∂_t H = 2 u·(k+G)` for a local potential; its value
  is NOT derived here: it is the hypothesis `slope`), the other matrix elements and the
  energies are continuous and the pairs are gapped, then
  `χ_00 / t² → C Σ p² / ΔE` (head `~ q²`), `χ_0G / t → C Σ p M(0,G)/ΔE` (wings `~ q`),
  `χ_GG' → χ(0)_GG'` (body `O(1)`). `head_coef_nonpos`: the head coefficient is `≤ 0`.

**`eps⁻¹` near `q = 0`** (`epsM v χ = 1 - diag(v) χ`, row-scaled as in EpsSpec, one
distinguished channel `z`, the `G = 0` row/column):

* `eps_conj`, `inv_scaled`: with `s = (t at z, 1 elsewhere)`,
  `diag(s) eps diag(s)⁻¹ = epsM (s² v) (χ / (s ⊗ s))` (the "scaled" eps `Ẽ(t)`), so
  `eps⁻¹_ij = Ẽ(t)⁻¹_ij s_j / s_i`.
* `q0_limit`: if the scaled Coulomb `s² v` and the scaled `χ` converge (the Coulomb head
  `8π/|q|²` times `t²` is `8π/|u|²`, `coulomb_head`; the `χ` limits are the four
  theorems above, assembled in `chiSc_tendsto`) and the limit `Ẽ0` is invertible, then
  `eps⁻¹` head `→ Ẽ0⁻¹_zz`, body `→ Ẽ0⁻¹_ij`, `t · (row wing) → Ẽ0⁻¹_zj`,
  `(column wing)/t → Ẽ0⁻¹_iz`: the unscaled row wing is `O(1/|q|)` (it diverges like
  `1/|q|` unless `Ẽ0⁻¹_zj = 0`) and the column wing is `O(|q|)`; all four limits depend
  on the direction `u`.
* `schur_body`: the body of `Ẽ0⁻¹` is the inverse of the head-projected matrix
  `P_ij = Ẽ0_ij - Ẽ0_iz Ẽ0_zj / Ẽ0_zz`; `schur_head`: `Ẽ0⁻¹_zz = 1/ε_M` with the
  macroscopic `ε_M = Ẽ0_zz - Ẽ0_{z·} (Ẽ0 body)⁻¹ Ẽ0_{·z}`.
* `parity_inv`: flipping the direction `u ↦ -u` flips the sign of the scaled wings of `χ`
  and keeps head and body (`chi0s_neg`: exact for the limit coefficients, which are
  linear/quadratic in `u`), hence flips the wings of `Ẽ0⁻¹` and keeps its head and body.
* `inv_perturb` (any complete normed ring), `q0_error`: EpsSpec at the finite `q0 = t0 u`
  against the limit: if `‖Ẽ(t0) - Ẽ0‖ ≤ δ` and `‖Ẽ0⁻¹‖ ≤ β` in the `ℓ∞` operator norm with
  `βδ < 1`, then the head, the body, `t0·(row wing)` and `(column wing)/t0` of
  EpsSpec's `eps⁻¹(q0)` are each within `β²δ/(1-βδ)` of their `q → 0` limits. With
  `δ = K t0` this is the `O(|q0|)` statement. `δ` and `β` are computed from the data in
  `bgw/bridge_q0/q0.py`.
-/
import GW.Bridge.EpsRPA
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option linter.unusedSectionVars false

namespace GW.Bridge

open Matrix Finset Filter Topology

/-! ### χ0 along a ray `q = t u` -/

/-- A ray `q = t u` of the finite-k-grid transition data: transitions `T` (the triples
`(k, v, c)`), the prefactor `C = 4/(N_k Ω)`, pair densities `M x t G` and the energies
`E_v(k + t u)`, `E_c(k)`. -/
structure KPRay (τ γ : Type*) where
  T : Finset τ
  C : ℝ
  M : τ → ℝ → γ → ℝ
  Ev : τ → ℝ → ℝ
  Ec : τ → ℝ → ℝ

namespace KPRay

variable {τ γ : Type*} (D : KPRay τ γ)

/-- EpsSpec's `χ(t u; G, G')`. -/
noncomputable def chi (t : ℝ) (g g' : γ) : ℝ :=
  D.C * ∑ x ∈ D.T, D.M x t g * D.M x t g' / (D.Ev x t - D.Ec x t)

/-- The k·p hypotheses on one ray, with `G = 0` channel `g0` and slopes `p`. -/
structure OK (g0 : γ) (p : τ → ℝ) : Prop where
  /-- `⟨v,k|c,k⟩ = 0`: distinct bands at the same `k` are orthogonal. -/
  orth : ∀ x ∈ D.T, D.M x 0 g0 = 0
  /-- The k·p slope: `d/dt M_x(t u, 0) = p_x` at `t = 0`. -/
  slope : ∀ x ∈ D.T, HasDerivAt (fun t => D.M x t g0) (p x) 0
  cont : ∀ x ∈ D.T, ∀ g, ContinuousAt (fun t => D.M x t g) 0
  ev : ∀ x ∈ D.T, ContinuousAt (D.Ev x) 0
  ec : ∀ x ∈ D.T, ContinuousAt (D.Ec x) 0
  gap : ∀ x ∈ D.T, D.Ev x 0 - D.Ec x 0 ≠ 0

/-- The head coefficient `C Σ p² / ΔE`. -/
noncomputable def headC (p : τ → ℝ) : ℝ := D.C * ∑ x ∈ D.T, p x * p x / (D.Ev x 0 - D.Ec x 0)

/-- The wing coefficient `C Σ p M(0, G) / ΔE`. -/
noncomputable def wingC (p : τ → ℝ) (g : γ) : ℝ :=
  D.C * ∑ x ∈ D.T, p x * D.M x 0 g / (D.Ev x 0 - D.Ec x 0)

variable {D} {g0 : γ} {p : τ → ℝ}

theorem ne_eventually : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 :=
  eventually_nhdsWithin_of_forall fun _ h => h

theorem M_div_tendsto (h : D.OK g0 p) {x : τ} (hx : x ∈ D.T) :
    Tendsto (fun t => D.M x t g0 / t) (𝓝[≠] 0) (𝓝 (p x)) := by
  have := (hasDerivAt_iff_tendsto_slope.mp (h.slope x hx))
  refine this.congr' (Eventually.of_forall fun t => ?_)
  simp only [slope_def_field, h.orth x hx, sub_zero]

theorem den_tendsto (h : D.OK g0 p) {x : τ} (hx : x ∈ D.T) :
    Tendsto (fun t => D.Ev x t - D.Ec x t) (𝓝[≠] 0) (𝓝 (D.Ev x 0 - D.Ec x 0)) :=
  ((h.ev x hx).tendsto.sub (h.ec x hx).tendsto).mono_left nhdsWithin_le_nhds

theorem M_tendsto (h : D.OK g0 p) {x : τ} (hx : x ∈ D.T) (g : γ) :
    Tendsto (fun t => D.M x t g) (𝓝[≠] 0) (𝓝 (D.M x 0 g)) :=
  (h.cont x hx g).tendsto.mono_left nhdsWithin_le_nhds

/-- **Head `~ q²`.** -/
theorem head_tendsto (h : D.OK g0 p) :
    Tendsto (fun t => D.chi t g0 g0 / t ^ 2) (𝓝[≠] 0) (𝓝 (D.headC p)) := by
  have hs : Tendsto (fun t => D.C * ∑ x ∈ D.T, (D.M x t g0 / t) * (D.M x t g0 / t) /
      (D.Ev x t - D.Ec x t)) (𝓝[≠] 0) (𝓝 (D.headC p)) := by
    refine tendsto_const_nhds.mul (tendsto_finset_sum _ fun x hx => ?_)
    exact ((M_div_tendsto h hx).mul (M_div_tendsto h hx)).div (den_tendsto h hx) (h.gap x hx)
  refine hs.congr' ?_
  filter_upwards [ne_eventually] with t ht
  rw [chi, mul_div_assoc, Finset.sum_div]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  field_simp; ring

/-- **Row wing `~ q`.** -/
theorem wing_tendsto (h : D.OK g0 p) (g : γ) :
    Tendsto (fun t => D.chi t g0 g / t) (𝓝[≠] 0) (𝓝 (D.wingC p g)) := by
  have hs : Tendsto (fun t => D.C * ∑ x ∈ D.T, (D.M x t g0 / t) * D.M x t g /
      (D.Ev x t - D.Ec x t)) (𝓝[≠] 0) (𝓝 (D.wingC p g)) := by
    refine tendsto_const_nhds.mul (tendsto_finset_sum _ fun x hx => ?_)
    exact ((M_div_tendsto h hx).mul (M_tendsto h hx g)).div (den_tendsto h hx) (h.gap x hx)
  refine hs.congr' ?_
  filter_upwards [ne_eventually] with t ht
  rw [chi, mul_div_assoc, Finset.sum_div]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  field_simp; ring

/-- **Column wing `~ q`.** -/
theorem wing'_tendsto (h : D.OK g0 p) (g : γ) :
    Tendsto (fun t => D.chi t g g0 / t) (𝓝[≠] 0) (𝓝 (D.wingC p g)) := by
  refine (wing_tendsto h g).congr' (Eventually.of_forall fun t => ?_)
  simp only [chi, mul_comm (D.M _ t g0)]

/-- **Body `O(1)`**, continuous at `q = 0`. -/
theorem body_tendsto (h : D.OK g0 p) (g g' : γ) :
    Tendsto (fun t => D.chi t g g') (𝓝[≠] 0) (𝓝 (D.chi 0 g g')) := by
  refine tendsto_const_nhds.mul (tendsto_finset_sum _ fun x hx => ?_)
  exact ((M_tendsto h hx g).mul (M_tendsto h hx g')).div (den_tendsto h hx) (h.gap x hx)

/-- The head coefficient is `≤ 0` for gapped pairs (`E_v < E_c`) and `C ≥ 0`. -/
theorem head_coef_nonpos (hC : 0 ≤ D.C) (hg : ∀ x ∈ D.T, D.Ev x 0 < D.Ec x 0) :
    D.headC p ≤ 0 := by
  unfold headC
  refine mul_nonpos_of_nonneg_of_nonpos hC (sum_nonpos fun x hx => ?_)
  exact div_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) (by linarith [hg x hx])

end KPRay

/-! ### The scaled eps and its inverse -/

variable {N : ℕ}

/-- The scale `s = (t at z, 1 elsewhere)`. -/
def scv (z : Fin N) (t : ℝ) : Fin N → ℝ := fun i => if i = z then t else 1

/-- The scaled Coulomb `s² v`. -/
def vSc (z : Fin N) (t : ℝ) (v : Fin N → ℝ) : Fin N → ℝ := fun i => scv z t i ^ 2 * v i

/-- The scaled `χ / (s ⊗ s)`. -/
noncomputable def chiSc (z : Fin N) (t : ℝ) (χ : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  of fun i j => χ i j / (scv z t i * scv z t j)

theorem scv_ne {z : Fin N} {t : ℝ} (ht : t ≠ 0) (i : Fin N) : scv z t i ≠ 0 := by
  unfold scv; split_ifs <;> simp [ht]

theorem eps_conj (z : Fin N) {t : ℝ} (ht : t ≠ 0) (v : Fin N → ℝ) (χ : Matrix (Fin N) (Fin N) ℝ) :
    diagonal (scv z t) * epsM v χ = epsM (vSc z t v) (chiSc z t χ) * diagonal (scv z t) := by
  ext i j
  have hi := scv_ne (z := z) ht i
  have hj := scv_ne (z := z) ht j
  simp only [epsM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, sub_apply,
    diagonal_mul, mul_diagonal, diagonal_apply, vSc, chiSc, of_apply]
  by_cases hij : i = j
  · subst hij; simp; field_simp; ring
  · simp [hij]; field_simp; ring

/-- The inverse diagonal. -/
theorem diag_inv {z : Fin N} {t : ℝ} (ht : t ≠ 0) :
    diagonal (fun i => (scv z t i)⁻¹) * diagonal (scv z t) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext fun i => inv_mul_cancel₀ (scv_ne ht i))

theorem diag_inv' {z : Fin N} {t : ℝ} (ht : t ≠ 0) :
    diagonal (scv z t) * diagonal (fun i => (scv z t i)⁻¹) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (scv_ne ht i))

/-- **`eps⁻¹_ij = Ẽ⁻¹_ij s_j / s_i`.** -/
theorem inv_scaled (z : Fin N) {t : ℝ} (ht : t ≠ 0) (v : Fin N → ℝ)
    (χ : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    (epsM v χ)⁻¹ i j = (epsM (vSc z t v) (chiSc z t χ))⁻¹ i j * scv z t j / scv z t i := by
  set D := diagonal (scv z t)
  set Di := diagonal (fun i => (scv z t i)⁻¹)
  set Et := epsM (vSc z t v) (chiSc z t χ)
  have e : epsM v χ = Di * Et * D := by
    rw [Matrix.mul_assoc, ← eps_conj z ht v χ, ← Matrix.mul_assoc, diag_inv ht, Matrix.one_mul]
  have hD : D⁻¹ = Di := inv_eq_left_inv (diag_inv ht)
  have hDi : Di⁻¹ = D := inv_eq_left_inv (diag_inv' ht)
  rw [e, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hD, hDi, ← Matrix.mul_assoc]
  simp only [Di, D, mul_diagonal, diagonal_mul]
  rw [div_eq_mul_inv]; ring

/-- The Coulomb head: `t² · c/t² = c`. -/
theorem coulomb_head {z : Fin N} {t c : ℝ} (ht : t ≠ 0) {v : Fin N → ℝ} (hv : v z = c / t ^ 2) :
    vSc z t v z = c := by
  simp only [vSc, scv, if_true, hv]; field_simp

theorem vSc_off {z : Fin N} {t : ℝ} (v : Fin N → ℝ) {i : Fin N} (hi : i ≠ z) :
    vSc z t v i = v i := by simp [vSc, scv, hi]

/-- **The `q → 0` limit of `eps⁻¹`.** -/
theorem q0_limit (z : Fin N) {v : ℝ → Fin N → ℝ} {χ : ℝ → Matrix (Fin N) (Fin N) ℝ}
    {v0 : Fin N → ℝ} {χ0 : Matrix (Fin N) (Fin N) ℝ}
    (hv : Tendsto (fun t => vSc z t (v t)) (𝓝[≠] 0) (𝓝 v0))
    (hχ : Tendsto (fun t => chiSc z t (χ t)) (𝓝[≠] 0) (𝓝 χ0))
    (hdet : IsUnit (epsM v0 χ0).det) :
    Tendsto (fun t => (epsM (v t) (χ t))⁻¹ z z) (𝓝[≠] 0) (𝓝 ((epsM v0 χ0)⁻¹ z z)) ∧
    (∀ i j, i ≠ z → j ≠ z →
      Tendsto (fun t => (epsM (v t) (χ t))⁻¹ i j) (𝓝[≠] 0) (𝓝 ((epsM v0 χ0)⁻¹ i j))) ∧
    (∀ j, j ≠ z →
      Tendsto (fun t => t * (epsM (v t) (χ t))⁻¹ z j) (𝓝[≠] 0) (𝓝 ((epsM v0 χ0)⁻¹ z j))) ∧
    (∀ i, i ≠ z →
      Tendsto (fun t => (epsM (v t) (χ t))⁻¹ i z / t) (𝓝[≠] 0) (𝓝 ((epsM v0 χ0)⁻¹ i z))) := by
  have heps : Tendsto (fun t => epsM (vSc z t (v t)) (chiSc z t (χ t))) (𝓝[≠] 0)
      (𝓝 (epsM v0 χ0)) := by
    have hd : Tendsto (fun t => diagonal (vSc z t (v t))) (𝓝[≠] 0) (𝓝 (diagonal v0)) :=
      (continuous_id.matrix_diagonal).continuousAt.tendsto.comp hv
    exact tendsto_const_nhds.sub (hd.mul hχ)
  have hinv : ContinuousAt Inv.inv (epsM v0 χ0) :=
    continuousAt_matrix_inv _ (by simpa using NormedRing.inverse_continuousAt hdet.unit)
  have hX := hinv.tendsto.comp heps
  have hent : ∀ i j, Tendsto (fun t => (epsM (vSc z t (v t)) (chiSc z t (χ t)))⁻¹ i j)
      (𝓝[≠] 0) (𝓝 ((epsM v0 χ0)⁻¹ i j)) := fun i j =>
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hX i) j
  have key : ∀ i j, ∀ᶠ t in 𝓝[≠] (0 : ℝ), (epsM (v t) (χ t))⁻¹ i j =
      (epsM (vSc z t (v t)) (chiSc z t (χ t)))⁻¹ i j * scv z t j / scv z t i := by
    intro i j
    filter_upwards [KPRay.ne_eventually] with t ht
    exact inv_scaled z ht _ _ i j
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (hent z z).congr' ?_
    filter_upwards [key z z, KPRay.ne_eventually] with t h ht
    rw [h, scv, if_pos rfl]; field_simp
  · intro i j hi hj
    refine (hent i j).congr' ?_
    filter_upwards [key i j] with t h
    rw [h]; simp [scv, hi, hj]
  · intro j hj
    refine (hent z j).congr' ?_
    filter_upwards [key z j, KPRay.ne_eventually] with t h ht
    rw [h]; simp only [scv, if_pos rfl, if_neg hj]; field_simp
  · intro i hi
    refine (hent i z).congr' ?_
    filter_upwards [key i z, KPRay.ne_eventually] with t h ht
    rw [h]; simp only [scv, if_pos rfl, if_neg hi]; field_simp

/-! ### The limit of the scaled χ from the k·p data -/

/-- The scaled `χ` limit on the sphere `gs` (channel `z` is `G = 0`): head `headC`,
wings `wingC`, body `χ(0)`. -/
noncomputable def chi0s {τ γ : Type*} (D : KPRay τ γ) (p : τ → ℝ) (z : Fin N) (gs : Fin N → γ) :
    Matrix (Fin N) (Fin N) ℝ :=
  of fun i j => if i = z ∧ j = z then D.headC p else if i = z then D.wingC p (gs j)
    else if j = z then D.wingC p (gs i) else D.chi 0 (gs i) (gs j)

/-- `χ(t)` on the sphere. -/
noncomputable def chiRay {τ γ : Type*} (D : KPRay τ γ) (gs : Fin N → γ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  of fun i j => D.chi t (gs i) (gs j)

/-- **The scaled `χ` converges** (head `/t²`, wings `/t`, body): the input of `q0_limit`. -/
theorem chiSc_tendsto {τ γ : Type*} {D : KPRay τ γ} {g0 : γ} {p : τ → ℝ} (h : D.OK g0 p)
    (z : Fin N) (gs : Fin N → γ) (hz : gs z = g0) :
    Tendsto (fun t => chiSc z t (chiRay D gs t)) (𝓝[≠] 0) (𝓝 (chi0s D p z gs)) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  simp only [chiSc, chiRay, chi0s, of_apply, scv]
  by_cases hi : i = z <;> by_cases hj : j = z
  · subst hi; subst hj; simp only [and_self, if_true]
    refine (KPRay.head_tendsto h).congr' (Eventually.of_forall fun t => ?_)
    rw [hz, sq]
  · subst hi; simp only [if_true, if_neg hj, true_and, mul_one]
    rw [hz]; exact KPRay.wing_tendsto h _
  · subst hj; simp only [if_true, if_neg hi, false_and, one_mul, and_true]
    rw [hz]; exact KPRay.wing'_tendsto h _
  · simp only [hi, hj, if_false, false_and, and_false, mul_one, div_one]
    exact KPRay.body_tendsto h _ _

/-! ### Schur complements: the head-projected body and the macroscopic head -/

/-- **Body of the inverse = inverse of the head-projected matrix.** If `A X = 1` and
`A_zz ≠ 0`, then for `j ≠ z` (and every `i`; for `i, j ≠ z` this is `P X_body = 1`),
`Σ_{k ≠ z} (A_ik - A_iz A_zk / A_zz) X_kj = δ_ij`. -/
theorem schur_body (z : Fin N) (A X : Matrix (Fin N) (Fin N) ℝ) (hAX : A * X = 1)
    (hzz : A z z ≠ 0) (i j : Fin N) (hj : j ≠ z) :
    ∑ k ∈ univ.erase z, (A i k - A i z * A z k / A z z) * X k j = if i = j then 1 else 0 := by
  have r1 : A z z * X z j + ∑ k ∈ univ.erase z, A z k * X k j = 0 := by
    have := congrFun (congrFun hAX z) j
    rw [mul_apply, ← add_sum_erase _ _ (mem_univ z), one_apply, if_neg (Ne.symm hj)] at this
    exact this
  have r2 : A i z * X z j + ∑ k ∈ univ.erase z, A i k * X k j = if i = j then 1 else 0 := by
    have := congrFun (congrFun hAX i) j
    rw [mul_apply, ← add_sum_erase _ _ (mem_univ z), one_apply] at this
    exact this
  have hx : X z j = -(∑ k ∈ univ.erase z, A z k * X k j) / A z z := by
    rw [eq_div_iff hzz]; linarith [mul_comm (X z j) (A z z)]
  rw [← r2, hx]
  simp only [sub_mul, sum_sub_distrib]
  have : ∑ k ∈ univ.erase z, A i z * A z k / A z z * X k j =
      A i z / A z z * ∑ k ∈ univ.erase z, A z k * X k j := by
    rw [mul_sum]; refine sum_congr rfl fun k _ => ?_; ring
  rw [this]; field_simp; ring

/-- **Head of the inverse = `1/ε_M`.** If `A X = 1` and `Bi` is a left inverse of the
body of `A` (on the complement of `z`), then
`X_zz (A_zz - Σ_{k,l ≠ z} A_zk Bi_kl A_lz) = 1`. -/
theorem schur_head (z : Fin N) (A X Bi : Matrix (Fin N) (Fin N) ℝ) (hAX : A * X = 1)
    (hB : ∀ k m, k ≠ z → m ≠ z →
      ∑ l ∈ univ.erase z, Bi k l * A l m = if k = m then 1 else 0) :
    X z z * (A z z - ∑ k ∈ univ.erase z, ∑ l ∈ univ.erase z, A z k * Bi k l * A l z) = 1 := by
  have col : ∀ l, l ≠ z → A l z * X z z + ∑ m ∈ univ.erase z, A l m * X m z = 0 := by
    intro l hl
    have := congrFun (congrFun hAX l) z
    rw [mul_apply, ← add_sum_erase _ _ (mem_univ z), one_apply, if_neg hl] at this
    exact this
  have hk : ∀ k ∈ univ.erase z, X k z = -(X z z * ∑ l ∈ univ.erase z, Bi k l * A l z) := by
    intro k hk'
    have hkz := ne_of_mem_erase hk'
    have e : ∑ l ∈ univ.erase z, Bi k l * (A l z * X z z + ∑ m ∈ univ.erase z, A l m * X m z) = 0 :=
      sum_eq_zero fun l hl => by rw [col l (ne_of_mem_erase hl), mul_zero]
    simp only [mul_add, sum_add_distrib, mul_sum] at e
    rw [sum_comm] at e
    have e2 : ∑ m ∈ univ.erase z, ∑ l ∈ univ.erase z, Bi k l * (A l m * X m z) = X k z := by
      have : ∀ m ∈ univ.erase z, ∑ l ∈ univ.erase z, Bi k l * (A l m * X m z) =
          (if k = m then 1 else 0) * X m z := by
        intro m hm
        rw [← hB k m hkz (ne_of_mem_erase hm), sum_mul]
        refine sum_congr rfl fun l _ => by ring
      rw [sum_congr rfl this]
      simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_erase, ne_eq, hkz, not_false_eq_true,
        mem_univ, and_self, if_true]
    have e3 : ∑ l ∈ univ.erase z, Bi k l * (A l z * X z z) =
        X z z * ∑ l ∈ univ.erase z, Bi k l * A l z := by
      rw [mul_sum]; refine sum_congr rfl fun l _ => by ring
    linarith
  have row : A z z * X z z + ∑ k ∈ univ.erase z, A z k * X k z = 1 := by
    have := congrFun (congrFun hAX z) z
    rw [mul_apply, ← add_sum_erase _ _ (mem_univ z), one_apply, if_pos rfl] at this
    exact this
  rw [sum_congr rfl fun k hk' => by rw [hk k hk']] at row
  rw [← row, mul_sub]
  simp only [mul_neg, mul_sum, sum_neg_distrib, sub_neg_eq_add, mul_add]
  congr 1
  · ring
  · refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring

/-! ### Parity in the direction `u ↦ -u` -/

/-- The sign flip `S = diag(-1 at z, 1 elsewhere)`. -/
def sgn (z : Fin N) : Fin N → ℝ := fun i => if i = z then -1 else 1

theorem sgn_sq (z : Fin N) : diagonal (sgn z) * diagonal (sgn z) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext fun i => by simp only [sgn]; split_ifs <;> norm_num)

/-- With the limit coefficients `headC` (quadratic in `u`: `p ↦ -p` leaves it) and
`wingC` (linear: flips), the scaled `χ` limit for `-u` is `S χ0s S`. -/
theorem chi0s_neg {τ γ : Type*} (D : KPRay τ γ) (p : τ → ℝ) (z : Fin N) (gs : Fin N → γ) :
    chi0s D (fun x => -p x) z gs = diagonal (sgn z) * chi0s D p z gs * diagonal (sgn z) := by
  ext i j
  simp only [chi0s, KPRay.headC, KPRay.wingC, of_apply, mul_diagonal, diagonal_mul, sgn]
  by_cases hi : i = z <;> by_cases hj : j = z
  · subst hi; subst hj; simp only [and_self, if_true, neg_mul_neg]; ring
  · subst hi; simp only [if_true, if_neg hj, true_and, neg_mul, sum_neg_distrib, neg_div]; ring
  · subst hj; simp only [if_true, if_neg hi, false_and, and_true, neg_mul, sum_neg_distrib,
      neg_div]; ring
  · simp only [if_neg hi, if_neg hj, false_and, and_false]; ring_nf

/-- **Parity of the limit.** If the scaled `χ` for `-u` is `S χ S`, the inverse scaled eps
for `-u` is `S Ẽ⁻¹ S`: head and body even, wings odd in `u`. -/
theorem parity_inv (z : Fin N) (v : Fin N → ℝ) (χ : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    (epsM v (diagonal (sgn z) * χ * diagonal (sgn z)))⁻¹ i j =
      sgn z i * (epsM v χ)⁻¹ i j * sgn z j := by
  set S := diagonal (sgn z)
  have hS : S⁻¹ = S := inv_eq_left_inv (sgn_sq z)
  have e : epsM v (S * χ * S) = S * epsM v χ * S := by
    unfold epsM
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, sgn_sq]
    congr 1
    simp only [S, ← Matrix.mul_assoc, diagonal_mul_diagonal, mul_comm (v _)]
  rw [e, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hS, ← Matrix.mul_assoc]
  simp only [S, mul_diagonal, diagonal_mul]

/-! ### Finite `q0` against the limit: an explicit bound -/

/-- **Perturbed inverse in a complete normed ring.** If `‖A⁻¹‖ ≤ β`, `‖E‖ ≤ δ`, `βδ < 1`,
then `A + E` is a unit and `‖(A + E)⁻¹ - A⁻¹‖ ≤ β² δ / (1 - β δ)`. -/
theorem inv_perturb {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [Nontrivial R]
    (A : Rˣ) (E : R) {β δ : ℝ} (hβ : ‖(↑A⁻¹ : R)‖ ≤ β) (hδ : ‖E‖ ≤ δ) (hlt : β * δ < 1) :
    ∃ B : Rˣ, (B : R) = A + E ∧ ‖(↑B⁻¹ : R) - ↑A⁻¹‖ ≤ β ^ 2 * δ / (1 - β * δ) := by
  have hA0 : 0 < ‖(↑A⁻¹ : R)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg _) hβ
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hδ
  have hprod : ‖(↑A⁻¹ : R)‖ * ‖E‖ < 1 :=
    lt_of_le_of_lt (mul_le_mul hβ hδ (norm_nonneg _) hβ0) hlt
  have hE : ‖E‖ < ‖(↑A⁻¹ : R)‖⁻¹ := by
    have := mul_lt_mul_of_pos_left hprod (inv_pos.mpr hA0)
    rwa [← mul_assoc, inv_mul_cancel₀ hA0.ne', one_mul, mul_one] at this
  set B := A.add E hE
  have hB : (B : R) = A + E := Units.val_add A E hE
  refine ⟨B, hB, ?_⟩
  have res : (↑B⁻¹ : R) - ↑A⁻¹ = -(↑B⁻¹ * E * ↑A⁻¹) := by
    have e1 : (↑B⁻¹ : R) * ↑B = 1 := Units.inv_mul B
    have e2 : (↑A : R) * ↑A⁻¹ = 1 := Units.mul_inv A
    calc (↑B⁻¹ : R) - ↑A⁻¹ = ↑B⁻¹ * (↑A * ↑A⁻¹) - (↑B⁻¹ * ↑B) * ↑A⁻¹ := by
          rw [e1, e2, mul_one, one_mul]
      _ = -(↑B⁻¹ * E * ↑A⁻¹) := by rw [hB]; noncomm_ring
  set d := ‖(↑B⁻¹ : R) - ↑A⁻¹‖
  have h1 : d ≤ ‖(↑B⁻¹ : R)‖ * δ * β := by
    simp only [d, res, norm_neg]
    calc ‖(↑B⁻¹ : R) * E * ↑A⁻¹‖ ≤ ‖(↑B⁻¹ : R) * E‖ * ‖(↑A⁻¹ : R)‖ := norm_mul_le _ _
      _ ≤ ‖(↑B⁻¹ : R)‖ * ‖E‖ * ‖(↑A⁻¹ : R)‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ‖(↑B⁻¹ : R)‖ * δ * β := by gcongr
  have h2 : ‖(↑B⁻¹ : R)‖ ≤ β + d := by
    calc ‖(↑B⁻¹ : R)‖ = ‖(↑A⁻¹ : R) + ((↑B⁻¹ : R) - ↑A⁻¹)‖ := by rw [add_sub_cancel]
      _ ≤ ‖(↑A⁻¹ : R)‖ + d := norm_add_le _ _
      _ ≤ β + d := by linarith
  have h3 : d ≤ (β + d) * δ * β := by
    refine h1.trans ?_
    have := mul_le_mul_of_nonneg_right h2 (mul_nonneg hδ0 hβ0)
    linarith [show ‖(↑B⁻¹ : R)‖ * δ * β = ‖(↑B⁻¹ : R)‖ * (δ * β) by ring,
      show (β + d) * δ * β = (β + d) * (δ * β) by ring]
  rw [le_div_iff₀ (by linarith)]
  nlinarith [h3]

section linfty

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- An entry is bounded by the `ℓ∞` operator norm (the maximal absolute row sum). -/
theorem entry_le_linfty (A : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) : |A i j| ≤ ‖A‖ := by
  have h1 : ‖A i j‖₊ ≤ ∑ k, ‖A i k‖₊ :=
    Finset.single_le_sum (f := fun k => ‖A i k‖₊) (fun _ _ => zero_le _) (mem_univ j)
  have h2 : ∑ k, ‖A i k‖₊ ≤ univ.sup fun i => ∑ k, ‖A i k‖₊ :=
    Finset.le_sup (f := fun i => ∑ k, ‖A i k‖₊) (mem_univ i)
  rw [linfty_opNorm_def, ← Real.norm_eq_abs, ← coe_nnnorm]
  exact_mod_cast h1.trans h2

/-- **EpsSpec at finite `q0 = t0 u` against the `q → 0` limit.** In the `ℓ∞` operator norm,
if the scaled eps at `t0` is within `δ` of the limit `Ẽ0 = epsM v0 χ0`, `‖Ẽ0⁻¹‖ ≤ β` and
`βδ < 1`, then the head, the body, `t0 · (row wing)` and `(column wing) / t0` of
`eps⁻¹(q0)` are within `β²δ/(1-βδ)` of their limits (`q0_limit`). -/
theorem q0_error (z : Fin N) {t0 : ℝ} (ht : t0 ≠ 0) (v : Fin N → ℝ) (χ : Matrix (Fin N) (Fin N) ℝ)
    (v0 : Fin N → ℝ) (χ0 : Matrix (Fin N) (Fin N) ℝ) (hdet : IsUnit (epsM v0 χ0).det) {β δ : ℝ}
    (hβ : ‖(epsM v0 χ0)⁻¹‖ ≤ β)
    (hδ : ‖epsM (vSc z t0 v) (chiSc z t0 χ) - epsM v0 χ0‖ ≤ δ) (hlt : β * δ < 1) :
    |(epsM v χ)⁻¹ z z - (epsM v0 χ0)⁻¹ z z| ≤ β ^ 2 * δ / (1 - β * δ) ∧
    (∀ i j, i ≠ z → j ≠ z →
      |(epsM v χ)⁻¹ i j - (epsM v0 χ0)⁻¹ i j| ≤ β ^ 2 * δ / (1 - β * δ)) ∧
    (∀ j, j ≠ z → |t0 * (epsM v χ)⁻¹ z j - (epsM v0 χ0)⁻¹ z j| ≤ β ^ 2 * δ / (1 - β * δ)) ∧
    (∀ i, i ≠ z → |(epsM v χ)⁻¹ i z / t0 - (epsM v0 χ0)⁻¹ i z| ≤ β ^ 2 * δ / (1 - β * δ)) := by
  haveI : Nonempty (Fin N) := ⟨z⟩
  set A := epsM v0 χ0
  set Et := epsM (vSc z t0 v) (chiSc z t0 χ)
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hdet
  have hAinv : (↑hu.unit⁻¹ : Matrix (Fin N) (Fin N) ℝ) = A⁻¹ := by
    rw [Matrix.coe_units_inv, IsUnit.unit_spec]
  obtain ⟨B, hB, hb⟩ := inv_perturb hu.unit (Et - A) (by rw [hAinv]; exact hβ) hδ hlt
  have hB' : (B : Matrix (Fin N) (Fin N) ℝ) = Et := by rw [hB, IsUnit.unit_spec]; abel
  have hBinv : (↑B⁻¹ : Matrix (Fin N) (Fin N) ℝ) = Et⁻¹ := by rw [Matrix.coe_units_inv, hB']
  rw [hBinv, hAinv] at hb
  have ent : ∀ i j, |Et⁻¹ i j - A⁻¹ i j| ≤ β ^ 2 * δ / (1 - β * δ) := fun i j =>
    (entry_le_linfty (Et⁻¹ - A⁻¹) i j).trans hb
  have key : ∀ i j, (epsM v χ)⁻¹ i j = Et⁻¹ i j * scv z t0 j / scv z t0 i :=
    fun i j => inv_scaled z ht v χ i j
  have hz : scv z t0 z = t0 := by simp [scv]
  have ho : ∀ i, i ≠ z → scv z t0 i = 1 := fun i hi => by simp [scv, hi]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key, hz, mul_div_assoc, div_self ht, mul_one]; exact ent z z
  · intro i j hi hj; rw [key, ho i hi, ho j hj, mul_one, div_one]; exact ent i j
  · intro j hj
    have e : t0 * (Et⁻¹ z j * 1 / t0) = Et⁻¹ z j := by field_simp
    rw [key, hz, ho j hj, e]; exact ent z j
  · intro i hi
    have e : Et⁻¹ i z * t0 / 1 / t0 = Et⁻¹ i z := by field_simp
    rw [key, hz, ho i hi, e]; exact ent i z

end linfty

end GW.Bridge
