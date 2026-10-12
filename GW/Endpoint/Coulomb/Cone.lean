/-
G2-coulomb (6/n): the cone formula.

For a tetrahedron with apex `0`, `C = M '' Δ3` (`M` invertible with columns `a, b, c`), and a
nonnegative function `g` homogeneous of degree `-k` (`k < 3`),

  ∫⁻_C g = |det M| / (3 - k) · ∫⁻_{T2} g (a + s₁ (b - a) + s₂ (c - a)) ds       (`lintegral_cone`).

Proof: `v ↦ M v` (linear change of variables), then the radial map
`Φ(r, s) = r (1 - s₁ - s₂, s₁, s₂)` from `(0,1] × T2` onto `Δ3 \ {0}` with Jacobian `r²`,
homogeneity `g(M Φ(r,s)) = r^{-k} g(M Φ(1,s))`, and `∫_0^1 r^{2-k} dr = 1/(3-k)`.
-/
import GW.Endpoint.Coulomb.Leaf

namespace GW.Endpoint.Coulomb

open MeasureTheory Set Finset
open scoped ENNReal

/-- The standard tetrahedron. -/
def D3 : Set E3 := {v | 0 ≤ v 0 ∧ 0 ≤ v 1 ∧ 0 ≤ v 2 ∧ v 0 + v 1 + v 2 ≤ 1}

theorem D3_closed : IsClosed D3 := by
  unfold D3
  refine IsClosed.inter (isClosed_le continuous_const (continuous_apply 0)) ?_
  refine IsClosed.inter (isClosed_le continuous_const (continuous_apply 1)) ?_
  refine IsClosed.inter (isClosed_le continuous_const (continuous_apply 2)) ?_
  exact isClosed_le ((continuous_apply 0).add (continuous_apply 1) |>.add (continuous_apply 2)) continuous_const

theorem D3_meas : MeasurableSet D3 := D3_closed.measurableSet

/-- The linear map of a matrix as a function. -/
def mv (M : Matrix (Fin 3) (Fin 3) ℝ) (v : E3) : E3 := M.mulVec v

theorem mv_eq (M : Matrix (Fin 3) (Fin 3) ℝ) : mv M = Matrix.toLin' M := by
  funext v; rfl

/-- **Linear change of variables.** -/
theorem lintegral_image_mv (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det ≠ 0) {A : Set E3} (hA : MeasurableSet A)
    (g : E3 → ℝ≥0∞) :
    ∫⁻ x in mv M '' A, g x = ENNReal.ofReal |M.det| * ∫⁻ v in A, g (mv M v) := by
  set L := Matrix.toLin' M
  have hL : ∀ x ∈ A, HasFDerivWithinAt (mv M) (LinearMap.toContinuousLinearMap L) A x := by
    intro x _
    rw [mv_eq]
    exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn (mv M) A := by
    intro x _ y _ hxy
    have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
    have := congrArg (fun z => M⁻¹.mulVec z) hxy
    simp only [mv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec] at this
    exact this
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hL hinj g]
  have hdet : (LinearMap.toContinuousLinearMap L).det = M.det := by
    rw [ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin']
  simp only [hdet]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-! ### The radial map -/

/-- `Φ(r, s₁, s₂) = r (1 - s₁ - s₂, s₁, s₂)`. -/
def Phi (w : E3) : E3 := ![w 0 * (1 - w 1 - w 2), w 0 * w 1, w 0 * w 2]

/-- Its domain `(0,1] × T2`. -/
def SPhi : Set E3 := {w | 0 < w 0 ∧ w 0 ≤ 1 ∧ 0 ≤ w 1 ∧ 0 ≤ w 2 ∧ w 1 + w 2 ≤ 1}

theorem SPhi_meas : MeasurableSet SPhi := by
  unfold SPhi
  refine (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter ?_
  refine (measurableSet_le (measurable_pi_apply 0) measurable_const).inter ?_
  refine (measurableSet_le measurable_const (measurable_pi_apply 1)).inter ?_
  refine (measurableSet_le measurable_const (measurable_pi_apply 2)).inter ?_
  exact measurableSet_le ((measurable_pi_apply 1).add (measurable_pi_apply 2)) measurable_const

/-- The Jacobian matrix. -/
def JPhi (w : E3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - w 1 - w 2, -w 0, -w 0; w 1, w 0, 0; w 2, 0, w 0]

theorem JPhi_det (w : E3) : (JPhi w).det = w 0 ^ 2 := by
  simp [JPhi, Matrix.det_fin_three]; ring

theorem hasFDerivAt_Phi (w : E3) :
    HasFDerivAt Phi (LinearMap.toContinuousLinearMap (Matrix.toLin' (JPhi w))) w := by
  apply hasFDerivAt_pi''
  intro i
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 w
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 w
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 w
  fin_cases i
  · have := h0.mul (((hasFDerivAt_const (1 : ℝ) w).sub h1).sub h2)
    convert this using 1
    ext v; simp [JPhi, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail]; ring
  · have := h0.mul h1
    convert this using 1
    ext v; simp [JPhi, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail]; ring
  · have := h0.mul h2
    convert this using 1
    ext v; simp [JPhi, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail]; ring

theorem Phi_injOn : InjOn Phi SPhi := by
  rintro w ⟨h0, -⟩ w' ⟨h0', -⟩ he
  have e0 := congrFun he 0
  have e1 := congrFun he 1
  have e2 := congrFun he 2
  simp only [Phi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at e0 e1 e2
  have hr : w 0 = w' 0 := by nlinarith
  have hw1 : w 1 = w' 1 := by
    rw [hr] at e1; exact mul_left_cancel₀ (ne_of_gt h0') e1
  have hw2 : w 2 = w' 2 := by
    rw [hr] at e2; exact mul_left_cancel₀ (ne_of_gt h0') e2
  ext i; fin_cases i <;> simp [hr, hw1, hw2]

theorem Phi_image : Phi '' SPhi = D3 \ {0} := by
  ext v
  constructor
  · rintro ⟨w, ⟨h0, h1, h2, h3, h4⟩, rfl⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Phi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    · nlinarith
    · positivity
    · positivity
    · nlinarith
    · intro h
      have := congrFun h 1; have h' := congrFun h 2; have h'' := congrFun h 0
      simp [Phi] at this h' h''
      rcases h'' with h'' | h''
      · linarith
      · rcases this with t | t <;> rcases h' with t' | t' <;> [linarith; linarith; linarith; linarith]
  · rintro ⟨⟨h0, h1, h2, h3⟩, hne⟩
    have hr : 0 < v 0 + v 1 + v 2 := by
      by_contra hc
      apply hne
      funext i; fin_cases i
      · show v 0 = 0; linarith
      · show v 1 = 0; linarith
      · show v 2 = 0; linarith
    refine ⟨![v 0 + v 1 + v 2, v 1 / (v 0 + v 1 + v 2), v 2 / (v 0 + v 1 + v 2)], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      try simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
    · exact hr
    · exact h3
    · positivity
    · positivity
    · rw [← add_div, div_le_one hr]; linarith
    · ext i; fin_cases i <;> simp [Phi] <;> field_simp <;> ring

/-- `Φ w = w₀ • (1 - w₁ - w₂, w₁, w₂)`. -/
def Phi1 (w : E3) : E3 := ![1 - w 1 - w 2, w 1, w 2]

theorem Phi_eq (w : E3) : Phi w = w 0 • Phi1 w := by
  ext i; fin_cases i <;> simp [Phi, Phi1]

/-- Fubini on `SPhi = (0,1] × T2`. -/
theorem lintegral_SPhi (F : ℝ → ℝ≥0∞) (G : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ w in SPhi, F (w 0) * G (w 1, w 2) = (∫⁻ r in Ioc 0 1, F r) * ∫⁻ s in T2, G s := by
  rw [← lintegral_indicator SPhi_meas, ← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator T2_meas]
  have hpt : ∀ w : E3, SPhi.indicator (fun w => F (w 0) * G (w 1, w 2)) w =
      (Ioc (0 : ℝ) 1).indicator F (w 0) * T2.indicator G (w 1, w 2) := by
    intro w
    by_cases h1 : w 0 ∈ Ioc (0 : ℝ) 1 <;> by_cases h2 : (w 1, w 2) ∈ T2
    · rw [indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem]
      exact ⟨h1.1, h1.2, h2.1, h2.2.1, h2.2.2⟩
    · rw [indicator_of_not_mem h2, mul_zero, indicator_of_not_mem]
      rintro ⟨-, -, a, b, c⟩; exact h2 ⟨a, b, c⟩
    · rw [indicator_of_not_mem h1, zero_mul, indicator_of_not_mem]
      rintro ⟨a, b, -⟩; exact h1 ⟨a, b⟩
    · rw [indicator_of_not_mem h1, zero_mul, indicator_of_not_mem]
      rintro ⟨a, b, -⟩; exact h1 ⟨a, b⟩
  simp_rw [hpt]
  set Ψ : ℝ × (Fin 2 → ℝ) → ℝ≥0∞ := fun p => (Ioc (0 : ℝ) 1).indicator F p.1 * T2.indicator G (p.2 0, p.2 1)
  have hΨ : ∀ w : E3, (Ioc (0 : ℝ) 1).indicator F (w 0) * T2.indicator G (w 1, w 2) =
      Ψ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0 w) := by
    intro w; simp [Ψ, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.removeNth]; rfl
  simp_rw [hΨ]
  have hmΨ : Measurable Ψ := by
    apply Measurable.mul
    · exact (hF.indicator measurableSet_Ioc).comp measurable_fst
    · exact (hG.indicator T2_meas).comp (((measurable_pi_apply 0).comp measurable_snd).prodMk
        ((measurable_pi_apply 1).comp measurable_snd))
  rw [(volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).lintegral_comp hmΨ]
  simp only [Ψ]
  rw [show (volume : Measure (ℝ × (Fin 2 → ℝ))) = (volume : Measure ℝ).prod volume from rfl]
  have hprod := lintegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin 2 → ℝ)))
    (f := (Ioc (0 : ℝ) 1).indicator F) (g := fun y : Fin 2 → ℝ => T2.indicator G (y 0, y 1))
    (hF.indicator measurableSet_Ioc).aemeasurable
    ((hG.indicator T2_meas).comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))).aemeasurable
  rw [hprod]
  congr 1
  have := (volume_preserving_finTwoArrow ℝ).lintegral_comp (hG.indicator T2_meas)
  simpa [MeasurableEquiv.finTwoArrow] using this

theorem lintegral_radial (m : ℕ) :
    ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (r ^ m) = ENNReal.ofReal (1 / (m + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le zero_le_one, integral_pow]; simp
  · exact (continuous_pow m).integrableOn_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr using pow_nonneg (le_of_lt hr.1) m

/-- The face map `s ↦ (1 - s₁ - s₂, s₁, s₂)`. -/
def fm (s : ℝ × ℝ) : E3 := ![1 - s.1 - s.2, s.1, s.2]

theorem measurable_fm : Measurable fm := by
  unfold fm
  apply measurable_pi_iff.mpr; intro i; fin_cases i <;> simp <;> fun_prop

/-- **The cone formula** (lintegral form). -/
theorem lintegral_cone (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det ≠ 0) (g : E3 → ℝ) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (k : ℕ) (hk : k ≤ 2) (hhom : ∀ r : ℝ, 0 < r → ∀ x, g (r • x) = (r⁻¹) ^ k * g x) :
    ∫⁻ x in mv M '' D3, ENNReal.ofReal (g x) =
      ENNReal.ofReal |M.det| * (ENNReal.ofReal (1 / (3 - k : ℕ)) * ∫⁻ s in T2, ENNReal.ofReal (g (mv M (fm s)))) := by
  rw [lintegral_image_mv M hM D3_meas]
  congr 1
  have hnull : (D3 \ {0} : Set E3) =ᵐ[volume] D3 := diff_null_ae_eq_self (measure_singleton 0)
  rw [← setLIntegral_congr hnull, ← Phi_image]
  have hd : ∀ w ∈ SPhi, HasFDerivWithinAt Phi (LinearMap.toContinuousLinearMap (Matrix.toLin' (JPhi w))) SPhi w :=
    fun w _ => (hasFDerivAt_Phi w).hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume SPhi_meas hd Phi_injOn]
  have hdet : ∀ w, (LinearMap.toContinuousLinearMap (Matrix.toLin' (JPhi w))).det = w 0 ^ 2 := by
    intro w
    rw [ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin', JPhi_det]
  simp only [hdet]
  have hpt : ∀ w ∈ SPhi, ENNReal.ofReal |w 0 ^ 2| * ENNReal.ofReal (g (mv M (Phi w))) =
      ENNReal.ofReal (w 0 ^ (2 - k)) * ENNReal.ofReal (g (mv M (fm (w 1, w 2)))) := by
    rintro w ⟨h0, -⟩
    rw [Phi_eq, show mv M (w 0 • Phi1 w) = w 0 • mv M (Phi1 w) by simp [mv, Matrix.mulVec_smul], hhom _ h0,
      abs_of_nonneg (by positivity)]
    have hf : Phi1 w = fm (w 1, w 2) := by ext i; fin_cases i <;> simp [Phi1, fm]
    rw [hf]
    have hgn := hg0 (mv M (fm (w 1, w 2)))
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : w 0 ^ 2 = w 0 ^ (2 - k) * w 0 ^ k := by rw [← pow_add]; congr 1; omega
    rw [this, inv_pow]; field_simp; ring
  rw [setLIntegral_congr_fun SPhi_meas (Filter.Eventually.of_forall hpt)]
  rw [lintegral_SPhi (fun r => ENNReal.ofReal (r ^ (2 - k))) (fun s => ENNReal.ofReal (g (mv M (fm s))))
    (by fun_prop) (ENNReal.measurable_ofReal.comp (hg.comp ((Matrix.toLin' M).continuous_of_finiteDimensional.measurable.comp
      measurable_fm)))]
  rw [lintegral_radial]
  congr 2
  push_cast [Nat.cast_sub (by omega : k ≤ 3), Nat.cast_sub hk]
  ring

/-- `M (1 - s₁ - s₂, s₁, s₂) = a + s₁ (b - a) + s₂ (c - a)` for the columns `a, b, c` of `M`. -/
theorem mv_fm (M : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ × ℝ) :
    mv M (fm s) = aff (fun i => M i 0) (fun i => M i 1 - M i 0) (fun i => M i 2 - M i 0) s := by
  ext i; simp [mv, fm, aff, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring

end GW.Endpoint.Coulomb
