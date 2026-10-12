/-
G2-coulomb (8/n): real-valued signed identity for `fk`, cone finiteness.
-/
import GW.Endpoint.Coulomb.Signed

namespace GW.Endpoint.Coulomb

open MeasureTheory Set Finset
open scoped ENNReal

theorem QF.measurable_fk (Q : QF) (k : ℕ) : Measurable (Q.fk k) := by
  unfold QF.fk
  exact ((Real.continuous_sqrt.comp Q.continuous_q).measurable.inv).pow_const k

theorem QF.fk_hom (Q : QF) (k : ℕ) (r : ℝ) (hr : 0 < r) (x : E3) : Q.fk k (r • x) = r⁻¹ ^ k * Q.fk k x := by
  unfold QF.fk
  rw [QF.q_smul, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq (le_of_lt hr), mul_inv, mul_pow]

theorem QF.continuousOn_fk (Q : QF) (k : ℕ) {S : Set E3} (h : ∀ x ∈ S, x ≠ 0) : ContinuousOn (Q.fk k) S := by
  unfold QF.fk
  apply ContinuousOn.pow
  apply ContinuousOn.inv₀ (Real.continuous_sqrt.comp Q.continuous_q).continuousOn
  intro x hx; exact ne_of_gt (Real.sqrt_pos.mpr (Q.q_pos (h x hx)))

theorem measure_image_mv_zero (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det = 0) (A : Set E3) :
    volume (mv M '' A) = 0 := by
  have hsub : mv M '' A ⊆ (LinearMap.range (Matrix.toLin' M) : Set E3) := by
    rintro _ ⟨v, -, rfl⟩; rw [mv_eq]; exact ⟨v, rfl⟩
  apply measure_mono_null hsub
  apply Measure.addHaar_submodule
  intro htop
  have hs : Function.Surjective (Matrix.toLin' M) := LinearMap.range_eq_top.mp htop
  have hinj : Function.Injective (Matrix.toLin' M) := LinearMap.injective_iff_surjective.mpr hs
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hM
  apply hv
  apply hinj
  rw [map_zero]; exact hMv

/-- A cone over a face avoiding the origin has finite `∫⁻ |x|^{-k}`. -/
theorem cone_finite (Q : QF) (M : Matrix (Fin 3) (Fin 3) ℝ) {k : ℕ} (hk : k ≤ 2)
    (h0 : ∀ s ∈ T2, mv M (fm s) ≠ 0) :
    ∫⁻ x in mv M '' D3, ENNReal.ofReal (Q.fk k x) < ⊤ := by
  by_cases hM : M.det = 0
  · rw [Measure.restrict_eq_zero.mpr (measure_image_mv_zero M hM D3)]; simp
  rw [lintegral_cone M hM (Q.fk k) (Q.measurable_fk k) (Q.fk_nonneg k) k hk (Q.fk_hom k)]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  have hc : ContinuousOn (fun s => Q.fk k (mv M (fm s))) T2 := by
    apply (Q.continuousOn_fk k (S := mv M '' (fm '' T2)) ?_).comp
    · rw [mv_eq]
      exact ((Matrix.toLin' M).continuous_of_finiteDimensional.comp
        (by unfold fm; exact continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop)).continuousOn
    · intro s hs; exact ⟨fm s, ⟨s, hs, rfl⟩, rfl⟩
    · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩; exact h0 s hs
  obtain ⟨C, hC⟩ := T2_compact.exists_bound_of_continuousOn hc
  calc ∫⁻ s in T2, ENNReal.ofReal (Q.fk k (mv M (fm s))) ≤ ∫⁻ _ in T2, ENNReal.ofReal C := by
        apply setLIntegral_mono measurable_const
        intro s hs; apply ENNReal.ofReal_le_ofReal
        have := hC s hs; rw [Real.norm_eq_abs] at this; exact le_trans (le_abs_self _) this
    _ < ⊤ := by rw [setLIntegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top volume_T2_lt

/-- The sign as a real number. -/
noncomputable def sg (a : ℝ) : ℝ := if 0 < a then 1 else if a < 0 then -1 else 0

namespace Tet

variable {T : Tet}

theorem face_ne_zero (hT : T.Ok) {j : Fin 4} (hj : T.al j ≠ 0) : ∀ s ∈ T2, mv (T.faceM j) (fm s) ≠ 0 := by
  intro s _ h0
  rw [mv_faceM] at h0
  set μ : Fin 4 → ℝ := Fin.insertNth j 0 (fm s)
  have hμ : ∑ c, fm s c • T.p (j.succAbove c) = ∑ i, μ i • T.p i := by
    rw [Fin.sum_univ_succAbove _ j]; simp [μ]
  have hμs : ∑ i, μ i = 1 := by
    rw [Fin.sum_univ_succAbove _ j]; simp [μ, Fin.sum_univ_three, fm]; ring
  rw [hμ] at h0
  have := lam_comb hT μ j
  rw [h0, hμs] at this
  simp [μ, lam] at this
  exact hj this

theorem cone_fin (Q : QF) (hT : T.Ok) {k : ℕ} (hk : k ≤ 2) {j : Fin 4} (hj : T.al j ≠ 0) :
    ∫⁻ x in T.cone j, ENNReal.ofReal (Q.fk k x) < ⊤ :=
  cone_finite Q (T.faceM j) hk (face_ne_zero hT hj)

open Classical in
/-- **Real signed identity**: `∫_T |x|^{-k} = Σ_j sg(c_j) ∫_{cone j} |x|^{-k}`. -/
theorem real_signed (Q : QF) (hT : T.Ok) {k : ℕ} (hk : k ≤ 2) :
    (∫⁻ x in T.K, ENNReal.ofReal (Q.fk k x)) < ⊤ ∧
    (∫⁻ x in T.K, ENNReal.ofReal (Q.fk k x)).toReal =
      ∑ j, sg (T.al j) * (∫⁻ x in T.cone j, ENNReal.ofReal (Q.fk k x)).toReal := by
  set G : E3 → ℝ≥0∞ := fun x => ENNReal.ofReal (Q.fk k x)
  have hG : Measurable G := ENNReal.measurable_ofReal.comp (Q.measurable_fk k)
  have hid := lintegral_signed hT G hG
  have hF : ∀ j ∈ Finset.univ.filter (fun j => 0 < T.al j), ∫⁻ x in T.cone j, G x ≠ ⊤ := by
    intro j hj; simp at hj; exact ne_of_lt (cone_fin Q hT hk (ne_of_gt hj))
  have hN : ∀ j ∈ Finset.univ.filter (fun j => T.al j < 0), ∫⁻ x in T.cone j, G x ≠ ⊤ := by
    intro j hj; simp at hj; exact ne_of_lt (cone_fin Q hT hk (ne_of_lt hj))
  have hFt : ∑ j ∈ Finset.univ.filter (fun j => 0 < T.al j), ∫⁻ x in T.cone j, G x ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr hF
  have hKt : ∫⁻ x in T.K, G x ≠ ⊤ := by
    intro h; rw [h, top_add] at hid; exact hFt hid
  refine ⟨lt_top_iff_ne_top.mpr hKt, ?_⟩
  have hr := congrArg ENNReal.toReal hid
  rw [ENNReal.toReal_sum hF, ENNReal.toReal_add hKt (ENNReal.sum_ne_top.mpr hN), ENNReal.toReal_sum hN] at hr
  have e : ∑ j, sg (T.al j) * (∫⁻ x in T.cone j, G x).toReal =
      ∑ j ∈ Finset.univ.filter (fun j => 0 < T.al j), (∫⁻ x in T.cone j, G x).toReal -
      ∑ j ∈ Finset.univ.filter (fun j => T.al j < 0), (∫⁻ x in T.cone j, G x).toReal := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [sg]
    by_cases h1 : 0 < T.al j
    · have : ¬ T.al j < 0 := by linarith
      simp [h1, this]
    · by_cases h2 : T.al j < 0 <;> simp [h1, h2]
  rw [e]; linarith

end Tet

end GW.Endpoint.Coulomb
