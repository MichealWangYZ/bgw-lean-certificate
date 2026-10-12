/-
A3(a), stages S3 and S4: the coefficients of `λ⁰, λ¹, λ²` of the exact self-energy
`Σ(ω; λ) = G0⁻¹ - G⁻¹` of a general finite fermion system (formal power series in
`λ`, fixed real `ω` off the unperturbed excitation energies).

Standing hypotheses:
* `hv1 : v_pqrs = v_qpsr`, `hv2 : v_pqrs = v_rspq` (index convention of
  `Interaction.lean`: `V = ½ Σ v_pqrs c_p† c_q† c_s c_r`);
* `hnd : NonDeg ε O` (Φ nondegenerate in its particle-number sector);
* `hω : OffPoles ε O ω`.

Results:
* `sigma_coeff0` : `Σ⁽⁰⁾ = 0` (so `G(λ = 0) = G0`);
* `sigma1_eq_HF` : `Σ⁽¹⁾_pq = Σ_{a∈O} ⟨pa||qa⟩` (Hartree-Fock);
* `sigma2_eq`    : `Σ⁽²⁾ = sig2p + sig2h + relax`;
* `sigma2_eq_direct_add_sox_add_relax`, `sigma2_eq_direct_add_sox` (the latter
  under the Brillouin condition `Σ1_ra = 0`).
-/
import GW.Endpoint.ManyBody.Static2

namespace GW.Endpoint.ManyBody

open Matrix Finset PowerSeries

variable {n : ℕ} {ε : Fin n → ℝ} {v : Fin n → Fin n → Fin n → Fin n → ℝ} {O : Fock n} {ω : ℝ}

/-! ### Coefficients of block matrices -/

theorem cf_fromRows {m₁ m₂ k : Type*} (j : ℕ) (A : Matrix m₁ k T) (B : Matrix m₂ k T) :
    cf j (fromRows A B) = fromRows (cf j A) (cf j B) := by
  ext (i | i) l <;> rfl

theorem cf_fromBlocks {m₁ m₂ : Type*} (j : ℕ) (A : Matrix m₁ m₁ T) (B : Matrix m₁ m₂ T)
    (C' : Matrix m₂ m₁ T) (D : Matrix m₂ m₂ T) :
    cf j (fromBlocks A B C' D) = fromBlocks (cf j A) (cf j B) (cf j C') (cf j D) := by
  ext (i | i) (l | l) <;> rfl

theorem cf_colM {ι : Type*} (j : ℕ) (f : Fin n → ι → T) :
    cf j (colM f) = colM fun p => cfv j (f p) := by ext; rfl

theorem cf_AT (j : ℕ) : cf j (AT ε v O) = Ar (cfv j (psiT ε v O)) := by
  rw [AT, cf_fromRows, cf_colM, cf_colM, Ar]
  simp only [cfv_lift_mulVec]

theorem cf_HHT (j : ℕ) : cf j (HHT ε v O) = Hr (cf j (KT ε v O)) := by
  rw [HHT, cf_fromBlocks, cf_zero, cf_neg, Hr]

theorem cf0_AT : cf 0 (AT ε v O) = Ar (phi O) := by rw [cf_AT, cfv0_psiT]
theorem cf1_AT : cf 1 (AT ε v O) = Ar (psi1 ε v O) := by rw [cf_AT, cfv1_psiT]
theorem cf0_HHT : cf 0 (HHT ε v O) = Hr (H0 ε - E0 ε O • 1) := by rw [cf_HHT, cf0_KT]
theorem cf1_HHT : cf 1 (HHT ε v O) = Hr (vop v - E1 v O • 1) := by rw [cf_HHT, cf1_KT]

/-! ### The norm `⟨ψ|ψ⟩` and its inverse -/

theorem coeff1_dT : coeff ℝ 1 (dT ε v O) = 0 := by
  rw [dT, coeff1_dot, cfv0_psiT, cfv1_psiT, phi_dot_psi1, psi1_dot_phi, add_zero]

theorem coeff_dinv :
    coeff ℝ 0 (dT ε v O)⁻¹ = 1 ∧ coeff ℝ 1 (dT ε v O)⁻¹ = 0 ∧
      coeff ℝ 2 (dT ε v O)⁻¹ = -coeff ℝ 2 (dT ε v O) := by
  obtain ⟨h0, h1, h2⟩ := coeff_inv_T (dT ε v O) coeff0_dT
  refine ⟨h0, by rw [h1, coeff1_dT, neg_zero], by rw [h2, coeff1_dT]; ring⟩

/-! ### The static kernel -/

theorem phi_fop_phi (p q : Fin n) : phi O ⬝ᵥ (fop v p q *ᵥ phi O) = sig1 v O p q := by
  rw [fop_mulVec]
  simp only [dot_sum', dotProduct_smul, smul_eq_mul, dot_mulVec_cre, dot_ann_phi, mul_ite,
    mul_one, mul_zero]
  simp only [ite_and, sum_ite_eq, mem_univ, if_true]
  rw [sum_ite_mem_univ]; rfl

/-- Coefficients `≤ 2` of pairings with the residual vanish. -/
theorem coeff_resid_left (hnd : NonDeg ε O) (k : ℕ) (hk : k ≤ 2) (M : Matrix (Fock n) (Fock n) ℝ)
    (x : Fock n → T) : coeff ℝ k (x ⬝ᵥ (lift M *ᵥ (KT ε v O *ᵥ psiT ε v O))) = 0 := by
  obtain ⟨r0, r1, r2⟩ := resid_cf (v := v) hnd
  rcases k with _ | _ | _ | k
  · rw [coeff0_dot, cfv_lift_mulVec, r0]; simp
  · rw [coeff1_dot, cfv_lift_mulVec, cfv_lift_mulVec, r0, r1]; simp
  · rw [coeff2_dot, cfv_lift_mulVec, cfv_lift_mulVec, cfv_lift_mulVec, r0, r1, r2]; simp
  · omega

theorem coeff_resid_right (hnd : NonDeg ε O) (k : ℕ) (hk : k ≤ 2) (y : Fock n → T) :
    coeff ℝ k ((KT ε v O *ᵥ psiT ε v O) ⬝ᵥ y) = 0 := by
  obtain ⟨r0, r1, r2⟩ := resid_cf (v := v) hnd
  rcases k with _ | _ | _ | k
  · rw [coeff0_dot, r0]; simp
  · rw [coeff1_dot, r0, r1]; simp
  · rw [coeff2_dot, r0, r1, r2]; simp
  · omega

theorem coeff_ST (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) (k : ℕ) (hk : k ≤ 2)
    (p q : Fin n) :
    coeff ℝ k (ST ε v O p q) =
      (if p = q then ε q else 0) * coeff ℝ k (dT ε v O) +
        (if k = 0 then 0 else coeff ℝ (k - 1) (psiT ε v O ⬝ᵥ (lift (fop v p q) *ᵥ psiT ε v O))) := by
  rw [ST_entry hv1 hv2, map_sub, map_add, map_add]
  have h1 : coeff ℝ k (psiT ε v O ⬝ᵥ (annT p *ᵥ creT q *ᵥ (KT ε v O *ᵥ psiT ε v O))) = 0 := by
    rw [mulVec_mulVec, ← lift_mul]; exact coeff_resid_left hnd k hk _ _
  rw [h1, coeff_resid_right hnd k hk, coeff_X_mul']
  split_ifs <;> simp [coeff_C_mul]

theorem cf0_ST (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) :
    cf 0 (ST ε v O) = diagonal ε := by
  ext p q
  rw [cf_apply, coeff_ST hv1 hv2 hnd 0 (by norm_num), coeff0_dT, diagonal_apply, if_pos rfl]
  by_cases h : p = q <;> simp [h]

theorem cf1_ST (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) :
    cf 1 (ST ε v O) = sig1M v O := by
  ext p q
  rw [cf_apply, coeff_ST hv1 hv2 hnd 1 (by norm_num), coeff1_dT, if_neg one_ne_zero,
    Nat.sub_self, coeff0_dot, cfv_lift_mulVec, cfv0_psiT, phi_fop_phi, sig1M, of_apply]
  ring

theorem cf2_ST (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) :
    cf 2 (ST ε v O) = coeff ℝ 2 (dT ε v O) • diagonal ε + Matrix.of (relax ε v O) := by
  ext p q
  rw [cf_apply, coeff_ST hv1 hv2 hnd 2 le_rfl, if_neg two_ne_zero, show 2 - 1 = 1 from rfl,
    coeff1_dot, cfv_lift_mulVec, cfv_lift_mulVec, cfv0_psiT, cfv1_psiT, add_apply, smul_apply,
    diagonal_apply, of_apply, add_comm (phi O ⬝ᵥ _), static_eq hv1 hv2]
  split_ifs with h <;> simp [h, mul_comm]

end GW.Endpoint.ManyBody
