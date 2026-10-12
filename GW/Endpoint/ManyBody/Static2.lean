/-
A3(a): the static part `S = ATᵀ HHT AT` of the Feshbach kernel, entry by entry:

  S_pq = δ_pq ε_q ⟨ψ|ψ⟩ + λ ⟨ψ|F_pq|ψ⟩ + ⟨ψ|c_p c_q† r⟩ - ⟨r|c_q† c_p ψ⟩,   r = (H - E) ψ

(`S_entry`), from `[H0, c_q†] = ε_q c_q†`, `[V, c_q†] = ccre`, `{c_p, ccre} = F_pq`
and the symmetry of `H - E`. Since `r = O(λ³)`, only the first two terms matter
through order `λ²`.
-/
import GW.Endpoint.ManyBody.Doubled

namespace GW.Endpoint.ManyBody

open Matrix Finset PowerSeries

variable {n : ℕ} {ε : Fin n → ℝ} {v : Fin n → Fin n → Fin n → Fin n → ℝ} {O : Fock n} {ω : ℝ}

/-- A ring identity for the static kernel. `e`, `x` are central. -/
theorem static_ring {R : Type*} [Ring R] (a c K e x f F d : R)
    (hK : K * c = c * K + e * c + x * f) (he : ∀ y, e * y = y * e) (hx : ∀ y, x * y = y * x)
    (hac : a * c + c * a = d) (hF : a * f + f * a = F) :
    a * K * c - c * K * a = a * c * K - K * c * a + e * d + x * F := by
  have h1 : c * K * a = K * c * a - e * c * a - x * f * a := by
    rw [hK]; noncomm_ring
  rw [h1, mul_assoc a K c, hK, ← hac, ← hF]
  have h2 : a * (e * c) = e * (a * c) := by rw [← mul_assoc, ← he a, mul_assoc]
  have h3 : a * (x * f) = x * (a * f) := by rw [← mul_assoc, ← hx a, mul_assoc]
  have h4 : e * c * a = e * (c * a) := mul_assoc _ _ _
  have h5 : x * f * a = x * (f * a) := mul_assoc _ _ _
  rw [mul_add, mul_add, h2, h3, h4, h5]; noncomm_ring

theorem lift_H0_mul_cre (q : Fin n) :
    lift (H0 ε) * creT q = creT q * lift (H0 ε) + (C ℝ (ε q) • (1 : Matrix (Fock n) (Fock n) T)) *
      creT q := by
  rw [← lift_mul, H0_mul_cre, lift_add, lift_mul, lift_smul, Matrix.smul_mul, Matrix.one_mul]

theorem lift_vop_mul_cre (q : Fin n) :
    lift (vop v) * creT q = creT q * lift (vop v) + lift (ccre v q) := by
  rw [← vop_mul_cre, lift_sub, lift_mul, lift_mul]; abel

theorem KT_mul_cre (q : Fin n) :
    KT ε v O * creT q = creT q * KT ε v O + (C ℝ (ε q) • (1 : Matrix (Fock n) (Fock n) T)) * creT q +
      ((X : T) • (1 : Matrix (Fock n) (Fock n) T)) * lift (ccre v q) := by
  simp only [KT, HT, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, lift_H0_mul_cre,
    lift_vop_mul_cre, smul_add]
  abel

theorem scalar_central {ι : Type*} [Fintype ι] [DecidableEq ι] (c : T) (y : Matrix ι ι T) :
    (c • (1 : Matrix ι ι T)) * y = y * (c • 1) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem lift_ann_ccre (hv1 : ∀ p q r s, v p q r s = v q p s r) (p q : Fin n) :
    annT p * lift (ccre v q) + lift (ccre v q) * annT p = lift (fop v p q) := by
  rw [← lift_mul, ← lift_mul, ← lift_add, ann_ccre v hv1]

/-- The operator form of the static kernel. -/
theorem static_op (hv1 : ∀ p q r s, v p q r s = v q p s r) (p q : Fin n) :
    annT p * KT ε v O * creT q - creT q * KT ε v O * annT p =
      annT p * creT q * KT ε v O - KT ε v O * creT q * annT p +
        (C ℝ (ε q) • (1 : Matrix (Fock n) (Fock n) T)) * (if p = q then 1 else 0) +
          ((X : T) • (1 : Matrix (Fock n) (Fock n) T)) * lift (fop v p q) :=
  static_ring _ _ _ _ _ _ _ _ (KT_mul_cre q) (scalar_central _) (scalar_central _)
    (lift_ann_cre_add p q) (lift_ann_ccre hv1 p q)

theorem mulVec_dot_T {ι : Type*} [Fintype ι] (M : Matrix ι ι T) (x y : ι → T) :
    (M *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Mᵀ *ᵥ y) := by
  rw [dot_mulVec_T, transpose_transpose]

/-- `S = ATᵀ HHT AT`. -/
noncomputable def ST (ε : Fin n → ℝ) (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n) :
    Matrix (Fin n) (Fin n) T := (AT ε v O)ᵀ * HHT ε v O * AT ε v O

theorem ST_entry (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (p q : Fin n) :
    ST ε v O p q =
      (if p = q then C ℝ (ε q) else 0) * dT ε v O +
        X * (psiT ε v O ⬝ᵥ (lift (fop v p q) *ᵥ psiT ε v O)) +
        psiT ε v O ⬝ᵥ (annT p *ᵥ creT q *ᵥ (KT ε v O *ᵥ psiT ε v O)) -
        (KT ε v O *ᵥ psiT ε v O) ⬝ᵥ (creT q *ᵥ annT p *ᵥ psiT ε v O) := by
  set ψ := psiT ε v O
  set K := KT ε v O
  have hS : ST ε v O p q = (creT p *ᵥ ψ) ⬝ᵥ (K *ᵥ creT q *ᵥ ψ) - (annT p *ᵥ ψ) ⬝ᵥ (K *ᵥ annT q *ᵥ ψ) := by
    rw [ST, AT, HHT, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_colM, mul_colM, colM_transpose_mul_colM,
      colM_transpose_mul_colM]
    simp only [add_apply, of_apply, neg_mulVec, dotProduct_neg, sub_eq_add_neg]; rfl
  have hK : Kᵀ = K := KT_transpose hv2
  have e1 : (creT p *ᵥ ψ) ⬝ᵥ (K *ᵥ creT q *ᵥ ψ) = ψ ⬝ᵥ ((annT p * K * creT q) *ᵥ ψ) := by
    rw [mulVec_dot_T, creT_transpose, ← mulVec_mulVec, ← mulVec_mulVec]
  have e2 : (annT p *ᵥ ψ) ⬝ᵥ (K *ᵥ annT q *ᵥ ψ) = ψ ⬝ᵥ ((creT q * K * annT p) *ᵥ ψ) := by
    rw [mulVec_dot_T, annT_transpose, mulVec_mulVec, mulVec_mulVec, dot_mulVec_T,
      dotProduct_comm, show (creT p * K * annT q)ᵀ = creT q * K * annT p by
      rw [transpose_mul, transpose_mul, annT_transpose, creT_transpose, hK, Matrix.mul_assoc]]
  rw [hS, e1, e2, ← dotProduct_sub, ← sub_mulVec, static_op hv1]
  simp only [add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub, ← mulVec_mulVec]
  rw [dot_mulVec_T K, hK]
  have h3 : ψ ⬝ᵥ ((C ℝ (ε q) • (1 : Matrix (Fock n) (Fock n) T)) *ᵥ
      (if p = q then (1 : Matrix (Fock n) (Fock n) T) else 0) *ᵥ ψ) =
      (if p = q then C ℝ (ε q) else 0) * dT ε v O := by
    split_ifs <;> simp [dT, ψ, smul_mulVec_assoc, dotProduct_smul]
  have h4 : ψ ⬝ᵥ (((X : T) • (1 : Matrix (Fock n) (Fock n) T)) *ᵥ lift (fop v p q) *ᵥ ψ) =
      X * (ψ ⬝ᵥ (lift (fop v p q) *ᵥ ψ)) := by
    simp [smul_mulVec_assoc, dotProduct_smul]
  rw [h3, h4]
  ring

end GW.Endpoint.ManyBody
