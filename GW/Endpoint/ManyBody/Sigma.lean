/-
A3(a), stages S3/S4: the main theorems on the exact self-energy (see `SelfEnergy.lean`
for the hypotheses and the static kernel).
-/
import GW.Endpoint.ManyBody.SelfEnergy

namespace GW.Endpoint.ManyBody

open Matrix Finset PowerSeries

variable {n : ℕ} {ε : Fin n → ℝ} {v : Fin n → Fin n → Fin n → Fin n → ℝ} {O : Fock n} {ω : ℝ}

/-! ### A generic symmetrization of the dynamic kernel -/

theorem kernel_symm {R : Type*} [CommRing R] {κ m : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype m] (𝓗 : Matrix κ κ R) (A : Matrix κ m R) (Q Ninv : Matrix κ κ R)
    (h𝓗 : 𝓗ᵀ = 𝓗) (hQ : Qᵀ = Q) (hQQ : Q * Q = Q) (hNQ : Ninv * Q = Q * Ninv) :
    Aᵀ * 𝓗 * Ninv * (Q * 𝓗 * A) = (Q * 𝓗 * A)ᵀ * Ninv * (Q * 𝓗 * A) := by
  have e : Ninv * Q = Q * Ninv * Q := by rw [Matrix.mul_assoc, hNQ, ← Matrix.mul_assoc, hQQ]
  rw [transpose_mul, transpose_mul, h𝓗, hQ]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Ninv Q, e]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Q Q, hQQ]

/-! ### Projector facts for `QT` and `NT` -/

theorem QT_transpose : (QT ε v O)ᵀ = QT ε v O := by
  rw [QT, transpose_sub, transpose_one, transpose_smul, transpose_mul, transpose_transpose]

theorem QT_idem : QT ε v O * QT ε v O = QT ε v O := by
  set A := AT ε v O
  set di := (dT ε v O)⁻¹
  have hPP : di • (A * Aᵀ) * (di • (A * Aᵀ)) = di • (A * Aᵀ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ,
      AT_gram, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_smul, mul_assoc, dT_inv_mul,
      mul_one]
  rw [QT, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, sub_zero]

theorem NT_QT_comm : NT ε v O ω * QT ε v O = QT ε v O * NT ε v O ω := by
  rw [NT, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_assoc _ (QT ε v O), QT_idem, ← Matrix.mul_assoc (QT ε v O),
    ← Matrix.mul_assoc (QT ε v O), QT_idem]

/-! ### The constant term of `NT` -/

theorem cf0_QT : cf 0 (QT ε v O) = 1 - Ar (phi O) * (Ar (phi O))ᵀ := by
  rw [QT, cf_sub, cf_one, if_pos rfl, cf0_smul, coeff_dinv.1, one_smul, cf0_mul, cf_transpose,
    cf0_AT]

theorem cf0_NT : cf 0 (NT ε v O ω) = N0 ε O ω := by
  rw [NT, cf_sub, cf0_Cω_smul, cf0_mul, cf0_mul, cf0_QT, cf0_HHT, N0]

theorem NT_det (hω : OffPoles ε O ω) : IsUnit (NT ε v O ω).det :=
  isUnit_det_of_cf0 _ _ (by rw [cf0_NT]; exact L0_mul_N0 hω)

theorem cf0_NT_inv (hω : OffPoles ε O ω) : cf 0 (NT ε v O ω)⁻¹ = L0 ε O ω :=
  cf0_inv _ _ (by rw [cf0_NT]; exact L0_mul_N0 hω)

theorem NT_inv_QT (hω : OffPoles ε O ω) :
    (NT ε v O ω)⁻¹ * QT ε v O = QT ε v O * (NT ε v O ω)⁻¹ := by
  have hu := NT_det (v := v) hω
  calc (NT ε v O ω)⁻¹ * QT ε v O
      = (NT ε v O ω)⁻¹ * QT ε v O * (NT ε v O ω * (NT ε v O ω)⁻¹) := by
        rw [mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = (NT ε v O ω)⁻¹ * (NT ε v O ω * QT ε v O) * (NT ε v O ω)⁻¹ := by
        rw [NT_QT_comm]; simp only [Matrix.mul_assoc]
    _ = QT ε v O * (NT ε v O ω)⁻¹ := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]

/-! ### The dynamic kernel `J = Q 𝓗 A` -/

/-- `J = Q 𝓗 A`. -/
noncomputable def JT (ε : Fin n → ℝ) (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n) :
    Matrix (Kap n) (Fin n) T := QT ε v O * HHT ε v O * AT ε v O

theorem JT_eq : JT ε v O = HHT ε v O * AT ε v O - (dT ε v O)⁻¹ • (AT ε v O * ST ε v O) := by
  rw [JT, QT, ST, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul]
  simp only [Matrix.mul_assoc]

theorem cf0_JT (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) : cf 0 (JT ε v O) = 0 := by
  rw [JT_eq, cf_sub, cf0_smul, coeff_dinv.1, one_smul, cf0_mul, cf0_mul, cf0_HHT, cf0_AT,
    cf0_ST hv1 hv2 hnd, H0r_A0, sub_self]

theorem cf1_JT (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) : cf 1 (JT ε v O) = Y2 v O := by
  rw [JT_eq, cf_sub, cf1_smul, coeff_dinv.1, coeff_dinv.2.1, one_smul, zero_smul, add_zero,
    cf1_mul, cf1_mul, cf0_HHT, cf1_HHT, cf0_AT, cf1_AT, cf0_ST hv1 hv2 hnd,
    cf1_ST hv1 hv2 hnd]
  have h := first_order_cols (ε := ε) hnd hv1 hv2
  rw [← sub_eq_zero] at h ⊢
  rw [← h]; abel

/-! ### The kernel `K = S + Jᵀ N⁻¹ J` -/

theorem KKT_eq (hv2 : ∀ p q r s, v p q r s = v r s p q) (hω : OffPoles ε O ω) :
    KKT ε v O ω = ST ε v O + (JT ε v O)ᵀ * (NT ε v O ω)⁻¹ * JT ε v O := by
  rw [KKT, ST, JT, kernel_symm _ _ _ _
    (by rw [HHT, fromBlocks_transpose, transpose_neg, KT_transpose hv2, transpose_zero])
    QT_transpose QT_idem (NT_inv_QT hω)]

theorem cf_dyn (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) (hω : OffPoles ε O ω) :
    cf 0 ((JT ε v O)ᵀ * (NT ε v O ω)⁻¹ * JT ε v O) = 0 ∧
      cf 1 ((JT ε v O)ᵀ * (NT ε v O ω)⁻¹ * JT ε v O) = 0 ∧
      cf 2 ((JT ε v O)ᵀ * (NT ε v O ω)⁻¹ * JT ε v O) =
        Matrix.of fun p q => sig2p ε v O ω p q + sig2h ε v O ω p q := by
  have h0 := cf0_JT hv1 hv2 hnd
  have h1 := cf1_JT hv1 hv2 hnd
  refine ⟨?_, ?_, ?_⟩
  · rw [cf0_mul, h0, Matrix.mul_zero]
  · simp only [cf1_mul, cf0_mul, cf_transpose, h0, transpose_zero, Matrix.zero_mul,
      Matrix.mul_zero, add_zero]
  · simp only [cf2_mul, cf1_mul, cf0_mul, cf_transpose, h0, h1, cf0_NT_inv hω, transpose_zero,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [Matrix.mul_assoc, L0_Y2, ← Matrix.mul_assoc, Y2_Dk_Y2 hv1 hv2]

/-! ### The main theorems -/

theorem sigma_cf (hv2 : ∀ p q r s, v p q r s = v r s p q) (hω : OffPoles ε O ω) (k : ℕ) :
    cf k (sigmaT ε v O ω) =
      cf k (diagonal fun p => C ℝ (ω - ε p)) - cf k (C ℝ ω • (1 : Matrix (Fin n) (Fin n) T)) +
        cf k ((dT ε v O)⁻¹ • KKT ε v O ω) := by
  rw [sigmaT_eq hv2 hω (NT_det hω), cf_add, cf_sub]

theorem cf_diag_C (k : ℕ) (f : Fin n → ℝ) :
    cf k (diagonal fun p => C ℝ (f p)) = if k = 0 then diagonal f else 0 := by
  ext p q; by_cases h : p = q <;> rcases k with _ | k <;> simp [cf, diagonal_apply, h, coeff_C]

/-- **Order 0.** `Σ⁽⁰⁾ = 0`: the unperturbed Green's function is `G0`. -/
theorem sigma_coeff0 (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) (hω : OffPoles ε O ω) :
    cf 0 (sigmaT ε v O ω) = 0 := by
  rw [sigma_cf hv2 hω 0, cf_diag_C, if_pos rfl, cf0_Cω_smul, cf0_smul,
    coeff_dinv.1, one_smul, KKT_eq hv2 hω, cf_add, cf0_ST hv1 hv2 hnd,
    (cf_dyn hv1 hv2 hnd hω).1, add_zero, smul_one_eq_diagonal, diagonal_sub, diagonal_add]
  ext p q; by_cases h : p = q <;> simp [diagonal_apply, h]

/-- **S3: first order is Hartree-Fock.** `Σ⁽¹⁾_pq = Σ_{a∈O} ⟨pa||qa⟩`. -/
theorem sigma1_eq_HF (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) (hω : OffPoles ε O ω) :
    cf 1 (sigmaT ε v O ω) = Matrix.of fun p q => ∑ a ∈ O, asym v p a q a := by
  rw [sigma_cf hv2 hω 1, cf_diag_C, if_neg one_ne_zero,
    cf_Cω_smul_succ 0, cf1_smul, coeff_dinv.1, coeff_dinv.2.1, one_smul, zero_smul, add_zero,
    KKT_eq hv2 hω, cf_add, cf1_ST hv1 hv2 hnd, (cf_dyn hv1 hv2 hnd hω).2.1, add_zero, sub_zero,
    zero_add]
  rfl

/-- **S4: second order.** `Σ⁽²⁾ = (2p1h) + (2h1p) + (density relaxation)`. -/
theorem sigma2_eq (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) (hω : OffPoles ε O ω) :
    cf 2 (sigmaT ε v O ω) =
      Matrix.of fun p q => sig2p ε v O ω p q + sig2h ε v O ω p q + relax ε v O p q := by
  rw [sigma_cf hv2 hω 2, cf_diag_C, if_neg two_ne_zero,
    cf_Cω_smul_succ 1, cf2_smul, coeff_dinv.1, coeff_dinv.2.1, coeff_dinv.2.2, one_smul,
    zero_smul, add_zero, KKT_eq hv2 hω, cf_add, cf_add, cf2_ST hv1 hv2 hnd,
    (cf_dyn hv1 hv2 hnd hω).2.2, cf0_ST hv1 hv2 hnd, (cf_dyn hv1 hv2 hnd hω).1, add_zero,
    sub_zero, zero_add]
  ext p q
  simp only [add_apply, smul_apply, of_apply, smul_eq_mul, neg_mul]
  ring

end GW.Endpoint.ManyBody
