/-
A3(a): the exact Green's function in Feshbach form.

On the doubled space `Kap n = Fock n ⊕ Fock n` (particle side ⊕ hole side):

* `HHT = (H - E) ⊕ -(H - E)`,
* `AT` has column `p` equal to `(c_p† ψ, c_p ψ)`,
* CAR gives `ATᵀ AT = ⟨ψ|ψ⟩ • 1` (`AT_gram`),
* `greenT = ⟨ψ|ψ⟩⁻¹ • ATᵀ (ω - HHT)⁻¹ AT` (`greenT_eq`),

so the generic `feshbach` identity applies (`greenT_inv`).
-/
import GW.Endpoint.ManyBody.Exact

namespace GW.Endpoint.ManyBody

open Matrix Finset PowerSeries

variable {n : ℕ} (ε : Fin n → ℝ) (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n) (ω : ℝ)

abbrev Kap (n : ℕ) := Fock n ⊕ Fock n

noncomputable def HHT : Matrix (Kap n) (Kap n) T := fromBlocks (KT ε v O) 0 0 (-KT ε v O)

noncomputable def AT : Matrix (Kap n) (Fin n) T :=
  fromRows (colM fun p => creT p *ᵥ psiT ε v O) (colM fun p => annT p *ᵥ psiT ε v O)

noncomputable def QT : Matrix (Kap n) (Kap n) T :=
  1 - (dT ε v O)⁻¹ • (AT ε v O * (AT ε v O)ᵀ)

noncomputable def NT : Matrix (Kap n) (Kap n) T :=
  C ℝ ω • 1 - QT ε v O * HHT ε v O * QT ε v O

noncomputable def KKT : Matrix (Fin n) (Fin n) T :=
  (AT ε v O)ᵀ * HHT ε v O * AT ε v O +
    (AT ε v O)ᵀ * HHT ε v O * (NT ε v O ω)⁻¹ * (QT ε v O * HHT ε v O * AT ε v O)

/-- The hypothesis on `ω`: off every unperturbed excitation energy of the Fock space
(on both the addition and the removal side). A co-finite condition; it implies
`ω ≠ 0` and `ω ≠ ε_p` for every `p`. -/
def OffPoles : Prop :=
  ∀ S : Fock n, ω - (energy ε S - energy ε O) ≠ 0 ∧ ω + (energy ε S - energy ε O) ≠ 0

variable {ε v O ω}

/-! ### Symmetry -/

theorem H0_transpose : (H0 ε)ᵀ = H0 ε := by rw [H0_eq_diagonal, diagonal_transpose]

theorem KT_transpose (hv2 : ∀ p q r s, v p q r s = v r s p q) : (KT ε v O)ᵀ = KT ε v O := by
  simp only [KT, HT, transpose_sub, transpose_add, transpose_smul, transpose_one,
    ← lift_transpose, H0_transpose, vop_transpose v hv2]

/-! ### Invertibility of `ω ∓ (H - E)` -/

theorem cf0_Cω_smul {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cf 0 (C ℝ ω • (1 : Matrix ι ι T)) = ω • 1 := by
  rw [cf0_smul, cf_one, if_pos rfl, coeff_C]; simp

theorem cf_Cω_smul_succ {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    cf (k + 1) (C ℝ ω • (1 : Matrix ι ι T)) = 0 := by
  ext i j; by_cases h : i = j <;> simp [cf, one_apply, h, coeff_C]

theorem cf0_MpT : cf 0 (MpT ε v O ω) = diagonal fun S => ω - (energy ε S - energy ε O) := by
  rw [MpT, cf_sub, cf0_Cω_smul, cf0_KT, H0_eq_diagonal, smul_one_eq_diagonal, smul_one_eq_diagonal,
    diagonal_sub, diagonal_sub]; rfl

theorem cf0_MmT : cf 0 (MmT ε v O ω) = diagonal fun S => ω + (energy ε S - energy ε O) := by
  rw [MmT, cf_add, cf0_Cω_smul, cf0_KT, H0_eq_diagonal, smul_one_eq_diagonal, smul_one_eq_diagonal,
    diagonal_sub, diagonal_add]; rfl

theorem diag_inv_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (hf : ∀ i, f i ≠ 0) :
    diagonal (fun i => (f i)⁻¹) * diagonal f = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext fun i => inv_mul_cancel₀ (hf i))

theorem MpT_det (hω : OffPoles ε O ω) : IsUnit (MpT ε v O ω).det :=
  isUnit_det_of_cf0 _ _ (by rw [cf0_MpT]; exact diag_inv_mul _ fun S => (hω S).1)

theorem MmT_det (hω : OffPoles ε O ω) : IsUnit (MmT ε v O ω).det :=
  isUnit_det_of_cf0 _ _ (by rw [cf0_MmT]; exact diag_inv_mul _ fun S => (hω S).2)

theorem MmT_inv_transpose (hv2 : ∀ p q r s, v p q r s = v r s p q) :
    ((MmT ε v O ω)⁻¹)ᵀ = (MmT ε v O ω)⁻¹ := by
  rw [transpose_nonsing_inv, MmT, transpose_add, transpose_smul, transpose_one, KT_transpose hv2]

/-! ### Gram matrix of `AT` (CAR) -/

theorem lift_ann_cre_add (p q : Fin n) :
    annT p * creT q + creT q * annT p = if p = q then 1 else 0 := by
  rw [← lift_mul, ← lift_mul, ← lift_add, ann_mul_cre_add]
  split_ifs
  · exact lift_one
  · exact lift_zero

theorem dot_mulVec_T {ι : Type*} [Fintype ι] (M : Matrix ι ι T) (x y : ι → T) :
    x ⬝ᵥ (M *ᵥ y) = (Mᵀ *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, mulVec_transpose]

theorem creT_transpose (p : Fin n) : (creT p)ᵀ = annT p := by
  rw [← lift_transpose, cre_transpose]

theorem annT_transpose (p : Fin n) : (annT p)ᵀ = creT p := by
  rw [← lift_transpose, ann_transpose]

theorem AT_gram : (AT ε v O)ᵀ * AT ε v O = dT ε v O • (1 : Matrix (Fin n) (Fin n) T) := by
  rw [AT, transpose_fromRows, fromCols_mul_fromRows, colM_transpose_mul_colM,
    colM_transpose_mul_colM]
  refine Matrix.ext fun p q => ?_
  simp only [add_apply, of_apply, smul_apply, smul_eq_mul]
  set ψ := psiT ε v O
  have e1 : (creT p *ᵥ ψ) ⬝ᵥ (creT q *ᵥ ψ) = ψ ⬝ᵥ ((annT p * creT q) *ᵥ ψ) := by
    rw [dotProduct_comm, dot_mulVec_T, creT_transpose, dotProduct_comm, mulVec_mulVec]
  have e2 : (annT p *ᵥ ψ) ⬝ᵥ (annT q *ᵥ ψ) = ψ ⬝ᵥ ((creT q * annT p) *ᵥ ψ) := by
    rw [dot_mulVec_T, annT_transpose, mulVec_mulVec, dotProduct_comm]
  rw [e1, e2, ← dotProduct_add, ← add_mulVec, lift_ann_cre_add, dT]
  split_ifs with h
  · subst h; simp; rfl
  · simp [h]

/-! ### The resolvent on the doubled space -/

variable (ε v O ω) in
/-- `(ω - HHT)⁻¹ AT`, block by block. -/
noncomputable def XT : Matrix (Kap n) (Fin n) T :=
  fromBlocks (MpT ε v O ω)⁻¹ 0 0 (MmT ε v O ω)⁻¹ * AT ε v O

theorem omega_sub_HHT :
    C ℝ ω • (1 : Matrix (Kap n) (Kap n) T) - HHT ε v O = fromBlocks (MpT ε v O ω) 0 0 (MmT ε v O ω) := by
  rw [← fromBlocks_one, fromBlocks_smul, HHT]
  ext (i | i) (j | j) <;> simp [MpT, MmT, sub_eq_add_neg]

theorem resolvent_XT (hω : OffPoles ε O ω) :
    (C ℝ ω • (1 : Matrix (Kap n) (Kap n) T) - HHT ε v O) * XT ε v O ω = AT ε v O := by
  rw [omega_sub_HHT, XT, ← Matrix.mul_assoc, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    mul_nonsing_inv _ (MpT_det hω), mul_nonsing_inv _ (MmT_det hω), fromBlocks_one, Matrix.one_mul]

theorem greenT_eq (hv2 : ∀ p q r s, v p q r s = v r s p q) :
    greenT ε v O ω = (dT ε v O)⁻¹ • ((AT ε v O)ᵀ * XT ε v O ω) := by
  rw [XT, AT, fromBlocks_mul_fromRows, transpose_fromRows, fromCols_mul_fromRows]
  rw [Matrix.zero_mul, Matrix.zero_mul, add_zero, zero_add, mul_colM, mul_colM,
    colM_transpose_mul_colM, colM_transpose_mul_colM]
  refine Matrix.ext fun p q => ?_
  simp only [greenT, of_apply, smul_apply, add_apply, smul_eq_mul]
  rw [mul_comm]
  congr 1
  set ψ := psiT ε v O
  set Mp := (MpT ε v O ω)⁻¹
  set Mm := (MmT ε v O ω)⁻¹
  have e1 : ψ ⬝ᵥ ((annT p * Mp * creT q) *ᵥ ψ) = (creT p *ᵥ ψ) ⬝ᵥ (Mp *ᵥ creT q *ᵥ ψ) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dot_mulVec_T, annT_transpose]
  have e2 : ψ ⬝ᵥ ((creT q * Mm * annT p) *ᵥ ψ) = (annT p *ᵥ ψ) ⬝ᵥ (Mm *ᵥ annT q *ᵥ ψ) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dot_mulVec_T (creT q), creT_transpose,
      dot_mulVec_T Mm, MmT_inv_transpose hv2, dotProduct_comm]
  rw [e1, e2]

/-! ### Inverting `G` -/

theorem coeff0_dT : coeff ℝ 0 (dT ε v O) = 1 := by
  rw [dT, coeff0_dot, cfv0_psiT, phi_dot_phi]

theorem dT_inv_mul : (dT ε v O)⁻¹ * dT ε v O = 1 := by
  rw [mul_comm]; apply PowerSeries.mul_inv_cancel
  rw [← coeff_zero_eq_constantCoeff_apply, coeff0_dT]; norm_num

/-- `G⁻¹ = ω - ⟨ψ|ψ⟩⁻¹ K` (Feshbach). -/
theorem greenT_inv (hv2 : ∀ p q r s, v p q r s = v r s p q) (hω : OffPoles ε O ω)
    (hN : IsUnit (NT ε v O ω).det) :
    (greenT ε v O ω)⁻¹ = C ℝ ω • 1 - (dT ε v O)⁻¹ • KKT ε v O ω := by
  apply inv_eq_left_inv
  rw [greenT_eq hv2]
  exact feshbach (HHT ε v O) (AT ε v O) (dT ε v O) (dT ε v O)⁻¹ (C ℝ ω) dT_inv_mul AT_gram
    (XT ε v O ω) (resolvent_XT hω) (NT ε v O ω)⁻¹ (nonsing_inv_mul _ hN)

theorem energy_insert {p : Fin n} (hp : p ∉ O) : energy ε (insert p O) = ε p + energy ε O := by
  simp [energy, sum_insert hp]

theorem energy_erase {p : Fin n} (hp : p ∈ O) : energy ε O = ε p + energy ε (O.erase p) := by
  simp [energy, add_sum_erase _ _ hp]

theorem omega_ne_eps (hω : OffPoles ε O ω) (p : Fin n) : ω - ε p ≠ 0 := by
  by_cases hp : p ∈ O
  · have := (hω (O.erase p)).2
    rwa [energy_erase (ε := ε) hp, show ω + (energy ε (O.erase p) - (ε p + energy ε (O.erase p))) =
      ω - ε p by ring] at this
  · have := (hω (insert p O)).1
    rwa [energy_insert hp, show ω - (ε p + energy ε O - energy ε O) = ω - ε p by ring] at this

theorem green0_inv (hω : OffPoles ε O ω) :
    (green0 ε ω)⁻¹ = diagonal fun p => C ℝ (ω - ε p) := by
  apply inv_eq_left_inv
  rw [green0, diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext fun p => by
    rw [← map_mul, mul_inv_cancel₀ (omega_ne_eps hω p), map_one])

/-- The exact self-energy in Feshbach form. -/
theorem sigmaT_eq (hv2 : ∀ p q r s, v p q r s = v r s p q) (hω : OffPoles ε O ω)
    (hN : IsUnit (NT ε v O ω).det) :
    sigmaT ε v O ω = (diagonal fun p => C ℝ (ω - ε p)) - C ℝ ω • 1 +
      (dT ε v O)⁻¹ • KKT ε v O ω := by
  rw [sigmaT, green0_inv hω, greenT_inv hv2 hω hN]; abel

end GW.Endpoint.ManyBody
