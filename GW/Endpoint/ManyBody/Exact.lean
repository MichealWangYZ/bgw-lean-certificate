/-
A3(a), stage S2: the exact one-particle Green's function of `H(λ) = H0 + λ V` as a
formal power series in `λ`, at a fixed real `ω`, and its Feshbach form.

Definitions (all over `T = ℝ⟦λ⟧`, `λ = X`):

* `psiT = Φ + λ ψ1 + λ² ψ2` and `ET = E0 + λ E1 + λ² E2` (Rayleigh-Schrödinger,
  `Perturb.lean`); `HT = H0 + λ V`, `KT = HT - ET`;
  the eigenvalue equation holds modulo `λ³` (`resid_cf0/1/2`);
* `greenT p q = (⟨ψ| c_p (ω - (H - E))⁻¹ c_q† |ψ⟩ + ⟨ψ| c_q† (ω + (H - E))⁻¹ c_p |ψ⟩) / ⟨ψ|ψ⟩`,
  with the matrix inverses and `⟨ψ|ψ⟩⁻¹` taken in `T` (the literal definition of the
  task statement);
* `green0 = diag (ω - ε_p)⁻¹` and `sigmaT = green0⁻¹ - greenT⁻¹`.

Only coefficients `0, 1, 2` in `λ` of `sigmaT` are asserted anywhere. Replacing `psiT`,
`ET` by any other series with the same coefficients up to `λ²` changes nothing below
`λ³`; the truncation at `λ²` is therefore not an approximation of the statements made.
-/
import GW.Endpoint.ManyBody.Static
import GW.Endpoint.ManyBody.Series
import GW.Endpoint.ManyBody.Feshbach
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace GW.Endpoint.ManyBody

open Matrix Finset PowerSeries

/-! ### Column matrices -/

section Cols
variable {R : Type*} [CommRing R] {ι m : Type*}

/-- The matrix whose column `p` is the vector `f p`. -/
def colM {R : Type*} {ι m : Type*} (f : m → ι → R) : Matrix ι m R := Matrix.of fun S p => f p S

omit [CommRing R] in
theorem colM_apply (f : m → ι → R) (S : ι) (p : m) : colM f S p = f p S := rfl

theorem mul_colM [Fintype ι] (M : Matrix ι ι R) (f : m → ι → R) : M * colM f = colM fun p => M *ᵥ f p := by
  ext S p; simp [colM, mul_apply, mulVec, dotProduct]

theorem colM_transpose_mul_colM [Fintype ι] (f g : m → ι → R) :
    (colM f)ᵀ * colM g = Matrix.of fun p q => f p ⬝ᵥ g q := by
  ext p q; simp [colM, mul_apply, dotProduct]

end Cols

variable {n : ℕ} (ε : Fin n → ℝ) (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n) (ω : ℝ)

/-! ### The lifted operators -/

/-- Lifted operators. -/
noncomputable abbrev annT (p : Fin n) : Matrix (Fock n) (Fock n) T := lift (ann p)
noncomputable abbrev creT (p : Fin n) : Matrix (Fock n) (Fock n) T := lift (cre p)

theorem lift_mul {m' : Type*} [Fintype m'] {l' o' : Type*} (M : Matrix l' m' ℝ)
    (N : Matrix m' o' ℝ) : lift (M * N) = lift M * lift N := by
  simp [lift, Matrix.map_mul]

theorem lift_add {l' o' : Type*} (M N : Matrix l' o' ℝ) : lift (M + N) = lift M + lift N := by
  ext; simp [lift]

theorem lift_sub {l' o' : Type*} (M N : Matrix l' o' ℝ) : lift (M - N) = lift M - lift N := by
  ext; simp [lift]

theorem lift_smul {l' o' : Type*} (c : ℝ) (M : Matrix l' o' ℝ) : lift (c • M) = C ℝ c • lift M := by
  ext; simp [lift, smul_eq_C_mul]

theorem lift_one {l' : Type*} [DecidableEq l'] : lift (1 : Matrix l' l' ℝ) = 1 := by
  ext i j; by_cases h : i = j <;> simp [lift, one_apply, h]

theorem lift_zero {l' o' : Type*} : lift (0 : Matrix l' o' ℝ) = 0 := by ext; simp [lift]

theorem lift_transpose {l' o' : Type*} (M : Matrix l' o' ℝ) : lift Mᵀ = (lift M)ᵀ := by
  ext; simp [lift]

theorem lift_mulVec {l' o' : Type*} [Fintype o'] (M : Matrix l' o' ℝ) (x : o' → ℝ) :
    lift M *ᵥ liftv x = liftv (M *ᵥ x) := by
  funext i; simp [lift, liftv, mulVec, dotProduct, map_sum]

theorem cf_lift_mul_eq {l' o' : Type*} [Fintype o'] (k : ℕ) (M : Matrix l' o' ℝ)
    (N : Matrix o' o' T) : cf k (lift M * N) = M * cf k N := by
  ext i j; simp [cf, lift, mul_apply, map_sum, coeff_C_mul]

theorem cfv_lift_mulVec {l' o' : Type*} [Fintype o'] (k : ℕ) (M : Matrix l' o' ℝ)
    (x : o' → T) : cfv k (lift M *ᵥ x) = M *ᵥ cfv k x := by
  funext i; simp [cfv, lift, mulVec, dotProduct, map_sum, coeff_C_mul]

/-! ### Perturbed ground state, energy, Hamiltonian -/

noncomputable def psiT : Fock n → T :=
  liftv (phi O) + (X : T) • liftv (psi1 ε v O) + ((X : T) ^ 2) • liftv (psi2 ε v O)

noncomputable def ET : T :=
  C ℝ (E0 ε O) + X * C ℝ (E1 v O) + X ^ 2 * C ℝ (E2 ε v O)

noncomputable def HT : Matrix (Fock n) (Fock n) T := lift (H0 ε) + (X : T) • lift (vop v)

/-- `H(λ) - E(λ)`. -/
noncomputable def KT : Matrix (Fock n) (Fock n) T := HT ε v - ET ε v O • 1

/-- `ω - (H - E)`. -/
noncomputable def MpT : Matrix (Fock n) (Fock n) T := C ℝ ω • 1 - KT ε v O

/-- `ω + (H - E)`. -/
noncomputable def MmT : Matrix (Fock n) (Fock n) T := C ℝ ω • 1 + KT ε v O

/-- `⟨ψ|ψ⟩`. -/
noncomputable def dT : T := psiT ε v O ⬝ᵥ psiT ε v O

/-- **The exact Green's function**, as a formal power series in `λ`. -/
noncomputable def greenT : Matrix (Fin n) (Fin n) T := Matrix.of fun p q =>
  (psiT ε v O ⬝ᵥ ((annT p * (MpT ε v O ω)⁻¹ * creT q) *ᵥ psiT ε v O) +
    psiT ε v O ⬝ᵥ ((creT q * (MmT ε v O ω)⁻¹ * annT p) *ᵥ psiT ε v O)) * (dT ε v O)⁻¹

/-- The unperturbed Green's function `diag (ω - ε_p)⁻¹`. -/
noncomputable def green0 : Matrix (Fin n) (Fin n) T := diagonal fun p => C ℝ (ω - ε p)⁻¹

/-- **The exact self-energy** `Σ = G0⁻¹ - G⁻¹`. -/
noncomputable def sigmaT : Matrix (Fin n) (Fin n) T := (green0 ε ω)⁻¹ - (greenT ε v O ω)⁻¹

/-! ### Coefficients of the basic series -/

variable {ε v O ω}

theorem cfv_psiT (k : ℕ) :
    cfv k (psiT ε v O) =
      if k = 0 then phi O else if k = 1 then psi1 ε v O else if k = 2 then psi2 ε v O else 0 := by
  funext S
  simp only [psiT, cfv, liftv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, coeff_C,
    coeff_X_mul', coeff_X2_mul]
  rcases k with _ | _ | _ | k <;> simp

theorem coeff_ET (k : ℕ) :
    coeff ℝ k (ET ε v O) =
      if k = 0 then E0 ε O else if k = 1 then E1 v O else if k = 2 then E2 ε v O else 0 := by
  simp only [ET, map_add, coeff_C, coeff_X_mul', coeff_X2_mul]
  rcases k with _ | _ | _ | k <;> simp

theorem cf_KT (k : ℕ) :
    cf k (KT ε v O) =
      if k = 0 then H0 ε - E0 ε O • 1 else if k = 1 then vop v - E1 v O • 1
      else if k = 2 then -(E2 ε v O • 1) else 0 := by
  ext S S'
  simp only [KT, HT, cf, lift, map_apply, sub_apply, add_apply, smul_apply, smul_eq_mul,
    one_apply, map_sub, map_add, coeff_C, coeff_X_mul', mul_ite, mul_one, mul_zero, coeff_ET]
  have h0 : constantCoeff ℝ (ET ε v O) = E0 ε O := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_ET]; simp
  have h1 : coeff ℝ 1 (ET ε v O) = E1 v O := by rw [coeff_ET]; simp
  have h2 : coeff ℝ 2 (ET ε v O) = E2 ε v O := by rw [coeff_ET]; simp
  have h3 : ∀ k, coeff ℝ (k + 1 + 1 + 1) (ET ε v O) = 0 := by intro k; rw [coeff_ET]; simp
  by_cases h : S = S' <;> rcases k with _ | _ | _ | k <;> simp [h, h0, h1, h2, h3]

theorem cf0_KT : cf 0 (KT ε v O) = H0 ε - E0 ε O • 1 := by rw [cf_KT]; simp
theorem cf1_KT : cf 1 (KT ε v O) = vop v - E1 v O • 1 := by rw [cf_KT]; simp
theorem cf2_KT : cf 2 (KT ε v O) = -(E2 ε v O • 1) := by rw [cf_KT]; simp
theorem cfv0_psiT : cfv 0 (psiT ε v O) = phi O := by rw [cfv_psiT]; simp
theorem cfv1_psiT : cfv 1 (psiT ε v O) = psi1 ε v O := by rw [cfv_psiT]; simp
theorem cfv2_psiT : cfv 2 (psiT ε v O) = psi2 ε v O := by rw [cfv_psiT]; simp

theorem sub_smul_one_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (c : ℝ)
    (x : ι → ℝ) : (M - c • 1) *ᵥ x = M *ᵥ x - c • x := by
  rw [sub_mulVec, smul_mulVec_assoc, one_mulVec]

/-- **S2 exit.** The Rayleigh-Schrödinger state solves `H(λ) ψ(λ) = E(λ) ψ(λ)` modulo `λ³`:
the coefficients 0, 1, 2 of the residual `(H - E) ψ` vanish. -/
theorem resid_cf (hnd : NonDeg ε O) :
    cfv 0 (KT ε v O *ᵥ psiT ε v O) = 0 ∧ cfv 1 (KT ε v O *ᵥ psiT ε v O) = 0 ∧
      cfv 2 (KT ε v O *ᵥ psiT ε v O) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cfv0_mulVec, cf0_KT, cfv0_psiT, sub_smul_one_mulVec]; exact eig_order0
  · rw [cfv1_mulVec, cf0_KT, cf1_KT, cfv0_psiT, cfv1_psiT, sub_smul_one_mulVec,
      sub_smul_one_mulVec]; exact eig_order1 hnd
  · rw [cfv2_mulVec, cf0_KT, cf1_KT, cf2_KT, cfv0_psiT, cfv1_psiT, cfv2_psiT, sub_smul_one_mulVec,
      sub_smul_one_mulVec, neg_mulVec, smul_mulVec_assoc, one_mulVec]
    have := eig_order2 (v := v) hnd
    rw [← this]; abel

end GW.Endpoint.ManyBody
