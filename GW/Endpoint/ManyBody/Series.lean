/-
A3(a): formal power series in the coupling `λ` (mathlib's `PowerSeries ℝ`, with `λ`
the variable `X`), matrices and vectors over it, and their low-order coefficients.

The self-energy theorems are statements about the coefficients `cf k` of
matrices over `T = ℝ⟦X⟧`. This is exactly the meaning of the diagrammatic
expansion: no convergence in `λ` and no analyticity are claimed or needed. The
analytic statement (that the Taylor coefficients of the true function
`λ ↦ Σ(ω; λ)` are these) is NOT proved here.

Only coefficients 0, 1, 2 are ever extracted, and the product rules below are
stated for exactly those.
-/
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Real.Basic

namespace GW.Endpoint.ManyBody

open Matrix PowerSeries

/-- Formal power series in the coupling. -/
abbrev T := PowerSeries ℝ

/-- Coefficient `k` of every entry of a matrix over `T`. -/
noncomputable def cf {m n : Type*} (k : ℕ) (M : Matrix m n T) : Matrix m n ℝ := M.map (coeff ℝ k)

/-- Coefficient `k` of every entry of a vector over `T`. -/
noncomputable def cfv {m : Type*} (k : ℕ) (x : m → T) : m → ℝ := fun i => coeff ℝ k (x i)

/-- Constant embedding of real matrices. -/
noncomputable def lift {m n : Type*} (M : Matrix m n ℝ) : Matrix m n T := M.map (C ℝ)

/-- Constant embedding of real vectors. -/
noncomputable def liftv {m : Type*} (x : m → ℝ) : m → T := fun i => C ℝ (x i)

section Scalars

theorem coeff0_mul (a b : T) : coeff ℝ 0 (a * b) = coeff ℝ 0 a * coeff ℝ 0 b := by
  simp [coeff_mul]

theorem coeff1_mul (a b : T) :
    coeff ℝ 1 (a * b) = coeff ℝ 0 a * coeff ℝ 1 b + coeff ℝ 1 a * coeff ℝ 0 b := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ]; simp [add_comm]

theorem coeff2_mul (a b : T) :
    coeff ℝ 2 (a * b) = coeff ℝ 0 a * coeff ℝ 2 b + coeff ℝ 1 a * coeff ℝ 1 b +
      coeff ℝ 2 a * coeff ℝ 0 b := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]; simp; ring

theorem coeff_C' (k : ℕ) (a : ℝ) : coeff ℝ k (C ℝ a) = if k = 0 then a else 0 := coeff_C k a

theorem coeff_X_mul' (k : ℕ) (a : T) :
    coeff ℝ k (X * a) = if k = 0 then 0 else coeff ℝ (k - 1) a := by
  rcases k with _ | k
  · simp
  · simp [coeff_succ_X_mul]

theorem coeff_X2_mul (k : ℕ) (a : T) :
    coeff ℝ k (X ^ 2 * a) = if k < 2 then 0 else coeff ℝ (k - 2) a := by
  rw [coeff_X_pow_mul']
  split_ifs with h1 h2 h2 <;> first | rfl | omega

end Scalars

variable {l m n : Type*}

section Matrices

theorem cf_apply (k : ℕ) (M : Matrix m n T) (i : m) (j : n) : cf k M i j = coeff ℝ k (M i j) := rfl

theorem cf_add (k : ℕ) (M N : Matrix m n T) : cf k (M + N) = cf k M + cf k N := by
  ext; simp [cf]

theorem cf_sub (k : ℕ) (M N : Matrix m n T) : cf k (M - N) = cf k M - cf k N := by
  ext; simp [cf]

theorem cf_neg (k : ℕ) (M : Matrix m n T) : cf k (-M) = -cf k M := by
  ext; simp [cf]

theorem cf_zero (k : ℕ) : cf k (0 : Matrix m n T) = 0 := by ext; simp [cf]

theorem cf_transpose (k : ℕ) (M : Matrix m n T) : cf k Mᵀ = (cf k M)ᵀ := by ext; simp [cf]

theorem cf_one [DecidableEq m] (k : ℕ) :
    cf k (1 : Matrix m m T) = if k = 0 then 1 else 0 := by
  ext i j
  by_cases h : i = j <;> by_cases hk : k = 0 <;> simp [cf, one_apply, h, hk]

theorem cf_lift (k : ℕ) (M : Matrix m n ℝ) : cf k (lift M) = if k = 0 then M else 0 := by
  ext i j; simp only [cf, lift, map_apply, coeff_C]; split_ifs <;> simp

theorem cf0_smul (a : T) (M : Matrix m n T) : cf 0 (a • M) = coeff ℝ 0 a • cf 0 M := by
  ext i j; simp [cf, coeff0_mul]

theorem cf1_smul (a : T) (M : Matrix m n T) :
    cf 1 (a • M) = coeff ℝ 0 a • cf 1 M + coeff ℝ 1 a • cf 0 M := by
  ext i j; simp [cf, coeff1_mul]

theorem cf2_smul (a : T) (M : Matrix m n T) :
    cf 2 (a • M) = coeff ℝ 0 a • cf 2 M + coeff ℝ 1 a • cf 1 M + coeff ℝ 2 a • cf 0 M := by
  ext i j; simp [cf, coeff2_mul]

variable [Fintype m]

theorem cf0_mul (M : Matrix l m T) (N : Matrix m n T) : cf 0 (M * N) = cf 0 M * cf 0 N := by
  ext i j; simp [cf, mul_apply, coeff0_mul]

theorem cf1_mul (M : Matrix l m T) (N : Matrix m n T) :
    cf 1 (M * N) = cf 0 M * cf 1 N + cf 1 M * cf 0 N := by
  ext i j; simp [cf, mul_apply, coeff1_mul, Finset.sum_add_distrib]

theorem cf2_mul (M : Matrix l m T) (N : Matrix m n T) :
    cf 2 (M * N) = cf 0 M * cf 2 N + cf 1 M * cf 1 N + cf 2 M * cf 0 N := by
  ext i j; simp [cf, mul_apply, coeff2_mul, Finset.sum_add_distrib]

end Matrices

section Vectors

theorem cfv_add (k : ℕ) (x y : m → T) : cfv k (x + y) = cfv k x + cfv k y := by
  funext; simp [cfv]

theorem cfv_sub (k : ℕ) (x y : m → T) : cfv k (x - y) = cfv k x - cfv k y := by
  funext; simp [cfv]

theorem cfv_liftv (k : ℕ) (x : m → ℝ) : cfv k (liftv x) = if k = 0 then x else 0 := by
  funext i; simp only [cfv, liftv, coeff_C]; split_ifs <;> simp

theorem cfv0_smul (a : T) (x : m → T) : cfv 0 (a • x) = coeff ℝ 0 a • cfv 0 x := by
  funext i; simp [cfv, coeff0_mul]

theorem cfv1_smul (a : T) (x : m → T) :
    cfv 1 (a • x) = coeff ℝ 0 a • cfv 1 x + coeff ℝ 1 a • cfv 0 x := by
  funext i; simp [cfv, coeff1_mul]

theorem cfv2_smul (a : T) (x : m → T) :
    cfv 2 (a • x) = coeff ℝ 0 a • cfv 2 x + coeff ℝ 1 a • cfv 1 x + coeff ℝ 2 a • cfv 0 x := by
  funext i; simp [cfv, coeff2_mul]

variable [Fintype m]

theorem cfv0_mulVec (M : Matrix l m T) (x : m → T) : cfv 0 (M *ᵥ x) = cf 0 M *ᵥ cfv 0 x := by
  funext i; simp [cfv, cf, mulVec, dotProduct, coeff0_mul]

theorem cfv1_mulVec (M : Matrix l m T) (x : m → T) :
    cfv 1 (M *ᵥ x) = cf 0 M *ᵥ cfv 1 x + cf 1 M *ᵥ cfv 0 x := by
  funext i; simp [cfv, cf, mulVec, dotProduct, coeff1_mul, Finset.sum_add_distrib]

theorem cfv2_mulVec (M : Matrix l m T) (x : m → T) :
    cfv 2 (M *ᵥ x) = cf 0 M *ᵥ cfv 2 x + cf 1 M *ᵥ cfv 1 x + cf 2 M *ᵥ cfv 0 x := by
  funext i; simp [cfv, cf, mulVec, dotProduct, coeff2_mul, Finset.sum_add_distrib]

theorem coeff0_dot (x y : m → T) : coeff ℝ 0 (x ⬝ᵥ y) = cfv 0 x ⬝ᵥ cfv 0 y := by
  simp [cfv, dotProduct, coeff0_mul]

theorem coeff1_dot (x y : m → T) :
    coeff ℝ 1 (x ⬝ᵥ y) = cfv 0 x ⬝ᵥ cfv 1 y + cfv 1 x ⬝ᵥ cfv 0 y := by
  simp [cfv, dotProduct, coeff1_mul, Finset.sum_add_distrib]

theorem coeff2_dot (x y : m → T) :
    coeff ℝ 2 (x ⬝ᵥ y) = cfv 0 x ⬝ᵥ cfv 2 y + cfv 1 x ⬝ᵥ cfv 1 y + cfv 2 x ⬝ᵥ cfv 0 y := by
  simp [cfv, dotProduct, coeff2_mul, Finset.sum_add_distrib]

end Vectors

/-! ### Inverses -/

/-- A matrix over `T` whose constant term has a left inverse has a unit determinant. -/
theorem isUnit_det_of_cf0 [Fintype m] [DecidableEq m] (M : Matrix m m T) (L : Matrix m m ℝ)
    (hL : L * cf 0 M = 1) : IsUnit M.det := by
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply]
  have h : coeff ℝ 0 M.det = (cf 0 M).det := by
    rw [coeff_zero_eq_constantCoeff_apply, RingHom.map_det]; congr 1; ext; simp [cf]
  rw [h]
  exact isUnit_det_of_left_inverse hL

/-- The constant term of the inverse is the inverse of the constant term. -/
theorem cf0_inv [Fintype m] [DecidableEq m] (M : Matrix m m T) (L : Matrix m m ℝ)
    (hL : L * cf 0 M = 1) : cf 0 M⁻¹ = L := by
  have hu := isUnit_det_of_cf0 M L hL
  have h1 : cf 0 (M⁻¹ * M) = 1 := by rw [nonsing_inv_mul _ hu, cf_one, if_pos rfl]
  rw [cf0_mul] at h1
  have hR : cf 0 M * L = 1 := mul_eq_one_comm.mp hL
  calc cf 0 M⁻¹ = cf 0 M⁻¹ * (cf 0 M * L) := by rw [hR, Matrix.mul_one]
    _ = L := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem coeff_inv_T (a : T) (h : coeff ℝ 0 a = 1) :
    coeff ℝ 0 a⁻¹ = 1 ∧ coeff ℝ 1 a⁻¹ = -coeff ℝ 1 a ∧
      coeff ℝ 2 a⁻¹ = coeff ℝ 1 a ^ 2 - coeff ℝ 2 a := by
  have h0 : constantCoeff ℝ a ≠ 0 := by rw [← coeff_zero_eq_constantCoeff_apply, h]; norm_num
  have hm := PowerSeries.mul_inv_cancel a h0
  have e0 : coeff ℝ 0 (a * a⁻¹) = 1 := by rw [hm]; simp
  have e1 : coeff ℝ 1 (a * a⁻¹) = 0 := by rw [hm]; simp
  have e2 : coeff ℝ 2 (a * a⁻¹) = 0 := by rw [hm]; simp
  rw [coeff0_mul, h, one_mul] at e0
  rw [coeff1_mul, h, one_mul, e0] at e1
  rw [coeff2_mul, h, one_mul, e0] at e2
  have e1' : coeff ℝ 1 a⁻¹ = -coeff ℝ 1 a := by linarith
  refine ⟨e0, e1', ?_⟩
  rw [e1'] at e2; nlinarith [e2]

end GW.Endpoint.ManyBody
