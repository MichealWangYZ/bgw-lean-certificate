/-
LL-C2B: formal screening for the ring family.

The C2A modules prove, for the classical real Gibbs model of Lin-Lindsey Part I
(arXiv:1809.02900v1, PDF section 4.7.1, printed pp. 42-43 and Fig. 4.11), that
the ring diagram of order `k` contributes

  contribution (ring k) G v i j = (-1)^(k+1) * (G i j * (v * (B * v)^k) i j) / 2^k

with `B = G ⊙ G` and the divisor `2^k` certified by `card_aut_ring`. This module
asks the one remaining question of that section: are those coefficients the
coefficients of a *screened* interaction?

The answer is yes, and it is stated against mathlib's own noncommutative formal
inverse. The coefficient ring here is `Matrix (Fin N) (Fin N) K`, which does not
commute, so `PowerSeries.inv` (a `[Field k]` interface) does not apply. But
`PowerSeries.invOfUnit` in the same pinned file lives under `[Ring R]` and needs
only that the constant coefficient is a unit; for `P = 1 + X * C A` it is `1`.
Both `mul_invOfUnit` and `invOfUnit_mul` are therefore available, which is what
makes the two-sided statements below honest rather than a commutativity slip.

Everything here is an identity in `PowerSeries (Matrix (Fin N) (Fin N) K)`.
Nothing is evaluated at a point, no convergence is claimed, and no radius is
asserted. A formal unit with constant coefficient `I` may specialize to a
singular matrix; `1 - X` is the standard reminder. The full quartic perturbation
series of the model and the selected geometric ring series are different series.

The construction holds `G` fixed. It is not a solution of a self-consistent
`G(z)`, and the Hartree contribution is not derived here.
-/
import GW.LL.StructuralRing
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Matrix.Hadamard

namespace GW.LL

open PowerSeries

-- Characteristic zero is a standing modelling assumption, not a proof device:
-- it is what makes `1/2` the physical symmetry weight rather than Lean's
-- totalized division (see `docs/LL-C2A-REVIEW.md`). It is therefore carried by
-- every statement in this file, including those whose proof does not need it.
set_option linter.unusedSectionVars false

noncomputable section

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}
variable (G v : Matrix (Fin N) (Fin N) K)

/-! ### The screening polynomials

The weight `1/2` is not decoration: it is the `k`-th ring's symmetry factor
`2^k` (C2A's `card_aut_ring`) distributed one bubble at a time. Characteristic
zero is assumed so that `1/2` is the physical weight rather than Lean's
totalized division; see `docs/LL-C2A-REVIEW.md`.
-/

/-- `A_L = ½ (v B)`, the kernel that screens on the left. -/
def AL : Matrix (Fin N) (Fin N) K := (2⁻¹ : K) • (v * bubble G)

/-- `A_R = ½ (B v)`, the kernel that screens on the right. These differ: the
matrices do not commute, and the two-sided statements below keep them apart. -/
def AR : Matrix (Fin N) (Fin N) K := (2⁻¹ : K) • (bubble G * v)

/-- The left screening polynomial `P_L = 1 + z A_L`. -/
def PL : PowerSeries (Matrix (Fin N) (Fin N) K) := 1 + X * C _ (AL G v)

/-- The right screening polynomial `P_R = 1 + z A_R`. -/
def PR : PowerSeries (Matrix (Fin N) (Fin N) K) := 1 + X * C _ (AR G v)

theorem constantCoeff_PL : constantCoeff _ (PL G v) = 1 := by
  simp [PL]

theorem constantCoeff_PR : constantCoeff _ (PR G v) = 1 := by
  simp [PR]

/-- `S_L`, the formal inverse of `P_L`, taken from the pinned library's
noncommutative interface rather than reconstructed here. -/
def SL : PowerSeries (Matrix (Fin N) (Fin N) K) := invOfUnit (PL G v) 1

/-- `S_R`, the formal inverse of `P_R`. -/
def SR : PowerSeries (Matrix (Fin N) (Fin N) K) := invOfUnit (PR G v) 1

/-! ### Both inverse identities

`invOfUnit` is two-sided, so neither direction is assumed. -/

theorem PL_mul_SL : PL G v * SL G v = 1 :=
  mul_invOfUnit _ _ (by simpa using constantCoeff_PL G v)

theorem SL_mul_PL : SL G v * PL G v = 1 :=
  invOfUnit_mul _ _ (by simpa using constantCoeff_PL G v)

theorem PR_mul_SR : PR G v * SR G v = 1 :=
  mul_invOfUnit _ _ (by simpa using constantCoeff_PR G v)

theorem SR_mul_PR : SR G v * PR G v = 1 :=
  invOfUnit_mul _ _ (by simpa using constantCoeff_PR G v)

/-- The screened interaction `W = S_L v`. -/
def W : PowerSeries (Matrix (Fin N) (Fin N) K) := SL G v * C _ v

/-! ### The screening equations

The polynomial on the right is `P_R`, not `P_L`. The bridge between them is
`v A_R = A_L v`, which is where the two orderings meet; no commutativity of
`v` and `B` is used anywhere. -/

/-- `v A_R = A_L v`: both sides are `½ v B v`. -/
theorem C_v_mul_PR : C _ v * PR G v = PL G v * C _ v := by
  have h : v * AR G v = AL G v * v := by
    simp only [AL, AR, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc]
  calc C _ v * PR G v
      = C _ v + X * C _ (v * AR G v) := by
        rw [PR, mul_add, mul_one, ← mul_assoc, ← X_mul, mul_assoc, ← map_mul]
    _ = C _ v + X * C _ (AL G v * v) := by rw [h]
    _ = PL G v * C _ v := by
        rw [PL, add_mul, one_mul, map_mul, mul_assoc]

theorem PL_mul_W : PL G v * W G v = C _ v := by
  rw [W, ← mul_assoc, PL_mul_SL, one_mul]

theorem W_mul_PR : W G v * PR G v = C _ v := by
  rw [W, mul_assoc, C_v_mul_PR, ← mul_assoc, SL_mul_PL, one_mul]

theorem W_eq_C_v_mul_SR : W G v = C _ v * SR G v := by
  conv_lhs => rw [← mul_one (W G v), ← PR_mul_SR G v, ← mul_assoc, W_mul_PR]

/-! ### The coefficients, in closed form

`W` is defined through the library inverse. `Wcoeff` is defined independently by
the closed formula. `coeff_W` below is the checked bridge: it is a theorem for
every `k`, not agreement sampled at a few orders. -/

/-- `W_k = (-½)^k (v (B v)^k)`, stated without reference to `W`. -/
def Wcoeff (k : ℕ) : Matrix (Fin N) (Fin N) K :=
  ((-2⁻¹ : K)) ^ k • (v * (bubble G * v) ^ k)

/-- The closed form assembled into a series, still without reference to `W`. -/
def Wexp : PowerSeries (Matrix (Fin N) (Fin N) K) := mk (Wcoeff G v)

theorem Wcoeff_zero : Wcoeff G v 0 = v := by simp [Wcoeff]

theorem Wcoeff_succ (k : ℕ) : Wcoeff G v (k + 1) = -(AL G v * Wcoeff G v k) := by
  have hm : v * (bubble G * v) ^ (k + 1) = v * bubble G * (v * (bubble G * v) ^ k) := by
    rw [pow_succ']
    simp [Matrix.mul_assoc]
  simp only [Wcoeff, AL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hm]
  rw [← neg_smul]
  congr 1
  ring

theorem Wcoeff_succ' (k : ℕ) : Wcoeff G v (k + 1) = -(Wcoeff G v k * AR G v) := by
  simp only [Wcoeff, AR, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ,
    ← Matrix.mul_assoc]
  rw [← neg_smul]
  congr 1
  ring

/-- `P_L` annihilates the closed-form series down to the constant `v`. This is
the whole content of the identification; the inverse then does the rest. -/
theorem PL_mul_Wexp : PL G v * Wexp G v = C _ v := by
  ext n
  cases n with
  | zero =>
      simp [PL, Wexp, coeff_mk, Wcoeff_zero]
  | succ k =>
      have hX : coeff _ (k + 1) (X * (C _ (AL G v) * Wexp G v))
          = AL G v * Wcoeff G v k := by
        rw [coeff_succ_X_mul, coeff_C_mul, Wexp, coeff_mk]
      rw [PL, add_mul, one_mul, map_add, mul_assoc, hX, Wexp, coeff_mk,
        Wcoeff_succ, coeff_succ_C, neg_add_cancel]

/-- The bridge: the library inverse's coefficients ARE the closed form. -/
theorem Wexp_eq_W : Wexp G v = W G v := by
  have h : SL G v * (PL G v * Wexp G v) = SL G v * C _ v := by rw [PL_mul_Wexp]
  rwa [← mul_assoc, SL_mul_PL, one_mul, ← W] at h

theorem coeff_W (k : ℕ) : coeff _ k (W G v) = Wcoeff G v k := by
  rw [← Wexp_eq_W, Wexp, coeff_mk]

theorem coeff_W_zero : coeff _ 0 (W G v) = v := by rw [coeff_W, Wcoeff_zero]

theorem coeff_W_succ (k : ℕ) :
    coeff _ (k + 1) (W G v) = -(AL G v * coeff _ k (W G v)) := by
  rw [coeff_W, coeff_W, Wcoeff_succ]

theorem coeff_W_succ' (k : ℕ) :
    coeff _ (k + 1) (W G v) = -(coeff _ k (W G v) * AR G v) := by
  rw [coeff_W, coeff_W, Wcoeff_succ']

/-! ### Back to the diagrams

`H_G` multiplies each coefficient entrywise by `G`. It is additive, and it is
NOT a ring homomorphism on matrices: `hadamardSeries_not_multiplicative` below
exhibits a failure, so no transport through matrix products is available and
none is used. -/

/-- Coefficientwise entrywise multiplication by `G`. -/
def hadamardSeries (U : PowerSeries (Matrix (Fin N) (Fin N) K)) :
    PowerSeries (Matrix (Fin N) (Fin N) K) :=
  mk fun k => Matrix.hadamard G (coeff _ k U)

theorem coeff_hadamardSeries (U : PowerSeries (Matrix (Fin N) (Fin N) K)) (k : ℕ) :
    coeff _ k (hadamardSeries G U) = Matrix.hadamard G (coeff _ k U) :=
  coeff_mk _ _

theorem constantCoeff_hadamardSeries (U : PowerSeries (Matrix (Fin N) (Fin N) K)) :
    constantCoeff _ (hadamardSeries G U) = Matrix.hadamard G (constantCoeff _ U) := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
    coeff_hadamardSeries]

theorem hadamardSeries_add (U V : PowerSeries (Matrix (Fin N) (Fin N) K)) :
    hadamardSeries G (U + V) = hadamardSeries G U + hadamardSeries G V := by
  ext k
  simp [coeff_hadamardSeries, Matrix.hadamard, Matrix.add_apply, mul_add]

/-- `H_G` is not multiplicative, so it cannot be transported through a matrix
product by a ring-hom API. An explicit failure at `N = 2` over `ℚ`, rather than
a comment claiming the restriction. -/
theorem hadamardSeries_not_multiplicative :
    ∃ (G₀ A₀ B₀ : Matrix (Fin 2) (Fin 2) ℚ),
      hadamardSeries G₀ (C _ A₀ * C _ B₀)
        ≠ hadamardSeries G₀ (C _ A₀) * hadamardSeries G₀ (C _ B₀) := by
  refine ⟨!![1, 1; 1, 0], !![1, 1; 1, 1], !![1, 1; 1, 1], fun h => ?_⟩
  have h01 := congrArg
    (fun U => constantCoeff (Matrix (Fin 2) (Fin 2) ℚ) U 0 1) h
  simp only [constantCoeff_hadamardSeries, map_mul, constantCoeff_C,
    Matrix.hadamard, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h01

/-- The ring series `T`, whose `k`-th coefficient is C2A's proved contribution
of the order-`k` ring diagram. Defined from the graph data, not from `W`. -/
def T : PowerSeries (Matrix (Fin N) (Fin N) K) :=
  mk fun k => Matrix.of fun i j => FeynDiagram.contribution (ring k) G v i j

theorem coeff_T (k : ℕ) (i j : Fin N) :
    coeff _ k (T G v) i j = FeynDiagram.contribution (ring k) G v i j := by
  rw [T, coeff_mk]; rfl

/-- **The screening identity.** The diagram series is minus the entrywise
`G`-dressing of the screened interaction: `T = -H_G W`. Proved from C2A's
`contribution_ring`, with the sign, the symmetry weight `2^k` and the matrix
order all carried through. -/
theorem T_eq_neg_hadamardSeries_W : T G v = -hadamardSeries G (W G v) := by
  ext k i j
  have h2 : ((2 : K)) ^ k ≠ 0 := pow_ne_zero _ (two_ne_zero)
  rw [coeff_T, contribution_ring]
  simp only [map_neg, Matrix.neg_apply, coeff_hadamardSeries, coeff_W, Wcoeff,
    Matrix.hadamard, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [neg_pow, neg_pow, pow_succ]
  field_simp
  ring

/-- A computable coefficient of `T`, built from C2A's `contributionOf` with the
divisor `2^k` that `card_aut_ring` certifies. `coeff_T_eq_Tcoeff` is the named
bridge that lets the executable evidence stand for the series coefficient; the
evaluator computes THIS, and the theorem is what links it to `coeff k (T G v)`. -/
def Tcoeff (k : ℕ) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun i j => FeynDiagram.contributionOf (2 ^ k) (ring k) G v i j

theorem coeff_T_eq_Tcoeff (k : ℕ) : coeff _ k (T G v) = Tcoeff G v k := by
  funext i j
  rw [coeff_T, contribution_ring_eq_contributionOf]
  rfl

/-- `Wcoeff` plays the same role for `W`; `coeff_W` is its bridge. Stated here
so that both executable series have a named, checked correspondence. -/
theorem Tcoeff_eq_neg_hadamard_Wcoeff (k : ℕ) :
    Tcoeff G v k = -Matrix.hadamard G (Wcoeff G v k) := by
  rw [← coeff_T_eq_Tcoeff, T_eq_neg_hadamardSeries_W, map_neg, coeff_hadamardSeries,
    coeff_W]

/-! ### Degree convention

`T` and `W` count bubbles: the Fock term sits at degree zero. A ring of order
`k` has `k + 1` interaction vertices, so counting interactions instead shifts
everything by one. Both series are recorded, and the relation between them is
proved rather than asserted in a comment.

This is emphatically not the expansion of a self-consistent `G(z)`: `G` is a
fixed input throughout. The Hartree contribution is a separate input and is not
derived here. -/

/-- The interaction-counting ring series. -/
def Tcoupling : PowerSeries (Matrix (Fin N) (Fin N) K) := X * T G v

/-- The interaction-counting screened interaction. -/
def Wcoupling : PowerSeries (Matrix (Fin N) (Fin N) K) := X * W G v

theorem constantCoeff_Tcoupling : constantCoeff _ (Tcoupling G v) = 0 := by
  simp [Tcoupling]

theorem constantCoeff_Wcoupling : constantCoeff _ (Wcoupling G v) = 0 := by
  simp [Wcoupling]

theorem coeff_succ_Tcoupling (k : ℕ) (i j : Fin N) :
    coeff _ (k + 1) (Tcoupling G v) i j = FeynDiagram.contribution (ring k) G v i j := by
  rw [Tcoupling, coeff_succ_X_mul, coeff_T]

theorem coeff_one_Wcoupling : coeff _ 1 (Wcoupling G v) = v := by
  rw [Wcoupling, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_W_zero]

end

end GW.LL
