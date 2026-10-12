/-
LL-C4 (first subtask): a finite static electronic RPA screening model, and an
exact statement of what does and does not carry over from C1-C3.

## The question

C1-C3 are about the classical real Gibbs model of Lin-Lindsey Part I. Their
screening algebra *looks* like electronic RPA screening. This file separates the
two claims and proves both halves:

* the **algebra** transfers -- proved by literal reuse. `geoW` below is the
  general geometric inverse over an arbitrary matrix `A`, and both C2B's
  classical `GW.LL.W` and the electronic screened interaction are instances of
  it (`classical_W_eq_geoW`, `electronicW`).
* a **direct identification `chi0 = bubble G` is wrong**, and that much is
  proved: the classical bubble has nonnegative diagonal while a `chi0` built
  from occupied-to-empty transitions with nonnegative weights has nonpositive
  diagonal (`bubble_diag_nonneg`, `chi0_diag_nonpos`, `bubble_chi0_diag_witness`).

**A correction, recorded here because the earlier version of this file got it
wrong.** Those opposite signs were originally presented as proving that the
physical content cannot transfer. That inference is too strong, and the C3/C4
review supplied the counterexample. The two screening polynomials are

```text
classical :  1 + z * (v * bubble G) / 2
electronic:  1 - z * (v * chi0)
```

so the sign is already carried by the prefactors. Setting `chi0 = -(1/2) bubble G`
makes the kernels **identical**, and that is realizable inside this file's own
model by admissible transitions -- see `chi0_eq_neg_half_bubble_witness`, where
`v * bubble G ≠ bubble G * v` so nothing degenerate is happening.
`electronicW_eq_classical_W` then shows every coefficient agrees.

What survives is the weaker and correct statement: **a direct identification
`B = chi0` is generally wrong, and the correctly signed, weighted and
convention-matched correspondence has not been derived here.** The sign lemmas
must not be used to dismiss the classical route.

## What is SPECIFIED rather than derived

The electronic quantities here are a **specification**, not a derivation from a
many-body Hamiltonian:

* transitions carry an occupied energy, an empty energy, a spectral weight and a
  real matrix-element vector; the spin/degeneracy factor lives in the weight and
  is an input;
* `chi0 i j = sum_t weight_t * m_t i * m_t j / (occ_t - emp_t)` at zero frequency;
* `eps = 1 - v * chi0`, and the screened interaction solves `eps * W = v`.

**No claim is made that this is BerkeleyGW's convention or BerkeleyGW's result.**
The repository holds no dielectric or screened-interaction fixture from a
production run, so the C4 roadmap row's "matched-input comparison" is NOT
attempted here and remains open.

Everything is finite, static and formal. No frequency integral, no `Sigma = i G W`,
no self-consistency, no vertex correction, no convergence claim. In particular
the Neumann series below is manipulated as formal coefficients; the finite
telescoping identity `eps * (partial sum) = v - (v chi0)^(K+1) v` is exact
algebra for every `K` and says nothing about whether the series converges.
-/
import GW.LL.Screening
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Notation

namespace GW.LL

open PowerSeries
open scoped Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}

/-! ### The geometric inverse, over an arbitrary matrix

This is C2B's algebra with the specific kernel abstracted away. Both settings
below are instances, so "the algebra transfers" is a proved statement about
definitions rather than an observation about how the formulas look. -/

/-- `P_A = 1 + z A`. -/
def geoP (A : Matrix (Fin N) (Fin N) K) : PowerSeries (Matrix (Fin N) (Fin N) K) :=
  1 + X * C _ A

/-- The formal inverse of `P_A`, from the pinned noncommutative interface. -/
def geoS (A : Matrix (Fin N) (Fin N) K) : PowerSeries (Matrix (Fin N) (Fin N) K) :=
  invOfUnit (geoP A) 1

/-- `W_A = S_A u`: the geometric resummation with source `u`. -/
def geoW (A u : Matrix (Fin N) (Fin N) K) : PowerSeries (Matrix (Fin N) (Fin N) K) :=
  geoS A * C _ u

theorem constantCoeff_geoP (A : Matrix (Fin N) (Fin N) K) :
    constantCoeff _ (geoP A) = 1 := by simp [geoP]

theorem geoP_mul_geoS (A : Matrix (Fin N) (Fin N) K) : geoP A * geoS A = 1 :=
  mul_invOfUnit _ _ (by simpa using constantCoeff_geoP A)

theorem geoS_mul_geoP (A : Matrix (Fin N) (Fin N) K) : geoS A * geoP A = 1 :=
  invOfUnit_mul _ _ (by simpa using constantCoeff_geoP A)

theorem geoP_mul_geoW (A u : Matrix (Fin N) (Fin N) K) :
    geoP A * geoW A u = C _ u := by
  rw [geoW, ← mul_assoc, geoP_mul_geoS, one_mul]

/-- The closed-form coefficients, defined without reference to `geoW`. -/
def geoCoeff (A u : Matrix (Fin N) (Fin N) K) (k : ℕ) : Matrix (Fin N) (Fin N) K :=
  (-1 : K) ^ k • (A ^ k * u)

theorem geoP_mul_mk_geoCoeff (A u : Matrix (Fin N) (Fin N) K) :
    geoP A * mk (geoCoeff A u) = C _ u := by
  ext n
  cases n with
  | zero => simp [geoP, geoCoeff]
  | succ k =>
      have hX : coeff _ (k + 1) (X * (C _ A * mk (geoCoeff A u)))
          = A * geoCoeff A u k := by
        rw [coeff_succ_X_mul, coeff_C_mul, coeff_mk]
      have hA : A ^ (k + 1) * u = A * (A ^ k * u) := by
        rw [pow_succ', Matrix.mul_assoc]
      rw [geoP, add_mul, one_mul, map_add, mul_assoc, hX, coeff_mk, coeff_succ_C,
        geoCoeff, geoCoeff, hA, Matrix.mul_smul, ← add_smul]
      simp [pow_succ]

/-- **The coefficient bridge**: the library inverse's coefficients are the
geometric ones, for every `k`. -/
theorem coeff_geoW (A u : Matrix (Fin N) (Fin N) K) (k : ℕ) :
    coeff _ k (geoW A u) = geoCoeff A u k := by
  have h : geoS A * (geoP A * mk (geoCoeff A u)) = geoS A * C _ u := by
    rw [geoP_mul_mk_geoCoeff]
  rw [← mul_assoc, geoS_mul_geoP, one_mul] at h
  rw [geoW, ← h, coeff_mk]

/-! ### The classical setting is an instance

C2B's `GW.LL.W` is `geoW` at the classical kernel `A_L = ½ v B`. This is
definitional: `GW.LL.PL` and `geoP (AL G v)` are the same series. -/

theorem classical_geoP_eq (G v : Matrix (Fin N) (Fin N) K) :
    geoP (AL G v) = PL G v := rfl

theorem classical_W_eq_geoW (G v : Matrix (Fin N) (Fin N) K) :
    GW.LL.W G v = geoW (AL G v) v := rfl

end

/-! ### The electronic specification -/

/-- One occupied-to-empty channel. `weight` carries spin and degeneracy and is
an input, not a derived quantity. -/
structure Transition (K : Type*) (N : ℕ) where
  occ : K
  emp : K
  weight : K
  m : Fin N → K

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}

/-- One transition's contribution to the static polarizability. -/
def Transition.contrib (t : Transition K N) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun i j => t.weight * t.m i * t.m j / (t.occ - t.emp)

/-- The static (zero-frequency) RPA polarizability. -/
def chi0 (ts : List (Transition K N)) : Matrix (Fin N) (Fin N) K :=
  (ts.map Transition.contrib).sum

/-- The dielectric matrix `eps = 1 - v chi0`. -/
def dielectric (v : Matrix (Fin N) (Fin N) K) (ts : List (Transition K N)) :
    Matrix (Fin N) (Fin N) K := 1 - v * chi0 ts

noncomputable section

/-- The electronic screened interaction, as a formal geometric resummation.
Same `geoW`, different kernel: `A = -(v chi0)`. -/
def electronicW (v : Matrix (Fin N) (Fin N) K) (ts : List (Transition K N)) :
    PowerSeries (Matrix (Fin N) (Fin N) K) :=
  geoW (-(v * chi0 ts)) v

/-- `(-M)^k = (-1)^k • M^k`, the bookkeeping that turns the geometric kernel
`-(v chi0)` into the textbook Neumann expansion. -/
theorem neg_pow_smul (M : Matrix (Fin N) (Fin N) K) (k : ℕ) :
    (-M) ^ k = ((-1 : K)) ^ k • M ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, ih, pow_succ, Matrix.smul_mul]
      simp [Matrix.mul_neg, smul_neg, mul_neg]

/-- **The Neumann series.** `coeff k = (v chi0)^k v`, the textbook expansion,
here obtained from the same library inverse C2B used. -/
theorem coeff_electronicW (v : Matrix (Fin N) (Fin N) K)
    (ts : List (Transition K N)) (k : ℕ) :
    coeff _ k (electronicW v ts) = (v * chi0 ts) ^ k * v := by
  rw [electronicW, coeff_geoW, geoCoeff, neg_pow_smul, Matrix.smul_mul, smul_smul,
    ← pow_add, ← two_mul, pow_mul]
  simp

theorem dielectric_eq_geoP (v : Matrix (Fin N) (Fin N) K)
    (ts : List (Transition K N)) :
    geoP (-(v * chi0 ts)) = 1 + X * C _ (-(v * chi0 ts)) := rfl

end

/-- A computable Neumann coefficient. `coeff_electronicW_eq_neumannCoeff` is the
named bridge that lets the evaluator's numbers stand for series coefficients. -/
def neumannCoeff (v : Matrix (Fin N) (Fin N) K) (ts : List (Transition K N))
    (k : ℕ) : Matrix (Fin N) (Fin N) K := (v * chi0 ts) ^ k * v

/-! ### Truncation is finite algebra, not convergence

`eps * (sum of the first K+1 Neumann terms) = v - (v chi0)^(K+1) v`, exactly,
for every `K`. Stated at the matrix level, with no inverse and no limit. -/

theorem coeff_electronicW_eq_neumannCoeff (v : Matrix (Fin N) (Fin N) K)
    (ts : List (Transition K N)) (k : ℕ) :
    coeff _ k (electronicW v ts) = neumannCoeff v ts k :=
  coeff_electronicW v ts k

/-- The partial Neumann sum `sum_{k<=K} (v chi0)^k v`. -/
def partialScreened (v : Matrix (Fin N) (Fin N) K) (ts : List (Transition K N)) :
    ℕ → Matrix (Fin N) (Fin N) K
  | 0 => v
  | k + 1 => partialScreened v ts k + (v * chi0 ts) ^ (k + 1) * v

theorem dielectric_mul_partialScreened (v : Matrix (Fin N) (Fin N) K)
    (ts : List (Transition K N)) (k : ℕ) :
    dielectric v ts * partialScreened v ts k = v - (v * chi0 ts) ^ (k + 1) * v := by
  induction k with
  | zero => simp [dielectric, partialScreened, sub_mul, pow_one]
  | succ n ih =>
      rw [partialScreened, mul_add, ih, dielectric, sub_mul, one_mul]
      rw [← Matrix.mul_assoc, ← pow_succ']
      abel

/-! ### Entrywise form, symmetry, and the sign of `chi0` -/

theorem chi0_apply (ts : List (Transition K N)) (i j : Fin N) :
    chi0 ts i j
      = (ts.map fun t => t.weight * t.m i * t.m j / (t.occ - t.emp)).sum := by
  induction ts with
  | nil => simp [chi0]
  | cons t rest ih =>
      simp only [chi0, List.map_cons, List.sum_cons, Matrix.add_apply,
        Transition.contrib, Matrix.of_apply] at *
      rw [ih]

theorem chi0_isSymm (ts : List (Transition K N)) : (chi0 ts).IsSymm := by
  ext i j
  rw [Matrix.transpose_apply, chi0_apply, chi0_apply]
  exact congrArg List.sum (List.map_congr_left fun t _ => by ring)

/-- The quadratic form `x · A x`. -/
def quadForm (A : Matrix (Fin N) (Fin N) K) (x : Fin N → K) : K :=
  ∑ i, ∑ j, x i * A i j * x j

theorem quadForm_add (A B : Matrix (Fin N) (Fin N) K) (x : Fin N → K) :
    quadForm (A + B) x = quadForm A x + quadForm B x := by
  simp only [quadForm, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- One transition's quadratic form is a perfect square times `w / (occ - emp)`. -/
theorem quadForm_contrib (t : Transition K N) (x : Fin N → K) :
    quadForm t.contrib x
      = t.weight / (t.occ - t.emp) * (∑ i, x i * t.m i) ^ 2 := by
  have hexp : (∑ i, x i * t.m i) * (∑ j, x j * t.m j)
      = ∑ i, ∑ j, (x i * t.m i) * (x j * t.m j) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  simp only [quadForm, Transition.contrib, Matrix.of_apply, sq]
  rw [hexp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring


section Order

-- `LinearOrderedField` is deprecated in the pinned mathlib (2025-04-10);
-- this is the replacement it recommends.
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {N : ℕ}

/-- **The specified `chi0` is negative semidefinite** when every transition runs
from an occupied level to a strictly higher empty one with nonnegative weight.
This is the check that the sign conventions are internally coherent. -/
theorem chi0_quadForm_nonpos (ts : List (Transition K N))
    (hts : ∀ t ∈ ts, t.occ < t.emp ∧ 0 ≤ t.weight) (x : Fin N → K) :
    quadForm (chi0 ts) x ≤ 0 := by
  induction ts with
  | nil => simp [quadForm, chi0]
  | cons t rest ih =>
      have ht := hts t (by simp)
      have hrest : ∀ u ∈ rest, u.occ < u.emp ∧ 0 ≤ u.weight :=
        fun u hu => hts u (List.mem_cons_of_mem _ hu)
      have hsplit : chi0 (t :: rest) = t.contrib + chi0 rest := by
        simp [chi0, List.map_cons, List.sum_cons]
      rw [hsplit, quadForm_add, quadForm_contrib]
      have hden : t.occ - t.emp < 0 := sub_neg.mpr ht.1
      have hterm : t.weight / (t.occ - t.emp) * (∑ i, x i * t.m i) ^ 2 ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨div_nonpos_of_nonneg_of_nonpos ht.2 hden.le,
          sq_nonneg _⟩)
      exact add_nonpos hterm (ih hrest)

/-- Each diagonal entry is nonpositive, under the same hypotheses. -/
theorem chi0_diag_nonpos (ts : List (Transition K N))
    (hts : ∀ t ∈ ts, t.occ < t.emp ∧ 0 ≤ t.weight) (i : Fin N) :
    chi0 ts i i ≤ 0 := by
  induction ts with
  | nil => simp [chi0]
  | cons t rest ih =>
      have ht := hts t (by simp)
      have hrest : ∀ u ∈ rest, u.occ < u.emp ∧ 0 ≤ u.weight :=
        fun u hu => hts u (List.mem_cons_of_mem _ hu)
      rw [chi0_apply, List.map_cons, List.sum_cons, ← chi0_apply]
      have hden : t.occ - t.emp < 0 := sub_neg.mpr ht.1
      have hnum : 0 ≤ t.weight * t.m i * t.m i := by
        rw [mul_assoc]
        exact mul_nonneg ht.2 (mul_self_nonneg _)
      have : t.weight * t.m i * t.m i / (t.occ - t.emp) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos hnum hden.le
      exact add_nonpos this (ih hrest)

/-- **The classical bubble has the opposite sign on the diagonal**: it is an
entrywise square. So `G ⊙ G` and a physical `chi0` are different objects, and
C2A/C2B are not electronic results. -/
theorem bubble_diag_nonneg (G : Matrix (Fin N) (Fin N) K) (i : Fin N) :
    0 ≤ bubble G i i := mul_self_nonneg _

/-- A witness where both diagonals are nonzero, so the contrast above is not
vacuous: the classical bubble is strictly positive where this `chi0` is strictly
negative. -/
theorem bubble_chi0_diag_witness :
    0 < bubble (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 ∧
      chi0 [({ occ := 0, emp := 1, weight := 1, m := fun _ => 1 } :
        Transition ℚ 1)] 0 0 < 0 := by
  constructor
  · simp [bubble, Matrix.one_apply]
  · simp [chi0, Transition.contrib]

end Order

/-! ### The sign difference is not an obstruction

The kernels differ by a prefactor that absorbs the sign. This section proves the
counterexample rather than only conceding it. -/

section KernelCoincidence

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}

/-- If `chi0 = -(1/2) bubble G` then the electronic kernel IS the classical one. -/
theorem electronic_kernel_eq_AL (G v : Matrix (Fin N) (Fin N) K)
    (ts : List (Transition K N)) (h : chi0 ts = (-(2⁻¹ : K)) • bubble G) :
    -(v * chi0 ts) = AL G v := by
  rw [h, AL, Matrix.mul_smul, neg_smul, neg_neg]

/-- ... hence the two screening polynomials coincide ... -/
theorem geoP_electronic_eq_PL (G v : Matrix (Fin N) (Fin N) K)
    (ts : List (Transition K N)) (h : chi0 ts = (-(2⁻¹ : K)) • bubble G) :
    geoP (-(v * chi0 ts)) = PL G v := by
  rw [electronic_kernel_eq_AL G v ts h]; rfl

/-- ... and so does every coefficient of the screened interaction. The classical
and electronic resummations are then literally the same formal series. -/
theorem electronicW_eq_classical_W (G v : Matrix (Fin N) (Fin N) K)
    (ts : List (Transition K N)) (h : chi0 ts = (-(2⁻¹ : K)) • bubble G) :
    electronicW v ts = GW.LL.W G v := by
  rw [electronicW, geoW, geoS, geoP_electronic_eq_PL G v ts h]
  rfl

end KernelCoincidence

/-- **The witness.** Admissible transitions -- each occupied below empty with
nonnegative weight -- realizing `chi0 = -(1/2) bubble G`, on a fixture where
`v * bubble G ≠ bubble G * v` so no commutativity accident is involved.

Supplied by the C3/C4 review as a counterexample to this file's original
non-transferability claim, and kept here as a checked theorem. -/
theorem chi0_eq_neg_half_bubble_witness :
    let G : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 3]
    let v : Matrix (Fin 2) (Fin 2) ℚ := !![2, 1; 1, 3]
    let ts : List (Transition ℚ 2) :=
      [{ occ := 0, emp := 2, weight := 4, m := ![1, 0] },
       { occ := 0, emp := 2, weight := 9, m := ![0, 1] }]
    (∀ t ∈ ts, t.occ < t.emp ∧ 0 ≤ t.weight)
      ∧ chi0 ts = (-(2⁻¹ : ℚ)) • bubble G
      ∧ v * bubble G ≠ bubble G * v := by
  refine ⟨by decide, ?_, ?_⟩
  · funext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [chi0, Transition.contrib, bubble, Matrix.smul_apply]
  · intro hcomm
    have := congrFun (congrFun hcomm 0) 1
    norm_num [Matrix.mul_apply, bubble, Fin.sum_univ_two] at this

/-! ### The GPP bridge, at the dielectric level only

`GW.GPP` already analyses a plasmon-pole self-energy kernel. The single-pole
model for the inverse dielectric is fixed by matching its zero-frequency value;
that identification is what the theorem below states, with the pole frequency
required nonzero exactly as the `GW.GPP.PoleDomain` side conditions require.

Connecting this to `GW.GPP.Data.sigmaChecked` needs the frequency integral
`Sigma = i G W`, which is NOT performed anywhere in this repository. -/

variable {K : Type*} [Field K] [CharZero K]

/-- The single plasmon pole for the inverse dielectric. -/
def gppInvEps (Omega2 wtilde omega : K) : K :=
  1 + Omega2 / (omega ^ 2 - wtilde ^ 2)

/-- The standard identification fixing the pole strength from the static value. -/
def gppOmega2FromStatic (invEps0 wtilde : K) : K := (1 - invEps0) * wtilde ^ 2

/-- **The plasmon-pole model reproduces the static value at zero frequency**,
under the stated identification and the nonvanishing-pole domain condition. -/
theorem gpp_static_limit (invEps0 wtilde : K) (hw : wtilde ≠ 0) :
    gppInvEps (gppOmega2FromStatic invEps0 wtilde) wtilde 0 = invEps0 := by
  have hw2 : wtilde ^ 2 ≠ 0 := pow_ne_zero _ hw
  field_simp [gppInvEps, gppOmega2FromStatic]
  ring

end GW.LL
