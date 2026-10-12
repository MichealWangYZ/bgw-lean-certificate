/-
R28-F3, linear algebra: a nearly orthonormal set of rows is within an explicit distance of
an EXACTLY orthonormal set (Löwdin), and an exactly orthonormal set of `k` rows in `ℝ^L`
extends by exactly `L - k` rows to a complete set.

* `lowdin`: for a real `k × L` matrix `R` with Gram defect `η = ‖R Rᵀ - 1‖_F² < 1`, the
  Löwdin rows `R* = (R Rᵀ)^{-1/2} R` satisfy `R* R*ᵀ = 1` and `‖R* - R‖_F² ≤ η`.
  (Exactly: `‖R* - R‖_F² = Σ_k (1 - √λ_k)²` and `η = Σ_k (1 - λ_k)²`, `λ_k` the eigenvalues
  of `R Rᵀ`; `(1 - √λ)² ≤ (1 - λ)²` for `λ ≥ 0`.) `(R Rᵀ)^{-1/2}` is built from Mathlib's
  spectral theorem (`Matrix.IsHermitian.spectral_theorem`); Mathlib has no polar
  decomposition or Löwdin orthogonalisation of rectangular matrices.
* `lowdin_nat`: the same on `ℕ`-indexed rows (`range` sums, the form `Cor.lean` uses).
* `exists_completion_nat`: exactly orthonormal rows `P_0 … P_{k-1}` in `ℝ^L` have `k ≤ L`
  and a completion by exactly `L - k` rows `C` with `Σ_n P_n P_nᵀ + Σ_n C_n C_nᵀ = 1`
  (Mathlib's `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`).
-/
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace GW.Bridge.Lowdin

open Matrix Finset

/-- The squared Frobenius norm. -/
def frob2 {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, M i j ^ 2

theorem frob2_eq_trace {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    frob2 M = trace (M * Mᵀ) := by
  simp [frob2, trace, mul_apply, sq]

section conj

variable {m : Type*} [Fintype m] [DecidableEq m] (V : Matrix m m ℝ)

/-- `V diag(d) Vᵀ`. -/
def cj (d : m → ℝ) : Matrix m m ℝ := V * diagonal d * Vᵀ

variable {V}

theorem cj_mul (h : Vᵀ * V = 1) (a b : m → ℝ) : cj V a * cj V b = cj V (a * b) := by
  unfold cj
  rw [show V * diagonal a * Vᵀ * (V * diagonal b * Vᵀ) =
      V * diagonal a * (Vᵀ * V) * diagonal b * Vᵀ by simp only [Matrix.mul_assoc], h,
    Matrix.mul_one, Matrix.mul_assoc V, diagonal_mul_diagonal]
  rfl

theorem cj_transpose (a : m → ℝ) : (cj V a)ᵀ = cj V a := by
  unfold cj
  rw [transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]

theorem trace_cj (h : Vᵀ * V = 1) (a : m → ℝ) : trace (cj V a) = ∑ k, a k := by
  unfold cj
  rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, h, Matrix.mul_one, trace_diagonal]

theorem cj_one (h : V * Vᵀ = 1) : cj V 1 = 1 := by
  unfold cj
  rw [show (1 : m → ℝ) = fun _ => 1 from rfl, diagonal_one, Matrix.mul_one, h]

theorem cj_sub (a b : m → ℝ) : cj V a - cj V b = cj V (a - b) := by
  unfold cj
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  rfl

end conj

/-- `(1 - √λ)² ≤ (1 - λ)²` for `λ ≥ 0`. -/
theorem sqrt_defect_le {l : ℝ} (hl : 0 ≤ l) : (1 - √l) ^ 2 ≤ (1 - l) ^ 2 := by
  have hs := Real.sq_sqrt hl
  have h0 := Real.sqrt_nonneg l
  have e : 1 - l = (1 - √l) * (1 + √l) := by nlinarith
  rw [e, mul_pow]
  have : 1 ≤ (1 + √l) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (1 - √l)]

/-- **Löwdin.** Rows with Gram defect `‖R Rᵀ - 1‖_F² < 1` are within Frobenius distance
`√‖R Rᵀ - 1‖_F²` of exactly orthonormal rows. -/
theorem lowdin {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] (R : Matrix m n ℝ)
    (h : frob2 (R * Rᵀ - 1) < 1) :
    ∃ S : Matrix m n ℝ, S * Sᵀ = 1 ∧ frob2 (S - R) ≤ frob2 (R * Rᵀ - 1) := by
  have hG : (R * Rᵀ).IsHermitian := by
    have := isHermitian_mul_conjTranspose_self R
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  set V : Matrix m m ℝ := (hG.eigenvectorUnitary : Matrix m m ℝ)
  set l := hG.eigenvalues
  have hst : star V = Vᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have h1 : Vᵀ * V = 1 := by
    rw [← hst]; exact Matrix.mem_unitaryGroup_iff'.mp hG.eigenvectorUnitary.2
  have h2 : V * Vᵀ = 1 := by
    rw [← hst]; exact Matrix.mem_unitaryGroup_iff.mp hG.eigenvectorUnitary.2
  have hGc : R * Rᵀ = cj V l := by
    have := hG.spectral_theorem
    rw [hst] at this
    rw [cj]
    convert this using 3
  -- the defect in the eigenbasis
  have hdef : frob2 (R * Rᵀ - 1) = ∑ k, (l k - 1) ^ 2 := by
    rw [frob2_eq_trace, hGc, ← cj_one h2, cj_sub, cj_transpose, cj_mul h1, trace_cj h1]
    refine sum_congr rfl fun k _ => ?_
    simp [sq]
  have hpos : ∀ k, 0 < l k := by
    intro k
    have hk : (l k - 1) ^ 2 ≤ frob2 (R * Rᵀ - 1) := by
      rw [hdef]
      exact single_le_sum (f := fun k => (l k - 1) ^ 2) (fun _ _ => sq_nonneg _) (mem_univ k)
    by_contra hn
    push_neg at hn
    nlinarith
  set μ : m → ℝ := fun k => 1 / √(l k)
  have hμ : ∀ k, μ k * l k * μ k = 1 := by
    intro k
    have hs := Real.sq_sqrt (hpos k).le
    have hs0 : √(l k) ≠ 0 := (Real.sqrt_pos.mpr (hpos k)).ne'
    simp only [μ]
    field_simp
  refine ⟨cj V μ * R, ?_, ?_⟩
  · rw [transpose_mul, cj_transpose, show cj V μ * R * (Rᵀ * cj V μ) = cj V μ * (R * Rᵀ) * cj V μ
      by simp only [Matrix.mul_assoc], hGc, cj_mul h1, cj_mul h1, ← cj_one h2]
    rw [show μ * l * μ = 1 from funext hμ]
  · have e : cj V μ * R - R = cj V (μ - 1) * R := by
      rw [← cj_sub, cj_one h2, Matrix.sub_mul, Matrix.one_mul]
    rw [hdef, e, frob2_eq_trace, transpose_mul, cj_transpose,
      show cj V (μ - 1) * R * (Rᵀ * cj V (μ - 1)) = cj V (μ - 1) * (R * Rᵀ) * cj V (μ - 1)
      by simp only [Matrix.mul_assoc], hGc, cj_mul h1, cj_mul h1, trace_cj h1]
    refine sum_le_sum fun k _ => ?_
    have hs := Real.sq_sqrt (hpos k).le
    have hs0 : 0 < √(l k) := Real.sqrt_pos.mpr (hpos k)
    have e2 : ((μ - 1) * l * (μ - 1)) k = (1 - √(l k)) ^ 2 := by
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, μ]
      field_simp
      nlinarith
    rw [e2, show (l k - 1) ^ 2 = (1 - l k) ^ 2 by ring]
    exact sqrt_defect_le (hpos k).le

/-! ### `ℕ`-indexed rows (the form of `Cor.lean`) -/

theorem sum2_fin (k L : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ i : Fin k, ∑ j : Fin L, f i j = ∑ i ∈ range k, ∑ j ∈ range L, f i j := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin L, f i j) k]
  exact sum_congr rfl fun i _ => Fin.sum_univ_eq_sum_range (f i) L

/-- The squared Frobenius Gram defect `‖R Rᵀ - 1‖_F²` of the rows `R 0 … R (k-1)` on
`v < L`. -/
noncomputable def gramDef (k L : ℕ) (R : ℕ → ℕ → ℝ) : ℝ :=
  ∑ n ∈ range k, ∑ n' ∈ range k,
    (∑ v ∈ range L, R n v * R n' v - if n = n' then 1 else 0) ^ 2

/-- Rows `0 … k-1` are exactly orthonormal on `v < L`. -/
def OrthRows (k L : ℕ) (P : ℕ → ℕ → ℝ) : Prop :=
  ∀ n < k, ∀ n' < k, ∑ v ∈ range L, P n v * P n' v = if n = n' then 1 else 0

/-- The squared Frobenius distance of two row sets. -/
noncomputable def rowDist2 (k L : ℕ) (P R : ℕ → ℕ → ℝ) : ℝ :=
  ∑ n ∈ range k, ∑ v ∈ range L, (P n v - R n v) ^ 2

/-- A `Fin` matrix as `ℕ`-indexed rows (`0` outside). -/
noncomputable def ofMat {k L : ℕ} (S : Matrix (Fin k) (Fin L) ℝ) (n v : ℕ) : ℝ :=
  if h : n < k ∧ v < L then S ⟨n, h.1⟩ ⟨v, h.2⟩ else 0

theorem ofMat_fin {k L : ℕ} (S : Matrix (Fin k) (Fin L) ℝ) (i : Fin k) (j : Fin L) :
    ofMat S i j = S i j := by
  simp [ofMat, i.isLt, j.isLt]

/-- **Löwdin, `ℕ`-indexed.** Gram defect `η < 1` gives exactly orthonormal rows `P` at
squared Frobenius distance `≤ η`. -/
theorem lowdin_nat (k L : ℕ) (R : ℕ → ℕ → ℝ) (h : gramDef k L R < 1) :
    ∃ P : ℕ → ℕ → ℝ, OrthRows k L P ∧ rowDist2 k L P R ≤ gramDef k L R := by
  set Rm : Matrix (Fin k) (Fin L) ℝ := fun n v => R n v
  have hg : frob2 (Rm * Rmᵀ - 1) = gramDef k L R := by
    unfold frob2 gramDef
    rw [← sum2_fin k k (fun n n' => (∑ v ∈ range L, R n v * R n' v - if n = n' then 1 else 0) ^ 2)]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [sub_apply, mul_apply, transpose_apply, one_apply, Rm, Fin.ext_iff]
    rw [Fin.sum_univ_eq_sum_range (fun v => R i v * R j v) L]
  obtain ⟨S, hS, hd⟩ := lowdin Rm (by rwa [hg])
  refine ⟨ofMat S, ?_, ?_⟩
  · intro n hn n' hn'
    have e := congrFun (congrFun hS ⟨n, hn⟩) ⟨n', hn'⟩
    simp only [mul_apply, transpose_apply, one_apply, Fin.mk.injEq] at e
    rw [← e, ← Fin.sum_univ_eq_sum_range (fun v => ofMat S n v * ofMat S n' v) L]
    refine sum_congr rfl fun v _ => ?_
    simp only [ofMat, dif_pos (And.intro hn v.isLt), dif_pos (And.intro hn' v.isLt)]
  · rw [← hg]
    refine le_trans (le_of_eq ?_) hd
    unfold rowDist2 frob2
    rw [← sum2_fin k L (fun n v => (ofMat S n v - R n v) ^ 2)]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [ofMat_fin]
    rfl

/-- **Completion.** Exactly orthonormal rows `P_0 … P_{k-1}` in `ℝ^L` have `k ≤ L` and are
completed by exactly `L - k` rows to a resolution of the identity. -/
theorem exists_completion_nat (k L : ℕ) (P : ℕ → ℕ → ℝ) (hP : OrthRows k L P) :
    k ≤ L ∧ ∃ C : ℕ → ℕ → ℝ, ∀ v < L, ∀ v' < L,
      ∑ n ∈ range k, P n v * P n v' + ∑ n ∈ range (L - k), C n v * C n v' =
        if v = v' then 1 else 0 := by
  let w : Fin k → EuclideanSpace ℝ (Fin L) := fun n => (WithLp.equiv 2 (Fin L → ℝ)).symm
    (fun v => P n v)
  have hin : ∀ n n' : Fin k, inner (w n) (w n') = ∑ v ∈ range L, P n v * P n' v := by
    intro n n'
    rw [← Fin.sum_univ_eq_sum_range (fun v => P n v * P n' v) L]
    simp only [w, PiLp.inner_apply, WithLp.equiv_symm_pi_apply, RCLike.inner_apply, conj_trivial]
    exact sum_congr rfl fun v _ => mul_comm _ _
  have hw : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro n n'
    rw [hin, hP n n.isLt n' n'.isLt]
    simp [Fin.ext_iff]
  have hkL : k ≤ L := by
    have := hw.linearIndependent.fintype_card_le_finrank
    simpa using this
  refine ⟨hkL, ?_⟩
  let v' : Fin L → EuclideanSpace ℝ (Fin L) := fun i => if h : (i : ℕ) < k then w ⟨i, h⟩ else 0
  let s : Set (Fin L) := {i | (i : ℕ) < k}
  have hv : Orthonormal ℝ (s.restrict v') := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : (i : ℕ) < k := hi
    have hj' : (j : ℕ) < k := hj
    simp only [Set.restrict_apply, v', dif_pos hi', dif_pos hj']
    rw [orthonormal_iff_ite.mp hw]
    simp [Fin.ext_iff]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp) hv
  have hcomp : ∀ x y : Fin L, ∑ i : Fin L, b i x * b i y = if x = y then 1 else 0 := by
    intro x y
    have := b.sum_inner_mul_inner (EuclideanSpace.single x 1) (EuclideanSpace.single y 1)
    simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
      conj_trivial, one_mul, mul_one, EuclideanSpace.single_apply] at this
    rw [this]
    by_cases h : x = y
    · subst h; simp
    · simp [h, Ne.symm h]
  let B : ℕ → ℕ → ℝ := fun i v => if h : i < L ∧ v < L then b ⟨i, h.1⟩ ⟨v, h.2⟩ else 0
  have hBP : ∀ i < k, ∀ v < L, B i v = P i v := by
    intro i hi v hv
    have hiL : i < L := lt_of_lt_of_le hi hkL
    simp only [B, dif_pos (And.intro hiL hv)]
    rw [hb ⟨i, hiL⟩ hi]
    simp only [v', dif_pos hi, w]
    rfl
  refine ⟨fun n v => B (k + n) v, fun v hv v' hv' => ?_⟩
  have e2 : ∑ i ∈ range L, B i v * B i v' = ∑ i : Fin L, b i ⟨v, hv⟩ * b i ⟨v', hv'⟩ := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => B i v * B i v') L]
    exact sum_congr rfl fun i _ => by simp [B, i.isLt, hv, hv']
  rw [hcomp, ← sum_range_add_sum_Ico _ hkL, sum_Ico_eq_sum_range] at e2
  simp only [Fin.mk.injEq] at e2
  rw [← e2]
  congr 1
  exact sum_congr rfl fun n hn => by
    rw [hBP n (mem_range.mp hn) v hv, hBP n (mem_range.mp hn) v' hv']

end GW.Bridge.Lowdin
