/-
Endpoint E1.4, certificate soundness (2/3): the componentwise Neumann
enclosure of a matrix inverse (`bgw/endpoint/iv.py`, `inverse_cw`) and the
power-of-two diagonal balancing used around it (`bgw/endpoint/cert.py:126-133`,
in `epsinv_iv`).

`inverse_cw(A, terms=m)` computes, from a float approximate inverse `R`:
`E ⊇ 1 - R A` (interval), `F = mag E`, `β ≥` every row sum of `F`, checks
`β < 1`, `P ≥ F |R|`, the partial sum `S ≥ ∑_{k=0}^{m} F^k P`,
`bpow ≥ β^(m+1)`, `tail ≥ bpow · (max row sum of P) / down(1 - β)`,
`B ≥ S + tail`, and returns `[R - B, R + B]` (rounded outward).

Main results:

* `neumann_cw`: for real square `A, R, F, P` with `|1 - R A| ≤ F` entrywise,
  every row sum of `F` at most `β < 1`, `F |R| ≤ P` entrywise and every row sum
  of `P` at most `ρ`: `A` is invertible and for every `m`, `i`, `j`
  `|A⁻¹ i j - R i j| ≤ (∑_{k=0}^{m} F^k P) i j + β^(m+1) ρ / (1 - β)`.
* `neumann_cw_set`: the same for every member of a set of matrices sharing one
  `F` (how it is applied to an interval matrix `A`).
* `inverse_cw_sound`: the conclusion in the exact shape of the code's
  computed quantities `T_k` (the `term` loop), `S`, `bpow`, `d = down(1-β)`,
  `tail`, `B`.
* `balance_inv`, `inv_mem_of_balanced`: with `s i > 0` and the balanced matrix
  `balance s A i j = A i j * (s j / s i)` (this is `eps * scale`,
  `scale = s[None,:] / s[:,None]`, cert.py:129-130), `(balance s A)⁻¹ =
  balance s A⁻¹`, so an enclosure `[lo, hi]` of `(balance s A)⁻¹ i j` gives
  `[lo * (s i / s j), hi * (s i / s j)]` for `A⁻¹ i j`; `s i / s j` is exactly
  `back = s[:,None] / s[None,:]` (cert.py:132-133).

Named gaps (not proved here): that the Python implements these hypotheses
(each is discharged in exact reals by the `CertInterval` lemmas under the IEEE
rounding hypothesis stated there), and that cert.py's quotients `scale` and `back` of
powers of two are the exact `s j / s i` and `s i / s j` it takes them to be (`I.exact`).
The balancing products `eps * I.exact(scale)` and `invb * I.exact(back)` are
outward-rounded interval products (`CertInterval.mul_mem` under the IEEE hypothesis), so
their exactness is no longer assumed (cert.py relied on it before commit 69e16ee,
LEAN-CERT finding 3; see the handoff `.agent/handoffs/LEAN-CERT.md`).
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic

namespace GW.Endpoint.Cert

open Matrix Finset Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise domination `|A| ≤ F`. -/
def Dom (A F : Matrix ι ι ℝ) : Prop := ∀ i j, |A i j| ≤ F i j

/-- Every row sum of `Y` is at most `c`. -/
def RowLe (Y : Matrix ι ι ℝ) (c : ℝ) : Prop := ∀ i, ∑ j, Y i j ≤ c

/-- The entrywise absolute value. -/
def absM (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := Matrix.of fun i j => |A i j|

section lemmas

variable {A B E F G Y : Matrix ι ι ℝ}

omit [Fintype ι] [DecidableEq ι] in
theorem Dom.nonneg (h : Dom A F) (i j : ι) : 0 ≤ F i j := (abs_nonneg _).trans (h i j)

omit [Fintype ι] [DecidableEq ι] in
theorem dom_absM (A : Matrix ι ι ℝ) : Dom A (absM A) := fun _ _ => le_rfl

omit [Fintype ι] [DecidableEq ι] in
theorem dom_mono (h : Dom A F) (hFG : ∀ i j, F i j ≤ G i j) : Dom A G :=
  fun i j => (h i j).trans (hFG i j)

omit [DecidableEq ι] in
theorem dom_mul (hA : Dom A F) (hB : Dom B G) : Dom (A * B) (F * G) := by
  intro i j
  simp only [mul_apply]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) (hA.nonneg i k)

omit [Fintype ι] in
theorem dom_one : Dom (1 : Matrix ι ι ℝ) 1 := by
  intro i j
  by_cases h : i = j <;> simp [one_apply, h]

theorem dom_pow (h : Dom E F) (k : ℕ) : Dom (E ^ k) (F ^ k) := by
  induction k with
  | zero => simpa using dom_one
  | succ k ih => rw [pow_succ, pow_succ]; exact dom_mul ih h

omit [Fintype ι] [DecidableEq ι] in
theorem dom_add (hA : Dom A F) (hB : Dom B G) : Dom (A + B) (F + G) := fun i j => by
  simp only [add_apply]; exact (abs_add _ _).trans (add_le_add (hA i j) (hB i j))

omit [Fintype ι] [DecidableEq ι] in
theorem dom_sum (s : Finset ℕ) (A F : ℕ → Matrix ι ι ℝ) (h : ∀ k ∈ s, Dom (A k) (F k)) :
    Dom (∑ k ∈ s, A k) (∑ k ∈ s, F k) := by
  intro i j
  rw [Matrix.sum_apply, Matrix.sum_apply]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => h k hk i j)

omit [DecidableEq ι] in
theorem matMul_nonneg (hF : ∀ i j, 0 ≤ F i j) (hY : ∀ i j, 0 ≤ Y i j) (i j : ι) :
    0 ≤ (F * Y) i j :=
  sum_nonneg fun k _ => mul_nonneg (hF i k) (hY k j)

omit [DecidableEq ι] in
theorem matMul_le_matMul_left (hF : ∀ i j, 0 ≤ F i j) {Y Y' : Matrix ι ι ℝ}
    (h : ∀ i j, Y i j ≤ Y' i j) (i j : ι) : (F * Y) i j ≤ (F * Y') i j :=
  sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k j) (hF i k)

theorem matPow_nonneg (hF : ∀ i j, 0 ≤ F i j) (k : ℕ) (i j : ι) : 0 ≤ (F ^ k) i j := by
  induction k generalizing i j with
  | zero => by_cases h : i = j <;> simp [one_apply, h]
  | succ k ih => rw [pow_succ]; exact matMul_nonneg ih hF i j

omit [DecidableEq ι] in
theorem rowLe_mul (hF0 : ∀ i j, 0 ≤ F i j) {β c : ℝ} (hF : RowLe F β) (hY : RowLe Y c)
    (hc : 0 ≤ c) : RowLe (F * Y) (β * c) := by
  intro i
  simp only [mul_apply]
  rw [sum_comm]
  simp_rw [← mul_sum]
  calc ∑ k, F i k * ∑ j, Y k j ≤ ∑ k, F i k * c :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hY k) (hF0 i k)
    _ = (∑ k, F i k) * c := by rw [sum_mul]
    _ ≤ β * c := mul_le_mul_of_nonneg_right (hF i) hc

theorem rowLe_pow_mul (hF0 : ∀ i j, 0 ≤ F i j) {β c : ℝ} (hβ0 : 0 ≤ β) (hF : RowLe F β)
    (hY : RowLe Y c) (hc : 0 ≤ c) (k : ℕ) :
    RowLe (F ^ k * Y) (β ^ k * c) := by
  induction k with
  | zero => simpa using hY
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, pow_succ', mul_assoc]
    exact rowLe_mul hF0 hF ih (mul_nonneg (pow_nonneg hβ0 k) hc)

omit [DecidableEq ι] in
theorem entry_le_rowSum (hY0 : ∀ i j, 0 ≤ Y i j) (i j : ι) : Y i j ≤ ∑ j', Y i j' :=
  single_le_sum (fun j' _ => hY0 i j') (mem_univ j)

end lemmas

/-- If every row sum of `F ≥ |E|` is at most `β < 1`, then `1 - E` is
invertible (its kernel is trivial: `v = E v` forces `max |v| ≤ β max |v|`). -/
theorem det_one_sub_ne_zero {E F : Matrix ι ι ℝ} {β : ℝ} (hF : Dom E F) (hβ : RowLe F β)
    (hβ1 : β < 1) : (1 - E).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hvE : E *ᵥ v = v := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at hv; exact hv.symm
  obtain ⟨i1, hi1⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push_neg at h; exact hv0 (funext h)
  haveI : Nonempty ι := ⟨i1⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max fun i => |v i|
  have key : |v i0| ≤ β * |v i0| := by
    calc |v i0| = |∑ j, E i0 j * v j| := by
          conv_lhs => rw [← hvE]
          simp only [mulVec, dotProduct]
      _ ≤ ∑ j, |E i0 j| * |v j| := (abs_sum_le_sum_abs _ _).trans (by simp [abs_mul])
      _ ≤ ∑ j, F i0 j * |v i0| :=
          sum_le_sum fun j _ => mul_le_mul (hF i0 j) (hi0 j) (abs_nonneg _) (hF.nonneg i0 j)
      _ = (∑ j, F i0 j) * |v i0| := by rw [sum_mul]
      _ ≤ β * |v i0| := mul_le_mul_of_nonneg_right (hβ i0) (abs_nonneg _)
  have h0 : |v i0| ≤ 0 := by nlinarith [abs_nonneg (v i0)]
  exact hi1 (abs_nonpos_iff.mp ((hi0 i1).trans h0))

/-- **Componentwise Neumann enclosure** (matches `iv.inverse_cw`).
For real square `A, R` with `F ≥ |1 - R A|` entrywise, every row sum of `F` at
most `β < 1`, `P ≥ F |R|` entrywise and every row sum of `P` at most `ρ`:
`A` is invertible and, for every `m` and all `i, j`,
`|A⁻¹ i j - R i j| ≤ (∑_{k=0}^{m} F^k P) i j + β^(m+1) ρ / (1 - β)`. -/
theorem neumann_cw (A R F P : Matrix ι ι ℝ) (β ρ : ℝ) (hF : Dom (1 - R * A) F)
    (hβ : RowLe F β) (hβ1 : β < 1) (hP : ∀ i j, (F * absM R) i j ≤ P i j)
    (hρ : RowLe P ρ) :
    IsUnit A ∧ ∀ m i j, |A⁻¹ i j - R i j| ≤
      (∑ k ∈ range (m + 1), F ^ k * P) i j + β ^ (m + 1) * ρ / (1 - β) := by
  set E := 1 - R * A with hE
  -- invertibility
  have hRA : (R * A).det ≠ 0 := by
    have := det_one_sub_ne_zero hF hβ hβ1
    rwa [hE, sub_sub_cancel] at this
  have hdetA : A.det ≠ 0 := by
    rw [det_mul] at hRA; exact right_ne_zero_of_mul hRA
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hdetA
  refine ⟨(Matrix.isUnit_iff_isUnit_det A).mpr hA, ?_⟩
  intro m i j
  -- the fixed-point identity X = E R + E X for X = A⁻¹ - R
  set X := A⁻¹ - R with hXdef
  have hEA : E * A⁻¹ = X := by
    rw [hE, sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv A hA,
      Matrix.mul_one]
  have hX : X = E * R + E * X := by
    rw [← Matrix.mul_add, hXdef, add_sub_cancel, hEA]
  -- the finite expansion X = ∑_{k≤m} E^k (E R) + E^(m+1) X
  have hexp : ∀ m : ℕ, X = (∑ k ∈ range (m + 1), E ^ k * (E * R)) + E ^ (m + 1) * X := by
    intro m
    induction m with
    | zero => simpa using hX
    | succ m ih =>
      conv_lhs => rw [ih]
      conv_lhs => rw [hX]
      rw [Matrix.mul_add, ← Matrix.mul_assoc (E ^ (m + 1)) E X, ← pow_succ,
        sum_range_succ (fun k => E ^ k * (E * R)) (m + 1)]
      exact (add_assoc _ _ _).symm
  have hF0 : ∀ i j, 0 ≤ F i j := hF.nonneg
  have hER : Dom (E * R) P := dom_mono (dom_mul hF (dom_absM R)) hP
  have hβ0 : 0 ≤ β := (sum_nonneg fun j _ => hF0 i j).trans (hβ i)
  have hρ0 : 0 ≤ ρ :=
    (sum_nonneg fun j _ => (hER.nonneg i j)).trans (hρ i)
  -- the row-sum bound on |X|
  haveI : Nonempty ι := ⟨i⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max fun i => ∑ j, absM X i j
  set r := ∑ j, absM X i0 j with hr
  have hr0 : 0 ≤ r := sum_nonneg fun j _ => abs_nonneg _
  have hXrow : RowLe (absM X) r := fun i => hi0 i
  have hdomX : Dom X (P + F * absM X) := by
    have := dom_add hER (dom_mul hF (dom_absM X))
    rwa [← hX] at this
  have hrle : r ≤ ρ + β * r := by
    calc r = ∑ j, |X i0 j| := rfl
      _ ≤ ∑ j, (P + F * absM X) i0 j := sum_le_sum fun j _ => hdomX i0 j
      _ = ∑ j, P i0 j + ∑ j, (F * absM X) i0 j := by simp [sum_add_distrib]
      _ ≤ ρ + β * r := add_le_add (hρ i0) (rowLe_mul hF0 hβ hXrow hr0 i0)
  have hrb : r ≤ ρ / (1 - β) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  -- assemble
  have hdom : Dom X ((∑ k ∈ range (m + 1), F ^ k * P) + F ^ (m + 1) * absM X) := by
    have := dom_add (dom_sum (range (m + 1)) _ _ fun k _ => dom_mul (dom_pow hF k) hER)
      (dom_mul (dom_pow hF (m + 1)) (dom_absM X))
    rwa [← hexp m] at this
  have htail : (F ^ (m + 1) * absM X) i j ≤ β ^ (m + 1) * ρ / (1 - β) := by
    have hnn : ∀ a b, 0 ≤ (F ^ (m + 1) * absM X) a b :=
      matMul_nonneg (matPow_nonneg hF0 (m + 1)) (fun _ _ => abs_nonneg _)
    calc (F ^ (m + 1) * absM X) i j ≤ ∑ j', (F ^ (m + 1) * absM X) i j' :=
          entry_le_rowSum hnn i j
      _ ≤ β ^ (m + 1) * r :=
          rowLe_pow_mul hF0 hβ0 hβ hXrow hr0 (m + 1) i
      _ ≤ β ^ (m + 1) * (ρ / (1 - β)) :=
          mul_le_mul_of_nonneg_left hrb (pow_nonneg hβ0 _)
      _ = β ^ (m + 1) * ρ / (1 - β) := by rw [mul_div_assoc]
  have := hdom i j
  rw [add_apply, hXdef, sub_apply] at this
  linarith

/-- The set form, as applied to an interval matrix: one `F` dominating
`|1 - R A0|` for every member `A0` of a set gives the enclosure for all of
them simultaneously. -/
theorem neumann_cw_set (S : Set (Matrix ι ι ℝ)) (R F P : Matrix ι ι ℝ) (β ρ : ℝ)
    (hF : ∀ A0 ∈ S, Dom (1 - R * A0) F) (hβ : RowLe F β) (hβ1 : β < 1)
    (hP : ∀ i j, (F * absM R) i j ≤ P i j) (hρ : RowLe P ρ) :
    ∀ A0 ∈ S, IsUnit A0 ∧ ∀ m i j, |A0⁻¹ i j - R i j| ≤
      (∑ k ∈ range (m + 1), F ^ k * P) i j + β ^ (m + 1) * ρ / (1 - β) :=
  fun A0 hA0 => neumann_cw A0 R F P β ρ (hF A0 hA0) hβ hβ1 hP hρ

/-- The `bpow` loop of `inverse_cw` (`bpow = β`, then `m` times
`bpow = up(bpow * β)`): any sequence with `b 0 ≥ β` and `b (k+1) ≥ b k * β`
dominates `β^(k+1)`. (Replacing a final `0` by `5e-324`, iv.py:284-285, only
increases it.) -/
theorem pow_le_of_chain {β : ℝ} (hβ0 : 0 ≤ β) (b : ℕ → ℝ) (h0 : β ≤ b 0)
    (hs : ∀ k, b k * β ≤ b (k + 1)) (k : ℕ) : β ^ (k + 1) ≤ b k := by
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    rw [pow_succ]; exact (mul_le_mul_of_nonneg_right ih hβ0).trans (hs k)

/-- **`inverse_cw` in the shape of its computed quantities.** With `F`, `β`,
`P`, `ρ` as in `neumann_cw`; `T 0 ≥ P` and `T (k+1) ≥ F T k` entrywise for
`k < m` (the `term = _matmul_up(F, term)` loop); `S ≥ ∑_{k≤m} T k`; `bpow ≥
β^(m+1)`; `0 < d ≤ 1 - β` (`d = down(1 - β)`); `tail ≥ bpow ρ / d`;
`B ≥ S + tail` entrywise: `A0` is invertible and `R - B ≤ A0⁻¹ ≤ R + B`
entrywise. -/
theorem inverse_cw_sound (A0 R F P : Matrix ι ι ℝ) (β ρ : ℝ) (hF : Dom (1 - R * A0) F)
    (hβ : RowLe F β) (hβ1 : β < 1) (hP : ∀ i j, (F * absM R) i j ≤ P i j)
    (hρ : RowLe P ρ) (m : ℕ) (T : ℕ → Matrix ι ι ℝ) (hT0 : ∀ i j, P i j ≤ T 0 i j)
    (hT : ∀ k < m, ∀ i j, (F * T k) i j ≤ T (k + 1) i j) (S : Matrix ι ι ℝ)
    (hS : ∀ i j, ∑ k ∈ range (m + 1), T k i j ≤ S i j) (bpow : ℝ)
    (hb : β ^ (m + 1) ≤ bpow) (d : ℝ) (hd0 : 0 < d) (hd : d ≤ 1 - β) (tail : ℝ)
    (ht : bpow * ρ / d ≤ tail) (B : Matrix ι ι ℝ) (hB : ∀ i j, S i j + tail ≤ B i j) :
    IsUnit A0 ∧ ∀ i j, A0⁻¹ i j ∈ Icc (R i j - B i j) (R i j + B i j) := by
  obtain ⟨hU, hbound⟩ := neumann_cw A0 R F P β ρ hF hβ hβ1 hP hρ
  refine ⟨hU, fun i j => ?_⟩
  have hF0 : ∀ i j, 0 ≤ F i j := hF.nonneg
  have hβ0 : 0 ≤ β := (sum_nonneg fun j _ => hF0 i j).trans (hβ i)
  have hP0 : ∀ i j, 0 ≤ P i j := fun a b =>
    (matMul_nonneg hF0 (fun _ _ => abs_nonneg _) a b).trans (hP a b)
  have hρ0 : 0 ≤ ρ := (sum_nonneg fun j _ => hP0 i j).trans (hρ i)
  have hTk : ∀ k ≤ m, ∀ a b, (F ^ k * P) a b ≤ T k a b := by
    intro k
    induction k with
    | zero => intro _ a b; simpa using hT0 a b
    | succ k ih =>
      intro hk a b
      rw [pow_succ', Matrix.mul_assoc]
      exact (matMul_le_matMul_left hF0 (ih (by omega)) a b).trans (hT k (by omega) a b)
  have hsum : (∑ k ∈ range (m + 1), F ^ k * P) i j ≤ S i j := by
    rw [Matrix.sum_apply]
    exact (sum_le_sum fun k hk => hTk k (by simpa [Nat.lt_succ_iff] using hk) i j).trans
      (hS i j)
  have htl : β ^ (m + 1) * ρ / (1 - β) ≤ tail := by
    have h1 : β ^ (m + 1) * ρ ≤ bpow * ρ := mul_le_mul_of_nonneg_right hb hρ0
    have h2 : 0 ≤ bpow * ρ := (mul_nonneg (pow_nonneg hβ0 _) hρ0).trans h1
    calc β ^ (m + 1) * ρ / (1 - β) ≤ bpow * ρ / (1 - β) :=
          div_le_div_of_nonneg_right h1 (by linarith)
      _ ≤ bpow * ρ / d := div_le_div_of_nonneg_left h2 hd0 hd
      _ ≤ tail := ht
  have := abs_le.mp ((hbound m i j).trans ((add_le_add hsum htl).trans (hB i j)))
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-! ### Exact diagonal balancing (cert.py:126-133) -/

/-- The balanced matrix `A i j * (s j / s i)`, i.e. `S⁻¹ A S` for
`S = diagonal s`; cert.py forms it as `eps * scale` (an outward-rounded interval product),
`scale = s[None, :] / s[:, None]`. -/
noncomputable def balance (s : ι → ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => A i j * (s j / s i)

theorem balance_eq (s : ι → ℝ) (hs : ∀ i, s i ≠ 0) (A : Matrix ι ι ℝ) :
    balance s A = diagonal (fun i => (s i)⁻¹) * A * diagonal s := by
  ext i j
  simp only [balance, of_apply, mul_diagonal, diagonal_mul]
  field_simp [hs i]

theorem det_balance (s : ι → ℝ) (hs : ∀ i, s i ≠ 0) (A : Matrix ι ι ℝ) :
    (balance s A).det = A.det := by
  rw [balance_eq s hs, det_mul, det_mul, det_diagonal, det_diagonal, mul_comm _ A.det,
    mul_assoc, ← prod_mul_distrib]
  simp [inv_mul_cancel₀ (hs _)]

/-- `(S⁻¹ A S)⁻¹ = S⁻¹ A⁻¹ S`, entrywise: `(balance s A)⁻¹ = balance s A⁻¹`. -/
theorem balance_inv (s : ι → ℝ) (hs : ∀ i, s i ≠ 0) (A : Matrix ι ι ℝ)
    (hA : IsUnit A.det) : (balance s A)⁻¹ = balance s A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  have hD : diagonal s * diagonal (fun i => (s i)⁻¹) = 1 := by
    have h : (fun i => s i * (s i)⁻¹) = fun _ => 1 := funext fun i => mul_inv_cancel₀ (hs i)
    rw [diagonal_mul_diagonal, h, diagonal_one]
  have hD' : diagonal (fun i => (s i)⁻¹) * diagonal s = 1 := by
    have h : (fun i => (s i)⁻¹ * s i) = fun _ => 1 := funext fun i => inv_mul_cancel₀ (hs i)
    rw [diagonal_mul_diagonal, h, diagonal_one]
  rw [balance_eq s hs, balance_eq s hs]
  calc diagonal (fun i => (s i)⁻¹) * A * diagonal s * (diagonal (fun i => (s i)⁻¹) * A⁻¹ *
        diagonal s)
      = diagonal (fun i => (s i)⁻¹) * A * (diagonal s * diagonal (fun i => (s i)⁻¹)) * A⁻¹ *
        diagonal s := by simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hD, Matrix.mul_one, Matrix.mul_assoc _ A, Matrix.mul_nonsing_inv A hA,
          Matrix.mul_one, hD']

omit [Fintype ι] [DecidableEq ι] in
/-- The balanced interval matrix encloses the balanced member (`s > 0`): the
entrywise product by the positive `scale` preserves enclosures. -/
theorem balance_mem (s : ι → ℝ) (hs : ∀ i, 0 < s i) {A0 lo hi : Matrix ι ι ℝ}
    (h : ∀ i j, A0 i j ∈ Icc (lo i j) (hi i j)) (i j : ι) :
    balance s A0 i j ∈ Icc (balance s lo i j) (balance s hi i j) := by
  have hp : 0 ≤ s j / s i := (div_pos (hs j) (hs i)).le
  exact ⟨mul_le_mul_of_nonneg_right (h i j).1 hp, mul_le_mul_of_nonneg_right (h i j).2 hp⟩

/-- **Transfer back** (cert.py:132-133, `back = s[:, None] / s[None, :]`): an
enclosure `[lo, hi]` of `(balance s A)⁻¹ i j` gives
`[lo * (s i / s j), hi * (s i / s j)]` for `A⁻¹ i j`. Invertibility of the
balanced matrix (the output of `neumann_cw` on it) suffices. -/
theorem inv_mem_of_balanced (s : ι → ℝ) (hs : ∀ i, 0 < s i) (A : Matrix ι ι ℝ)
    (hA : IsUnit (balance s A).det) {i j : ι} {lo hi : ℝ}
    (h : (balance s A)⁻¹ i j ∈ Icc lo hi) :
    A⁻¹ i j ∈ Icc (lo * (s i / s j)) (hi * (s i / s j)) := by
  have hs0 : ∀ i, s i ≠ 0 := fun i => (hs i).ne'
  rw [det_balance s hs0] at hA
  rw [balance_inv s hs0 A hA] at h
  have he : A⁻¹ i j = balance s A⁻¹ i j * (s i / s j) := by
    simp only [balance, of_apply]
    field_simp [hs0 i, hs0 j]
  have hp : 0 ≤ s i / s j := (div_pos (hs i) (hs j)).le
  rw [he]
  exact ⟨mul_le_mul_of_nonneg_right h.1 hp, mul_le_mul_of_nonneg_right h.2 hp⟩

end GW.Endpoint.Cert
