/-
A3(a), stage S1: the fermionic Fock space of `n` spin-orbitals, for general `n`.

Basis: `Finset (Fin n)`, the set of occupied modes. Jordan-Wigner sign
`sgn S p = (-1)^#{k ∈ S | k < p}`. The annihilation operator is the real matrix

  (c_p)_{T S} = sgn S p   if p ∈ S and T = S \ {p},   0 otherwise,

and `c_p† = c_pᵀ`. This generalizes `GW/Endpoint/HubbardDimerFock.lean` (n = 4,
there checked by `decide +kernel`) to arbitrary `n`, with the canonical
anticommutation relations PROVED for all `n` (`ann_mul_cre_add`, `ann_mul_ann_add`,
`cre_mul_cre_add`).

Reuse decision: mathlib's `ExteriorAlgebra` with `CliffordAlgebra.contractLeft`
gives the CAR abstractly, but the pinned version has no ready basis indexed by
finsets, inner product or transpose/adjoint for it, and every later stage needs
concrete matrices (resolvents, determinants, transposes). The explicit
Jordan-Wigner matrices are therefore used, following the dimer file.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

namespace GW.Endpoint.ManyBody

open Matrix Finset

variable {n : ℕ}

/-- The Fock basis: sets of occupied spin-orbitals. -/
abbrev Fock (n : ℕ) := Finset (Fin n)

/-- Jordan-Wigner sign `(-1)^{#occupied modes below p}`. -/
def sgn (S : Fock n) (p : Fin n) : ℝ := (-1) ^ (S.filter (· < p)).card

theorem sgn_sq (S : Fock n) (p : Fin n) : sgn S p * sgn S p = 1 := by
  unfold sgn; rw [← pow_add, ← two_mul, pow_mul]; norm_num

theorem sgn_insert_self (S : Fock n) (p : Fin n) : sgn (insert p S) p = sgn S p := by
  unfold sgn; congr 2
  ext k; simp only [mem_filter, mem_insert]
  constructor
  · rintro ⟨h | h, hk⟩
    · exact absurd (h ▸ hk) (lt_irrefl _)
    · exact ⟨h, hk⟩
  · rintro ⟨h, hk⟩; exact ⟨Or.inr h, hk⟩

theorem sgn_erase_self (S : Fock n) (p : Fin n) : sgn (S.erase p) p = sgn S p := by
  unfold sgn; congr 2
  ext k; simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨_, h⟩, hk⟩; exact ⟨h, hk⟩
  · rintro ⟨h, hk⟩; exact ⟨⟨ne_of_lt hk, h⟩, hk⟩

/-- Inserting `p ∉ S` flips the sign seen by `q` iff `p < q`. -/
theorem sgn_insert {S : Fock n} {p : Fin n} (hp : p ∉ S) (q : Fin n) :
    sgn (insert p S) q = if p < q then -sgn S q else sgn S q := by
  unfold sgn
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_not_mem (by simp [hp])]; ring
  · rfl

/-- Erasing `p ∈ S` flips the sign seen by `q` iff `p < q`. -/
theorem sgn_erase {S : Fock n} {p : Fin n} (hp : p ∈ S) (q : Fin n) :
    sgn (S.erase p) q = if p < q then -sgn S q else sgn S q := by
  have h := sgn_insert (S := S.erase p) (p := p) (by simp) q
  rw [insert_erase hp] at h
  split_ifs with hpq
  · rw [if_pos hpq] at h; rw [h]; ring
  · rw [if_neg hpq] at h; exact h.symm

/-! ### Annihilation and creation operators -/

/-- Annihilation operator `c_p` (column index = input state). -/
def ann (p : Fin n) : Matrix (Fock n) (Fock n) ℝ :=
  Matrix.of fun T S => if p ∈ S ∧ T = S.erase p then sgn S p else 0

/-- Creation operator `c_p† = c_pᵀ` (real matrices: adjoint = transpose). -/
def cre (p : Fin n) : Matrix (Fock n) (Fock n) ℝ := (ann p)ᵀ

theorem ann_mulVec (p : Fin n) (f : Fock n → ℝ) (T : Fock n) :
    (ann p *ᵥ f) T = if p ∈ T then 0 else sgn T p * f (insert p T) := by
  simp only [mulVec, dotProduct, ann, of_apply]
  split_ifs with hT
  · apply sum_eq_zero; intro S _
    rw [if_neg]; · ring
    rintro ⟨_, rfl⟩; simp at hT
  · rw [sum_eq_single (insert p T)]
    · rw [if_pos ⟨mem_insert_self _ _, by rw [erase_insert hT]⟩, sgn_insert_self]
    · intro S _ hS
      rw [if_neg]; · ring
      rintro ⟨hp, rfl⟩; exact hS (insert_erase hp).symm
    · simp

theorem cre_mulVec (p : Fin n) (f : Fock n → ℝ) (T : Fock n) :
    (cre p *ᵥ f) T = if p ∈ T then sgn T p * f (T.erase p) else 0 := by
  simp only [mulVec, dotProduct, cre, ann, transpose_apply, of_apply]
  split_ifs with hT
  · rw [sum_eq_single (T.erase p)]
    · rw [if_pos ⟨hT, rfl⟩]
    · intro S _ hS; rw [if_neg]; · ring
      rintro ⟨_, rfl⟩; exact hS rfl
    · simp
  · apply sum_eq_zero; intro S _; rw [if_neg]; · ring
    rintro ⟨h, _⟩; exact hT h

/-- Matrices on the Fock space are determined by their action on vectors. -/
theorem ext_mulVec {M N : Matrix (Fock n) (Fock n) ℝ} (h : ∀ f, M *ᵥ f = N *ᵥ f) : M = N :=
  ext_of_mulVec_single fun _ => h _

/-! ### Canonical anticommutation relations, for every `n` -/

/-- `{c_p, c_q†} = δ_pq`. -/
theorem ann_mul_cre_add (p q : Fin n) :
    ann p * cre q + cre q * ann p = if p = q then 1 else 0 := by
  apply ext_mulVec; intro f; funext T
  simp only [add_mulVec, ← mulVec_mulVec, Pi.add_apply, ann_mulVec, cre_mulVec]
  by_cases hpq : p = q
  · subst hpq
    simp only [if_true, one_mulVec]
    by_cases hT : p ∈ T
    · simp only [hT, if_true, mem_erase, ne_eq, not_true_eq_false, false_and, if_false,
        insert_erase hT, sgn_erase_self]
      rw [← mul_assoc, sgn_sq, one_mul, zero_add]
    · simp only [hT, if_false, mem_insert_self, if_true, erase_insert hT, sgn_insert_self]
      rw [← mul_assoc, sgn_sq, one_mul, add_zero]
  · simp only [hpq, if_false, zero_mulVec, Pi.zero_apply]
    have hqp : q ≠ p := Ne.symm hpq
    by_cases hp : p ∈ T <;> by_cases hq : q ∈ T
    · simp [hp, hq, hpq]
    · simp [hp, hq, mem_insert, hqp, hpq]
    · simp only [hp, hq, if_false, if_true, mem_insert, hqp, false_or, mem_erase, ne_eq, hpq,
        not_false_eq_true, true_and]
      rw [sgn_insert hp, sgn_erase hq, erase_insert_of_ne hpq]
      rcases lt_or_gt_of_ne hpq with h | h
      · rw [if_pos h, if_neg (not_lt.mpr h.le)]; ring
      · rw [if_neg (not_lt.mpr h.le), if_pos h]; ring
    · simp [hp, hq, hpq, hqp]

/-- `{c_p, c_q} = 0`. -/
theorem ann_mul_ann_add (p q : Fin n) : ann p * ann q + ann q * ann p = 0 := by
  apply ext_mulVec; intro f; funext T
  simp only [add_mulVec, ← mulVec_mulVec, Pi.add_apply, ann_mulVec, zero_mulVec, Pi.zero_apply]
  by_cases hpq : p = q
  · subst hpq; by_cases hp : p ∈ T <;> simp [hp]
  by_cases hp : p ∈ T <;> by_cases hq : q ∈ T
  · simp [hp, hq]
  · simp [hp, hq]
  · simp [hp, hq]
  · simp only [hp, hq, if_false, mem_insert, Ne.symm hpq, hpq, false_or]
    rw [sgn_insert hp, sgn_insert hq, insert_comm]
    rcases lt_or_gt_of_ne hpq with h | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le)]; ring
    · rw [if_neg (not_lt.mpr h.le), if_pos h]; ring

/-- `{c_p†, c_q†} = 0`. -/
theorem cre_mul_cre_add (p q : Fin n) : cre p * cre q + cre q * cre p = 0 := by
  have h := congrArg transpose (ann_mul_ann_add q p)
  simpa [transpose_add, transpose_mul, cre] using h

theorem cre_transpose (p : Fin n) : (cre p)ᵀ = ann p := by simp [cre]
theorem ann_transpose (p : Fin n) : (ann p)ᵀ = cre p := rfl

/-- CAR in the rewriting form used below. -/
theorem ann_mul_cre (p q : Fin n) :
    ann p * cre q = (if p = q then 1 else 0) - cre q * ann p := by
  rw [← ann_mul_cre_add]; abel

theorem ann_mul_ann (p q : Fin n) : ann p * ann q = -(ann q * ann p) := by
  rw [eq_neg_iff_add_eq_zero, ann_mul_ann_add]

theorem cre_mul_cre (p q : Fin n) : cre p * cre q = -(cre q * cre p) := by
  rw [eq_neg_iff_add_eq_zero, cre_mul_cre_add]

theorem ann_mul_self (p : Fin n) : ann p * ann p = 0 := by
  have h := ann_mul_ann_add p p
  rw [← two_smul ℝ] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

theorem cre_mul_self (p : Fin n) : cre p * cre p = 0 := by
  have h := cre_mul_cre_add p p
  rw [← two_smul ℝ] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

/-! ### Number operators and the one-body Hamiltonian `H0 = Σ ε_p c_p† c_p` -/

/-- `n_p = c_p† c_p` is diagonal with the occupation of `p`. -/
theorem num_mulVec (p : Fin n) (f : Fock n → ℝ) (T : Fock n) :
    ((cre p * ann p) *ᵥ f) T = if p ∈ T then f T else 0 := by
  rw [← mulVec_mulVec, cre_mulVec]
  split_ifs with hT
  · rw [ann_mulVec, if_neg (by simp), insert_erase hT, sgn_erase_self, ← mul_assoc, sgn_sq,
      one_mul]
  · rfl

theorem num_eq_diagonal (p : Fin n) :
    cre p * ann p = diagonal (fun S : Fock n => if p ∈ S then (1 : ℝ) else 0) := by
  apply ext_mulVec; intro f; funext T
  rw [num_mulVec, mulVec_diagonal]; split_ifs <;> ring

/-- Energy of a basis state: `E S = Σ_{p ∈ S} ε_p`. -/
def energy (ε : Fin n → ℝ) (S : Fock n) : ℝ := ∑ p ∈ S, ε p

/-- The one-body Hamiltonian `H0 = Σ_p ε_p c_p† c_p`. -/
def H0 (ε : Fin n → ℝ) : Matrix (Fock n) (Fock n) ℝ := ∑ p, ε p • (cre p * ann p)

/-- `H0` is diagonal in the occupation basis with eigenvalue `Σ_{p∈S} ε_p`. -/
theorem H0_eq_diagonal (ε : Fin n → ℝ) : H0 ε = diagonal (energy ε) := by
  ext S T
  simp only [H0, num_eq_diagonal, Matrix.sum_apply, smul_apply, diagonal_apply, smul_eq_mul]
  by_cases h : S = T
  · subst h; simp only [if_true, mul_ite, mul_one, mul_zero, energy]
    rw [sum_ite_mem, univ_inter]
  · simp [h]

/-- Particle number `N = Σ_p c_p† c_p`, diagonal with the cardinality. -/
theorem numOp_eq_diagonal :
    (∑ p : Fin n, cre p * ann p) = diagonal (fun S : Fock n => (S.card : ℝ)) := by
  have h := H0_eq_diagonal (fun _ : Fin n => (1 : ℝ))
  simp only [H0, one_smul] at h
  rw [h]; funext S; unfold energy; simp

/-! ### Commutators with `H0` -/

theorem num_mul_cre (q p : Fin n) :
    cre q * ann q * cre p = cre p * (cre q * ann q) + (if q = p then cre p else 0) := by
  have h1 : cre q * ann q * cre p = cre q * (if q = p then 1 else 0) - cre q * cre p * ann q := by
    rw [mul_assoc, ann_mul_cre, mul_sub, mul_assoc]
  rw [h1, cre_mul_cre]
  split_ifs with h
  · subst h; simp only [mul_one, neg_mul, sub_neg_eq_add, mul_assoc]; abel
  · simp only [mul_zero, neg_mul, sub_neg_eq_add, mul_assoc, zero_add, add_zero]

theorem num_mul_ann (q p : Fin n) :
    cre q * ann q * ann p = ann p * (cre q * ann q) - (if q = p then ann p else 0) := by
  have h2 : cre q * ann p = (if p = q then 1 else 0) - ann p * cre q := by
    rw [ann_mul_cre]; abel
  have h1 : cre q * ann q * ann p = -((cre q * ann p) * ann q) := by
    rw [mul_assoc, ann_mul_ann, mul_neg, mul_assoc]
  rw [h1, h2]
  by_cases h : p = q
  · subst h; simp only [if_true, one_mul, sub_mul, neg_sub, mul_assoc]
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp only [zero_mul, zero_sub, neg_mul, neg_neg, mul_assoc, sub_zero]

/-- `[H0, c_p†] = ε_p c_p†`. -/
theorem H0_mul_cre (ε : Fin n → ℝ) (p : Fin n) :
    H0 ε * cre p = cre p * H0 ε + ε p • cre p := by
  simp only [H0, sum_mul, mul_sum, smul_mul_assoc, mul_smul_comm, num_mul_cre, smul_add,
    sum_add_distrib, smul_ite, smul_zero, sum_ite_eq', mem_univ, if_true]

/-- `[H0, c_p] = -ε_p c_p`. -/
theorem H0_mul_ann (ε : Fin n → ℝ) (p : Fin n) :
    H0 ε * ann p = ann p * H0 ε - ε p • ann p := by
  simp only [H0, sum_mul, mul_sum, smul_mul_assoc, mul_smul_comm, num_mul_ann, smul_sub,
    sum_sub_distrib, smul_ite, smul_zero, sum_ite_eq', mem_univ, if_true]

/-! ### Eigenvectors of `H0` -/

/-- `x` is an eigenvector of `H0 ε` with eigenvalue `e` (zero allowed). -/
def IsEig (ε : Fin n → ℝ) (e : ℝ) (x : Fock n → ℝ) : Prop := H0 ε *ᵥ x = e • x

theorem IsEig.cre {ε : Fin n → ℝ} {e : ℝ} {x : Fock n → ℝ} (h : IsEig ε e x) (p : Fin n) :
    IsEig ε (e + ε p) (cre p *ᵥ x) := by
  unfold IsEig at *
  rw [mulVec_mulVec, H0_mul_cre, add_mulVec, ← mulVec_mulVec, h, mulVec_smul, smul_mulVec_assoc,
    add_smul]

theorem IsEig.ann {ε : Fin n → ℝ} {e : ℝ} {x : Fock n → ℝ} (h : IsEig ε e x) (p : Fin n) :
    IsEig ε (e - ε p) (ann p *ᵥ x) := by
  unfold IsEig at *
  rw [mulVec_mulVec, H0_mul_ann, sub_mulVec, ← mulVec_mulVec, h, mulVec_smul, smul_mulVec_assoc,
    sub_smul]

theorem IsEig.add {ε : Fin n → ℝ} {e : ℝ} {x y : Fock n → ℝ} (hx : IsEig ε e x)
    (hy : IsEig ε e y) : IsEig ε e (x + y) := by
  unfold IsEig at *; rw [mulVec_add, hx, hy, smul_add]

theorem IsEig.smul {ε : Fin n → ℝ} {e : ℝ} {x : Fock n → ℝ} (hx : IsEig ε e x) (c : ℝ) :
    IsEig ε e (c • x) := by
  unfold IsEig at *; rw [mulVec_smul, hx, smul_comm]

theorem IsEig.zero (ε : Fin n → ℝ) (e : ℝ) : IsEig ε e (0 : Fock n → ℝ) := by
  simp [IsEig]

theorem IsEig.sum {ι : Type*} (s : Finset ι) {ε : Fin n → ℝ} {e : ℝ} {x : ι → Fock n → ℝ}
    (h : ∀ i ∈ s, IsEig ε e (x i)) : IsEig ε e (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsEig.zero ε e
  | @insert a s hi ih =>
    rw [sum_insert hi]
    exact (h _ (mem_insert_self _ _)).add (ih fun j hj => h j (mem_insert_of_mem hj))

/-- On an eigenvector, a function of the energy acts as the scalar at the eigenvalue. This
is how every resolvent below is evaluated (Lean's `(0 : ℝ)⁻¹ = 0` is harmless here: the
identity holds for every function `φ`). -/
theorem IsEig.diagonal_mulVec {ε : Fin n → ℝ} {e : ℝ} {x : Fock n → ℝ} (h : IsEig ε e x)
    (φ : ℝ → ℝ) : diagonal (fun S => φ (energy ε S)) *ᵥ x = φ e • x := by
  unfold IsEig at h
  rw [H0_eq_diagonal] at h
  funext S
  have hS := congrFun h S
  simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hS ⊢
  by_cases hx : x S = 0
  · simp [hx]
  · have : energy ε S = e := mul_right_cancel₀ hx hS
    rw [this]

end GW.Endpoint.ManyBody
