/-
A3(a), stage S1/S2 support: the Slater-determinant reference state `Φ_O` (the basis
vector of the occupied set `O`) and the vacuum algebra used by every later stage.

Everything below is derived from the CAR of `Fock.lean` and the two vacuum
conditions `c_r Φ = 0` (r ∉ O) and `c_a† Φ = 0` (a ∈ O); no Wick theorem is
assumed. The overlaps proved here are the only "contractions" the second-order
self-energy needs:

* one-particle / one-hole norms (`dot_cre_phi`, `dot_ann_phi`);
* the Gram matrices of the 2p1h states `c_r† c_s† c_a Φ` and of the 2h1p states
  `c_r† c_b c_a Φ` (`gram_2p1h`, `gram_2h1p`), and the two-hole Gram matrix
  (`gram_2h`);
* the orthogonality of 2p1h/2h1p states to the 1p/1h states (`orth_1p_2p1h`,
  `orth_1h_2h1p`);
* case lemmas that split `c_i† c_j† c_l Φ` and `c_j† c_l c_k Φ` into their
  2p1h/2h1p part and their 1p/1h part (`cc_a_phi`, `c_aa_phi`).
-/
import GW.Endpoint.ManyBody.Fock

namespace GW.Endpoint.ManyBody

open Matrix Finset

variable {n : ℕ}

/-! ### Vector forms of the CAR -/

theorem ann_cre_mulVec (p q : Fin n) (w : Fock n → ℝ) :
    ann p *ᵥ cre q *ᵥ w = (if p = q then w else 0) - cre q *ᵥ ann p *ᵥ w := by
  rw [mulVec_mulVec, ann_mul_cre, sub_mulVec, mulVec_mulVec]
  split_ifs <;> simp

theorem cre_ann_mulVec (p q : Fin n) (w : Fock n → ℝ) :
    cre p *ᵥ ann q *ᵥ w = (if p = q then w else 0) - ann q *ᵥ cre p *ᵥ w := by
  have h := ann_cre_mulVec q p w
  by_cases e : p = q
  · subst e; rw [if_pos rfl] at h ⊢; rw [h]; abel
  · rw [if_neg (Ne.symm e)] at h; rw [if_neg e, h]; abel

theorem ann_ann_mulVec (p q : Fin n) (w : Fock n → ℝ) :
    ann p *ᵥ ann q *ᵥ w = -(ann q *ᵥ ann p *ᵥ w) := by
  rw [mulVec_mulVec, ann_mul_ann, neg_mulVec, mulVec_mulVec]

theorem cre_cre_mulVec (p q : Fin n) (w : Fock n → ℝ) :
    cre p *ᵥ cre q *ᵥ w = -(cre q *ᵥ cre p *ᵥ w) := by
  rw [mulVec_mulVec, cre_mul_cre, neg_mulVec, mulVec_mulVec]

theorem ann_self_mulVec (p : Fin n) (w : Fock n → ℝ) : ann p *ᵥ ann p *ᵥ w = 0 := by
  rw [mulVec_mulVec, ann_mul_self, zero_mulVec]

theorem cre_self_mulVec (p : Fin n) (w : Fock n → ℝ) : cre p *ᵥ cre p *ᵥ w = 0 := by
  rw [mulVec_mulVec, cre_mul_self, zero_mulVec]

theorem dot_ite_zero {α : Type*} [Fintype α] (c : Prop) [Decidable c] (x y : α → ℝ) :
    x ⬝ᵥ (if c then y else 0) = if c then x ⬝ᵥ y else 0 := by
  split_ifs <;> simp

theorem ite_zero_dot {α : Type*} [Fintype α] (c : Prop) [Decidable c] (x y : α → ℝ) :
    (if c then x else 0) ⬝ᵥ y = if c then x ⬝ᵥ y else 0 := by
  split_ifs <;> simp

theorem mulVec_ite_zero {α : Type*} [Fintype α] (M : Matrix α α ℝ) (c : Prop) [Decidable c]
    (y : α → ℝ) : M *ᵥ (if c then y else 0) = if c then M *ᵥ y else 0 := by
  split_ifs <;> simp

/-- Moving an operator across the (real) inner product: `c_p† = c_pᵀ`. -/
theorem cre_dot (p : Fin n) (x y : Fock n → ℝ) : (cre p *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (ann p *ᵥ y) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, ann_transpose]

theorem ann_dot (p : Fin n) (x y : Fock n → ℝ) : (ann p *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (cre p *ᵥ y) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, cre_transpose]

theorem mulVec_dot_of_symm {M : Matrix (Fock n) (Fock n) ℝ} (hM : Mᵀ = M) (x y : Fock n → ℝ) :
    (M *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (M *ᵥ y) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hM]

/-! ### The reference Slater determinant -/

/-- The Slater determinant with occupied set `O`: the basis vector `|O⟩`. -/
def phi (O : Fock n) : Fock n → ℝ := Pi.single O 1

variable {O : Fock n}

theorem ann_phi {r : Fin n} (hr : r ∉ O) : ann r *ᵥ phi O = 0 := by
  funext T
  rw [ann_mulVec]
  split_ifs with h
  · rfl
  · simp only [phi, Pi.zero_apply]
    rw [Pi.single_apply, if_neg, mul_zero]
    rintro rfl; exact hr (mem_insert_self _ _)

theorem cre_phi {a : Fin n} (ha : a ∈ O) : cre a *ᵥ phi O = 0 := by
  funext T
  rw [cre_mulVec]
  split_ifs with h
  · simp only [phi, Pi.zero_apply]
    rw [Pi.single_apply, if_neg, mul_zero]
    rintro rfl; simp at ha
  · rfl

theorem phi_dot_phi (O : Fock n) : phi O ⬝ᵥ phi O = 1 := by
  simp [phi]

theorem phi_isEig (ε : Fin n → ℝ) (O : Fock n) : IsEig ε (energy ε O) (phi O) := by
  unfold IsEig
  rw [H0_eq_diagonal]; funext T
  simp only [phi, mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs with h
  · subst h; rfl
  · simp

/-- The Slater determinant is an eigenvector of the particle number `|O|`. -/
theorem phi_isEig_num (O : Fock n) : IsEig (fun _ => 1) (O.card : ℝ) (phi O) := by
  have h := phi_isEig (fun _ : Fin n => (1 : ℝ)) O
  simpa [energy] using h

/-! ### Elementary moves on `Φ` -/

theorem ann_ann_phi_of_not_mem {r : Fin n} (hr : r ∉ O) (z : Fin n) :
    ann r *ᵥ ann z *ᵥ phi O = 0 := by
  rw [ann_ann_mulVec, ann_phi hr, mulVec_zero, neg_zero]

theorem cre_ann_phi_of_mem {b : Fin n} (hb : b ∈ O) (z : Fin n) :
    cre b *ᵥ ann z *ᵥ phi O = if b = z then phi O else 0 := by
  rw [cre_ann_mulVec, cre_phi hb, mulVec_zero, sub_zero]

/-- `c_r c_x† c_y† c_z Φ` for `r ∉ O`. -/
theorem lemA {r : Fin n} (hr : r ∉ O) (x y z : Fin n) :
    ann r *ᵥ cre x *ᵥ cre y *ᵥ ann z *ᵥ phi O =
      (if r = x then cre y *ᵥ ann z *ᵥ phi O else 0) -
        (if r = y then cre x *ᵥ ann z *ᵥ phi O else 0) := by
  rw [ann_cre_mulVec, ann_cre_mulVec, ann_ann_phi_of_not_mem hr, mulVec_zero, sub_zero]
  congr 1
  split_ifs <;> simp

/-- `c_s c_y† c_z Φ` for `s ∉ O`. -/
theorem lemB {s : Fin n} (hs : s ∉ O) (y z : Fin n) :
    ann s *ᵥ cre y *ᵥ ann z *ᵥ phi O = if s = y then ann z *ᵥ phi O else 0 := by
  rw [ann_cre_mulVec, ann_ann_phi_of_not_mem hs, mulVec_zero, sub_zero]

/-- `c_r c_x† c_y c_z Φ` for `r ∉ O`. -/
theorem lemC {r : Fin n} (hr : r ∉ O) (x y z : Fin n) :
    ann r *ᵥ cre x *ᵥ ann y *ᵥ ann z *ᵥ phi O =
      if r = x then ann y *ᵥ ann z *ᵥ phi O else 0 := by
  rw [ann_cre_mulVec, ann_ann_mulVec r y, ann_ann_phi_of_not_mem hr, mulVec_zero, neg_zero,
    mulVec_zero, sub_zero]

/-- `c_b† c_y c_z Φ` for `b ∈ O`. -/
theorem lemD {b : Fin n} (hb : b ∈ O) (y z : Fin n) :
    cre b *ᵥ ann y *ᵥ ann z *ᵥ phi O =
      (if b = y then ann z *ᵥ phi O else 0) - (if b = z then ann y *ᵥ phi O else 0) := by
  rw [cre_ann_mulVec, cre_ann_phi_of_mem hb]
  congr 1
  split_ifs <;> simp

/-! ### Norms and Gram matrices -/

theorem dot_cre_phi (p q : Fin n) :
    (cre p *ᵥ phi O) ⬝ᵥ (cre q *ᵥ phi O) = if p = q ∧ p ∉ O then 1 else 0 := by
  by_cases hp : p ∈ O
  · rw [cre_phi hp, zero_dotProduct, if_neg (fun h => h.2 hp)]
  · rw [cre_dot, ann_cre_mulVec, ann_phi hp, mulVec_zero, sub_zero]
    split_ifs with h1 h2 h2
    · exact phi_dot_phi O
    · exact absurd ⟨h1, hp⟩ h2
    · exact absurd h2.1 h1
    · simp

theorem dot_ann_phi (p q : Fin n) :
    (ann p *ᵥ phi O) ⬝ᵥ (ann q *ᵥ phi O) = if p = q ∧ p ∈ O then 1 else 0 := by
  by_cases hp : p ∈ O
  · rw [ann_dot, cre_ann_phi_of_mem hp]
    rcases eq_or_ne p q with rfl | e
    · simp [hp, phi_dot_phi]
    · simp [e]
  · rw [ann_phi hp, zero_dotProduct, if_neg (fun h => hp h.2)]

/-- Two-hole Gram matrix: `⟨c_b c_a Φ, c_b' c_a' Φ⟩`. -/
theorem gram_2h (a b a' b' : Fin n) :
    (ann b *ᵥ ann a *ᵥ phi O) ⬝ᵥ (ann b' *ᵥ ann a' *ᵥ phi O) =
      if a' ∈ O ∧ b' ∈ O then
        (if a = a' then 1 else 0) * (if b = b' then 1 else 0) -
          (if a = b' then 1 else 0) * (if b = a' then 1 else 0)
      else 0 := by
  by_cases h : a' ∈ O ∧ b' ∈ O
  · rw [if_pos h]
    by_cases hb : b ∈ O
    · rw [ann_dot, lemD hb, dotProduct_sub]
      simp only [dot_ite_zero, dotProduct_zero, dot_ann_phi]
      obtain ⟨ha', hb'⟩ := h
      by_cases e1 : b = b' <;> by_cases e2 : b = a' <;> by_cases e3 : a = a' <;>
        by_cases e4 : a = b' <;> subst_vars <;> simp_all
    · rw [ann_ann_mulVec, ann_phi hb, mulVec_zero, neg_zero, zero_dotProduct]
      have h1 : b ≠ b' := fun e => hb (e ▸ h.2)
      have h2 : b ≠ a' := fun e => hb (e ▸ h.1)
      simp [h1, h2]
  · rw [if_neg h]
    have : ann b' *ᵥ ann a' *ᵥ phi O = 0 := by
      by_cases ha : a' ∈ O
      · have hb' : b' ∉ O := fun hb' => h ⟨ha, hb'⟩
        exact ann_ann_phi_of_not_mem hb' a'
      · rw [ann_phi ha, mulVec_zero]
    rw [this, dotProduct_zero]

/-- 2p1h Gram matrix: for `r s r' s' ∉ O` and `a a' ∈ O`,
`⟨c_r† c_s† c_a Φ, c_r'† c_s'† c_a' Φ⟩ = δ_aa' (δ_rr' δ_ss' - δ_rs' δ_sr')`. -/
theorem gram_2p1h {r s a r' s' a' : Fin n} (hr : r ∉ O) (hs : s ∉ O) (ha : a ∈ O) :
    (cre r *ᵥ cre s *ᵥ ann a *ᵥ phi O) ⬝ᵥ (cre r' *ᵥ cre s' *ᵥ ann a' *ᵥ phi O) =
      (if a = a' then 1 else 0) *
        ((if r = r' then 1 else 0) * (if s = s' then 1 else 0) -
          (if r = s' then 1 else 0) * (if s = r' then 1 else 0)) := by
  rw [cre_dot, cre_dot, lemA hr, mulVec_sub, dotProduct_sub]
  simp only [mulVec_ite_zero, mulVec_zero, dot_ite_zero, dotProduct_zero, lemB hs, dot_ann_phi]
  by_cases e1 : r = r' <;> by_cases e2 : s = s' <;> by_cases e3 : r = s' <;>
    by_cases e4 : s = r' <;> by_cases e5 : a = a' <;> simp_all

/-- 2h1p Gram matrix: for `r r' ∉ O` and `a b a' b' ∈ O`,
`⟨c_r† c_b c_a Φ, c_r'† c_b' c_a' Φ⟩ = δ_rr' (δ_aa' δ_bb' - δ_ab' δ_ba')`. -/
theorem gram_2h1p {r a b r' a' b' : Fin n} (hr : r ∉ O) (ha' : a' ∈ O) (hb' : b' ∈ O) :
    (cre r *ᵥ ann b *ᵥ ann a *ᵥ phi O) ⬝ᵥ (cre r' *ᵥ ann b' *ᵥ ann a' *ᵥ phi O) =
      (if r = r' then 1 else 0) *
        ((if a = a' then 1 else 0) * (if b = b' then 1 else 0) -
          (if a = b' then 1 else 0) * (if b = a' then 1 else 0)) := by
  rw [cre_dot, lemC hr]
  by_cases h : r = r'
  · rw [if_pos h, if_pos h, gram_2h, if_pos ⟨ha', hb'⟩, one_mul]
  · rw [if_neg h, if_neg h]; simp

/-- 2p1h states are orthogonal to the one-particle states. -/
theorem orth_1p_2p1h (p : Fin n) {r s : Fin n} (hr : r ∉ O) (hs : s ∉ O) (a : Fin n) :
    (cre p *ᵥ phi O) ⬝ᵥ (cre r *ᵥ cre s *ᵥ ann a *ᵥ phi O) = 0 := by
  by_cases hp : p ∈ O
  · rw [cre_phi hp, zero_dotProduct]
  · rw [cre_dot, lemA hp, dotProduct_sub]
    simp only [dot_ite_zero, dotProduct_zero]
    rw [← ann_dot, ← ann_dot, ann_phi hs, ann_phi hr]
    simp

/-- 2h1p states are orthogonal to the one-hole states. -/
theorem orth_1h_2h1p (p : Fin n) {r : Fin n} (hr : r ∉ O) (a b : Fin n) :
    (ann p *ᵥ phi O) ⬝ᵥ (cre r *ᵥ ann b *ᵥ ann a *ᵥ phi O) = 0 := by
  rw [← ann_dot, ann_ann_phi_of_not_mem hr, zero_dotProduct]

/-! ### Splitting `c† c† c Φ` and `c† c c Φ` -/

/-- For `l ∈ O`: `c_i† c_j† c_l Φ` is its 2p1h part plus one-particle terms. -/
theorem cc_a_phi {l : Fin n} (hl : l ∈ O) (i j : Fin n) :
    cre i *ᵥ cre j *ᵥ ann l *ᵥ phi O =
      (if i ∉ O ∧ j ∉ O then cre i *ᵥ cre j *ᵥ ann l *ᵥ phi O else 0) +
        (if i ∉ O ∧ j = l then cre i *ᵥ phi O else 0) -
          (if i = l ∧ j ∉ O then cre j *ᵥ phi O else 0) := by
  by_cases hi : i ∈ O
  · rw [cre_cre_mulVec i j, cre_ann_phi_of_mem hi]
    by_cases e : i = l
    · subst e
      by_cases hj : j ∈ O
      · simp [hi, hj, cre_phi hj]
      · simp [hi, hj]
    · simp [hi, e]
  · have hil : i ≠ l := fun h => hi (h ▸ hl)
    by_cases hj : j ∈ O
    · rw [cre_ann_phi_of_mem hj]
      by_cases e : j = l
      · subst e; simp [hi, hj]
      · simp [hi, hj, e, hil]
    · have hjl : j ≠ l := fun h => hj (h ▸ hl)
      simp [hi, hj, hil, hjl]

/-- `c_j† c_l c_k Φ` is its 2h1p part plus one-hole terms. -/
theorem c_aa_phi (j l k : Fin n) :
    cre j *ᵥ ann l *ᵥ ann k *ᵥ phi O =
      (if j ∉ O then cre j *ᵥ ann l *ᵥ ann k *ᵥ phi O else 0) +
        (if j = l ∧ l ∈ O then ann k *ᵥ phi O else 0) -
          (if j = k ∧ k ∈ O then ann l *ᵥ phi O else 0) := by
  by_cases hj : j ∈ O
  · rw [lemD hj]
    by_cases e1 : j = l <;> by_cases e2 : j = k
    · subst e1; subst e2; simp [hj]
    · subst e1; simp [hj, e2]
    · subst e2; simp [hj, e1]
    · simp [hj, e1, e2]
  · have h1 : ¬(j = l ∧ l ∈ O) := fun h => hj (h.1 ▸ h.2)
    have h2 : ¬(j = k ∧ k ∈ O) := fun h => hj (h.1 ▸ h.2)
    simp [hj, h1, h2]

/-- `c_j† c_l Φ` is its 1p1h part plus the diagonal term. -/
theorem c_a_phi (j l : Fin n) :
    cre j *ᵥ ann l *ᵥ phi O =
      (if l ∈ O ∧ j ∉ O then cre j *ᵥ ann l *ᵥ phi O else 0) +
        (if j = l ∧ l ∈ O then phi O else 0) := by
  by_cases hl : l ∈ O
  · by_cases hj : j ∈ O
    · rw [cre_ann_phi_of_mem hj]
      by_cases e : j = l
      · subst e; simp [hl]
      · simp [e, hj]
    · have e : j ≠ l := fun h => hj (h ▸ hl)
      simp [hl, hj, e]
  · simp [ann_phi hl, hl]

end GW.Endpoint.ManyBody
