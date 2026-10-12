/-
A3(a): the vectors `[V, c_t†] Φ` and `[c_t, V] Φ`, split into their 2p1h / 2h1p part
and their one-particle / one-hole part, and the one matrix element of `V` that the
first-order density change needs.

* `ccre_phi`: `[V, c_t†] Φ = y2p t + Σ_{r ∉ O} Σ1_{rt} c_r† Φ`,
  `y2p t = ½ Σ_{r,s ∉ O} Σ_{a ∈ O} ⟨rs||ta⟩ c_r† c_s† c_a Φ`;
* `cann_phi`: `[c_t, V] Φ = y2h t + Σ_{a ∈ O} Σ1_{ta} c_a Φ`,
  `y2h t = ½ Σ_{r ∉ O} Σ_{a,b ∈ O} ⟨tr||ab⟩ c_r† c_b c_a Φ`;
* `phi_vop_1p1h`: `⟨Φ| V c_x† c_y |Φ⟩ = Σ1_{yx}` for `x ∉ O`, `y ∈ O`;

where `Σ1_{pq} = Σ_{a ∈ O} ⟨pa||qa⟩` is the Hartree-Fock potential of the occupied
orbitals (`sig1`).
-/
import GW.Endpoint.ManyBody.Interaction
import Mathlib.Algebra.Module.BigOperators

namespace GW.Endpoint.ManyBody

open Matrix Finset

variable {n : ℕ} (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n)

/-- Hartree-Fock potential of the occupied set: `Σ1_pq = Σ_{a ∈ O} ⟨pa||qa⟩`. -/
def sig1 (p q : Fin n) : ℝ := ∑ a ∈ O, asym v p a q a

/-- 2p1h part of `[V, c_t†] Φ`. -/
noncomputable def y2p (t : Fin n) : Fock n → ℝ :=
  (2⁻¹ : ℝ) • ∑ r ∈ Oᶜ, ∑ s ∈ Oᶜ, ∑ a ∈ O, asym v r s t a • (cre r *ᵥ cre s *ᵥ ann a *ᵥ phi O)

/-- 2h1p part of `[c_t, V] Φ`. -/
noncomputable def y2h (t : Fin n) : Fock n → ℝ :=
  (2⁻¹ : ℝ) • ∑ r ∈ Oᶜ, ∑ a ∈ O, ∑ b ∈ O, asym v t r a b • (cre r *ᵥ ann b *ᵥ ann a *ᵥ phi O)

variable {v O}

/-! ### Sum bookkeeping -/

theorem sum_univ_eq_sum_of {M : Type*} [AddCommMonoid M] (s : Finset (Fin n)) (f : Fin n → M)
    (h : ∀ i, i ∉ s → f i = 0) : ∑ i, f i = ∑ i ∈ s, f i :=
  (sum_subset (subset_univ s) (fun i _ hi => h i hi)).symm

theorem sum_ite_mem_univ {M : Type*} [AddCommMonoid M] (s : Finset (Fin n)) (f : Fin n → M) :
    ∑ i, (if i ∈ s then f i else 0) = ∑ i ∈ s, f i := by
  rw [sum_ite_mem, univ_inter]

theorem sum_ite_not_mem_univ {M : Type*} [AddCommMonoid M] (s : Finset (Fin n)) (f : Fin n → M) :
    ∑ i, (if i ∉ s then f i else 0) = ∑ i ∈ sᶜ, f i := by
  rw [← sum_ite_mem_univ sᶜ f]; simp only [mem_compl]

theorem sum_sum_ite_and {M : Type*} [AddCommMonoid M] (s t : Finset (Fin n))
    (F : Fin n → Fin n → M) :
    ∑ i, ∑ j, (if i ∈ s ∧ j ∈ t then F i j else 0) = ∑ i ∈ s, ∑ j ∈ t, F i j := by
  simp only [ite_and, sum_ite_irrel, sum_const_zero]
  rw [sum_ite_mem_univ]; congr 1; funext i; rw [sum_ite_mem_univ]

/-! ### `[V, c_t†] Φ` -/

theorem ccre_mulVec (t : Fin n) (w : Fock n → ℝ) :
    ccre v t *ᵥ w = (2⁻¹ : ℝ) • ∑ i, ∑ j, ∑ l, asym v i j t l • (cre i *ᵥ cre j *ᵥ ann l *ᵥ w) := by
  simp only [ccre, smul_mulVec_assoc, sum_mulVec', ← mulVec_mulVec]

theorem cann_mulVec (t : Fin n) (w : Fock n → ℝ) :
    cann v t *ᵥ w = (2⁻¹ : ℝ) • ∑ j, ∑ k, ∑ l, asym v t j k l • (cre j *ᵥ ann l *ᵥ ann k *ᵥ w) := by
  simp only [cann, smul_mulVec_assoc, sum_mulVec', ← mulVec_mulVec]

theorem ccre_phi (hv1 : ∀ p q r s, v p q r s = v q p s r) (t : Fin n) :
    ccre v t *ᵥ phi O = y2p v O t + ∑ r ∈ Oᶜ, sig1 v O r t • (cre r *ᵥ phi O) := by
  rw [ccre_mulVec]
  have hl : ∀ i j, ∑ l, asym v i j t l • (cre i *ᵥ cre j *ᵥ ann l *ᵥ phi O) =
      (if i ∈ Oᶜ ∧ j ∈ Oᶜ then
          ∑ l ∈ O, asym v i j t l • (cre i *ᵥ cre j *ᵥ ann l *ᵥ phi O) else 0) +
        (if i ∈ Oᶜ ∧ j ∈ O then asym v i j t j • (cre i *ᵥ phi O) else 0) -
          (if i ∈ O ∧ j ∈ Oᶜ then asym v i j t i • (cre j *ᵥ phi O) else 0) := by
    intro i j
    rw [sum_univ_eq_sum_of O _ (fun l hl => by rw [ann_phi hl]; simp)]
    by_cases hi : i ∈ O <;> by_cases hj : j ∈ O
    · rw [sum_congr rfl (fun l hl => by rw [cc_a_phi hl i j])]
      simp [hi, hj]
    · rw [sum_congr rfl (fun l hl => by rw [cc_a_phi hl i j])]
      simp [hi, hj, smul_ite, sum_ite_eq]
    · rw [sum_congr rfl (fun l hl => by rw [cc_a_phi hl i j])]
      simp [hi, hj, smul_ite, sum_ite_eq]
    · have e1 : ∀ l ∈ O, cre i *ᵥ cre j *ᵥ ann l *ᵥ phi O = cre i *ᵥ cre j *ᵥ ann l *ᵥ phi O +
          (if i ∉ O ∧ j = l then cre i *ᵥ phi O else 0) -
            (if i = l ∧ j ∉ O then cre j *ᵥ phi O else 0) := by
        intro l hl
        have hjl : j ≠ l := fun e => hj (e ▸ hl)
        have hil : i ≠ l := fun e => hi (e ▸ hl)
        simp [hjl, hil]
      simp [hi, hj]
  simp only [hl, sum_add_distrib, sum_sub_distrib, sum_sum_ite_and, smul_add, smul_sub]
  rw [y2p, add_sub_assoc]
  congr 1
  -- the one-particle terms
  rw [sum_comm (s := O) (t := Oᶜ)]
  have e : ∀ y ∈ Oᶜ, ∑ x ∈ O, asym v x y t x • (cre y *ᵥ phi O) =
      -∑ x ∈ O, asym v y x t x • (cre y *ᵥ phi O) := by
    intro y _
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun x _ => by rw [asym_swap12 v hv1 x y t x, neg_smul]
  rw [sum_congr rfl e, sum_neg_distrib, smul_neg, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
  norm_num [sig1, Finset.sum_smul]

/-! ### `[c_t, V] Φ` -/

theorem cann_phi (t : Fin n) :
    cann v t *ᵥ phi O = y2h v O t + ∑ a ∈ O, sig1 v O t a • (ann a *ᵥ phi O) := by
  rw [cann_mulVec]
  have hkl : ∀ j, ∑ k, ∑ l, asym v t j k l • (cre j *ᵥ ann l *ᵥ ann k *ᵥ phi O) =
      ∑ k ∈ O, ∑ l ∈ O, ((if j ∈ Oᶜ then asym v t j k l • (cre j *ᵥ ann l *ᵥ ann k *ᵥ phi O)
        else 0) + (if j = l then asym v t l k l • (ann k *ᵥ phi O) else 0) -
          (if j = k then asym v t k k l • (ann l *ᵥ phi O) else 0)) := by
    intro j
    rw [sum_univ_eq_sum_of O _ (fun k hk => by simp [ann_phi hk])]
    refine sum_congr rfl fun k hk => ?_
    rw [sum_univ_eq_sum_of O _ (fun l hl => by simp [ann_ann_phi_of_not_mem hl])]
    refine sum_congr rfl fun l hl => ?_
    conv_lhs => rw [c_aa_phi j l k]
    simp only [mem_compl, hk, hl, and_true, smul_add, smul_sub, smul_ite, smul_zero]
    by_cases h1 : j = l
    · subst h1; by_cases h2 : j = k
      · subst h2; simp
      · simp [h2]
    · by_cases h2 : j = k
      · subst h2; simp [h1]
      · simp [h1, h2]
  simp only [hkl, sum_add_distrib, sum_sub_distrib]
  have e1 : (∑ x, ∑ k ∈ O, ∑ l ∈ O,
      if x ∈ Oᶜ then asym v t x k l • (cre x *ᵥ ann l *ᵥ ann k *ᵥ phi O) else 0) =
      ∑ x ∈ Oᶜ, ∑ k ∈ O, ∑ l ∈ O, asym v t x k l • (cre x *ᵥ ann l *ᵥ ann k *ᵥ phi O) := by
    simp only [sum_ite_irrel, sum_const_zero, sum_ite_mem_univ]
  have e2 : (∑ x, ∑ k ∈ O, ∑ l ∈ O, if x = l then asym v t l k l • (ann k *ᵥ phi O) else 0) =
      ∑ k ∈ O, ∑ l ∈ O, asym v t l k l • (ann k *ᵥ phi O) := by
    rw [sum_comm]; refine sum_congr rfl fun k _ => ?_
    rw [sum_comm]; refine sum_congr rfl fun l _ => ?_
    rw [sum_ite_eq']; simp
  have e3 : (∑ x, ∑ k ∈ O, ∑ l ∈ O, if x = k then asym v t k k l • (ann l *ᵥ phi O) else 0) =
      ∑ k ∈ O, ∑ l ∈ O, asym v t k k l • (ann l *ᵥ phi O) := by
    rw [sum_comm]; refine sum_congr rfl fun k _ => ?_
    simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, if_true]
  rw [e1, e2, e3, y2h, smul_sub, smul_add, add_sub_assoc]
  congr 1
  -- one-hole terms: relabel and antisymmetrize the second
  have e4 : ∑ k ∈ O, ∑ l ∈ O, asym v t k k l • (ann l *ᵥ phi O) =
      -∑ k ∈ O, ∑ l ∈ O, asym v t l k l • (ann k *ᵥ phi O) := by
    rw [sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [asym_swap34 v t k k l, neg_smul]
  rw [e4, smul_neg, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
  norm_num [sig1, Finset.sum_smul]

/-! ### The one-particle-one-hole matrix element of `V` -/

theorem dot_mulVec_cre (j : Fin n) (x w : Fock n → ℝ) : x ⬝ᵥ (cre j *ᵥ w) = (ann j *ᵥ x) ⬝ᵥ w := by
  rw [ann_dot]

/-- `⟨Φ| V c_j† c_l |Φ⟩ = Σ1_{lj}` for `j ∉ O`, `l ∈ O`. -/
theorem phi_vop_1p1h (hv1 : ∀ p q r s, v p q r s = v q p s r) {j l : Fin n} (hj : j ∉ O)
    (hl : l ∈ O) : phi O ⬝ᵥ (vop v *ᵥ cre j *ᵥ ann l *ᵥ phi O) = sig1 v O l j := by
  have hc : vop v * cre j = cre j * vop v + ccre v j := by
    rw [← vop_mul_cre]; abel
  rw [mulVec_mulVec, hc, add_mulVec, ← mulVec_mulVec, dotProduct_add, dot_mulVec_cre, ann_phi hj,
    zero_dotProduct, zero_add, ccre_mulVec, dotProduct_smul]
  simp only [dot_sum', dotProduct_smul, dot_mulVec_cre]
  simp only [gram_2h, hl, true_and, smul_eq_mul, mul_ite, mul_zero, mul_sub, mul_one]
  simp only [sum_ite_mem_univ, sum_sub_distrib, sum_ite_irrel, sum_const_zero, sum_ite_eq,
    sum_ite_eq', mem_univ, if_true, ite_mul, one_mul, zero_mul]
  have e : ∑ i ∈ O, asym v i l j i = -∑ i ∈ O, asym v l i j i := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun i _ => asym_swap12 v hv1 i l j i
  rw [e, sig1]; ring

end GW.Endpoint.ManyBody
