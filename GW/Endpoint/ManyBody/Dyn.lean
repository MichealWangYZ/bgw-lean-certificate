/-
A3(a), stage S4 (real level): the dynamic second-order self-energy, i.e. the
2p1h and 2h1p propagators, evaluated in closed form from the Gram matrices of
`Slater.lean`. This is where the direct (ring) and exchange (SOX) terms appear.

  ⟨y2p p| (ω - (H0 - E0))⁻¹ |y2p q⟩
      = ½ Σ_{a∈O} Σ_{r,s∉O} ⟨pa||rs⟩⟨rs||qa⟩ / (ω + ε_a - ε_r - ε_s)      (`dyn_particle`)
  ⟨y2h p| (ω + (H0 - E0))⁻¹ |y2h q⟩
      = ½ Σ_{r∉O} Σ_{a,b∈O} ⟨pr||ab⟩⟨ab||qr⟩ / (ω + ε_r - ε_a - ε_b)      (`dyn_hole`)

(the resolvents are the diagonal matrices `Dp`, `Dm`; `hv1`, `hv2` are the symmetry
assumptions of `Interaction.lean`).
-/
import GW.Endpoint.ManyBody.Perturb

namespace GW.Endpoint.ManyBody

open Matrix Finset

variable {n : ℕ} (ε : Fin n → ℝ) (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n) (ω : ℝ)

/-- `(ω - (H0 - E0))⁻¹` on the (N+1)-particle side, diagonal. -/
noncomputable def Dp : Matrix (Fock n) (Fock n) ℝ :=
  diagonal fun S => (ω - (energy ε S - energy ε O))⁻¹

/-- `(ω + (H0 - E0))⁻¹` on the (N-1)-particle side, diagonal. -/
noncomputable def Dm : Matrix (Fock n) (Fock n) ℝ :=
  diagonal fun S => (ω + (energy ε S - energy ε O))⁻¹

/-- The standard particle (2p1h) part of the second-order self-energy (direct + SOX). -/
noncomputable def sig2p (p q : Fin n) : ℝ :=
  (2⁻¹ : ℝ) * ∑ a ∈ O, ∑ r ∈ Oᶜ, ∑ s ∈ Oᶜ,
    asym v p a r s * asym v r s q a / (ω + ε a - ε r - ε s)

/-- The standard hole (2h1p) part of the second-order self-energy (direct + SOX). -/
noncomputable def sig2h (p q : Fin n) : ℝ :=
  (2⁻¹ : ℝ) * ∑ r ∈ Oᶜ, ∑ a ∈ O, ∑ b ∈ O,
    asym v p r a b * asym v a b q r / (ω + ε r - ε a - ε b)

variable {ε v O ω}

theorem state2p_isEig (r s a : Fin n) :
    IsEig ε (energy ε O - ε a + ε s + ε r) (cre r *ᵥ cre s *ᵥ ann a *ᵥ phi O) :=
  ((((phi_isEig ε O).ann a).cre s).cre r)

theorem state2h_isEig (r a b : Fin n) :
    IsEig ε (energy ε O - ε a - ε b + ε r) (cre r *ᵥ ann b *ᵥ ann a *ᵥ phi O) :=
  ((((phi_isEig ε O).ann a).ann b).cre r)

theorem Dp_state (r s a : Fin n) :
    Dp ε O ω *ᵥ (cre r *ᵥ cre s *ᵥ ann a *ᵥ phi O) =
      (ω + ε a - ε r - ε s)⁻¹ • (cre r *ᵥ cre s *ᵥ ann a *ᵥ phi O) := by
  rw [Dp, (state2p_isEig r s a).diagonal_mulVec (fun e => (ω - (e - energy ε O))⁻¹)]
  congr 2; ring

theorem Dm_state (r a b : Fin n) :
    Dm ε O ω *ᵥ (cre r *ᵥ ann b *ᵥ ann a *ᵥ phi O) =
      (ω + ε r - ε a - ε b)⁻¹ • (cre r *ᵥ ann b *ᵥ ann a *ᵥ phi O) := by
  rw [Dm, (state2h_isEig r a b).diagonal_mulVec (fun e => (ω + (e - energy ε O))⁻¹)]
  congr 2; ring

theorem smul_sum' {ι α : Type*} (s : Finset ι) (c : ℝ) (f : ι → α → ℝ) :
    c • ∑ i ∈ s, f i = ∑ i ∈ s, c • f i := Finset.smul_sum

theorem sum3_rotate {M : Type*} [AddCommMonoid M] (A B C : Finset (Fin n))
    (f : Fin n → Fin n → Fin n → M) :
    ∑ r ∈ A, ∑ s ∈ B, ∑ a ∈ C, f r s a = ∑ a ∈ C, ∑ r ∈ A, ∑ s ∈ B, f r s a := by
  calc ∑ r ∈ A, ∑ s ∈ B, ∑ a ∈ C, f r s a = ∑ r ∈ A, ∑ a ∈ C, ∑ s ∈ B, f r s a :=
        sum_congr rfl fun r _ => sum_comm
    _ = _ := sum_comm

theorem dyn_particle (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (p q : Fin n) :
    y2p v O p ⬝ᵥ (Dp ε O ω *ᵥ y2p v O q) = sig2p ε v O ω p q := by
  simp only [y2p, mulVec_smul, mulVec_sum', Dp_state, smul_smul, dotProduct_smul, smul_dotProduct,
    dot_sum', sum_dot', dotProduct_smul, smul_dotProduct, smul_eq_mul]
  -- evaluate the Gram matrix
  have hg : ∀ r ∈ Oᶜ, ∀ s ∈ Oᶜ, ∀ a ∈ O, ∀ r' s' a' : Fin n,
      (cre r *ᵥ cre s *ᵥ ann a *ᵥ phi O) ⬝ᵥ (cre r' *ᵥ cre s' *ᵥ ann a' *ᵥ phi O) =
        (if a = a' then 1 else 0) * ((if r = r' then 1 else 0) * (if s = s' then 1 else 0) -
          (if r = s' then 1 else 0) * (if s = r' then 1 else 0)) := by
    intro r hr s hs a ha r' s' a'
    exact gram_2p1h (mem_compl.mp hr) (mem_compl.mp hs) ha
  have inner : ∀ x ∈ Oᶜ, ∀ x1 ∈ Oᶜ, ∀ x2 ∈ O,
      (∑ x3 ∈ Oᶜ, ∑ x4 ∈ Oᶜ, ∑ x5 ∈ O, asym v x3 x4 p x5 *
        ((cre x3 *ᵥ cre x4 *ᵥ ann x5 *ᵥ phi O) ⬝ᵥ (cre x *ᵥ cre x1 *ᵥ ann x2 *ᵥ phi O))) =
        2 * asym v x x1 p x2 := by
    intro x hx x1 hx1 x2 hx2
    rw [sum_congr rfl fun x3 h3 => sum_congr rfl fun x4 h4 => sum_congr rfl fun x5 h5 => by
      rw [hg x3 h3 x4 h4 x5 h5]]
    simp only [mul_sub, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul, sum_sub_distrib,
      sum_ite_eq', hx, hx1, hx2, if_true, sum_ite_irrel, sum_const_zero]
    rw [asym_swap12 v hv1 x1 x p x2]; ring
  rw [sum_congr rfl fun x hx => sum_congr rfl fun x1 hx1 => sum_congr rfl fun x2 hx2 => by
    rw [inner x hx x1 hx1 x2 hx2]]
  rw [sig2p]
  simp only [mul_sum]
  rw [sum3_rotate]
  refine sum_congr rfl fun a _ => sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
  rw [asym_herm v hv1 hv2 r s p a, div_eq_mul_inv]; ring

theorem dyn_hole (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (p q : Fin n) :
    y2h v O p ⬝ᵥ (Dm ε O ω *ᵥ y2h v O q) = sig2h ε v O ω p q := by
  simp only [y2h, mulVec_smul, mulVec_sum', Dm_state, smul_smul, dotProduct_smul, smul_dotProduct,
    dot_sum', sum_dot', dotProduct_smul, smul_dotProduct, smul_eq_mul]
  have inner : ∀ x ∈ Oᶜ, ∀ x1 ∈ O, ∀ x2 ∈ O,
      (∑ x3 ∈ Oᶜ, ∑ x4 ∈ O, ∑ x5 ∈ O, asym v p x3 x4 x5 *
        ((cre x3 *ᵥ ann x5 *ᵥ ann x4 *ᵥ phi O) ⬝ᵥ (cre x *ᵥ ann x2 *ᵥ ann x1 *ᵥ phi O))) =
        2 * asym v p x x1 x2 := by
    intro x hx x1 hx1 x2 hx2
    rw [sum_congr rfl fun x3 h3 => sum_congr rfl fun x4 _ => sum_congr rfl fun x5 _ => by
      rw [gram_2h1p (mem_compl.mp h3) hx1 hx2]]
    simp only [mul_sub, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul, sum_sub_distrib,
      sum_ite_eq', hx, hx1, hx2, if_true, sum_ite_irrel, sum_const_zero]
    rw [asym_swap34 v p x x2 x1]; ring
  rw [sum_congr rfl fun x hx => sum_congr rfl fun x1 hx1 => sum_congr rfl fun x2 hx2 => by
    rw [inner x hx x1 hx1 x2 hx2]]
  rw [sig2h]
  simp only [mul_sum]
  refine sum_congr rfl fun r _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [asym_herm v hv1 hv2 q r a b, div_eq_mul_inv]; ring

end GW.Endpoint.ManyBody
