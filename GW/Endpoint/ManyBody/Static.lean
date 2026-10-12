/-
A3(a), stage S4 (real level): the static second-order term, from the first-order
change of the one-particle density matrix.

  ⟨ψ1| F_pq |Φ⟩ + ⟨Φ| F_pq |ψ1⟩ = relax_pq,
  relax_pq = Σ_{a∈O} Σ_{r∉O} (⟨pa||qr⟩ + ⟨pr||qa⟩) Σ1_ra / (ε_a - ε_r)      (`static_eq`)

with `F_pq = {c_p, [V, c_q†]} = Σ ⟨pj||ql⟩ c_j† c_l` and `Σ1` the HF potential of the
occupied orbitals. This term is NOT part of the textbook "direct + SOX" formula:
it is the Hartree-Fock diagram with a first-order insertion on its internal line.
It vanishes when the occupied-empty block of `Σ1` vanishes (Brillouin condition,
`relax_eq_zero_of_brillouin`), e.g. when `H0` is the Fock operator of the
reference. Only this sufficient direction is proved; in general it does not vanish
otherwise (nonzero in the numerical check `bgw/endpoint/manybody/check_sigma2.py`).
-/
import GW.Endpoint.ManyBody.Dyn

namespace GW.Endpoint.ManyBody

open Matrix Finset

variable {n : ℕ} (ε : Fin n → ℝ) (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n)

/-- The density-relaxation (static) part of the second-order self-energy. -/
noncomputable def relax (p q : Fin n) : ℝ :=
  ∑ a ∈ O, ∑ r ∈ Oᶜ, (asym v p a q r + asym v p r q a) * sig1 v O r a / (ε a - ε r)

variable {ε v O}

theorem sig1_symm (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (p q : Fin n) : sig1 v O p q = sig1 v O q p := by
  unfold sig1; exact sum_congr rfl fun a _ => asym_herm v hv1 hv2 p a q a

theorem Rr_transpose : (Rr ε O)ᵀ = Rr ε O := by simp [Rr]

theorem Rr_1p1h (j l : Fin n) :
    Rr ε O *ᵥ (cre j *ᵥ ann l *ᵥ phi O) = (ε l - ε j)⁻¹ • (cre j *ᵥ ann l *ᵥ phi O) := by
  rw [Rr, (((phi_isEig ε O).ann l).cre j).diagonal_mulVec (fun e => (energy ε O - e)⁻¹)]
  congr 2; ring

theorem Rr_phi : Rr ε O *ᵥ phi O = 0 := by
  rw [Rr, (phi_isEig ε O).diagonal_mulVec (fun e => (energy ε O - e)⁻¹)]; simp

/-- `⟨c_j† c_l Φ | V Φ⟩ = Σ1_{lj}` (j ∉ O, l ∈ O). -/
theorem dot_1p1h_vphi (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) {j l : Fin n} (hj : j ∉ O) (hl : l ∈ O) :
    (cre j *ᵥ ann l *ᵥ phi O) ⬝ᵥ (vop v *ᵥ phi O) = sig1 v O l j := by
  rw [dotProduct_comm, mulVec_dot_of_symm (vop_transpose v hv2), phi_vop_1p1h hv1 hj hl]

theorem dot_psi1_1p1h (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) {j l : Fin n} (hj : j ∉ O) (hl : l ∈ O) :
    psi1 ε v O ⬝ᵥ (cre j *ᵥ ann l *ᵥ phi O) = (ε l - ε j)⁻¹ * sig1 v O l j := by
  rw [psi1, mulVec_dot_of_symm Rr_transpose, Rr_1p1h, dotProduct_smul, dotProduct_comm,
    dot_1p1h_vphi hv1 hv2 hj hl, smul_eq_mul]

theorem fop_mulVec (p q : Fin n) (w : Fock n → ℝ) :
    fop v p q *ᵥ w = ∑ j, ∑ l, asym v p j q l • (cre j *ᵥ ann l *ᵥ w) := by
  simp only [fop, sum_mulVec', smul_mulVec_assoc, ← mulVec_mulVec]

theorem psi1_dot_phi : psi1 ε v O ⬝ᵥ phi O = 0 := by
  rw [dotProduct_comm]; exact phi_dot_psi1

theorem psi1_dot_ca (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (j l : Fin n) :
    psi1 ε v O ⬝ᵥ (cre j *ᵥ ann l *ᵥ phi O) =
      if l ∈ O ∧ j ∈ Oᶜ then (ε l - ε j)⁻¹ * sig1 v O l j else 0 := by
  rw [c_a_phi j l, dotProduct_add, dot_ite_zero, dot_ite_zero, psi1_dot_phi]
  by_cases hl : l ∈ O <;> by_cases hj : j ∈ O
  · simp [hl, hj]
  · have := dot_psi1_1p1h (ε := ε) hv1 hv2 hj hl
    simp only [hl, hj, not_false_eq_true, and_self, if_true, and_true, mem_compl, this,
      dot_ite_zero, if_false, add_zero]
    simp [hl, hj]
  · simp [hl, hj]
  · simp [hl, hj]

theorem static_left (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (p q : Fin n) :
    psi1 ε v O ⬝ᵥ (fop v p q *ᵥ phi O) =
      ∑ a ∈ O, ∑ r ∈ Oᶜ, asym v p r q a * ((ε a - ε r)⁻¹ * sig1 v O a r) := by
  rw [fop_mulVec]
  simp only [dot_sum', dotProduct_smul, smul_eq_mul, psi1_dot_ca hv1 hv2, mul_ite, mul_zero]
  rw [sum_comm]
  simp only [ite_and, sum_ite_irrel, sum_const_zero, sum_ite_mem_univ]

theorem static_right (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (p q : Fin n) :
    phi O ⬝ᵥ (fop v p q *ᵥ psi1 ε v O) =
      ∑ a ∈ O, ∑ r ∈ Oᶜ, asym v p a q r * ((ε a - ε r)⁻¹ * sig1 v O a r) := by
  rw [fop_mulVec]
  have e : ∀ j l, phi O ⬝ᵥ (cre j *ᵥ ann l *ᵥ psi1 ε v O) =
      if j ∈ O ∧ l ∈ Oᶜ then (ε j - ε l)⁻¹ * sig1 v O j l else 0 := by
    intro j l
    rw [dot_mulVec_cre, ← cre_dot, dotProduct_comm, psi1_dot_ca hv1 hv2]
  simp only [dot_sum', dotProduct_smul, smul_eq_mul, e, mul_ite, mul_zero]
  simp only [ite_and, sum_ite_irrel, sum_const_zero, sum_ite_mem_univ]

/-- The static second-order term is the density-relaxation term. -/
theorem static_eq (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (p q : Fin n) :
    psi1 ε v O ⬝ᵥ (fop v p q *ᵥ phi O) + phi O ⬝ᵥ (fop v p q *ᵥ psi1 ε v O) = relax ε v O p q := by
  rw [static_left hv1 hv2, static_right hv1 hv2, ← sum_add_distrib, relax]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun r _ => ?_
  rw [sig1_symm hv1 hv2 a r, div_eq_mul_inv]; ring

/-- Under the Brillouin condition (no occupied-empty block of `Σ1`) the static term vanishes. -/
theorem relax_eq_zero_of_brillouin (hB : ∀ a ∈ O, ∀ r ∉ O, sig1 v O r a = 0) (p q : Fin n) :
    relax ε v O p q = 0 := by
  unfold relax
  exact sum_eq_zero fun a ha => sum_eq_zero fun r hr => by
    rw [hB a ha r (mem_compl.mp hr)]; ring

end GW.Endpoint.ManyBody
