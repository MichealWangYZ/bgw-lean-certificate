/-
A3(a), stage S2 (real level): Rayleigh-Schrödinger perturbation theory to second
order about the Slater determinant `Φ = phi O`.

Nondegeneracy (`NonDeg`): no other basis state with `|O|` particles has the energy
`E0 = Σ_{a∈O} ε_a`. The reduced resolvent is the diagonal matrix
`Rr = diag((E0 - E_S)⁻¹)`; Lean's `0⁻¹ = 0` makes its `Φ` entry (and any other
degenerate entry) zero, and `NonDeg` plus particle-number conservation is exactly
what makes that harmless (`H0_Rr`).

  E1 = ⟨Φ|V|Φ⟩,  ψ1 = Rr V Φ,  E2 = ⟨Φ|V|ψ1⟩,  ψ2 = Rr (V - E1) ψ1,

with `⟨Φ|ψ1⟩ = ⟨Φ|ψ2⟩ = 0`, and the three eigenvalue equations
(`eig_order0`, `eig_order1`, `eig_order2`):

  (H0 - E0) Φ = 0,
  (H0 - E0) ψ1 + (V - E1) Φ = 0,
  (H0 - E0) ψ2 + (V - E1) ψ1 - E2 Φ = 0.
-/
import GW.Endpoint.ManyBody.Decomp
import Mathlib.Tactic.FieldSimp

namespace GW.Endpoint.ManyBody

open Matrix Finset

variable {n : ℕ} (ε : Fin n → ℝ) (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n)

/-- Unperturbed ground energy. -/
def E0 : ℝ := energy ε O

/-- Nondegeneracy of `Φ` within its particle-number sector. -/
def NonDeg : Prop := ∀ S : Fock n, S.card = O.card → S ≠ O → energy ε S ≠ energy ε O

/-- Reduced resolvent `Q (E0 - H0)⁻¹ Q` as a diagonal matrix. -/
noncomputable def Rr : Matrix (Fock n) (Fock n) ℝ :=
  diagonal fun S => (energy ε O - energy ε S)⁻¹

noncomputable def E1 : ℝ := phi O ⬝ᵥ (vop v *ᵥ phi O)
noncomputable def psi1 : Fock n → ℝ := Rr ε O *ᵥ (vop v *ᵥ phi O)
noncomputable def E2 : ℝ := phi O ⬝ᵥ (vop v *ᵥ psi1 ε v O)
noncomputable def psi2 : Fock n → ℝ :=
  Rr ε O *ᵥ (vop v *ᵥ psi1 ε v O - E1 v O • psi1 ε v O)

variable {ε v O}

theorem phi_dot (x : Fock n → ℝ) : phi O ⬝ᵥ x = x O := by
  simp [phi, dotProduct, Pi.single_apply]

theorem phi_dot_Rr (x : Fock n → ℝ) : phi O ⬝ᵥ (Rr ε O *ᵥ x) = 0 := by
  simp [phi_dot, Rr, mulVec_diagonal]

/-- A diagonal matrix preserves eigenvectors of any diagonal `H0`. -/
theorem IsEig.diagonal {ε' : Fin n → ℝ} {e : ℝ} {x : Fock n → ℝ} (h : IsEig ε' e x)
    (g : Fock n → ℝ) : IsEig ε' e (diagonal g *ᵥ x) := by
  unfold IsEig at *
  rw [H0_eq_diagonal] at *
  funext S
  have := congrFun h S
  simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this ⊢
  rw [← mul_assoc, mul_comm (energy ε' S), mul_assoc, this]; ring

/-- `(H0 - E0) Rr x = (Φ·x) Φ - x` on the `|O|`-particle sector. -/
theorem H0_Rr (hnd : NonDeg ε O) {x : Fock n → ℝ} (hx : IsEig (fun _ => 1) (O.card : ℝ) x) :
    H0 ε *ᵥ (Rr ε O *ᵥ x) - energy ε O • (Rr ε O *ᵥ x) = (phi O ⬝ᵥ x) • phi O - x := by
  rw [H0_eq_diagonal] at *
  have hnum : ∀ S : Fock n, x S ≠ 0 → S.card = O.card := by
    intro S hS
    have := congrFun hx S
    unfold IsEig at hx
    have h2 := congrFun hx S
    rw [H0_eq_diagonal] at h2
    simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul, energy, sum_const, nsmul_eq_mul,
      mul_one] at h2
    exact_mod_cast mul_right_cancel₀ hS h2
  funext S
  simp only [Rr, mulVec_diagonal, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, phi_dot, phi,
    Pi.single_apply]
  by_cases hS : S = O
  · subst hS; simp
  · rw [if_neg hS, mul_zero, zero_sub]
    by_cases hx0 : x S = 0
    · simp [hx0]
    · have hne : energy ε O - energy ε S ≠ 0 :=
        sub_ne_zero.mpr (Ne.symm (hnd S (hnum S hx0) hS))
      rw [← sub_mul, ← mul_assoc, show energy ε S - energy ε O = -(energy ε O - energy ε S) by ring,
        neg_mul, mul_inv_cancel₀ hne, neg_one_mul]

theorem vphi_num : IsEig (fun _ => 1) (O.card : ℝ) (vop v *ᵥ phi O) :=
  vop_isEig_num v (phi_isEig_num O)

theorem psi1_num : IsEig (fun _ => 1) (O.card : ℝ) (psi1 ε v O) :=
  (vphi_num (v := v)).diagonal _

theorem phi_dot_psi1 : phi O ⬝ᵥ psi1 ε v O = 0 := phi_dot_Rr _

theorem phi_dot_psi2 : phi O ⬝ᵥ psi2 ε v O = 0 := phi_dot_Rr _

theorem eig_order0 : H0 ε *ᵥ phi O - E0 ε O • phi O = 0 := by
  rw [phi_isEig ε O, E0, sub_self]

theorem eig_order1 (hnd : NonDeg ε O) :
    H0 ε *ᵥ psi1 ε v O - E0 ε O • psi1 ε v O + (vop v *ᵥ phi O - E1 v O • phi O) = 0 := by
  rw [psi1, E0, H0_Rr hnd vphi_num, E1]; abel

theorem eig_order2 (hnd : NonDeg ε O) :
    H0 ε *ᵥ psi2 ε v O - E0 ε O • psi2 ε v O +
      (vop v *ᵥ psi1 ε v O - E1 v O • psi1 ε v O) - E2 ε v O • phi O = 0 := by
  have hx : IsEig (fun _ => 1) (O.card : ℝ) (vop v *ᵥ psi1 ε v O - E1 v O • psi1 ε v O) := by
    have h1 := vop_isEig_num v (psi1_num (ε := ε) (v := v) (O := O))
    have h2 := (psi1_num (ε := ε) (v := v) (O := O)).smul (-E1 v O)
    have := h1.add h2
    rwa [neg_smul, ← sub_eq_add_neg] at this
  rw [psi2, E0, H0_Rr hnd hx, dotProduct_sub, dotProduct_smul, phi_dot_psi1, smul_zero, sub_zero,
    E2]; abel

end GW.Endpoint.ManyBody
