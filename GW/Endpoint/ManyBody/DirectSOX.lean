/-
A3(a): splitting the antisymmetrized second-order self-energy into its direct
(ring) and second-order-exchange (SOX) halves, in the non-antisymmetrized integrals
`v_pqrs = ⟨pq|rs⟩` (`sig2_eq_dir_add_sox`, uses only `hv1 : v_pqrs = v_qpsr`):

  dir2_pq = Σ_{a∈O} Σ_{r,s∉O} v_pars v_rsqa / (ω + ε_a - ε_r - ε_s)
          + Σ_{r∉O} Σ_{a,b∈O} v_prab v_abqr / (ω + ε_r - ε_a - ε_b),
  sox2_pq = - Σ_{a∈O} Σ_{r,s∉O} v_pars v_rsaq / (ω + ε_a - ε_r - ε_s)
            - Σ_{r∉O} Σ_{a,b∈O} v_prab v_abrq / (ω + ε_r - ε_a - ε_b).

The direct half is the one in which the propagating line keeps the first electron
slot (`p → r → q`), i.e. the ring; it is the term G0W0 contains (`GWSecond.lean`).
-/
import GW.Endpoint.ManyBody.Sigma

namespace GW.Endpoint.ManyBody

open Matrix Finset

variable {n : ℕ} (ε : Fin n → ℝ) (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n) (ω : ℝ)

/-- Second-order direct (ring) self-energy. -/
noncomputable def dir2 (p q : Fin n) : ℝ :=
  (∑ a ∈ O, ∑ r ∈ Oᶜ, ∑ s ∈ Oᶜ, v p a r s * v r s q a / (ω + ε a - ε r - ε s)) +
    ∑ r ∈ Oᶜ, ∑ a ∈ O, ∑ b ∈ O, v p r a b * v a b q r / (ω + ε r - ε a - ε b)

/-- Second-order exchange (SOX) self-energy. -/
noncomputable def sox2 (p q : Fin n) : ℝ :=
  -(∑ a ∈ O, ∑ r ∈ Oᶜ, ∑ s ∈ Oᶜ, v p a r s * v r s a q / (ω + ε a - ε r - ε s)) -
    ∑ r ∈ Oᶜ, ∑ a ∈ O, ∑ b ∈ O, v p r a b * v a b r q / (ω + ε r - ε a - ε b)

variable {ε v O ω}

theorem sig2p_split (hv1 : ∀ p q r s, v p q r s = v q p s r) (p q : Fin n) :
    sig2p ε v O ω p q =
      (∑ a ∈ O, ∑ r ∈ Oᶜ, ∑ s ∈ Oᶜ, v p a r s * v r s q a / (ω + ε a - ε r - ε s)) -
        ∑ a ∈ O, ∑ r ∈ Oᶜ, ∑ s ∈ Oᶜ, v p a r s * v r s a q / (ω + ε a - ε r - ε s) := by
  unfold sig2p asym
  rw [← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  set D := fun r s => ω + ε a - ε r - ε s
  have hX : ∀ r s, (v p a r s - v p a s r) * (v r s q a - v r s a q) / (ω + ε a - ε r - ε s) =
      v p a r s * v r s q a / D r s - v p a r s * v r s a q / D r s
        - v p a s r * v r s q a / D r s + v p a s r * v r s a q / D r s := by
    intro r s; simp only [D]; ring
  have hC : ∑ r ∈ Oᶜ, ∑ s ∈ Oᶜ, v p a s r * v r s q a / D r s =
      ∑ r ∈ Oᶜ, ∑ s ∈ Oᶜ, v p a r s * v r s a q / D r s := by
    rw [sum_comm]
    exact sum_congr rfl fun r _ => sum_congr rfl fun s _ => by
      simp only [D]; rw [hv1 s r q a]; ring_nf
  have hD : ∑ r ∈ Oᶜ, ∑ s ∈ Oᶜ, v p a s r * v r s a q / D r s =
      ∑ r ∈ Oᶜ, ∑ s ∈ Oᶜ, v p a r s * v r s q a / D r s := by
    rw [sum_comm]
    exact sum_congr rfl fun r _ => sum_congr rfl fun s _ => by
      simp only [D]; rw [hv1 s r a q]; ring_nf
  rw [sum_congr rfl fun r _ => sum_congr rfl fun s _ => hX r s]
  simp only [sum_add_distrib, sum_sub_distrib]
  rw [hC, hD]; simp only [D]; ring

theorem sig2h_split (hv1 : ∀ p q r s, v p q r s = v q p s r) (p q : Fin n) :
    sig2h ε v O ω p q =
      (∑ r ∈ Oᶜ, ∑ a ∈ O, ∑ b ∈ O, v p r a b * v a b q r / (ω + ε r - ε a - ε b)) -
        ∑ r ∈ Oᶜ, ∑ a ∈ O, ∑ b ∈ O, v p r a b * v a b r q / (ω + ε r - ε a - ε b) := by
  unfold sig2h asym
  rw [← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  set D := fun a b => ω + ε r - ε a - ε b
  have hX : ∀ a b, (v p r a b - v p r b a) * (v a b q r - v a b r q) / (ω + ε r - ε a - ε b) =
      v p r a b * v a b q r / D a b - v p r a b * v a b r q / D a b
        - v p r b a * v a b q r / D a b + v p r b a * v a b r q / D a b := by
    intro a b; simp only [D]; ring
  have hC : ∑ a ∈ O, ∑ b ∈ O, v p r b a * v a b q r / D a b =
      ∑ a ∈ O, ∑ b ∈ O, v p r a b * v a b r q / D a b := by
    rw [sum_comm]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by
      simp only [D]; rw [hv1 b a q r]; ring_nf
  have hD : ∑ a ∈ O, ∑ b ∈ O, v p r b a * v a b r q / D a b =
      ∑ a ∈ O, ∑ b ∈ O, v p r a b * v a b q r / D a b := by
    rw [sum_comm]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by
      simp only [D]; rw [hv1 b a r q]; ring_nf
  rw [sum_congr rfl fun a _ => sum_congr rfl fun b _ => hX a b]
  simp only [sum_add_distrib, sum_sub_distrib]
  rw [hC, hD]; simp only [D]; ring

/-- The standard second-order self-energy is direct + SOX. -/
theorem sig2_eq_dir_add_sox (hv1 : ∀ p q r s, v p q r s = v q p s r) (p q : Fin n) :
    sig2p ε v O ω p q + sig2h ε v O ω p q = dir2 ε v O ω p q + sox2 ε v O ω p q := by
  rw [sig2p_split hv1, sig2h_split hv1, dir2, sox2]; ring

/-- **S4 exit.** `Σ⁽²⁾ = direct + SOX + density relaxation`. -/
theorem sigma2_eq_direct_add_sox_add_relax (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) (hω : OffPoles ε O ω) :
    cf 2 (sigmaT ε v O ω) =
      Matrix.of fun p q => dir2 ε v O ω p q + sox2 ε v O ω p q + relax ε v O p q := by
  rw [sigma2_eq hv1 hv2 hnd hω]
  ext p q; simp only [of_apply, sig2_eq_dir_add_sox hv1]

/-- **S4 exit (Brillouin case).** If the occupied-empty block of the first-order
(HF) potential vanishes, `Σ⁽²⁾ = direct + SOX`. -/
theorem sigma2_eq_direct_add_sox (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) (hω : OffPoles ε O ω)
    (hB : ∀ a ∈ O, ∀ r ∉ O, sig1 v O r a = 0) :
    cf 2 (sigmaT ε v O ω) = Matrix.of fun p q => dir2 ε v O ω p q + sox2 ε v O ω p q := by
  rw [sigma2_eq_direct_add_sox_add_relax hv1 hv2 hnd hω]
  ext p q; simp only [of_apply, relax_eq_zero_of_brillouin hB, add_zero]

end GW.Endpoint.ManyBody
