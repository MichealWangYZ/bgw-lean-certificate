/-
A3(a), S5 exit: the structure of the G0W0 error for a general finite fermion system,
through second order in the coupling (formal power series in `λ`; the GW second-order
coefficient is the `η → 0⁺` limit of `GWSecond.lean`).

* first order: exact = GW = Hartree-Fock;
* second order: exact - GW = SOX + (density relaxation), and = SOX under the
  Brillouin condition (`Σ1_ra = 0` for `a ∈ O`, `r ∉ O`); as a statement about G0W0
  this needs `ω` off the GW poles (`GWOffPoles`, a hypothesis of
  `gw_error_second_order`; `gw_error_coeff2` does not assume it).

What this does NOT say: nothing about the true (analytic) function `λ ↦ Σ(ω; λ)`
beyond its formal expansion; nothing about third order; nothing about a real solid.
-/
import GW.Endpoint.ManyBody.GWSecond

namespace GW.Endpoint.ManyBody

open Matrix Finset Filter Topology
open GW.Endpoint.HubbardDimer (ftDamped)

variable {n : ℕ} {ε : Fin n → ℝ} {v : Fin n → Fin n → Fin n → Fin n → ℝ} {O : Fock n} {ω : ℝ}

/-- First order: the exact self-energy coefficient equals the G0W0 one (Hartree + bare
exchange with the occupied orbitals of `G0`). -/
theorem gw_error_first_order (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) (hω : OffPoles ε O ω) :
    cf 1 (sigmaT ε v O ω) = Matrix.of fun p q => sigH v O p q + sigX v O p q := by
  rw [sigma1_eq_HF hv1 hv2 hnd hω]; ext p q; simp only [of_apply, gw1_eq_HF]; rfl

/-- **`gw_error_second_order`.** `Σ_exact⁽²⁾ - Σ_GW⁽²⁾ → SOX + relax` as `η → 0⁺`. -/
theorem gw_error_second_order (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) (hω : OffPoles ε O ω)
    (hωGW : GWOffPoles ε O ω) (p q : Fin n) :
    Tendsto (fun η => ((cf 2 (sigmaT ε v O ω) p q : ℝ) : ℂ) - ftDamped η (sigGW2t ε v O p q) ω)
      (𝓝[>] 0) (𝓝 ((sox2 ε v O ω p q + relax ε v O p q : ℝ) : ℂ)) := by
  have h := (tendsto_const_nhds (x := ((cf 2 (sigmaT ε v O ω) p q : ℝ) : ℂ))).sub
    (gw2_limit hv1 hωGW p q)
  convert h using 2
  rw [sigma2_eq_direct_add_sox_add_relax hv1 hv2 hnd hω, of_apply]; push_cast; ring

/-- **Brillouin case.** `Σ_exact⁽²⁾ - Σ_GW⁽²⁾ → SOX`: the second-order error of G0W0 is
exactly the second-order exchange diagram. -/
theorem gw_error_second_order_brillouin (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) (hω : OffPoles ε O ω)
    (hωGW : GWOffPoles ε O ω) (hB : ∀ a ∈ O, ∀ r ∉ O, sig1 v O r a = 0) (p q : Fin n) :
    Tendsto (fun η => ((cf 2 (sigmaT ε v O ω) p q : ℝ) : ℂ) - ftDamped η (sigGW2t ε v O p q) ω)
      (𝓝[>] 0) (𝓝 ((sox2 ε v O ω p q : ℝ) : ℂ)) := by
  have h := gw_error_second_order hv1 hv2 hnd hω hωGW p q
  rwa [relax_eq_zero_of_brillouin hB, add_zero] at h

/-- The same statement as an identity of coefficients, with `Σ_GW⁽²⁾ := dir2`:
`Σ_exact⁽²⁾ - Σ_GW⁽²⁾ = SOX + relax`. `gw2_limit` proves `dir2` is the G0W0 value only
at `ω` with `GWOffPoles ε O ω`, which this theorem does not assume; elsewhere it is an
identity of the totalized `dir2`, `sox2`. -/
theorem gw_error_coeff2 (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) (hω : OffPoles ε O ω) :
    cf 2 (sigmaT ε v O ω) - Matrix.of (dir2 ε v O ω) =
      Matrix.of fun p q => sox2 ε v O ω p q + relax ε v O p q := by
  rw [sigma2_eq_direct_add_sox_add_relax hv1 hv2 hnd hω]
  ext p q; simp only [sub_apply, of_apply]; ring

end GW.Endpoint.ManyBody
