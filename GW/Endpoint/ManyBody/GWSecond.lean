/-
A3(a), stage S5: the G0W0 self-energy of the same general finite fermion system,
through second order in the coupling, and the structure of the GW error.

G0W0 is built from the SAME `G0` as the exact expansion (orbital energies `ε`,
occupied set `O`, occupations `f_m = [m ∈ O]`) and the RPA screened interaction
`W = λ v + λ² v χ0 v + O(λ³)`:

* first order: `Σ_GW⁽¹⁾ = Σ_H + Σ_x`, the Hartree and bare-exchange potentials of
  the occupied orbitals (`sigH`, `sigX`); `gw1_eq_HF`: this is `Σ1`.
* second order: `Σ_GW⁽²⁾ = i G0 W⁽²⁾` with `W⁽²⁾ = v χ0 v` and `χ0 = -i G0 G0`, built
  in the time domain on the orbital-pair basis (`G0t`, `chi0t`, `W2t`, `sigGW2t`):

    G0_m(τ)   = -i [θ(τ)(1 - f_m) - θ(-τ) f_m] e^{-i ε_m τ},
    χ0_{m m'}(τ) = -i G0_m(τ) G0_{m'}(-τ)        (pair (m, m'): density φ_{m'}* φ_m),
    W⁽²⁾_{(pn),(nq)}(τ) = Σ_{m m'} v_{p m' n m} χ0_{m m'}(τ) v_{m n m' q},
    Σ⁽²⁾_pq(τ) = i Σ_n G0_n(τ) W⁽²⁾_{(pn),(nq)}(τ)

  (this is `Σ(1,2) = i G0(1,2) W(1,2)` with `W(1,2) = ∫ v(1,3) χ0(3,4) v(4,2)` and
  `χ0(3,4) = -i G0(3,4) G0(4,3)`, projected on the orbitals; `v` is instantaneous, so
  the λ² term of the RPA series `W = (1 - λ v χ0)⁻¹ λ v` is the pointwise product
  `v χ0(τ) v`). Frequency: the damped Fourier transform `ftDamped` of the dimer
  development (`HubbardDimerSigma.lean`), limit `η → 0⁺`, real `ω` off the poles.

Proved (`gw2_limit`, for `ω` with `GWOffPoles ε O ω`): the transform converges to
`dir2`, the second-order DIRECT (ring) self-energy. Hence (`gw_error_second_order`, which
also assumes `GWOffPoles`):

  Σ_exact⁽¹⁾ = Σ_GW⁽¹⁾,   Σ_exact⁽²⁾ - Σ_GW⁽²⁾ = SOX + relax,

and `= SOX` under the Brillouin condition. `sox2` is exactly the part of the
second-order exact self-energy that G0W0 lacks; `relax` is the static
density-relaxation term that G0W0 with a fixed `G0` also lacks.

Remark (visible in the hypotheses): `dir2` alone has poles at `ω = ε_r + ε_s - ε_a`
and `ω = ε_a + ε_b - ε_r` also for `r = s` and `a = b` (self-screening); they cancel
against `sox2` in the exact result, whose poles are Fock-space excitations only.
-/
import GW.Endpoint.ManyBody.DirectSOX
import GW.Endpoint.HubbardDimerSigma

namespace GW.Endpoint.ManyBody

open Matrix Finset Complex MeasureTheory Filter Topology
open GW.Endpoint.HubbardDimer (ftDamped twoSided expSum ftDamped_twoSided_limit)

variable {n : ℕ} (ε : Fin n → ℝ) (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n)

/-- Occupation `f_m ∈ {0, 1}`. -/
def occ (m : Fin n) : ℝ := if m ∈ O then 1 else 0

/-- Hartree potential of the occupied orbitals. -/
def sigH (p q : Fin n) : ℝ := ∑ a ∈ O, v p a q a

/-- Bare exchange of the occupied orbitals. -/
def sigX (p q : Fin n) : ℝ := -∑ a ∈ O, v p a a q

/-- Time-ordered `G0_m(τ)`. -/
noncomputable def G0t (m : Fin n) (τ : ℝ) : ℂ :=
  -I * ((if 0 < τ then 1 - occ O m else -occ O m : ℝ) : ℂ) * Complex.exp (-(I * ε m * τ))

/-- Independent-particle response on the pair `(m, m')`: `χ0 = -i G0 G0`. -/
noncomputable def chi0t (m m' : Fin n) (τ : ℝ) : ℂ := -I * G0t ε O m τ * G0t ε O m' (-τ)

/-- `W⁽²⁾ = v χ0 v` on the pairs `(p n)`, `(n q)`. -/
noncomputable def W2t (p nn q : Fin n) (τ : ℝ) : ℂ :=
  ∑ m, ∑ m', (v p m' nn m : ℂ) * chi0t ε O m m' τ * (v m nn m' q : ℂ)

/-- `Σ⁽²⁾_GW(τ) = i G0 W⁽²⁾`. -/
noncomputable def sigGW2t (p q : Fin n) (τ : ℝ) : ℂ :=
  I * ∑ nn, G0t ε O nn τ * W2t ε v O p nn q τ

/-- The poles of the second-order GW self-energy. -/
def GWOffPoles (ω : ℝ) : Prop :=
  (∀ a ∈ O, ∀ r ∉ O, ∀ s ∉ O, ω + ε a - ε r - ε s ≠ 0) ∧
    (∀ r ∉ O, ∀ a ∈ O, ∀ b ∈ O, ω + ε r - ε a - ε b ≠ 0)

variable {ε v O}

theorem gw1_eq_HF (p q : Fin n) : sigH v O p q + sigX v O p q = sig1 v O p q := by
  simp only [sigH, sigX, sig1, asym, sum_sub_distrib]; ring

/-! ### `Σ⁽²⁾_GW(τ)` as a two-sided exponential sum -/

/-- The triples `(n, m, m')` as a list. -/
noncomputable def triples (n : ℕ) : List (Fin n × Fin n × Fin n) := Finset.univ.toList

/-- Forward (particle) coefficient. -/
noncomputable def cPlus (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n) (p q : Fin n) (t : Fin n × Fin n × Fin n) : ℝ :=
  v p t.2.2 t.1 t.2.1 * v t.2.1 t.1 t.2.2 q * ((1 - occ O t.1) * (1 - occ O t.2.1) * occ O t.2.2)

/-- Backward (hole) coefficient. -/
noncomputable def cMinus (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n) (p q : Fin n) (t : Fin n × Fin n × Fin n) : ℝ :=
  v p t.2.2 t.1 t.2.1 * v t.2.1 t.1 t.2.2 q * (occ O t.1 * occ O t.2.1 * (1 - occ O t.2.2))

/-- Pole position `ε_n + ε_m - ε_m'`. -/
def pole (ε : Fin n → ℝ) (t : Fin n × Fin n × Fin n) : ℝ := ε t.1 + ε t.2.1 - ε t.2.2

theorem list_sum_triples {M : Type*} [AddCommMonoid M] (f : Fin n × Fin n × Fin n → M) :
    ((triples n).map f).sum = ∑ nn, ∑ m, ∑ m', f (nn, m, m') := by
  rw [triples, Finset.sum_map_toList, Fintype.sum_prod_type, sum_congr rfl fun _ _ =>
    Fintype.sum_prod_type _]

theorem sigGW2t_eq (p q : Fin n) {τ : ℝ} (hτ : τ ≠ 0) :
    sigGW2t ε v O p q τ =
      twoSided ((triples n).map fun t => (-I * (cPlus v O p q t : ℂ), pole ε t))
        ((triples n).map fun t => (I * (cMinus v O p q t : ℂ), pole ε t)) τ := by
  have hI3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  have hI4 : I ^ 4 = 1 := Complex.I_pow_four
  have hI5 : I ^ 5 = I := by rw [pow_succ, hI4, one_mul]
  unfold twoSided expSum
  rw [List.map_map, List.map_map]
  split_ifs with h
  · rw [list_sum_triples]
    simp only [sigGW2t, W2t, chi0t, G0t, Function.comp, mul_sum]
    refine sum_congr rfl fun nn _ => sum_congr rfl fun m _ => sum_congr rfl fun m' _ => ?_
    rw [if_pos h, if_pos h, if_neg (by linarith)]
    simp only [cPlus, pole]
    push_cast
    rw [show -(I * ((ε nn : ℂ) + (ε m : ℂ) - (ε m' : ℂ)) * (τ : ℂ)) =
      -(I * ε nn * τ) + -(I * ε m * τ) + -(I * ε m' * -(τ : ℂ)) by ring,
      Complex.exp_add, Complex.exp_add]
    ring_nf; simp only [hI3, hI4, hI5, I_sq]
  · have h' : τ < 0 := lt_of_le_of_ne (not_lt.mp h) hτ
    rw [list_sum_triples]
    simp only [sigGW2t, W2t, chi0t, G0t, Function.comp, mul_sum]
    refine sum_congr rfl fun nn _ => sum_congr rfl fun m _ => sum_congr rfl fun m' _ => ?_
    rw [if_neg h, if_neg h, if_pos (by linarith)]
    simp only [cMinus, pole]
    push_cast
    rw [show -(I * ((ε nn : ℂ) + (ε m : ℂ) - (ε m' : ℂ)) * (τ : ℂ)) =
      -(I * ε nn * τ) + -(I * ε m * τ) + -(I * ε m' * -(τ : ℂ)) by ring,
      Complex.exp_add, Complex.exp_add]
    ring_nf; simp only [hI3, hI4, hI5, I_sq]

theorem ftDamped_congr_ne_zero {f g : ℝ → ℂ} (h : ∀ τ, τ ≠ 0 → f τ = g τ) (η ω : ℝ) :
    ftDamped η f ω = ftDamped η g ω := by
  unfold ftDamped
  apply integral_congr_ae
  have h0 : ∀ᵐ τ : ℝ ∂volume, τ ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with τ hτ
  rw [h τ hτ]

/-! ### The limit `η → 0⁺` -/

theorem occ_mem {m : Fin n} (h : m ∈ O) : occ O m = 1 := by simp [occ, h]
theorem occ_not_mem {m : Fin n} (h : m ∉ O) : occ O m = 0 := by simp [occ, h]

theorem sum_occ_restrict (g : Fin n → Fin n → Fin n → ℝ) :
    ∑ nn, ∑ m, ∑ m', g nn m m' * ((1 - occ O nn) * (1 - occ O m) * occ O m') =
      ∑ nn ∈ Oᶜ, ∑ m ∈ Oᶜ, ∑ m' ∈ O, g nn m m' := by
  rw [sum_univ_eq_sum_of Oᶜ _ fun nn hn => sum_eq_zero fun m _ => sum_eq_zero fun m' _ => by
    rw [occ_mem (m := nn) (by simpa using hn)]; ring]
  refine sum_congr rfl fun nn hn => ?_
  rw [sum_univ_eq_sum_of Oᶜ _ fun m hm => sum_eq_zero fun m' _ => by
    rw [occ_mem (m := m) (by simpa using hm)]; ring]
  refine sum_congr rfl fun m hm => ?_
  rw [sum_univ_eq_sum_of O _ fun m' hm' => by rw [occ_not_mem hm']; ring]
  refine sum_congr rfl fun m' hm' => ?_
  rw [occ_not_mem (mem_compl.mp hn), occ_not_mem (mem_compl.mp hm), occ_mem hm']; ring

theorem sum_occ_restrict' (g : Fin n → Fin n → Fin n → ℝ) :
    ∑ nn, ∑ m, ∑ m', g nn m m' * (occ O nn * occ O m * (1 - occ O m')) =
      ∑ nn ∈ O, ∑ m ∈ O, ∑ m' ∈ Oᶜ, g nn m m' := by
  rw [sum_univ_eq_sum_of O _ fun nn hn => sum_eq_zero fun m _ => sum_eq_zero fun m' _ => by
    rw [occ_not_mem hn]; ring]
  refine sum_congr rfl fun nn hn => ?_
  rw [sum_univ_eq_sum_of O _ fun m hm => sum_eq_zero fun m' _ => by rw [occ_not_mem hm]; ring]
  refine sum_congr rfl fun m hm => ?_
  rw [sum_univ_eq_sum_of Oᶜ _ fun m' hm' => by rw [occ_mem (m := m') (by simpa using hm')]; ring]
  refine sum_congr rfl fun m' hm' => ?_
  rw [occ_mem hn, occ_mem hm, occ_not_mem (mem_compl.mp hm')]; ring

/-- The real value of the limit is the direct (ring) self-energy. -/
theorem gw2_value (hv1 : ∀ p q r s, v p q r s = v q p s r) (ω : ℝ) (p q : Fin n) :
    (∑ nn, ∑ m, ∑ m', cPlus v O p q (nn, m, m') / (ω - pole ε (nn, m, m'))) +
      (∑ nn, ∑ m, ∑ m', cMinus v O p q (nn, m, m') / (ω - pole ε (nn, m, m'))) =
      dir2 ε v O ω p q := by
  have e1 : ∀ nn m m', cPlus v O p q (nn, m, m') / (ω - pole ε (nn, m, m')) =
      (v p m' nn m * v m nn m' q / (ω - pole ε (nn, m, m'))) *
        ((1 - occ O nn) * (1 - occ O m) * occ O m') := by
    intro nn m m'; simp only [cPlus]; ring
  have e2 : ∀ nn m m', cMinus v O p q (nn, m, m') / (ω - pole ε (nn, m, m')) =
      (v p m' nn m * v m nn m' q / (ω - pole ε (nn, m, m'))) *
        (occ O nn * occ O m * (1 - occ O m')) := by
    intro nn m m'; simp only [cMinus]; ring
  simp only [e1, e2]
  rw [sum_occ_restrict (O := O) (fun nn m m' => v p m' nn m * v m nn m' q / (ω - pole ε (nn, m, m'))),
    sum_occ_restrict' (O := O) (fun nn m m' => v p m' nn m * v m nn m' q / (ω - pole ε (nn, m, m')))]
  rw [dir2]
  congr 1
  · -- particles: (nn, m, m') = (r, s, a)
    rw [sum3_rotate]
    refine sum_congr rfl fun a _ => sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
    rw [hv1 s r a q, pole]; ring_nf
  · -- holes: (nn, m, m') = (a, b, r)
    rw [sum3_rotate]
    refine sum_congr rfl fun r _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [hv1 b a r q, pole]; ring_nf

/-- **S5: G0W0 at second order is the direct (ring) term.** For real `ω` off the GW
poles, the damped Fourier transform of `Σ⁽²⁾_GW(τ) = i G0 v χ0 v` converges as
`η → 0⁺` to `dir2`. -/
theorem gw2_limit (hv1 : ∀ p q r s, v p q r s = v q p s r) {ω : ℝ} (hω : GWOffPoles ε O ω)
    (p q : Fin n) :
    Tendsto (fun η => ftDamped η (sigGW2t ε v O p q) ω) (𝓝[>] 0)
      (𝓝 ((dir2 ε v O ω p q : ℝ) : ℂ)) := by
  have hc : ∀ η, ftDamped η (sigGW2t ε v O p q) ω =
      ftDamped η (twoSided ((triples n).map fun t => (-I * (cPlus v O p q t : ℂ), pole ε t))
        ((triples n).map fun t => (I * (cMinus v O p q t : ℂ), pole ε t))) ω :=
    fun η => ftDamped_congr_ne_zero (fun τ hτ => sigGW2t_eq p q hτ) η ω
  simp only [hc]
  convert ftDamped_twoSided_limit _ _ ω ?_ ?_ using 2
  · rw [List.map_map, List.map_map, list_sum_triples, list_sum_triples, ← gw2_value hv1 ω p q]
    push_cast
    congr 1 <;> refine sum_congr rfl fun nn _ => sum_congr rfl fun m _ => sum_congr rfl fun m' _ => ?_
    · simp only [Function.comp]
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring_nf; rw [I_sq]; ring
    · simp only [Function.comp]
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring_nf; rw [I_sq]; ring
  · simp only [List.mem_map]
    rintro _ ⟨t, _, rfl⟩ hz
    have hc : cPlus v O p q t ≠ 0 := by
      intro h; apply hz; simp [h]
    obtain ⟨nn, m, m'⟩ := t
    simp only [cPlus] at hc
    have hn : nn ∉ O := fun h => hc (by rw [occ_mem h]; ring)
    have hm : m ∉ O := fun h => hc (by rw [occ_mem h]; ring)
    have hm' : m' ∈ O := Classical.byContradiction fun h => hc (by rw [occ_not_mem h]; ring)
    have := hω.1 m' hm' nn hn m hm
    intro h0; apply this
    simp only [pole] at h0; linarith
  · simp only [List.mem_map]
    rintro _ ⟨t, _, rfl⟩ hz
    have hc : cMinus v O p q t ≠ 0 := by
      intro h; apply hz; simp [h]
    obtain ⟨nn, m, m'⟩ := t
    simp only [cMinus] at hc
    have hn : nn ∈ O := Classical.byContradiction fun h => hc (by rw [occ_not_mem h]; ring)
    have hm : m ∈ O := Classical.byContradiction fun h => hc (by rw [occ_not_mem h]; ring)
    have hm' : m' ∉ O := fun h => hc (by rw [occ_mem h]; ring)
    have := hω.2 m' hm' nn hn m hm
    intro h0; apply this
    simp only [pole] at h0; linarith

end GW.Endpoint.ManyBody
