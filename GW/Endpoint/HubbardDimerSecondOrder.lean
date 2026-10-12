/-
A3 dimer, part 2 (Task 4): the exact U² coefficients of the exact, G0W0@HF and
HF gaps of the half-filled Hubbard dimer, and their diagrammatic identification:
the U² term that G0W0@HF gets wrong is exactly the second-order exchange (SOX)
diagram.

Setup (restricted HF reference of `HubbardDimer.lean`; orbital index
`0 = B` bonding/occupied, `1 = A` antibonding/empty; energies `epsB`, `epsA`):

* Two-electron integrals, physicists' notation
  `<pq|rs> = Σ_{ijkl} φ_p(i) φ_q(j) φ_r(k) φ_s(l) v_ijkl` with the contact
  interaction of the Fock-space file in the site basis, `v_ijkl = U` iff
  `i = j = k = l` (`vSite`). `eri_eq`: `<pq|rs> = U/2` if the number of `A`
  labels is even, `0` otherwise.
* Second-order self-energy (as in `bgw/endpoint/second_order.py`, a, b occupied,
  r, s empty), split into its direct (ring, the "2" terms, contained in GW)
  and exchange (SOX, the "-1" terms, not in GW) parts:
    Σ2_pp(E) = Σ_{a r s} <pa|rs>(2<rs|pa> - <rs|ap>)/(E + e_a - e_r - e_s)
             + Σ_{a b r} <pr|ab>(2<ab|pr> - <ab|rp>)/(E + e_r - e_a - e_b).
* Gap contributions at the HF energies:
  `gap2dir = Σ2dir_AA(epsA) - Σ2dir_BB(epsB) = U²/(4t)` (`gap2dir_eq`),
  `gap2x   = Σ2x_AA(epsA)   - Σ2x_BB(epsB)   = -U²/(8t)` (`gap2x_eq`).

Results (t > 0):
* `gw_U2_coeff` (i): `|gapGW - (gapHF + gap2dir)| <= U³/(4t²)` on `[0, t]`, and
  `(gapGW - gapHF)/U² -> 1/(4t)`: the U² coefficient of G0W0@HF is HF + direct.
* `exact_U2_coeff` (ii): `|gapExact - (gapHF + gap2dir + gap2x)| <= U⁴/(512t³)`
  on `[0, 2t]`, and `(gapExact - gapHF)/U² -> 1/(8t)`: HF + direct + exchange.
* `gw_error_is_minus_sox` (iii): `|(gapGW - gapExact) + gap2x| <= 3U³/(16t²)`,
  i.e. `gapGW - gapExact = -(SOX)·… = U²/(8t) + O(U³)`.
* `hf_U2_coeff`: `gapHF = 2t` exactly (zero U² coefficient; first-order shifts
  cancel in the gap).
* `sigBB_second_order`, `sigAA_second_order`: the G0W0@HF correlation
  self-energy at the HF energy equals the second-order DIRECT self-energy up
  to o(U²) (GW's U² content is the ring diagram, not the exchange diagram).

What this does NOT say: these are statements about this two-site model and
this restricted-HF reference only; the O(U³) remainders are explicit only on the
stated intervals of U.
-/
import GW.Endpoint.HubbardDimer

namespace GW.Endpoint.HubbardDimer

open Filter Topology

/-! ### Two-electron integrals in the orbital basis -/

/-- Orbital `p` in the site basis: `0 ↦ phiB`, `1 ↦ phiA`. -/
noncomputable def orb : Fin 2 → Fin 2 → ℝ := ![phiB, phiA]

/-- HF orbital energies: `0 ↦ epsB`, `1 ↦ epsA`. -/
noncomputable def epsOrb (t U : ℝ) : Fin 2 → ℝ := ![epsB t U, epsA t U]

/-- Site-basis contact interaction `<ij|kl> = U δ_ij δ_ik δ_il`. -/
noncomputable def vSite (U : ℝ) (i j k l : Fin 2) : ℝ := if i = j ∧ i = k ∧ i = l then U else 0

/-- `<pq|rs>` in the HF orbital basis, by transformation from the site basis. -/
noncomputable def eri (U : ℝ) (p q r s : Fin 2) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2,
    orb p i * orb q j * orb r k * orb s l * vSite U i j k l

/-- The orbital-basis integrals: `U/2` for an even number of antibonding labels, else `0`. -/
theorem eri_eq (U : ℝ) (p q r s : Fin 2) :
    eri U p q r s = if (p.val + q.val + r.val + s.val) % 2 = 0 then U / 2 else 0 := by
  have h4 := s2_pow4
  fin_cases p <;> fin_cases q <;> fin_cases r <;> fin_cases s <;>
    simp [eri, vSite, orb, phiB, phiA, Fin.sum_univ_two] <;> ring_nf <;> rw [h4] <;> ring

/-! ### Second-order self-energy: direct (ring) and exchange (SOX) parts -/

/-- Occupied and empty orbitals of the restricted HF reference. -/
def occS : Finset (Fin 2) := {0}
def virS : Finset (Fin 2) := {1}

/-- Second-order direct (ring) self-energy, the "2" terms. -/
noncomputable def sig2dir (t U : ℝ) (p : Fin 2) (E : ℝ) : ℝ :=
  (∑ a ∈ occS, ∑ r ∈ virS, ∑ s ∈ virS, eri U p a r s * (2 * eri U r s p a) /
      (E + epsOrb t U a - epsOrb t U r - epsOrb t U s)) +
    ∑ a ∈ occS, ∑ b ∈ occS, ∑ r ∈ virS, eri U p r a b * (2 * eri U a b p r) /
      (E + epsOrb t U r - epsOrb t U a - epsOrb t U b)

/-- Second-order exchange (SOX) self-energy, the "-1" terms. -/
noncomputable def sig2x (t U : ℝ) (p : Fin 2) (E : ℝ) : ℝ :=
  (∑ a ∈ occS, ∑ r ∈ virS, ∑ s ∈ virS, eri U p a r s * (-eri U r s a p) /
      (E + epsOrb t U a - epsOrb t U r - epsOrb t U s)) +
    ∑ a ∈ occS, ∑ b ∈ occS, ∑ r ∈ virS, eri U p r a b * (-eri U a b r p) /
      (E + epsOrb t U r - epsOrb t U a - epsOrb t U b)

/-- Contribution to the gap `Σ_AA(epsA) - Σ_BB(epsB)`. -/
noncomputable def gap2dir (t U : ℝ) : ℝ := sig2dir t U 1 (epsA t U) - sig2dir t U 0 (epsB t U)
noncomputable def gap2x (t U : ℝ) : ℝ := sig2x t U 1 (epsA t U) - sig2x t U 0 (epsB t U)

section Values
variable {t : ℝ} (U : ℝ)

theorem sig2dir_B (ht : 0 < t) : sig2dir t U 0 (epsB t U) = -(U ^ 2 / (8 * t)) := by
  simp [sig2dir, occS, virS, eri_eq, epsOrb, epsA, epsB]
  have := ht.ne'
  field_simp; ring_nf; field_simp

theorem sig2dir_A (ht : 0 < t) : sig2dir t U 1 (epsA t U) = U ^ 2 / (8 * t) := by
  simp [sig2dir, occS, virS, eri_eq, epsOrb, epsA, epsB]
  have := ht.ne'
  field_simp; ring_nf; field_simp

theorem sig2x_B (ht : 0 < t) : sig2x t U 0 (epsB t U) = U ^ 2 / (16 * t) := by
  simp [sig2x, occS, virS, eri_eq, epsOrb, epsA, epsB]
  have := ht.ne'
  field_simp; ring_nf; field_simp

theorem sig2x_A (ht : 0 < t) : sig2x t U 1 (epsA t U) = -(U ^ 2 / (16 * t)) := by
  simp [sig2x, occS, virS, eri_eq, epsOrb, epsA, epsB]
  have := ht.ne'
  field_simp; ring_nf; field_simp

/-- Second-order direct (ring) gap contribution: `+U²/(4t)`. -/
theorem gap2dir_eq (ht : 0 < t) : gap2dir t U = U ^ 2 / (4 * t) := by
  unfold gap2dir; rw [sig2dir_A U ht, sig2dir_B U ht]; field_simp; ring

/-- Second-order exchange (SOX) gap contribution: `-U²/(8t)`. -/
theorem gap2x_eq (ht : 0 < t) : gap2x t U = -(U ^ 2 / (8 * t)) := by
  unfold gap2x; rw [sig2x_A U ht, sig2x_B U ht]; field_simp; ring

end Values

/-! ### The U² coefficients -/

section Coefficients
variable {t : ℝ}

/-- Helper: `f / U² → c` along `U → 0⁺` from `|f U - c U²| <= K U³` near 0. -/
theorem tendsto_div_sq_of_bound {f : ℝ → ℝ} {c K δ : ℝ} (hδ : 0 < δ)
    (h : ∀ U, 0 < U → U ≤ δ → |f U - c * U ^ 2| ≤ K * U ^ 3) :
    Tendsto (fun U => f U / U ^ 2) (𝓝[>] 0) (𝓝 c) := by
  have hK : Tendsto (fun U : ℝ => c - |K| * U) (𝓝[>] 0) (𝓝 c) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa using ((continuous_const.sub (continuous_const.mul continuous_id)).tendsto (0 : ℝ) :
      Tendsto (fun U : ℝ => c - |K| * U) (𝓝 0) _)
  have hK' : Tendsto (fun U : ℝ => c + |K| * U) (𝓝[>] 0) (𝓝 c) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa using ((continuous_const.add (continuous_const.mul continuous_id)).tendsto (0 : ℝ) :
      Tendsto (fun U : ℝ => c + |K| * U) (𝓝 0) _)
  have hev : ∀ᶠ U in 𝓝[>] (0 : ℝ), U ∈ Set.Ioo 0 δ := Ioo_mem_nhdsGT hδ
  have key : ∀ U, 0 < U → U ≤ δ → |f U / U ^ 2 - c| ≤ |K| * U := by
    intro U h0 h1
    have hU2 : 0 < U ^ 2 := pow_pos h0 2
    have e : f U / U ^ 2 - c = (f U - c * U ^ 2) / U ^ 2 := by field_simp; ring
    rw [e, abs_div, abs_of_pos hU2, div_le_iff₀ hU2]
    calc |f U - c * U ^ 2| ≤ K * U ^ 3 := h U h0 h1
      _ ≤ |K| * U ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      _ = |K| * U * U ^ 2 := by ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hK hK' ?_ ?_
  · filter_upwards [hev] with U hU
    have := key U hU.1 hU.2.le; rw [abs_le] at this; linarith
  · filter_upwards [hev] with U hU
    have := key U hU.1 hU.2.le; rw [abs_le] at this; linarith

/-- HF: the gap is `2t` exactly, so its U² coefficient is zero. -/
theorem hf_U2_coeff (U : ℝ) : gapHF t U = 2 * t := gapHF_eq t U

/-- Exact gap: `gapExact - 2t - U²/(8t) ∈ [-U⁴/(512t³), 0]` on `[0, 2t]`. -/
theorem exact_expansion {U : ℝ} (ht : 0 < t) (hU : 0 ≤ U) (hUt : U ≤ 2 * t) :
    -(U ^ 4 / (512 * t ^ 3)) ≤ gapExact t U - (2 * t + U ^ 2 / (8 * t)) ∧
      gapExact t U - (2 * t + U ^ 2 / (8 * t)) ≤ 0 := by
  obtain ⟨l, r⟩ := hf_error_bounds ht hU hUt
  rw [gapHF_eq] at l r
  constructor <;> linarith

/-- **(ii) Exact U² coefficient = HF + direct + exchange.** -/
theorem exact_U2_coeff (ht : 0 < t) :
    (∀ U, 0 ≤ U → U ≤ 2 * t →
      |gapExact t U - (gapHF t U + gap2dir t U + gap2x t U)| ≤ U ^ 4 / (512 * t ^ 3)) ∧
    Tendsto (fun U => (gapExact t U - gapHF t U) / U ^ 2) (𝓝[>] 0) (𝓝 (1 / (8 * t))) := by
  have hb : ∀ U, 0 ≤ U → U ≤ 2 * t →
      |gapExact t U - (gapHF t U + gap2dir t U + gap2x t U)| ≤ U ^ 4 / (512 * t ^ 3) := by
    intro U hU hUt
    obtain ⟨l, r⟩ := exact_expansion ht hU hUt
    have e : gapHF t U + gap2dir t U + gap2x t U = 2 * t + U ^ 2 / (8 * t) := by
      rw [gapHF_eq, gap2dir_eq U ht, gap2x_eq U ht]; field_simp; ring
    rw [e, abs_le]; constructor <;> linarith [show 0 ≤ U ^ 4 / (512 * t ^ 3) by positivity]
  refine ⟨hb, tendsto_div_sq_of_bound (K := 1 / (256 * t ^ 2)) (by linarith : (0 : ℝ) < 2 * t) ?_⟩
  intro U hU hUt
  have h := hb U hU.le hUt
  have e : gapHF t U + gap2dir t U + gap2x t U = gapHF t U + 1 / (8 * t) * U ^ 2 := by
    rw [gap2dir_eq U ht, gap2x_eq U ht]; field_simp; ring
  rw [e, show gapExact t U - (gapHF t U + 1 / (8 * t) * U ^ 2) =
    gapExact t U - gapHF t U - 1 / (8 * t) * U ^ 2 by ring] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have : 1 / (256 * t ^ 2) * U ^ 3 * (512 * t ^ 3) = 2 * t * U ^ 3 := by field_simp; ring
  rw [this]; nlinarith [pow_pos hU 3]

/-- **(i) G0W0@HF U² coefficient = HF + direct (ring) only.** -/
theorem gw_U2_coeff (ht : 0 < t) :
    (∀ U, 0 ≤ U → U ≤ t → |gapGW t U - (gapHF t U + gap2dir t U)| ≤ U ^ 3 / (4 * t ^ 2)) ∧
    Tendsto (fun U => (gapGW t U - gapHF t U) / U ^ 2) (𝓝[>] 0) (𝓝 (1 / (4 * t))) := by
  have hb : ∀ U, 0 ≤ U → U ≤ t → |gapGW t U - (gapHF t U + gap2dir t U)| ≤ U ^ 3 / (4 * t ^ 2) := by
    intro U hU hUt
    obtain ⟨g1, g2⟩ := gw_error_bounds ht hU hUt
    obtain ⟨x1, x2⟩ := exact_expansion ht hU (by linarith)
    have e : gapHF t U + gap2dir t U = 2 * t + U ^ 2 / (4 * t) := by
      rw [gapHF_eq, gap2dir_eq U ht]
    have q : U ^ 4 / (512 * t ^ 3) ≤ U ^ 3 / (512 * t ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : U ^ 4 * (512 * t ^ 2) ≤ U ^ 3 * (512 * t ^ 3) := by
        have : U ^ 4 * (512 * t ^ 2) = (U ^ 3 * (512 * t ^ 2)) * U := by ring
        rw [this, show U ^ 3 * (512 * t ^ 3) = (U ^ 3 * (512 * t ^ 2)) * t by ring]
        exact mul_le_mul_of_nonneg_left hUt (by positivity)
      exact this
    have s1 : U ^ 2 / (4 * t) = U ^ 2 / (8 * t) + U ^ 2 / (8 * t) := by field_simp; ring
    have s2' : U ^ 3 / (4 * t ^ 2) = 3 * U ^ 3 / (16 * t ^ 2) + U ^ 3 / (512 * t ^ 2)
        + 31 * U ^ 3 / (512 * t ^ 2) := by field_simp; ring
    have s3 : 0 ≤ U ^ 3 / (16 * t ^ 2) := by positivity
    have s4 : 0 ≤ 31 * U ^ 3 / (512 * t ^ 2) := by positivity
    have s5 : U ^ 3 / (16 * t ^ 2) ≤ U ^ 3 / (4 * t ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_nonneg hU 3, sq_nonneg t]
    rw [e, abs_le]; constructor <;> linarith
  refine ⟨hb, tendsto_div_sq_of_bound (K := 1 / (4 * t ^ 2)) ht ?_⟩
  intro U hU hUt
  have h := hb U hU.le hUt
  rw [gap2dir_eq U ht, show gapGW t U - (gapHF t U + U ^ 2 / (4 * t)) =
    gapGW t U - gapHF t U - 1 / (4 * t) * U ^ 2 by field_simp; ring] at h
  refine h.trans (le_of_eq ?_); field_simp

/-- **(iii) The G0W0@HF gap error is minus the SOX contribution, up to O(U³):**
`|(gapGW - gapExact) - (-gap2x)| <= 3U³/(16t²)` on `[0, t]`, with
`-gap2x = U²/(8t)`. -/
theorem gw_error_is_minus_sox (ht : 0 < t) :
    (∀ U, 0 ≤ U → U ≤ t → |(gapGW t U - gapExact t U) + gap2x t U| ≤ 3 * U ^ 3 / (16 * t ^ 2)) ∧
    (∀ U, -gap2x t U = U ^ 2 / (8 * t)) ∧
    Tendsto (fun U => (gapGW t U - gapExact t U) / U ^ 2) (𝓝[>] 0) (𝓝 (1 / (8 * t))) := by
  refine ⟨?_, fun U => by rw [gap2x_eq U ht]; ring, gw_error_leading ht⟩
  intro U hU hUt
  obtain ⟨g1, g2⟩ := gw_error_bounds ht hU hUt
  rw [gap2x_eq U ht, abs_le]
  have : 0 ≤ U ^ 3 / (16 * t ^ 2) := by positivity
  have e : 3 * U ^ 3 / (16 * t ^ 2) = 3 * (U ^ 3 / (16 * t ^ 2)) := by ring
  constructor <;> linarith

end Coefficients

/-! ### GW's second-order content is the direct (ring) diagram -/

section GWContent
variable {t : ℝ}

theorem hRPA_continuous (t : ℝ) : Continuous fun U => hRPA t U := by
  unfold hRPA; fun_prop

theorem hRPA_zero (ht : 0 < t) : hRPA t 0 = 2 * t := by
  unfold hRPA; rw [show 4 * t ^ 2 + 4 * t * 0 = (2 * t) ^ 2 by ring]
  exact Real.sqrt_sq (by linarith)

/-- The G0W0@HF removal self-energy at the HF energy, divided by U², tends to the
second-order direct coefficient `-1/(8t)` (`sig2dir_B`), so
`sigBB(epsB) - Σ2dir_BB(epsB) = o(U²)`. -/
theorem sigBB_second_order (ht : 0 < t) :
    Tendsto (fun U => sigBB t U (epsB t U) / U ^ 2) (𝓝[>] 0) (𝓝 (-(1 / (8 * t)))) ∧
    Tendsto (fun U => (sigBB t U (epsB t U) - sig2dir t U 0 (epsB t U)) / U ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hc : Tendsto (fun U => t / hRPA t U / (-(2 * t) - hRPA t U)) (𝓝[>] 0)
      (𝓝 (-(1 / (8 * t)))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have := ht.ne'
    have h0 := hRPA_zero ht
    have hh : Tendsto (fun U => hRPA t U) (𝓝 0) (𝓝 (2 * t)) := h0 ▸ (hRPA_continuous t).tendsto 0
    have := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => t) (𝓝 0) (𝓝 t)).div hh
      (by positivity)).div ((tendsto_const_nhds : Tendsto (fun _ : ℝ => -(2 * t)) (𝓝 0) _).sub hh)
      (by nlinarith : -(2 * t) - 2 * t ≠ 0)
    convert this using 2; field_simp; ring_nf; field_simp
  have hev : (fun U => t / hRPA t U / (-(2 * t) - hRPA t U)) =ᶠ[𝓝[>] 0]
      fun U => sigBB t U (epsB t U) / U ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with U hU
    have hU' : (U : ℝ) ≠ 0 := ne_of_gt hU
    have hp := hRPA_pos ht (le_of_lt hU)
    have hd : -(2 * t) - hRPA t U ≠ 0 := by linarith
    unfold sigBB; rw [show epsB t U - epsA t U - hRPA t U = -(2 * t) - hRPA t U by
      unfold epsA epsB; ring]
    field_simp; ring
  have h1 := hc.congr' hev
  refine ⟨h1, ?_⟩
  have hev2 : (fun U => sigBB t U (epsB t U) / U ^ 2 - (-(1 / (8 * t)))) =ᶠ[𝓝[>] 0]
      fun U => (sigBB t U (epsB t U) - sig2dir t U 0 (epsB t U)) / U ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with U hU
    have hU' : (U : ℝ) ≠ 0 := ne_of_gt hU
    have := ht.ne'
    rw [sig2dir_B U ht, sub_div, neg_div, show U ^ 2 / (8 * t) / U ^ 2 = 1 / (8 * t) by field_simp; ring]
  simpa using (h1.sub_const (-(1 / (8 * t)))).congr' hev2

/-- Same for the addition self-energy: `sigAA(epsA)/U² -> 1/(8t)`, the
second-order direct coefficient (`sig2dir_A`). -/
theorem sigAA_second_order (ht : 0 < t) :
    Tendsto (fun U => sigAA t U (epsA t U) / U ^ 2) (𝓝[>] 0) (𝓝 (1 / (8 * t))) ∧
    Tendsto (fun U => (sigAA t U (epsA t U) - sig2dir t U 1 (epsA t U)) / U ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hc : Tendsto (fun U => t / hRPA t U / (2 * t + hRPA t U)) (𝓝[>] 0)
      (𝓝 (1 / (8 * t))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have := ht.ne'
    have h0 := hRPA_zero ht
    have hh : Tendsto (fun U => hRPA t U) (𝓝 0) (𝓝 (2 * t)) := h0 ▸ (hRPA_continuous t).tendsto 0
    have := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => t) (𝓝 0) (𝓝 t)).div hh
      (by positivity)).div ((tendsto_const_nhds : Tendsto (fun _ : ℝ => 2 * t) (𝓝 0) _).add hh)
      (by nlinarith : 2 * t + 2 * t ≠ 0)
    convert this using 2; field_simp; ring
  have hev : (fun U => t / hRPA t U / (2 * t + hRPA t U)) =ᶠ[𝓝[>] 0]
      fun U => sigAA t U (epsA t U) / U ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with U hU
    have hU' : (U : ℝ) ≠ 0 := ne_of_gt hU
    have hp := hRPA_pos ht (le_of_lt hU)
    have hd : 2 * t + hRPA t U ≠ 0 := by linarith
    unfold sigAA; rw [show epsA t U - epsB t U + hRPA t U = 2 * t + hRPA t U by
      unfold epsA epsB; ring]
    field_simp; ring
  have h1 := hc.congr' hev
  refine ⟨h1, ?_⟩
  have hev2 : (fun U => sigAA t U (epsA t U) / U ^ 2 - 1 / (8 * t)) =ᶠ[𝓝[>] 0]
      fun U => (sigAA t U (epsA t U) - sig2dir t U 1 (epsA t U)) / U ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with U hU
    have hU' : (U : ℝ) ≠ 0 := ne_of_gt hU
    have := ht.ne'
    rw [sig2dir_A U ht, sub_div, show U ^ 2 / (8 * t) / U ^ 2 = 1 / (8 * t) by field_simp; ring]
  simpa using (h1.sub_const (1 / (8 * t))).congr' hev2

end GWContent

end GW.Endpoint.HubbardDimer
