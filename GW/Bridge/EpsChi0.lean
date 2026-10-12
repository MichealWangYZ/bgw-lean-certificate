/-
BRIDGE-EPS E1: the static independent-particle polarisability `chi0` derived from the
time-ordered `G0` of a general finite fermion system.

Setting (finite, T = 0, time-ordered, as `GW.Endpoint.ManyBody.GWSecond`):

* orbitals `m : ι` (a `Fintype`; spin-orbitals: spin is NOT summed here, see
  `EpsBloch.lean`), energies `ε m`, occupied set `O`, `f_m = [m ∈ O]`;
* `G0_m(τ) = -i [θ(τ)(1 - f_m) - θ(-τ) f_m] e^{-i ε_m τ}` (`gF`, equal to
  `ManyBody.G0t` on `Fin n`: `gF_eq_G0t`);
* the pair response `χ0_{m m'}(τ) = -i G0_m(τ) G0_{m'}(-τ)` of the pair density
  `φ_{m'}^* φ_m` (`chi0F`, equal to `ManyBody.chi0t`: `chi0F_eq_chi0t`); this is
  `χ0(1,2) = -i G0(1,2) G0(2,1)` projected on the orbitals;
* density channels `g : γ` (in E2 the normalised plane waves `|q + G⟩`) and the real
  amplitudes `P m m' g = ⟨g | φ_{m'}^* φ_m⟩`; the channel response is
  `χ0_{g g'}(τ) = Σ_{m m'} P_{m m'}(g) χ0_{m m'}(τ) P_{m m'}(g')` (`chiF`), i.e. the
  matrix element `⟨g| χ0 |g'⟩` of `χ0(r, r', τ) = Σ_{m m'} (φ_{m'}^* φ_m)(r)
  χ0_{m m'}(τ) (φ_{m'}^* φ_m)^*(r')` (real orbitals).

Proved:

* `chiF_limit` (**E1, dynamic**): for real `ω` off the excitation energies
  (`ω ≠ ε_m - ε_m'` whenever exactly one of `m, m'` is occupied), the damped transform
  `ftDamped η chiF ω` tends as `η → 0⁺` to

    χ0_{g g'}(ω) = Σ_{m m'} P P ((1 - f_m) f_{m'} - f_m (1 - f_{m'})) / (ω - (ε_m - ε_{m'}))

  (`chiW`). The signs come from `ftDamped_twoSided_limit`, not from an assumption.
* `chiW_zero` (**E1, static closed form**): at `ω = 0`

    χ0_{g g'} = Σ_{v ∈ O} Σ_{c ∉ O} [P_{cv}(g) P_{cv}(g') + P_{vc}(g) P_{vc}(g')] / (ε_v - ε_c)

  (`chiS`): each occupied/empty pair enters TWICE, once per time ordering (the
  `τ > 0` particle-first term, pair `(c, v)`, and the `τ < 0` hole-first term, pair
  `(v, c)`), both with the same denominator `ε_v - ε_c` and coefficient exactly `+1`.
  No spin factor appears at this level (spin-orbitals); it is derived in E2.
* `chiS_diag_nonpos`: with a gap (`ε_v < ε_c`) the static `χ0` has nonpositive diagonal.
* `chiW_continuousAt`: `χ0(ω) → χ0(0)` as `ω → 0` (gapped), i.e. `chiS` is the static
  limit of the dynamic response.

Not claimed: finite temperature, metals (`ε_v = ε_c` for an occupied/empty pair), a
distributional limit at the poles; the damping is put on the product (as in
`GWSecond.lean`); complex orbitals (the amplitudes are real, as in `ManyBody`).
-/
import GW.Endpoint.ManyBody.GWSecond

set_option linter.unusedSectionVars false

namespace GW.Bridge

open Complex Finset Filter Topology MeasureTheory
open GW.Endpoint.HubbardDimer (ftDamped twoSided expSum ftDamped_twoSided_limit)

variable {ι γ : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite fermion system with density channels: energies, occupied set, and the
real pair amplitudes `P m m' g = ⟨g | φ_{m'}^* φ_m⟩`. -/
structure FSys (ι γ : Type*) where
  ε : ι → ℝ
  O : Finset ι
  P : ι → ι → γ → ℝ

variable (S : FSys ι γ)

/-- Occupation `f_m ∈ {0, 1}`. -/
def FSys.f (m : ι) : ℝ := if m ∈ S.O then 1 else 0

/-- Time-ordered `G0_m(τ)`. -/
noncomputable def gF (m : ι) (τ : ℝ) : ℂ :=
  -I * ((if 0 < τ then 1 - S.f m else -S.f m : ℝ) : ℂ) * Complex.exp (-(I * S.ε m * τ))

/-- The pair response `χ0_{m m'}(τ) = -i G0_m(τ) G0_{m'}(-τ)`. -/
noncomputable def chi0F (m m' : ι) (τ : ℝ) : ℂ := -I * gF S m τ * gF S m' (-τ)

/-- The channel response `⟨g| χ0(τ) |g'⟩`. -/
noncomputable def chiF (g g' : γ) (τ : ℝ) : ℂ :=
  ∑ m, ∑ m', ((S.P m m' g * S.P m m' g' : ℝ) : ℂ) * chi0F S m m' τ

/-- The occupation factor `(1 - f_m) f_{m'} - f_m (1 - f_{m'})`. -/
def FSys.occW (m m' : ι) : ℝ := (1 - S.f m) * S.f m' - S.f m * (1 - S.f m')

/-- The frequency-domain response (the E1 limit). -/
noncomputable def chiW (g g' : γ) (ω : ℝ) : ℝ :=
  ∑ m, ∑ m', S.P m m' g * S.P m m' g' * (S.occW m m' / (ω - (S.ε m - S.ε m')))

/-- The static closed form. -/
noncomputable def chiS (g g' : γ) : ℝ :=
  ∑ v ∈ S.O, ∑ c ∈ S.Oᶜ, (S.P c v g * S.P c v g' + S.P v c g * S.P v c g') / (S.ε v - S.ε c)

/-- `ω` is off the excitation energies. -/
def ExcOff (ω : ℝ) : Prop := ∀ m m', (m ∈ S.O ↔ m' ∉ S.O) → ω - (S.ε m - S.ε m') ≠ 0

/-! ### `gF`, `chi0F` are the many-body objects -/

theorem gF_eq_G0t {N : ℕ} (ε : Fin N → ℝ) (O : Finset (Fin N)) (P : Fin N → Fin N → γ → ℝ)
    (m : Fin N) (τ : ℝ) :
    gF ⟨ε, O, P⟩ m τ = GW.Endpoint.ManyBody.G0t ε O m τ := by
  simp only [gF, FSys.f, GW.Endpoint.ManyBody.G0t, GW.Endpoint.ManyBody.occ]

theorem chi0F_eq_chi0t {N : ℕ} (ε : Fin N → ℝ) (O : Finset (Fin N)) (P : Fin N → Fin N → γ → ℝ)
    (m m' : Fin N) (τ : ℝ) :
    chi0F ⟨ε, O, P⟩ m m' τ = GW.Endpoint.ManyBody.chi0t ε O m m' τ := by
  simp only [chi0F, gF_eq_G0t, GW.Endpoint.ManyBody.chi0t]

/-! ### Two-sided exponential form -/

/-- Forward list `(-i P P (1 - f_m) f_{m'}, ε_m - ε_{m'})`. -/
noncomputable def lpX (g g' : γ) : List (ℂ × ℝ) :=
  (univ : Finset (ι × ι)).toList.map fun p =>
    (-I * ((S.P p.1 p.2 g * S.P p.1 p.2 g' * ((1 - S.f p.1) * S.f p.2) : ℝ) : ℂ),
      S.ε p.1 - S.ε p.2)

/-- Backward list `(-i P P f_m (1 - f_{m'}), ε_m - ε_{m'})`. -/
noncomputable def lnX (g g' : γ) : List (ℂ × ℝ) :=
  (univ : Finset (ι × ι)).toList.map fun p =>
    (-I * ((S.P p.1 p.2 g * S.P p.1 p.2 g' * (S.f p.1 * (1 - S.f p.2)) : ℝ) : ℂ),
      S.ε p.1 - S.ε p.2)

theorem sum_pairs_toList {M : Type*} [AddCommMonoid M] (h : ι × ι → M) :
    ((univ : Finset (ι × ι)).toList.map h).sum = ∑ m, ∑ m', h (m, m') := by
  rw [Finset.sum_map_toList, Fintype.sum_prod_type]

theorem chi0F_pos (m m' : ι) {τ : ℝ} (h : 0 < τ) :
    chi0F S m m' τ = -I * (((1 - S.f m) * S.f m' : ℝ) : ℂ) *
      Complex.exp (-(I * ((S.ε m - S.ε m' : ℝ) : ℂ) * τ)) := by
  simp only [chi0F, gF, if_pos h, if_neg (show ¬ (0 < -τ) by linarith)]
  push_cast
  rw [show -(I * ((S.ε m : ℂ) - (S.ε m' : ℂ)) * (τ : ℂ)) =
    -(I * S.ε m * τ) + -(I * S.ε m' * -(τ : ℂ)) by ring, Complex.exp_add]
  ring_nf; simp only [show I ^ 3 = -I by rw [pow_succ, I_sq]; ring]; ring

theorem chi0F_neg (m m' : ι) {τ : ℝ} (h : τ < 0) :
    chi0F S m m' τ = -I * ((S.f m * (1 - S.f m') : ℝ) : ℂ) *
      Complex.exp (-(I * ((S.ε m - S.ε m' : ℝ) : ℂ) * τ)) := by
  simp only [chi0F, gF, if_neg (show ¬ (0 < τ) by linarith), if_pos (show 0 < -τ by linarith)]
  push_cast
  rw [show -(I * ((S.ε m : ℂ) - (S.ε m' : ℂ)) * (τ : ℂ)) =
    -(I * S.ε m * τ) + -(I * S.ε m' * -(τ : ℂ)) by ring, Complex.exp_add]
  ring_nf; simp only [show I ^ 3 = -I by rw [pow_succ, I_sq]; ring]; ring

theorem chiF_eq (g g' : γ) {τ : ℝ} (hτ : τ ≠ 0) :
    chiF S g g' τ = twoSided (lpX S g g') (lnX S g g') τ := by
  unfold chiF twoSided expSum lpX lnX
  rw [List.map_map, List.map_map]
  split_ifs with h
  · rw [sum_pairs_toList]
    refine sum_congr rfl fun m _ => sum_congr rfl fun m' _ => ?_
    rw [chi0F_pos S m m' h]
    simp only [Function.comp]; push_cast; ring
  · have h' : τ < 0 := lt_of_le_of_ne (not_lt.mp h) hτ
    rw [sum_pairs_toList]
    refine sum_congr rfl fun m _ => sum_congr rfl fun m' _ => ?_
    rw [chi0F_neg S m m' h']
    simp only [Function.comp]; push_cast; ring

theorem f_mem {m : ι} (h : m ∈ S.O) : S.f m = 1 := by simp [FSys.f, h]
theorem f_not_mem {m : ι} (h : m ∉ S.O) : S.f m = 0 := by simp [FSys.f, h]

/-! ### E1: the limit `η → 0⁺` -/

/-- **E1 (dynamic).** The damped Fourier transform of the channel response
`⟨g| -i G0 G0 |g'⟩` tends, as `η → 0⁺`, to `chiW`, for real `ω` off the excitation
energies. -/
theorem chiF_limit (g g' : γ) {ω : ℝ} (hω : ExcOff S ω) :
    Tendsto (fun η => ftDamped η (chiF S g g') ω) (𝓝[>] 0) (𝓝 ((chiW S g g' ω : ℝ) : ℂ)) := by
  have hc : ∀ η, ftDamped η (chiF S g g') ω = ftDamped η (twoSided (lpX S g g') (lnX S g g')) ω :=
    fun η => GW.Endpoint.ManyBody.ftDamped_congr_ne_zero (fun τ hτ => chiF_eq S g g' hτ) η ω
  simp only [hc]
  convert ftDamped_twoSided_limit _ _ ω ?_ ?_ using 2
  · unfold lpX lnX
    rw [List.map_map, List.map_map, sum_pairs_toList, sum_pairs_toList, ← sum_add_distrib]
    unfold chiW FSys.occW
    push_cast
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m' _ => ?_
    simp only [Function.comp]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    push_cast
    ring_nf; rw [I_sq]; ring_nf
  · unfold lpX
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    rintro _ ⟨⟨m, m'⟩, rfl⟩ hz
    have hm : m ∉ S.O := by
      intro h; apply hz; simp [f_mem S h]
    have hm' : m' ∈ S.O := Classical.byContradiction fun h => hz (by simp [f_not_mem S h])
    exact hω m m' ⟨fun h => absurd h hm, fun h => absurd hm' h⟩
  · unfold lnX
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    rintro _ ⟨⟨m, m'⟩, rfl⟩ hz
    have hm : m ∈ S.O := Classical.byContradiction fun h => hz (by simp [f_not_mem S h])
    have hm' : m' ∉ S.O := by
      intro h; apply hz; simp [f_mem S h]
    exact hω m m' ⟨fun _ => hm', fun _ => hm⟩

/-! ### E1: the static closed form -/

theorem sum_split (s : Finset ι) (h : ι → ℝ) : ∑ m, h m = ∑ m ∈ s, h m + ∑ m ∈ sᶜ, h m :=
  (sum_add_sum_compl s h).symm

/-- **E1 (static).** At `ω = 0` the response is the closed form `chiS`: every
occupied/empty pair twice (both time orderings), denominator `ε_v - ε_c`. -/
theorem chiW_zero (g g' : γ) : chiW S g g' 0 = chiS S g g' := by
  unfold chiW chiS
  rw [sum_split S.O]
  have hO : ∀ m ∈ S.O, ∑ m', S.P m m' g * S.P m m' g' * (S.occW m m' / (0 - (S.ε m - S.ε m'))) =
      ∑ c ∈ S.Oᶜ, S.P m c g * S.P m c g' / (S.ε m - S.ε c) := by
    intro m hm
    rw [sum_split S.O, sum_eq_zero fun m' hm' => by
      simp [FSys.occW, f_mem S hm, f_mem S hm'], zero_add]
    refine sum_congr rfl fun c hc => ?_
    have hc' : c ∉ S.O := mem_compl.mp hc
    simp only [FSys.occW, f_mem S hm, f_not_mem S hc']
    rw [show (0 : ℝ) - (S.ε m - S.ε c) = -(S.ε m - S.ε c) by ring, div_neg]; ring
  have hE : ∀ m ∈ S.Oᶜ, ∑ m', S.P m m' g * S.P m m' g' * (S.occW m m' / (0 - (S.ε m - S.ε m'))) =
      ∑ v ∈ S.O, S.P m v g * S.P m v g' / (S.ε v - S.ε m) := by
    intro m hm
    have hm' : m ∉ S.O := mem_compl.mp hm
    rw [sum_split S.O, sum_eq_zero (s := S.Oᶜ) fun m' hm'' => by
      simp [FSys.occW, f_not_mem S hm', f_not_mem S (mem_compl.mp hm'')], add_zero]
    refine sum_congr rfl fun v hv => ?_
    simp only [FSys.occW, f_mem S hv, f_not_mem S hm']
    rw [show (0 : ℝ) - (S.ε m - S.ε v) = S.ε v - S.ε m by ring]; ring
  rw [sum_congr rfl hO, sum_congr rfl hE, sum_comm (s := S.Oᶜ), ← sum_add_distrib]
  refine sum_congr rfl fun v _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun c _ => ?_
  ring

/-- With a gap the static `χ0` has nonpositive diagonal. -/
theorem chiS_diag_nonpos (hgap : ∀ v ∈ S.O, ∀ c ∈ S.Oᶜ, S.ε v < S.ε c) (g : γ) :
    chiS S g g ≤ 0 := by
  unfold chiS
  refine sum_nonpos fun v hv => sum_nonpos fun c hc => ?_
  have h1 := mul_self_nonneg (S.P c v g)
  have h2 := mul_self_nonneg (S.P v c g)
  exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith [hgap v hv c hc])

/-- The gap condition makes `ω = 0` off the excitation energies. -/
theorem excOff_zero (hgap : ∀ v ∈ S.O, ∀ c ∈ S.Oᶜ, S.ε v < S.ε c) : ExcOff S 0 := by
  intro m m' h
  by_cases hm : m ∈ S.O
  · have := hgap m hm m' (mem_compl.mpr (h.mp hm)); intro h0; linarith
  · have hm' : m' ∈ S.O := by by_contra hc; exact hm (h.mpr hc)
    have := hgap m' hm' m (mem_compl.mpr hm); intro h0; linarith

/-- `χ0(ω)` is continuous at `ω = 0` off the excitation energies: `chiS` is the static
limit of the dynamic response. -/
theorem chiW_continuousAt (g g' : γ) (h0 : ExcOff S 0) :
    Tendsto (fun ω => chiW S g g' ω) (𝓝 0) (𝓝 (chiW S g g' 0)) := by
  unfold chiW
  refine tendsto_finset_sum _ fun m _ => tendsto_finset_sum _ fun m' _ => ?_
  by_cases hw : S.occW m m' = 0
  · simp [hw]
  have hne : (0 : ℝ) - (S.ε m - S.ε m') ≠ 0 := by
    apply h0 m m'
    unfold FSys.occW at hw
    by_cases hm : m ∈ S.O <;> by_cases hm' : m' ∈ S.O <;>
      simp_all [f_mem, f_not_mem]
  exact tendsto_const_nhds.mul (tendsto_const_nhds.div
    ((continuous_id.sub continuous_const).tendsto 0) hne)

end GW.Bridge
