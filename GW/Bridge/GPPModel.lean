/-
BRIDGE B2: the Hybertsen-Louie generalized plasmon-pole model of one entry
`eps⁻¹_{GG'}(ω)`, and exactly when it exists.

One entry, real flavour. Inputs: the static value `eps⁻¹_{GG'}(0)`, written through
`I = δ_{GG'} - eps⁻¹_{GG'}(0)`, and the f-sum parameter `Ω² = Ω²_{GG'}`. The model is

    eps⁻¹_{GG'}(ω) = δ_{GG'} + Ω² / (ω² - w̃²),     w̃² = Ω² / I          (`gppC`)

(`GW.LL.gppInvEps` is the `δ = 1` entry when `0 ≤ Ω²/I`: `gppC_eq_gppInvEps`). For
`w̃ > 0` it is one positive pole in the B1 form `R · 2 w̃ / (ω² - w̃²)` with `R = Ω² / (2 w̃)`
(`gppC_pole_form`), i.e. exactly what `FreqIntegral.wct_limit` produces.

Proved:

* `gppC_static` (static match): `eps⁻¹(0) = δ - I` whenever `I ≠ 0 ≠ Ω²`.
* `gppC_tail`, `fsum_moment` (first moment, by construction): `ω² (eps⁻¹(ω) - δ) → Ω²`
  as `ω → ∞`, and the discrete spectral weight `-π R` at `w̃` has first moment
  `-π R w̃ = -(π/2) Ω²`, the HL f-sum constraint for the SUPPLIED `Ω²` (a consequence of the
  ansatz; that `Ω²` is the system's response moment is not derived here, REVIEW-28 F2).
  The spectral function and its moment integral are informal; `fsum_moment` checks only
  the algebra `-π R w̃ = -(π/2) Ω²` for `R = Ω²/(2 w̃)`, `w̃ ≠ 0`.
* `single_pole_exists_iff` (**validity**): a single pole `R · 2w/(ω² - w²)`, `w > 0`,
  matching BOTH the static value (`-I` at `ω = 0`) and the tail (`ω² f → Ω²`) exists iff

      (I = 0 ∧ Ω² = 0)  ∨  0 < Ω² / I.

  If `0 < Ω²/I`, `single_pole_unique` gives
  `w = √(Ω²/I)`, `R = Ω²/(2w)`. The degenerate `I = Ω² = 0` branch is not unique:
  zero residue matches both constraints for any `w > 0`. So a mode is invalid
  exactly when `w̃² = Ω²/I < 0`, or when exactly one of `I`, `Ω²` vanishes.
  A valid mode with `I < 0` (and `Ω² < 0`) has negative spectral weight `R < 0`
  (`valid_neg_weight`). The model accepts it, and BerkeleyGW does not reject it for the
  sign of `R`: if kept (`keepM`: `|I|, |Ω²|, |wt2| ≥ TOL_Small`) it gets
  `wtilde = √wt2` (`wtM`, `keep_facts`); otherwise it is dropped like any other entry.
* BerkeleyGW's rule (named departure, `bgw_invalid_mode`): a kept mode with
  `wt2 < 0` gets `wtilde = WINV = 1/TOL_Zero = 10^12`. That is the `w → ∞` limit of the
  statically matched pole (`R = I w / 2`): its CH and SX kernels tend to the static
  COHSEX value `-I` (`sch_static_limit`, `ssx_static_limit`,
  `static_pole_limit`), with exact error `|I| |x| / |w - x|` for CH
  (`sch_static_error`); the tail constraint is then violated at every `w > 0` (this pole
  matches the static value, so `bgw_invalid_mode` excludes the tail match: its tail
  coefficient `I w²` has the sign of `I`, opposite to `Ω²` since `Ω²/I < 0`, and
  `|I| w² → ∞`). Entries with `|I| < TOL_Small` or `|Ω²| < TOL_Small` are dropped
  (`bgw_dropped`): contribution `0`, which for `I ≠ 0 = Ω²` violates the static match.
-/
import GW.Endpoint.Kernel.SigmaSpec
import GW.LL.Electronic

namespace GW.Bridge

open Filter Topology

/-- The HL correlation part `eps⁻¹(ω) - δ = Ω² / (ω² - Ω²/I)` of one entry. -/
noncomputable def gppC (I O ω : ℝ) : ℝ := O / (ω ^ 2 - O / I)

/-- One positive pole in the B1 frequency form. -/
noncomputable def singlePole (R w ω : ℝ) : ℝ := R * (2 * w / (ω ^ 2 - w ^ 2))

/-- The HL `w̃ = √(Ω²/I)`. -/
noncomputable def wTilde (I O : ℝ) : ℝ := √(O / I)

theorem gppC_eq_gppInvEps {I O : ℝ} (h : 0 ≤ O / I) (ω : ℝ) :
    gppC I O ω = GW.LL.gppInvEps O (wTilde I O) ω - 1 := by
  unfold gppC GW.LL.gppInvEps wTilde; rw [Real.sq_sqrt h]; ring

theorem gppC_pole_form {I O : ℝ} (h : 0 < O / I) (ω : ℝ) :
    gppC I O ω = singlePole (O / (2 * wTilde I O)) (wTilde I O) ω := by
  have hw : 0 < wTilde I O := Real.sqrt_pos.mpr h
  unfold gppC singlePole
  rw [show O / I = wTilde I O ^ 2 from (Real.sq_sqrt h.le).symm]
  field_simp

/-- **Static match.** -/
theorem gppC_static {I O : ℝ} (_hI : I ≠ 0) (hO : O ≠ 0) : gppC I O 0 = -I := by
  unfold gppC
  rw [show (0 : ℝ) ^ 2 - O / I = -(O / I) by ring, div_neg, div_div_eq_mul_div,
    mul_div_cancel_left₀ _ hO]

/-- `ω² · N / (ω² - c) = N / (1 - c / ω²)` for `ω ≠ 0` (both sides totalized alike). -/
theorem tail_helper (c N : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    ω ^ 2 * (N / (ω ^ 2 - c)) = N / (1 - c / ω ^ 2) := by
  have hω2 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω
  have e : ω ^ 2 - c = ω ^ 2 * (1 - c / ω ^ 2) := by field_simp
  rw [e]
  by_cases hq : 1 - c / ω ^ 2 = 0
  · simp [hq]
  · field_simp; ring

/-- The tail of any single pole: `ω² · R 2w/(ω² - w²) → 2 R w`. -/
theorem singlePole_tail (R w : ℝ) :
    Tendsto (fun ω => ω ^ 2 * singlePole R w ω) atTop (𝓝 (2 * R * w)) := by
  have hq : Tendsto (fun ω : ℝ => 1 - w ^ 2 / ω ^ 2) atTop (𝓝 1) := by
    have : Tendsto (fun ω : ℝ => w ^ 2 / ω ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
    simpa using tendsto_const_nhds.sub this
  have hl : Tendsto (fun ω : ℝ => R * (2 * w / (1 - w ^ 2 / ω ^ 2))) atTop (𝓝 (2 * R * w)) := by
    have := tendsto_const_nhds (x := R).mul (tendsto_const_nhds (x := 2 * w).div hq one_ne_zero)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  refine hl.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ω hω
  unfold singlePole
  rw [mul_left_comm, tail_helper _ _ hω.ne']

/-- **f-sum tail.** `ω² (eps⁻¹(ω) - δ) → Ω²` for every `I` (valid or not). -/
theorem gppC_tail (I O : ℝ) : Tendsto (fun ω => ω ^ 2 * gppC I O ω) atTop (𝓝 O) := by
  have hq : Tendsto (fun ω : ℝ => 1 - O / I / ω ^ 2) atTop (𝓝 1) := by
    have : Tendsto (fun ω : ℝ => O / I / ω ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
    simpa using tendsto_const_nhds.sub this
  have hl : Tendsto (fun ω : ℝ => O / (1 - O / I / ω ^ 2)) atTop (𝓝 O) := by
    simpa using tendsto_const_nhds.div hq one_ne_zero
  refine hl.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ω hω
  unfold gppC
  rw [tail_helper _ _ hω.ne']

/-- **f-sum first moment, by construction.** The GPP spectral function
`Im eps⁻¹(ω) = -π R [δ(ω - w̃) - δ(ω + w̃)]` has `∫₀^∞ ω Im eps⁻¹ = -π R w̃` (informal:
no spectral function or integral is formalised), and with `R = Ω²/(2 w̃)` this is
`-(π/2) Ω²`. The Lean statement is only this last substitution, for `w̃ ≠ 0`. -/
theorem fsum_moment {O w : ℝ} (hw : w ≠ 0) : -Real.pi * (O / (2 * w)) * w = -(Real.pi / 2) * O := by
  field_simp; ring

/-- A single pole matches the static value `-I`. -/
def MatchStatic (I R w : ℝ) : Prop := singlePole R w 0 = -I

/-- A single pole matches the f-sum tail `Ω²`. -/
def MatchTail (O R w : ℝ) : Prop := Tendsto (fun ω => ω ^ 2 * singlePole R w ω) atTop (𝓝 O)

theorem matchTail_iff (O R w : ℝ) : MatchTail O R w ↔ 2 * R * w = O :=
  ⟨fun h => tendsto_nhds_unique (singlePole_tail R w) h, fun h => h ▸ singlePole_tail R w⟩

theorem singlePole_zero (R : ℝ) {w : ℝ} (hw : w ≠ 0) : singlePole R w 0 = -(2 * R / w) := by
  unfold singlePole; field_simp; ring

theorem matchStatic_iff {I R w : ℝ} (hw : 0 < w) : MatchStatic I R w ↔ 2 * R / w = I := by
  unfold MatchStatic; rw [singlePole_zero R hw.ne', neg_inj]

/-- **Validity of a GPP mode.** A single positive pole matching both the static value
and the f-sum tail exists iff `(I = 0 ∧ Ω² = 0) ∨ 0 < Ω²/I`. -/
theorem single_pole_exists_iff (I O : ℝ) :
    (∃ R w, 0 < w ∧ MatchStatic I R w ∧ MatchTail O R w) ↔ (I = 0 ∧ O = 0) ∨ 0 < O / I := by
  constructor
  · rintro ⟨R, w, hw, hs, ht⟩
    rw [matchStatic_iff hw] at hs
    rw [matchTail_iff] at ht
    by_cases hI : I = 0
    · left
      refine ⟨hI, ?_⟩
      have hR : R = 0 := by
        rw [hI] at hs; field_simp at hs; linarith
      rw [← ht, hR]; ring
    · right
      have hO : O / I = w ^ 2 := by
        rw [← ht, ← hs]; field_simp
        have hR : R ≠ 0 := by rintro rfl; apply hI; rw [← hs]; simp
        field_simp; ring
      rw [hO]; positivity
  · rintro (⟨rfl, rfl⟩ | h)
    · exact ⟨0, 1, one_pos, by simp [MatchStatic, singlePole], by
        rw [matchTail_iff]; ring⟩
    · have hw : 0 < wTilde I O := Real.sqrt_pos.mpr h
      have hI : I ≠ 0 := by rintro rfl; simp at h
      have hsq : wTilde I O ^ 2 = O / I := Real.sq_sqrt h.le
      generalize wTilde I O = w at hw hsq
      have hO : O = w ^ 2 * I := by rw [hsq]; field_simp
      refine ⟨O / (2 * w), w, hw, ?_, ?_⟩
      · rw [matchStatic_iff hw, hO]; field_simp; ring
      · rw [matchTail_iff]; field_simp; ring

/-- If `0 < Ω²/I`, a matching pole is the HL one: `w = √(Ω²/I)`, `R = Ω²/(2w)`. (False
for `I = Ω² = 0`, where `R = 0` and `w > 0` is free.) -/
theorem single_pole_unique {I O R w : ℝ} (h : 0 < O / I) (hw : 0 < w) (hs : MatchStatic I R w)
    (ht : MatchTail O R w) : w = wTilde I O ∧ R = O / (2 * w) := by
  rw [matchStatic_iff hw] at hs
  rw [matchTail_iff] at ht
  have hI : I ≠ 0 := by rintro rfl; simp at h
  have hR : R ≠ 0 := by rintro rfl; apply hI; rw [← hs]; simp
  have hO : O / I = w ^ 2 := by rw [← ht, ← hs]; field_simp; ring
  refine ⟨?_, ?_⟩
  · unfold wTilde; rw [hO, Real.sqrt_sq hw.le]
  · rw [← ht]; field_simp; ring

/-- A valid mode with `I < 0` has negative spectral weight `R = Ω²/(2w̃) < 0`. -/
theorem valid_neg_weight {I O : ℝ} (h : 0 < O / I) (hI : I < 0) : O / (2 * wTilde I O) < 0 := by
  have hw : 0 < wTilde I O := Real.sqrt_pos.mpr h
  have hO : O < 0 := by
    by_contra hO; push_neg at hO
    have : O / I ≤ 0 := div_nonpos_of_nonneg_of_nonpos hO hI.le
    linarith
  exact div_neg_of_neg_of_pos hO (by positivity)

/-- Exactly one of `I`, `Ω²` zero: invalid. -/
theorem invalid_of_one_zero {I O : ℝ} (h : (I = 0 ∧ O ≠ 0) ∨ (I ≠ 0 ∧ O = 0)) :
    ¬ ∃ R w, 0 < w ∧ MatchStatic I R w ∧ MatchTail O R w := by
  rw [single_pole_exists_iff]
  rintro (⟨h1, h2⟩ | h3)
  · rcases h with ⟨_, h⟩ | ⟨h, _⟩ <;> contradiction
  · rcases h with ⟨h, _⟩ | ⟨_, h⟩ <;> simp [h] at h3

/-! ### BerkeleyGW's treatment (named departures) -/

open GW.Endpoint.Kernel.Sig

/-- **Invalid-mode rule.** A kept mode (`|I|, |Ω²|, |wt2| ≥ TOL_Small`) with `wt2 < 0`
gets `wtilde = WINV = 10^12`, and no single positive pole matches both constraints. -/
theorem bgw_invalid_mode {I O : ℝ} (hk : keepM I O) (hneg : ¬ 0 < wt2 I O) :
    wtM I O = WINV ∧ ¬ ∃ R w, 0 < w ∧ MatchStatic I R w ∧ MatchTail O R w := by
  refine ⟨by simp [wtM, hk, hneg], ?_⟩
  rw [single_pole_exists_iff]
  have hTS : (0 : ℝ) < TS := by unfold TS; positivity
  have hI : I ≠ 0 := fun h => by have := hk.1.1; rw [h, abs_zero] at this; linarith
  have hw : wt2 I O = O / I := by simp [wt2, hk.1]
  rintro (⟨h, _⟩ | h)
  · exact hI h
  · exact hneg (hw ▸ h)

/-- Dropped entries contribute nothing. -/
theorem bgw_dropped {I O x : ℝ} (h : ¬ keepM I O) : wtM I O = 0 ∧ schM I O x = 0 ∧ ssxM I O x = 0 := by
  simp [wtM, schM, ssxM, h]

/-- The statically matched pole `R = I w / 2` tends, as `w → ∞`, to the frequency-independent
(static COHSEX) value `-I` at every `ω`. -/
theorem static_pole_limit (I ω : ℝ) :
    Tendsto (fun w => singlePole (I * w / 2) w ω) atTop (𝓝 (-I)) := by
  have hq : Tendsto (fun w : ℝ => ω ^ 2 / w ^ 2 - 1) atTop (𝓝 (-1)) := by
    have : Tendsto (fun w : ℝ => ω ^ 2 / w ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
    simpa using this.sub tendsto_const_nhds
  have hl : Tendsto (fun w : ℝ => I / (ω ^ 2 / w ^ 2 - 1)) atTop (𝓝 (-I)) := by
    have := tendsto_const_nhds (x := I).div hq (by norm_num)
    simpa [div_neg] using this
  refine hl.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
  unfold singlePole
  by_cases hd : ω ^ 2 - w ^ 2 = 0
  · have h1 : ω ^ 2 / w ^ 2 - 1 = 0 := by
      rw [sub_eq_zero] at hd ⊢; rw [hd, div_self (by positivity)]
    rw [hd, h1]; simp
  · have h1 : ω ^ 2 / w ^ 2 - 1 ≠ 0 := by
      intro h; apply hd; field_simp at h; linarith
    field_simp; ring

/-- The CH kernel `w I / (x - w)` tends to the static value `-I` as `w → ∞`. -/
theorem sch_static_limit (I x : ℝ) : Tendsto (fun w => w * I / (x - w)) atTop (𝓝 (-I)) := by
  have hq : Tendsto (fun w : ℝ => x / w - 1) atTop (𝓝 (-1)) := by
    have : Tendsto (fun w : ℝ => x / w) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa using this.sub tendsto_const_nhds
  have hl : Tendsto (fun w : ℝ => I / (x / w - 1)) atTop (𝓝 (-I)) := by
    simpa [div_neg] using tendsto_const_nhds (x := I).div hq (by norm_num)
  refine hl.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
  by_cases hd : x - w = 0
  · have h1 : x / w - 1 = 0 := by rw [sub_eq_zero] at hd ⊢; rw [hd, div_self hw.ne']
    rw [hd, h1]; simp
  · have h1 : x / w - 1 ≠ 0 := by intro h; apply hd; field_simp at h; linarith
    field_simp; ring

/-- The generic SX kernel `w² I / (x² - w²)` tends to `-I` as `w → ∞`. -/
theorem ssx_static_limit (I x : ℝ) :
    Tendsto (fun w => w ^ 2 * I / (x ^ 2 - w ^ 2)) atTop (𝓝 (-I)) := by
  refine (static_pole_limit I x).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
  unfold singlePole; ring

/-- Exact error of the invalid-mode CH kernel against the static value. -/
theorem sch_static_error {I x w : ℝ} (hd : x - w ≠ 0) :
    |w * I / (x - w) - (-I)| = |I| * |x| / |w - x| := by
  rw [show w * I / (x - w) - -I = -(I * x) / (w - x) by
    field_simp [sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hd))]; ring]
  rw [abs_div, abs_neg, abs_mul]

end GW.Bridge
