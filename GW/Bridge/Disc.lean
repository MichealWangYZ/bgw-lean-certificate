/-
BRIDGE-DISC: the discontinuity of the theory GPP kernel at `(x, Ω²) = (0, 0)`, and why it
does not reach BerkeleyGW's Σ (nor O1).

**D1 (the discontinuity).** The theory kernel of one HL mode per unit weight is
`thK occ I Ω² x` (`Bloch.thK`: `occupiedTerm`/`emptyTerm` with `w̃ = √(Ω²/I)`). Writing a
valid mode (`0 < Ω²/I`) by its pole, `Ω² = w̃² I`, it is `I w̃ / (2(x ∓ w̃))`
(`thK_emp_eq`, `thK_occ_eq`). Hence

* at `x = 0` it is `∓ I/2` for EVERY valid `Ω²`, however small (`thK_emp_x0`, `thK_occ_x0`),
  so its limit along `Ω² → 0` (valid side) is `∓ I/2` (`thK_x0_tendsto`);
* at `Ω² = 0` it is `0` for every `x` (`thK_zero_strength`; with `w̃ = 0` this is Lean's
  totalized `0/0`, the convention discussed below), so the limit along `x → 0` there is `0`;
* for `x ≠ 0` it tends to `0` as `Ω² → 0` (`thK_tendsto_zero_of_ne`): BerkeleyGW's comment
  (`Sigma/mtxel_cor.f90:743-745`, "if Omega2 -> 0, both the SX and the CH terms vanish")
  is right exactly for `x ≠ 0`;
* for `I ≠ 0` the kernel is not continuous at `(0, 0)` (`thK_not_continuousAt`), and in
  every neighbourhood of `(0, 0)` it takes EVERY real value (`thK_cluster`, with
  `thK_zero_strength` for the value `0`). (For `I = 0` it is identically `0`.)

Physics (`residue_eq`, `emp_as_pole`, `wTilde_tendsto_zero`, `gppC_limit_off0`,
`gppC_static`): the mode is one pole of `W_c` at `w̃` with residue `R = Ω²/(2w̃) = I w̃/2`, and
its Σ term on an empty band is `R / (x - w̃)`. As `Ω² → 0` BOTH the residue and the pole
energy vanish, at the same rate; at `x = 0` (the external energy on the band's own energy)
`R/(0 - w̃) = -I/2` stays finite. In frequency, `eps⁻¹ - δ = gppC` keeps its static value
`-I` at `ω = 0` for every `Ω² ≠ 0` (`gppC_static`) while tending to `0` at every `ω ≠ 0`: a
zero-weight pole merging with `ω = 0`. At `Ω² = 0` exactly the mode has no strength at all:
`gppC I 0 ω = 0` for every `ω` (`gppC_zero_strength`; genuinely for `ω ≠ 0`, by Lean's
totalized `0/0` at `ω = 0`), its `W_c` pole has residue `0` in the B1/B3 system
(`blochSys_R_zero`, `singlePole_zero_strength`), so it contributes NOTHING to the theory Σ
at any energy (`thK_zero_strength`). With `w̃ = √(0/I) = 0`, the residue `Ω²/(2w̃)` and
the kernel `thK` are both `0/0`: the value `0` is the totalized convention, justified by
`W_c(ω) = 0` for every `ω ≠ 0`. (With `I ≠ 0` such a mode has no single-pole HL
representation, `invalid_of_one_zero`; the theory value `0` is the one consistent with
that vanishing of the `W_c` entry off `ω = 0`.)

**D2 (why those modes have `Ω² = 0` exactly).** In crystal coordinates the ideal fcc
reciprocal metric is `idealB c = c (4δ - 1) = c [[3,-1,-1],[-1,3,-1],[-1,-1,3]]`, the Gram
matrix of `b₁ = (-1,1,1)`, `b₂ = (1,-1,1)`, `b₃ = (1,1,-1)` (units `2π/a`): `dotM_ideal`.
So `(q+G')·B·(q+G) = c (cart(q+G')·cart(q+G))`, and the HL `Ω²_{GG'}` (off the `q = 0`
head row, given `factW ≠ 0` (`ω_p² ≠ 0` and `ρ(0) ≠ 0`) and `c ≠ 0`) is zero if
`ρ(G - G') = 0` or `v = 0` (by definition), and for `ρ(G - G') ≠ 0` and `v ≠ 0` it is zero
iff `q+G ⊥ q+G'` in Cartesian space (`omB_ideal_eq_zero_iff`). The structural reason for
the modes of BRIDGE-MEASURE finding 2 is the orthogonality (their `ρ(G - G')` is
nonzero). Because `2(q+G)` is an integer vector, the ideal dot is `c k / 4` with `k ∈ ℤ`
(`dotM_ideal_int`): either exactly `0` or at least `c/4` in size (`ideal_gap`), a margin
no rounding can blur. The exported binary64 `bdot` is the ideal matrix with `c = bdot₁₁/3`
up to ONE ulp (`2⁻⁵⁴`) on each off-diagonal entry (`bExp_sub_ideal`; `c` is itself dyadic,
`cExp`), and any metric within `δ` entrywise moves the dot by at most `δ Σ|u_a||w_b|`
(`dotM_perturb`). So on an orthogonal pair the spec's `Om2S` is pure rounding, bounded by
`om2S_orth_bound`.

**The drop rule gives the ideal-metric value** (`drop_eq_ideal`, `disc_mode`): if that
rounding residue is below `TOL_Small`, BerkeleyGW drops the mode (`bgw_dropped`) and its
contribution is `0`, which is EXACTLY the theory value with the ideal metric
(`thK occ I 0 x = 0`, the totalized `0/0` convention above), at every `x` including
`x = 0`, for every `I`. The theory with the ROUNDED metric instead gives `∓ I/2` at
`x = 0` when the rounded `Ω²` has the sign of `I` (`0 < Ω²/I`, `thK_emp_x0`): that value,
not the spec,
is the artefact behind BRIDGE-MEASURE's +28 meV "switch". At the level of Σ,
`sigA_eq_theory_disc` extends `sigA_eq_theory`: the orthogonal modes need not be
`ModeOK`, and the theory is `SigTD`, the B3 theory with the ideal-metric `Ω² = 0` on them.
-/
import GW.Bridge.Compare

namespace GW.Bridge

open Filter Topology Finset GW.Endpoint.Kernel.Sig GW.Endpoint.Kernel.Eps

/-! ### D1: the kernel near `(x, Ω²) = (0, 0)` -/

/-- `w̃` of the mode parametrised by its pole: `Ω² = w² I`. -/
theorem wTilde_param {I w : ℝ} (hI : I ≠ 0) (hw : 0 ≤ w) : wTilde I (w ^ 2 * I) = w := by
  unfold wTilde; rw [mul_div_assoc, div_self hI, mul_one, Real.sqrt_sq hw]

/-- A valid mode (`0 < Ω²/I`) is `Ω² = w² I` with `w > 0`. -/
theorem valid_param {I O : ℝ} (h : 0 < O / I) : I ≠ 0 ∧ 0 < wTilde I O ∧ O = wTilde I O ^ 2 * I := by
  have hI : I ≠ 0 := by rintro rfl; simp at h
  refine ⟨hI, Real.sqrt_pos.mpr h, ?_⟩
  rw [wTilde, Real.sq_sqrt h.le]; field_simp

theorem thK_emp_param {I w : ℝ} (hI : I ≠ 0) (hw : 0 < w) (x : ℝ) :
    thK false I (w ^ 2 * I) x = I * w / (2 * (x - w)) := by
  unfold thK GW.GPP.emptyTerm
  simp only [Bool.false_eq_true, if_false]
  rw [wTilde_param hI hw.le]
  by_cases hx : x - w = 0
  · simp [hx]
  · field_simp; ring

theorem thK_occ_param {I w : ℝ} (hI : I ≠ 0) (hw : 0 < w) (x : ℝ) :
    thK true I (w ^ 2 * I) x = I * w / (2 * (x + w)) := by
  unfold thK GW.GPP.occupiedTerm
  simp only [if_true]
  rw [wTilde_param hI hw.le]
  by_cases hx : x + w = 0
  · simp [hx]
  · field_simp; ring

/-- The empty-band kernel of a valid mode, written by its pole: `I w̃ / (2(x - w̃))`. -/
theorem thK_emp_eq {I O : ℝ} (h : 0 < O / I) (x : ℝ) :
    thK false I O x = I * wTilde I O / (2 * (x - wTilde I O)) := by
  obtain ⟨hI, hw, hO⟩ := valid_param h
  conv_lhs => rw [hO]
  exact thK_emp_param hI hw x

/-- The occupied-band kernel of a valid mode: `I w̃ / (2(x + w̃))`. -/
theorem thK_occ_eq {I O : ℝ} (h : 0 < O / I) (x : ℝ) :
    thK true I O x = I * wTilde I O / (2 * (x + wTilde I O)) := by
  obtain ⟨hI, hw, hO⟩ := valid_param h
  conv_lhs => rw [hO]
  exact thK_occ_param hI hw x

/-- **At `x = 0`, empty band:** `-I/2` for every valid `Ω²`, however small. -/
theorem thK_emp_x0 {I O : ℝ} (h : 0 < O / I) : thK false I O 0 = -I / 2 := by
  obtain ⟨-, hw, -⟩ := valid_param h
  rw [thK_emp_eq h]; field_simp; ring

/-- **At `x = 0`, occupied band:** `I/2` for every valid `Ω²`. -/
theorem thK_occ_x0 {I O : ℝ} (h : 0 < O / I) : thK true I O 0 = I / 2 := by
  obtain ⟨-, hw, -⟩ := valid_param h
  rw [thK_occ_eq h]; field_simp; ring

/-- **Zero strength.** A mode with `Ω² = 0` contributes `0` at every `x`. With
`w̃ = √(0/I) = 0` this is Lean's totalized `0/0`, a convention justified by
`W_c(ω) = 0` for every `ω ≠ 0` (`gppC_zero_strength`). -/
theorem thK_zero_strength (occ : Bool) (I x : ℝ) : thK occ I 0 x = 0 := by
  cases occ <;> simp [thK, GW.GPP.emptyTerm, GW.GPP.occupiedTerm]

/-- The valid side of `Ω² = 0` for a given `I`: the modes that have an HL pole. -/
def ValidSide (I : ℝ) : Set ℝ := {O | 0 < O / I}

theorem validSide_neBot {I : ℝ} (hI : I ≠ 0) : (𝓝[ValidSide I] (0 : ℝ)).NeBot := by
  rcases lt_or_gt_of_ne hI with h | h
  · have hs : Set.Iio (0 : ℝ) ⊆ ValidSide I := fun O hO => div_pos_of_neg_of_neg hO h
    exact Filter.NeBot.mono (by infer_instance) (nhdsWithin_mono _ hs)
  · have hs : Set.Ioi (0 : ℝ) ⊆ ValidSide I := fun O hO => div_pos hO h
    exact Filter.NeBot.mono (by infer_instance) (nhdsWithin_mono _ hs)

/-- **Limit along `Ω² → 0` at `x = 0`** (valid side): `-I/2` (empty), `I/2` (occupied). -/
theorem thK_x0_tendsto (I : ℝ) :
    Tendsto (fun O => thK false I O 0) (𝓝[ValidSide I] 0) (𝓝 (-I / 2)) ∧
      Tendsto (fun O => thK true I O 0) (𝓝[ValidSide I] 0) (𝓝 (I / 2)) := by
  refine ⟨tendsto_const_nhds.congr' ?_, tendsto_const_nhds.congr' ?_⟩ <;>
  · filter_upwards [self_mem_nhdsWithin] with O hO
    first | exact (thK_emp_x0 hO).symm | exact (thK_occ_x0 hO).symm

/-- **Limit along `x → 0` at `Ω² = 0`:** `0`. -/
theorem thK_O0_tendsto (occ : Bool) (I : ℝ) :
    Tendsto (fun x => thK occ I 0 x) (𝓝 0) (𝓝 0) := by
  simp only [thK_zero_strength]; exact tendsto_const_nhds

/-- `w̃ → 0` as `Ω² → 0`. -/
theorem wTilde_tendsto_zero (I : ℝ) : Tendsto (fun O => wTilde I O) (𝓝 0) (𝓝 0) := by
  have hc : Continuous fun O : ℝ => √(O / I) := Real.continuous_sqrt.comp (continuous_id.div_const I)
  simpa [wTilde] using hc.tendsto 0

/-- **Away from `x = 0` the kernel does vanish as `Ω² → 0`** (BerkeleyGW's comment is right
for `x ≠ 0`). -/
theorem thK_tendsto_zero_of_ne (occ : Bool) (I : ℝ) {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun O => thK occ I O x) (𝓝[ValidSide I] 0) (𝓝 0) := by
  have hw := (wTilde_tendsto_zero I).mono_left (nhdsWithin_le_nhds (s := ValidSide I))
  cases occ
  · have hf : ContinuousAt (fun w : ℝ => I * w / (2 * (x - w))) 0 :=
      (continuousAt_const.mul continuousAt_id).div (continuousAt_const.mul
        (continuousAt_const.sub continuousAt_id)) (by simpa using hx)
    have := hf.tendsto.comp hw
    simp only [mul_zero, zero_div] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with O hO
    exact (thK_emp_eq hO x).symm
  · have hf : ContinuousAt (fun w : ℝ => I * w / (2 * (x + w))) 0 :=
      (continuousAt_const.mul continuousAt_id).div (continuousAt_const.mul
        (continuousAt_const.add continuousAt_id)) (by simpa using hx)
    have := hf.tendsto.comp hw
    simp only [mul_zero, zero_div] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with O hO
    exact (thK_occ_eq hO x).symm

/-- **The discontinuity.** For `I ≠ 0` the kernel `(x, Ω²) ↦ thK I Ω² x` is not continuous
at `(0, 0)` (empty band; the occupied band is the same with `I/2`). -/
theorem thK_not_continuousAt {I : ℝ} (hI : I ≠ 0) :
    ¬ ContinuousAt (fun p : ℝ × ℝ => thK false I p.2 p.1) (0, 0) := by
  intro hc
  haveI := validSide_neBot hI
  have hg : Tendsto (fun O : ℝ => ((0 : ℝ), O)) (𝓝[ValidSide I] 0) (𝓝 ((0 : ℝ), (0 : ℝ))) :=
    tendsto_const_nhds.prodMk_nhds (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
  have h1 := hc.tendsto.comp hg
  have h2 := (thK_x0_tendsto I).1
  have : thK false I 0 0 = -I / 2 := tendsto_nhds_unique h1 h2
  rw [thK_zero_strength] at this
  exact hI (by linarith)

theorem thK_not_continuousAt_occ {I : ℝ} (hI : I ≠ 0) :
    ¬ ContinuousAt (fun p : ℝ × ℝ => thK true I p.2 p.1) (0, 0) := by
  intro hc
  haveI := validSide_neBot hI
  have hg : Tendsto (fun O : ℝ => ((0 : ℝ), O)) (𝓝[ValidSide I] 0) (𝓝 ((0 : ℝ), (0 : ℝ))) :=
    tendsto_const_nhds.prodMk_nhds (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
  have : thK true I 0 0 = I / 2 := tendsto_nhds_unique (hc.tendsto.comp hg) (thK_x0_tendsto I).2
  rw [thK_zero_strength] at this
  exact hI (by linarith)

/-- **The value set near `(0, 0)` is all of `ℝ`.** For `I ≠ 0`, every `c ≠ 0` is taken by a
valid mode with `|x|, |Ω²| < ε` (and `c = 0` by `Ω² = 0`, `thK_zero_strength`). -/
theorem thK_cluster {I c ε : ℝ} (hI : I ≠ 0) (hc : c ≠ 0) (hε : 0 < ε) :
    ∃ x O, |x| < ε ∧ |O| < ε ∧ 0 < O / I ∧ x ≠ wTilde I O ∧ thK false I O x = c := by
  set t := 1 + I / (2 * c) with ht
  set w := min 1 (ε / (|t| + |I| + 1)) with hwdef
  have hd : 0 < |t| + |I| + 1 := by positivity
  have hw : 0 < w := lt_min one_pos (div_pos hε hd)
  have hw1 : w ≤ 1 := min_le_left _ _
  have hwe : w * (|t| + |I| + 1) ≤ ε := by
    have := min_le_right 1 (ε / (|t| + |I| + 1)); rw [← hwdef] at this
    calc w * (|t| + |I| + 1) ≤ ε / (|t| + |I| + 1) * (|t| + |I| + 1) :=
          mul_le_mul_of_nonneg_right this hd.le
      _ = ε := by field_simp
  have ht1 : t - 1 = I / (2 * c) := by rw [ht]; ring
  have ht0 : t - 1 ≠ 0 := by rw [ht1]; exact div_ne_zero hI (mul_ne_zero two_ne_zero hc)
  refine ⟨t * w, w ^ 2 * I, ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hw]; nlinarith [abs_nonneg t, abs_nonneg I]
  · rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < w ^ 2)]
    have : w ^ 2 * |I| ≤ w * |I| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg I); nlinarith
    nlinarith [abs_nonneg t, abs_nonneg I]
  · rw [mul_div_assoc, div_self hI, mul_one]; positivity
  · rw [wTilde_param hI hw.le]
    intro h; apply ht0
    have : w * (t - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hw.ne'
    · exact h'
  · rw [thK_emp_param hI hw]
    have : t * w - w = w * (t - 1) := by ring
    rw [this, ht1]; field_simp; ring

/-! ### D1: the physics, a zero-strength pole at zero energy -/

/-- The residue of the mode's `W_c` pole: `R = Ω²/(2w̃) = I w̃ / 2`, which vanishes with `w̃`. -/
theorem residue_eq {I O : ℝ} (h : 0 < O / I) : O / (2 * wTilde I O) = I * wTilde I O / 2 := by
  obtain ⟨-, hw, hO⟩ := valid_param h
  rw [show O / (2 * wTilde I O) = wTilde I O ^ 2 * I / (2 * wTilde I O) by rw [← hO]]
  field_simp; ring

/-- The empty-band term is the pole term `R / (x - w̃)` of Σ_c (B1). -/
theorem emp_as_pole (I O x : ℝ) : thK false I O x = O / (2 * wTilde I O) / (x - wTilde I O) := by
  unfold thK GW.GPP.emptyTerm; simp only [Bool.false_eq_true, if_false]; rw [div_div, mul_assoc]

/-- ... and the occupied-band term is `R / (x + w̃)`. -/
theorem occ_as_pole (I O x : ℝ) : thK true I O x = O / (2 * wTilde I O) / (x + wTilde I O) := by
  unfold thK GW.GPP.occupiedTerm; simp only [if_true]; rw [div_div, mul_assoc]

/-- As `Ω² → 0` the residue tends to `0` (together with the pole `w̃`, `wTilde_tendsto_zero`). -/
theorem residue_tendsto_zero (I : ℝ) :
    Tendsto (fun O => O / (2 * wTilde I O)) (𝓝[ValidSide I] 0) (𝓝 0) := by
  have hw := (wTilde_tendsto_zero I).mono_left (nhdsWithin_le_nhds (s := ValidSide I))
  have : Tendsto (fun O => I * wTilde I O / 2) (𝓝[ValidSide I] 0) (𝓝 (I * 0 / 2)) :=
    (tendsto_const_nhds.mul hw).div_const 2
  rw [mul_zero, zero_div] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with O hO
  exact (residue_eq hO).symm

/-- **`W_c` of a zero-strength mode is identically zero** (B2 `gppC`): genuinely for
`ω ≠ 0`, and at `ω = 0` by Lean's totalized `0/0`. -/
theorem gppC_zero_strength (I ω : ℝ) : gppC I 0 ω = 0 := by simp [gppC]

/-- A pole of residue `0` is zero at every frequency. -/
theorem singlePole_zero_strength (w ω : ℝ) : singlePole 0 w ω = 0 := by simp [singlePole]

/-- For `ω ≠ 0`, `eps⁻¹ - δ = gppC I Ω² ω → 0` as `Ω² → 0`; at `ω = 0` it is `-I` for every
`Ω² ≠ 0` (`gppC_static`). The limit of `W_c` is `-I` concentrated on `ω = 0`, not `0`. -/
theorem gppC_limit_off0 (I : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    Tendsto (fun O => gppC I O ω) (𝓝 0) (𝓝 0) := by
  have hc : ContinuousAt (fun O : ℝ => O / (ω ^ 2 - O / I)) 0 :=
    continuousAt_id.div (continuousAt_const.sub (continuousAt_id.div_const I))
      (by simpa using pow_ne_zero 2 hω)
  simpa [gppC] using hc.tendsto

/-- In the B1/B3 Bloch system a mode with `Ω² = 0` has residue `0`: it adds nothing to
`W_c`, hence nothing to the theory Σ (`thK_zero_strength` is its closed-form term). With
`w̃ = 0` the residue `Ω²/(2w̃)` is Lean's totalized `0/0`, a convention justified by
`W_c(ω) = 0` for every `ω ≠ 0`. -/
theorem blochSys_R_zero (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vc : V3 → ℝ) (st : St) (a : ℕ)
    (x : Σ _ : ℕ, ℕ) (k : ℕ × ℕ) (h : OTq gl vc x.1 k.1 k.2 = 0) :
    (blochSys gl E vc st a).R x k = 0 := by
  simp [blochSys, h]

/-! ### D2: the ideal fcc metric -/

/-- `u·B·w` for a metric `B` in crystal coordinates. -/
noncomputable def dotM (B : Fin 3 → Fin 3 → ℝ) (u w : Fin 3 → ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, u a * B a b * w b

/-- `bdot` of a run as a metric on `Fin 3`. -/
noncomputable def bdF (gl : Gl) (a b : Fin 3) : ℝ := bd gl a b

theorem dotB_eq_dotM (gl : Gl) (u w : Fin 3 → ℝ) : dotB gl u w = dotM (bdF gl) u w := rfl

/-- The ideal fcc reciprocal metric `c [[3,-1,-1],[-1,3,-1],[-1,-1,3]]`. -/
noncomputable def idealB (c : ℝ) (a b : Fin 3) : ℝ := if a = b then 3 * c else -c

/-- Cartesian coordinates (units `2π/a`) of `Σ u_a b_a`, `b₁ = (-1,1,1)`, `b₂ = (1,-1,1)`,
`b₃ = (1,1,-1)`. -/
noncomputable def cart (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-u 0 + u 1 + u 2, u 0 - u 1 + u 2, u 0 + u 1 - u 2]

/-- The ideal metric is `c` times the Cartesian dot product. -/
theorem dotM_ideal (c : ℝ) (u w : Fin 3 → ℝ) :
    dotM (idealB c) u w = c * ∑ i : Fin 3, cart u i * cart w i := by
  simp [dotM, idealB, cart, Fin.sum_univ_three]; ring

/-- On half-integer vectors (`u = m/2`, `w = n/2`) the ideal dot is `c k / 4`, `k ∈ ℤ`. -/
theorem dotM_ideal_int (c : ℝ) (m n : Fin 3 → ℤ) :
    dotM (idealB c) (fun a => (m a : ℝ) / 2) (fun b => (n b : ℝ) / 2) =
      c * ((∑ a : Fin 3, ∑ b : Fin 3, m a * (if a = b then 3 else -1) * n b : ℤ) : ℝ) / 4 := by
  simp [dotM, idealB, Fin.sum_univ_three]; ring

/-- **The gap.** An ideal dot of half-integer vectors is `0` or at least `c/4` in size. -/
theorem ideal_gap {c : ℝ} (hc : 0 < c) (m n : Fin 3 → ℤ) :
    dotM (idealB c) (fun a => (m a : ℝ) / 2) (fun b => (n b : ℝ) / 2) = 0 ∨
      c / 4 ≤ |dotM (idealB c) (fun a => (m a : ℝ) / 2) (fun b => (n b : ℝ) / 2)| := by
  rw [dotM_ideal_int]
  set k : ℤ := ∑ a : Fin 3, ∑ b : Fin 3, m a * (if a = b then 3 else -1) * n b
  rcases eq_or_ne k 0 with h | h
  · left; rw [h]; simp
  · right
    have hk : (1 : ℝ) ≤ |(k : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
    rw [abs_div, abs_mul, abs_of_pos hc, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    nlinarith

/-- `2 vec qd G` is an integer vector. -/
theorem vec_half (qd : QD) (G : V3) :
    vec qd G = fun a => (((![qd.qh.1 + 2 * G.1, qd.qh.2.1 + 2 * G.2.1, qd.qh.2.2 + 2 * G.2.2] :
      Fin 3 → ℤ) a : ℤ) : ℝ) / 2 := by
  funext a; fin_cases a <;> simp [vec] <;> ring

/-- The gap for the sphere vectors `q + G` Sigma uses. -/
theorem ideal_gap_vec {c : ℝ} (hc : 0 < c) (qd : QD) (G G' : V3) :
    dotM (idealB c) (vec qd G) (vec qd G') = 0 ∨ c / 4 ≤ |dotM (idealB c) (vec qd G) (vec qd G')| := by
  rw [vec_half qd G, vec_half qd G']; exact ideal_gap hc _ _

/-- **Rounding moves the dot by at most `δ Σ|u_a||w_b|`.** -/
theorem dotM_perturb {B B' : Fin 3 → Fin 3 → ℝ} {δ : ℝ} (hB : ∀ a b, |B a b - B' a b| ≤ δ)
    (u w : Fin 3 → ℝ) :
    |dotM B u w - dotM B' u w| ≤ δ * ∑ a : Fin 3, ∑ b : Fin 3, |u a| * |w b| := by
  have e : dotM B u w - dotM B' u w = ∑ a : Fin 3, ∑ b : Fin 3, u a * (B a b - B' a b) * w b := by
    simp only [dotM, ← sum_sub_distrib]; congr 1; funext a; congr 1; funext b; ring
  rw [e, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_)
  rw [abs_mul, abs_mul]
  have := hB a b
  nlinarith [abs_nonneg (u a), abs_nonneg (w b), mul_nonneg (abs_nonneg (u a)) (abs_nonneg (w b))]

/-! ### The exported Si-EPM `bdot` -/

/-- The exported binary64 `bdot` of the Si-EPM run (bohr⁻²): diagonal
`5065758257150985·2⁻⁵²`, off-diagonal `-6754344342867979·2⁻⁵⁴` (checked against the WFN
header by `tests/test_bridge_disc.py`). -/
noncomputable def bExp (a b : Fin 3) : ℝ :=
  if a = b then 5065758257150985 / 2 ^ 52 else -6754344342867979 / 2 ^ 54

/-- The ideal scale `c = bdot₁₁/3`, itself a dyadic (so the ideal metric is exact binary64). -/
noncomputable def cExp : ℝ := 6754344342867980 / 2 ^ 54

theorem cExp_eq : 3 * cExp = 5065758257150985 / 2 ^ 52 := by unfold cExp; norm_num

theorem cExp_pos : 0 < cExp := by unfold cExp; positivity

/-- **The exported `bdot` is the ideal fcc metric up to one ulp (`2⁻⁵⁴`) off the diagonal.** -/
theorem bExp_sub_ideal (a b : Fin 3) : bExp a b - idealB cExp a b = if a = b then 0 else 1 / 2 ^ 54 := by
  unfold bExp idealB cExp
  split_ifs <;> norm_num

theorem bExp_close (a b : Fin 3) : |bExp a b - idealB cExp a b| ≤ 1 / 2 ^ 54 := by
  rw [bExp_sub_ideal]; split_ifs
  · norm_num
  · rw [abs_of_pos (by norm_num)]

/-! ### D2: `Ω²` in a metric, its ideal zeros, the rounded residue -/

section omega

variable (gl : Gl) (vc : V3 → ℝ)

/-- The HL `Ω²_{ij}` of `Bloch.OmT` with the metric `B` in place of `bdot`. -/
noncomputable def OmB (B : Fin 3 → Fin 3 → ℝ) (qd : QD) (i j : ℕ) : ℝ :=
  factW gl * (rhoF gl (gs qd i - gs qd j)).getD 0 *
    (if qd.qh = 0 ∧ gs qd i = 0 then (if gs qd j = 0 then 1 else 0)
     else vc (key qd (gs qd i)) / (8 * Real.pi) * dotM B (vec qd (gs qd j)) (vec qd (gs qd i)))

theorem omB_bd (qd : QD) (i j : ℕ) : OmB gl vc (bdF gl) qd i j = OmT gl vc qd i j := rfl

theorem om2S_eq_omB (vb : V3 → ℝ) (qd : QD) (i j : ℕ) :
    Om2S gl vb qd i j = OmB gl vb (bdF gl) qd i j := om2S_eq gl vb qd i j

/-- Mode `(i, j)` is a Cartesian-orthogonal pair `q+G_j ⊥ q+G_i` off the `q = 0` head row. -/
def Orth (qd : QD) (i j : ℕ) : Prop :=
  ¬ (qd.qh = 0 ∧ gs qd i = 0) ∧
    ∑ k : Fin 3, cart (vec qd (gs qd j)) k * cart (vec qd (gs qd i)) k = 0

/-- **The structural reason.** Off the head row, with `ρ(G_i - G_j) ≠ 0` and `v ≠ 0`, the
ideal-metric `Ω²` vanishes exactly when `q+G_i ⊥ q+G_j`. -/
theorem omB_ideal_eq_zero_iff {c : ℝ} (hc : c ≠ 0) (qd : QD) (i j : ℕ)
    (hrow : ¬ (qd.qh = 0 ∧ gs qd i = 0)) (hf : factW gl ≠ 0)
    (hr : (rhoF gl (gs qd i - gs qd j)).getD 0 ≠ 0) (hv : vc (key qd (gs qd i)) ≠ 0) :
    OmB gl vc (idealB c) qd i j = 0 ↔ Orth qd i j := by
  unfold OmB Orth
  rw [if_neg hrow, dotM_ideal]
  have hp : (8 * Real.pi) ≠ 0 := by positivity
  simp only [hrow, not_false_eq_true, true_and, mul_eq_zero, hf, hr, hv, hc, div_eq_zero_iff, hp,
    false_or, or_false]

theorem omB_ideal_zero (c : ℝ) {qd : QD} {i j : ℕ} (h : Orth qd i j) :
    OmB gl vc (idealB c) qd i j = 0 := by
  unfold OmB
  rw [if_neg h.1, dotM_ideal, h.2]; ring

/-- **The spec's `Ω²` on an orthogonal pair is pure rounding.** -/
theorem om2S_orth_bound (vb : V3 → ℝ) {c δ : ℝ} (hB : ∀ a b : Fin 3, |bdF gl a b - idealB c a b| ≤ δ)
    {qd : QD} {i j : ℕ} (h : Orth qd i j) :
    |Om2S gl vb qd i j| ≤ |factW gl * (rhoF gl (gs qd i - gs qd j)).getD 0 *
        (vb (key qd (gs qd i)) / (8 * Real.pi))| *
      (δ * ∑ a : Fin 3, ∑ b : Fin 3, |vec qd (gs qd j) a| * |vec qd (gs qd i) b|) := by
  rw [om2S_eq_omB]
  unfold OmB
  rw [if_neg h.1]
  have h0 : dotM (idealB c) (vec qd (gs qd j)) (vec qd (gs qd i)) = 0 := by rw [dotM_ideal, h.2, mul_zero]
  have hp := dotM_perturb hB (vec qd (gs qd j)) (vec qd (gs qd i))
  rw [h0, sub_zero] at hp
  rw [show factW gl * (rhoF gl (gs qd i - gs qd j)).getD 0 *
      (vb (key qd (gs qd i)) / (8 * Real.pi) * dotM (bdF gl) (vec qd (gs qd j)) (vec qd (gs qd i))) =
      factW gl * (rhoF gl (gs qd i - gs qd j)).getD 0 * (vb (key qd (gs qd i)) / (8 * Real.pi)) *
        dotM (bdF gl) (vec qd (gs qd j)) (vec qd (gs qd i)) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)

/-- **BerkeleyGW's drop rule gives the ideal-metric value.** A mode whose spec `Ω²` is below
`TOL_Small` and whose ideal-metric `Ω²` is `0` contributes the same to the spec as to the
theory with the ideal metric: `0`, at every `x` (including `x = 0`) and every `I`. -/
theorem drop_eq_ideal (vb : V3 → ℝ) (c : ℝ) (occ : Bool) (I x : ℝ) {qd : QD} {i j : ℕ}
    (hs : |Om2S gl vb qd i j| < TS) (h0 : OmB gl vc (idealB c) qd i j = 0) :
    specMode occ I (Om2S gl vb qd i j) x = thK occ I (OmB gl vc (idealB c) qd i j) x := by
  have hk : ¬ keepM I (Om2S gl vb qd i j) := fun h => absurd h.1.2 (not_le.mpr hs)
  obtain ⟨-, h1, h2⟩ := bgw_dropped (x := x) hk
  rw [h0, thK_zero_strength]
  unfold specMode; rw [h1, h2]; cases occ <;> simp

/-- **D2, one mode.** For a Cartesian-orthogonal pair, a metric within `δ` of the ideal one and
a rounding residue below `TOL_Small`, the spec (rounded metric) equals the theory with the
ideal metric, and both are `0`. -/
theorem disc_mode (vb : V3 → ℝ) {c δ : ℝ} (hB : ∀ a b : Fin 3, |bdF gl a b - idealB c a b| ≤ δ)
    (occ : Bool) (I x : ℝ) {qd : QD} {i j : ℕ} (h : Orth qd i j)
    (hsmall : |factW gl * (rhoF gl (gs qd i - gs qd j)).getD 0 * (vb (key qd (gs qd i)) / (8 * Real.pi))| *
      (δ * ∑ a : Fin 3, ∑ b : Fin 3, |vec qd (gs qd j) a| * |vec qd (gs qd i) b|) < TS) :
    specMode occ I (Om2S gl vb qd i j) x = thK occ I (OmB gl vc (idealB c) qd i j) x ∧
      thK occ I (OmB gl vc (idealB c) qd i j) x = 0 := by
  have h0 := omB_ideal_zero gl vc c h
  refine ⟨drop_eq_ideal gl vc vb c occ I x ((om2S_orth_bound gl vb hB h).trans_lt hsmall) h0, ?_⟩
  rw [h0, thK_zero_strength]

end omega

/-! ### D2 at the level of Σ -/

section sigma

variable (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ) (st : St)

open Classical in
/-- The theory `Ω²` with the ideal-metric zeros: `0` on Cartesian-orthogonal pairs
(`omB_ideal_zero`), the B3 `OmT` elsewhere. -/
noncomputable def OmD (vc : V3 → ℝ) (t j i : ℕ) : ℝ :=
  if Orth (gl.qs.getD t default) j i then 0 else OTq gl vc t j i

/-- The theory correlation of band `n1` at `q_t` with `OmD`. -/
noncomputable def PTD (vc : V3 → ℝ) (t a n1 iw : ℕ) : ℝ :=
  quad gl vc st t a n1 (fun j i =>
    thK (decide (n1 < gl.nocc)) (ITq gl E t j i) (OmD gl vc t j i) (xT gl st t a n1 iw))

/-- The theory Σ with the ideal-metric `Ω² = 0` on the orthogonal pairs. -/
noncomputable def SigTD (vc : V3 → ℝ) (a iw : ℕ) : ℝ :=
  ∑ t ∈ range gl.qs.length, (Xq gl vc st t a + ∑ n1 ∈ range (nbq st t), PTD gl E st vc t a n1 iw)

/-- **B4 with the orthogonal pairs.** As `sigA_eq_theory`, but every mode need only be
`ModeOK` (and not an orthogonal pair) OR an orthogonal pair whose rounded `Ω²` is below
`TOL_Small`; the theory is then `SigTD`. -/
theorem sigA_eq_theory_disc (vc : V3 → ℝ) (a iw : ℕ) (hC : ∀ k, vb k = vc k)
    (hW : ∀ t < gl.qs.length, WingFree gl E vb oq (gl.qs.getD t default))
    (hX : ∀ t < gl.qs.length, ∀ n1 < nbq st t, TZ ≤ |xT gl st t a n1 iw|)
    (hM : ∀ t < gl.qs.length, ∀ n1 < nbq st t, ∀ j < nG gl t, ∀ i < nG gl t,
      (¬ Orth (gl.qs.getD t default) j i ∧
        ModeOK (decide (n1 < gl.nocc)) (ITq gl E t j i) (OTq gl vc t j i) (xT gl st t a n1 iw)) ∨
      (Orth (gl.qs.getD t default) j i ∧ |OTq gl vc t j i| < TS)) :
    SigA gl E vb oq st a iw = SigTD gl E st vc a iw + COR gl E vb oq st a := by
  have hv : vb = vc := funext hC
  subst hv
  unfold SigA SigTD COR
  rw [← sum_add_distrib]
  refine sum_congr rfl fun t ht => ?_
  have ht' := mem_range.mp ht
  have hP : ∀ n1 ∈ range (nbq st t), Pq gl E vb oq st t a n1 iw = PTD gl E st vb t a n1 iw := by
    intro n1 hn1
    have hn1' := mem_range.mp hn1
    rw [Pq_eq_quad, PTD]
    apply quad_congr
    intro j hj i hi
    have hI : Iq gl E vb oq t j i = ITq gl E t j i := by
      simp only [Iq, ITq, IeS, IT, epsS_eq gl E vb oq (hW t ht') j i]
    have hO : Oq gl vb t j i = OTq gl vb t j i := by simp only [Oq, OTq, om2S_eq]
    have hx : wxS gl st t a n1 iw = xT gl st t a n1 iw := by
      rw [wxS_eq, if_neg (not_lt.mpr (hX t ht' n1 hn1'))]
    rw [hI, hO, hx]
    rcases hM t ht' n1 hn1' j hj i hi with ⟨hno, hok⟩ | ⟨ho, hs⟩
    · rw [OmD, if_neg hno]; exact mode_eq hok
    · rw [OmD, if_pos ho, thK_zero_strength]
      have hk : ¬ keepM (ITq gl E t j i) (OTq gl vb t j i) := fun h => absurd h.1.2 (not_le.mpr hs)
      obtain ⟨-, h1, h2⟩ := bgw_dropped (x := xT gl st t a n1 iw) hk
      unfold specMode; rw [h1, h2]; split_ifs <;> simp
  rw [sum_congr rfl fun n1 hn1 => by rw [hP n1 hn1], sum_add_distrib]
  ring

end sigma

end GW.Bridge
