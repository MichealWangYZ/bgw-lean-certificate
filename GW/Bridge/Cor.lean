/-
BRIDGE-COR: a proved enclosure of the omitted-band (dynamic) Coulomb-hole tail, replacing
the empirical factor `½` of the static remainder `COR` (`Compare.cor_eq`, Deslippe et al.
2013).

Setting. `st` is the computed state (the run's bands at every `k - q`, dyadic rows as in
SigmaSpec). The omitted bands are a real completion `cp : Compl` (`K t` rows `C t n` on
the `k - q` sphere, energies `ε t n`), with `CompleteK κ`: computed plus omitted rows
resolve `κ` times the identity (`κ = 1`: completeness; a real completion of computed rows
`R` exists iff `κ I - RᵀR` is positive semidefinite, e.g. for `κ ≥ ‖R‖₂²`: standard linear
algebra, not formalised here). `SigTall = SigT + tailT` and `SigAall = SigA + tailS` are
the theory and spec Σ with the completion's rows appended (not shown to be the true omitted
eigenvectors: REVIEW-28 F3; `SigAall` keeps the static remainder `CORall`, nonzero in
general: `CorResidual.cor_all_decomp`, F4). For further dyadic rows of a larger state: its
`SigT`, `SigA` (`sig{T,A}all_of_state`, `completeK_of_complete`). Omitted energies: only `x ≤ -D`.

**C1 (one mode, one omitted band).** With `y = -x = ε_n - E ≥ D > 0` and a valid GPP mode
(`0 < Ω²/I`, `w̃ = √(Ω²/I) > 0`) the theory CH term is the static CH term `-I/2` times

    θ = w̃/(w̃ + y) = w̃/(w̃ - x),   0 < θ ≤ θ_hi = w̃/(w̃ + D)   (`thK_empty_ratio`,
                                                               `thK_empty_enclosure`)

and `θ ≥ w̃/(w̃ + Y)` if also `y ≤ Y` (`theta_lower`; no such `Y` is assumed below).
There is no positive lower bound from `D` alone: `θ → 0` as `y → ∞`. Invalid modes
(`Ω²/I < 0`, or exactly one of `I`, `Ω²` zero) and zero modes `I = Ω² = 0` (together
Lean's `Ω²/I ≤ 0`, `w̃ = 0`) have theory value `0` (`thK_empty_invalid`; for invalid modes
the Lean totalisation of "no HL pole", BRIDGE's rule; for zero modes the zero-residue
value). Every mode obeys `|thK| ≤ |I|/2` for `x ≤ 0` (`thK_empty_abs`). As an enclosure:
`|thK - θ_hi/2·(-I/2)| ≤ θ_hi/2·|I|/2` (`thK_tail_mode`). BerkeleyGW's own rule on an
omitted band (`specK_tail_mode`): kept modes (valid or invalid, `w = wtM`, the invalid
rule `w = 1/TOL_Zero`) are in the generic branch for `D > 1/2` and give the same form
with `w = wtM`; dropped modes give `0`. The energy step `iw = 0 → 1` has the kernel
`ψ = θ(w, y-1) - θ(w, y) ∈ (0, ψ(w, D)]` for `w > 0`, `y ≥ D > 1` (`psi_pos`, `psi_anti`,
`thK_diff_mode`; BerkeleyGW's rule, `specK_diff_mode`, needs `D > 3/2`).

**C2 (closure).** Summed over modes and omitted bands the weights `M_i v_i M_j` have mixed
signs, so a ratio bound fails. `tail_core` bounds `|dyn_tail - Σ c·T|` by
`Σ |v_i| √T_ii √T_jj r_ji` (Cauchy-Schwarz over the omitted bands), where the omitted-band
pair sums `T_ij = Σ_n M_n(G_i) M_n(G_j)` are EXACTLY computable from completeness alone,
`T = κ Σ_v A_v(G_i) A_v(G_j) - Σ_computed M_n M_n` (`tailK_eq`; no shift-closure of the
sphere is needed; with it, `cloP_eq_rho` gives BerkeleyGW's `ρ_aa(G_i - G_j)`). Main
statements: `sigT_all_bands`, `sigT_diff_all_bands` (theory Σ; generic per-mode form
`sigT_tail_enclose`), `sigA_all_bands`, `sigA_diff_all_bands` (`SigAall`: the omitted
rows' `ACq + Pq` added; static remainder `CORall` = scale + shift + `Gch` kept, `CorResidual`).
-/
import GW.Bridge.Compare

namespace GW.Bridge

open Finset GW.Endpoint.Kernel.Sig GW.Endpoint.Kernel.Eps

/-! ### C1: one GPP mode on one omitted empty band -/

/-- The dynamic-to-static ratio `θ = w/(w + y)` of one mode, `y = ε_n - E`. -/
noncomputable def theta (w y : ℝ) : ℝ := w / (w + y)

theorem theta_pos {w y : ℝ} (hw : 0 < w) (hy : 0 ≤ y) : 0 < theta w y :=
  div_pos hw (by linarith)

theorem theta_le_one {w y : ℝ} (hw : 0 < w) (hy : 0 ≤ y) : theta w y ≤ 1 :=
  (div_le_one (by linarith)).mpr (by linarith)

/-- `θ` decreases in `y`: an omitted band at `y ≥ D` has `θ ≤ θ(w, D)`. -/
theorem theta_anti {w y y' : ℝ} (hw : 0 < w) (hy : 0 ≤ y) (h : y ≤ y') :
    theta w y' ≤ theta w y :=
  div_le_div_of_nonneg_left hw.le (by linarith) (by linarith)

/-- A lower bound needs an upper bound `Y` on the omitted energies (not assumed below). -/
theorem theta_lower {w y Y : ℝ} (hw : 0 < w) (hy : 0 ≤ y) (h : y ≤ Y) :
    theta w Y ≤ theta w y :=
  theta_anti hw hy h

/-- **C1, exact.** A valid mode on an empty band with `x ≤ 0`: dynamic CH = `θ` × static CH. -/
theorem thK_empty_ratio {I O x : ℝ} (hv : 0 < O / I) (hx : x ≤ 0) :
    thK false I O x = theta (wTilde I O) (-x) * (-I / 2) := by
  have hI : I ≠ 0 := by rintro rfl; simp at hv
  have hw : 0 < wTilde I O := Real.sqrt_pos.mpr hv
  have hO : O = wTilde I O ^ 2 * I := by rw [wTilde, Real.sq_sqrt hv.le]; field_simp
  unfold thK theta GW.GPP.emptyTerm
  simp only [Bool.false_eq_true, if_false]
  generalize wTilde I O = w at hw hO ⊢
  subst hO
  have h1 : x - w ≠ 0 := by intro h; linarith
  have h2 : w + -x ≠ 0 := by intro h; linarith
  field_simp
  ring

/-- **C1.** `dyn = θ · static` with `0 < θ ≤ w̃/(w̃ + D)` for `x ≤ -D`, `D > 0`. -/
theorem thK_empty_enclosure {I O D x : ℝ} (hv : 0 < O / I) (hD : 0 < D) (hx : x ≤ -D) :
    ∃ θ, thK false I O x = θ * (-I / 2) ∧ θ = theta (wTilde I O) (-x) ∧ 0 < θ ∧
      θ ≤ theta (wTilde I O) D := by
  have hw : 0 < wTilde I O := Real.sqrt_pos.mpr hv
  exact ⟨_, thK_empty_ratio hv (by linarith), rfl, theta_pos hw (by linarith),
    theta_anti hw hD.le (by linarith)⟩

/-- Invalid and zero modes (`Ω²/I ≤ 0`, which in Lean includes `I = Ω² = 0`):
`w̃ = √(Ω²/I) = 0` and the theory kernel is `0`. -/
theorem thK_empty_invalid {I O x : ℝ} (hv : O / I ≤ 0) : thK false I O x = 0 := by
  unfold thK GW.GPP.emptyTerm wTilde
  simp [Real.sqrt_eq_zero'.mpr hv]

/-- Every mode: `|thK| ≤ |I|/2` on an empty band with `x ≤ 0`. -/
theorem thK_empty_abs {I O x : ℝ} (hx : x ≤ 0) : |thK false I O x| ≤ |I| / 2 := by
  by_cases hv : 0 < O / I
  · have hw : 0 < wTilde I O := Real.sqrt_pos.mpr hv
    rw [thK_empty_ratio hv hx, abs_mul, abs_of_pos (theta_pos hw (by linarith)), abs_div,
      abs_neg, abs_two]
    have := theta_le_one hw (by linarith : (0 : ℝ) ≤ -x)
    have h0 : 0 ≤ |I| / 2 := by positivity
    nlinarith
  · rw [thK_empty_invalid (not_lt.mp hv), abs_zero]; positivity

theorem mid_enclose {θ m s : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ m) : |θ * s - m / 2 * s| ≤ m / 2 * |s| := by
  rw [← sub_mul, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg s)
  rw [abs_le]; constructor <;> linarith

/-- The per-mode centre `θ_hi/2 · (-I/2)` (valid modes; `0` otherwise). -/
noncomputable def cK (I O D : ℝ) : ℝ :=
  if 0 < O / I then theta (wTilde I O) D / 2 * (-I / 2) else 0

/-- The per-mode radius `θ_hi/2 · |I|/2` (valid modes; `0` otherwise). -/
noncomputable def rK (I O D : ℝ) : ℝ :=
  if 0 < O / I then theta (wTilde I O) D / 2 * (|I| / 2) else 0

theorem rK_nonneg (I O D : ℝ) (hD : 0 < D) : 0 ≤ rK I O D := by
  unfold rK; split_ifs with hv
  · have := theta_pos (Real.sqrt_pos.mpr hv) hD.le (w := wTilde I O)
    positivity
  · exact le_rfl

theorem abs_neg_half (I : ℝ) : |-I / 2| = |I| / 2 := by rw [abs_div, abs_neg, abs_two]

/-- **C1 as an enclosure**, every mode. -/
theorem thK_tail_mode {I O D x : ℝ} (hD : 0 < D) (hx : x ≤ -D) :
    |thK false I O x - cK I O D| ≤ rK I O D := by
  unfold cK rK
  split_ifs with hv
  · rw [thK_empty_ratio hv (by linarith)]
    have hw : 0 < wTilde I O := Real.sqrt_pos.mpr hv
    have := mid_enclose (s := -I / 2) (theta_pos hw (by linarith : (0 : ℝ) ≤ -x)).le
      (theta_anti hw hD.le (by linarith : D ≤ -x))
    rwa [abs_neg_half] at this
  · rw [thK_empty_invalid (not_lt.mp hv)]; simp

/-! #### BerkeleyGW's rule on an omitted band -/

theorem wtM_pos {I O : ℝ} (hk : keepM I O) : 0 < wtM I O := by
  unfold wtM; rw [if_pos hk]; split_ifs with h
  · exact Real.sqrt_pos.mpr h
  · unfold WINV; positivity

/-- A kept mode (valid, or invalid with `w = 1/TOL_Zero`) on an omitted band with
`x ≤ -D`, `D > 1/2`, is in the generic branch: `½ CH = θ(wtM, -x) · (-I/2)`. -/
theorem schM_tail_ratio {I O D x : ℝ} (hk : keepM I O) (hD : 1 / 2 < D) (hx : x ≤ -D) :
    (1 / 2) * schM I O x = theta (wtM I O) (-x) * (-I / 2) := by
  have hw := wtM_pos hk
  have hU : IeU I = I := by simp [IeU, hk.1.1]
  have hg : (x - wtM I O) ^ 2 > GAM2 ∧ wtM I O ^ 2 < (x - wtM I O) ^ 2 * LIM1 := by
    unfold GAM2 LIM1
    have h1 : x - wtM I O < -(1 / 2) := by linarith
    have h2 : wtM I O ^ 2 < (x - wtM I O) ^ 2 := by nlinarith
    constructor
    · nlinarith
    · nlinarith [sq_nonneg (x - wtM I O)]
  unfold schM
  rw [if_pos hk]
  dsimp only
  rw [if_pos hg, hU]
  unfold theta
  generalize wtM I O = w at hw hg ⊢
  have h1 : x - w ≠ 0 := by intro h; linarith
  have h2 : w + -x ≠ 0 := by intro h; linarith
  field_simp
  ring

/-- The spec's omitted-band kernel: `ACq` (`IeU/4`) plus `½ CH`. -/
noncomputable def specK (I O x : ℝ) : ℝ := IeU I / 4 + (1 / 2) * schM I O x

noncomputable def cS (I O D : ℝ) : ℝ :=
  IeU I / 4 + if keepM I O then theta (wtM I O) D / 2 * (-I / 2) else 0

noncomputable def rS (I O D : ℝ) : ℝ :=
  if keepM I O then theta (wtM I O) D / 2 * (|I| / 2) else 0

theorem rS_nonneg (I O D : ℝ) (hD : 0 < D) : 0 ≤ rS I O D := by
  unfold rS; split_ifs with hk
  · have := theta_pos (wtM_pos hk) hD.le (w := wtM I O)
    positivity
  · exact le_rfl

/-- **C1, BerkeleyGW's rule**, every mode. -/
theorem specK_tail_mode {I O D x : ℝ} (hD : 1 / 2 < D) (hx : x ≤ -D) :
    |specK I O x - cS I O D| ≤ rS I O D := by
  unfold specK cS rS
  split_ifs with hk
  · rw [schM_tail_ratio hk hD hx, add_sub_add_left_eq_sub]
    have hw := wtM_pos hk
    have := mid_enclose (s := -I / 2) (theta_pos hw (by linarith : (0 : ℝ) ≤ -x)).le
      (theta_anti hw (by linarith) (by linarith : D ≤ -x))
    rwa [abs_neg_half] at this
  · have : schM I O x = 0 := by unfold schM; rw [if_neg hk]
    rw [this]; simp

/-! #### The energy step `iw = 0 → 1` (for the linearised QP equation) -/

/-- `ψ(w, y) = θ(w, y - 1) - θ(w, y)`: the kernel of `Σ(E + 1 eV) - Σ(E)` per unit static. -/
noncomputable def psi (w y : ℝ) : ℝ := theta w (y - 1) - theta w y

theorem psi_eq {w y : ℝ} (hw : 0 < w) (hy : 1 < y) : psi w y = w / ((w + y - 1) * (w + y)) := by
  unfold psi theta
  have h1 : w + (y - 1) ≠ 0 := by intro h; linarith
  have h2 : w + y ≠ 0 := by intro h; linarith
  have h3 : w + y - 1 ≠ 0 := by intro h; linarith
  field_simp; ring

theorem psi_pos {w y : ℝ} (hw : 0 < w) (hy : 1 < y) : 0 < psi w y := by
  rw [psi_eq hw hy]; apply div_pos hw; apply mul_pos <;> linarith

theorem psi_anti {w y D : ℝ} (hw : 0 < w) (hD : 1 < D) (h : D ≤ y) : psi w y ≤ psi w D := by
  rw [psi_eq hw (by linarith), psi_eq hw hD]
  apply div_le_div_of_nonneg_left hw.le (mul_pos (by linarith) (by linarith))
  apply mul_le_mul <;> linarith

noncomputable def cKd (I O D : ℝ) : ℝ :=
  if 0 < O / I then psi (wTilde I O) D / 2 * (-I / 2) else 0

noncomputable def rKd (I O D : ℝ) : ℝ :=
  if 0 < O / I then psi (wTilde I O) D / 2 * (|I| / 2) else 0

theorem rKd_nonneg (I O D : ℝ) (hD : 1 < D) : 0 ≤ rKd I O D := by
  unfold rKd; split_ifs with hv
  · have := psi_pos (Real.sqrt_pos.mpr hv) hD (w := wTilde I O)
    positivity
  · exact le_rfl

/-- The energy step of the theory kernel on an omitted band, every mode (`x = x(iw = 0)`). -/
theorem thK_diff_mode {I O D x : ℝ} (hD : 1 < D) (hx : x ≤ -D) :
    |(thK false I O (x + 1) - thK false I O x) - cKd I O D| ≤ rKd I O D := by
  unfold cKd rKd
  split_ifs with hv
  · rw [thK_empty_ratio hv (by linarith), thK_empty_ratio hv (by linarith), ← sub_mul,
      show -(x + 1) = -x - 1 by ring]
    have hw : 0 < wTilde I O := Real.sqrt_pos.mpr hv
    have := mid_enclose (s := -I / 2) (psi_pos hw (by linarith : (1 : ℝ) < -x)).le
      (psi_anti hw hD (by linarith : D ≤ -x))
    rwa [abs_neg_half] at this
  · rw [thK_empty_invalid (not_lt.mp hv), thK_empty_invalid (not_lt.mp hv)]; simp

noncomputable def cSd (I O D : ℝ) : ℝ :=
  if keepM I O then psi (wtM I O) D / 2 * (-I / 2) else 0

noncomputable def rSd (I O D : ℝ) : ℝ :=
  if keepM I O then psi (wtM I O) D / 2 * (|I| / 2) else 0

theorem rSd_nonneg (I O D : ℝ) (hD : 1 < D) : 0 ≤ rSd I O D := by
  unfold rSd; split_ifs with hk
  · have := psi_pos (wtM_pos hk) hD (w := wtM I O)
    positivity
  · exact le_rfl

/-- The energy step of BerkeleyGW's omitted-band kernel, every mode (`D > 3/2`). -/
theorem specK_diff_mode {I O D x : ℝ} (hD : 3 / 2 < D) (hx : x ≤ -D) :
    |(specK I O (x + 1) - specK I O x) - cSd I O D| ≤ rSd I O D := by
  unfold specK cSd rSd
  split_ifs with hk
  · rw [add_sub_add_left_eq_sub, schM_tail_ratio hk (by linarith : (1 : ℝ) / 2 < D - 1)
      (by linarith), schM_tail_ratio hk (by linarith : (1 : ℝ) / 2 < D) hx, ← sub_mul,
      show -(x + 1) = -x - 1 by ring]
    have hw := wtM_pos hk
    have := mid_enclose (s := -I / 2) (psi_pos hw (by linarith : (1 : ℝ) < -x)).le
      (psi_anti hw (by linarith) (by linarith : D ≤ -x))
    rwa [abs_neg_half] at this
  · have h : ∀ z, schM I O z = 0 := fun z => by unfold schM; rw [if_neg hk]
    rw [h, h]; simp

/-! ### C2: completeness without shift-closure -/

/-- The amplitude of state `a` (coefficients `ca` on `Gk`) at the `k - q` sphere entry `v`
shifted by `G`: `A_v(G) = Σ_u [Gk_u - Gq_v = G] c_a(u)`. -/
noncomputable def amp (gl : Gl) (Gk : List V3) (ca : List ℤ) (Gq : List V3) (v : ℕ) (G : V3) : ℝ :=
  ∑ u ∈ range Gk.length, if Gk.getD u 0 - Gq.getD v 0 = G then dy gl.SC (ca.getD u 0) else 0

theorem pd_eq_amp (gl : Gl) (Gk : List V3) (ca : List ℤ) (Gq : List V3) (cc : List ℤ) (G : V3) :
    pd gl Gk ca Gq cc G = ∑ v ∈ range Gq.length, amp gl Gk ca Gq v G * dy gl.SC (cc.getD v 0) := by
  unfold pd amp
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun u _ => ?_
  split_ifs <;> simp

/-- **Closure from completeness alone.** `Σ_n M_n(G) M_n(G') = Σ_v A_v(G) A_v(G')`. -/
theorem pd_closure_amp (gl : Gl) (Gk : List V3) (ca : List ℤ) (Gq : List V3) (cs : List (List ℤ))
    (nb : ℕ) (G G' : V3) (hc : Complete gl Gq cs nb) :
    ∑ n ∈ range nb, pd gl Gk ca Gq (cs.getD n []) G * pd gl Gk ca Gq (cs.getD n []) G' =
      ∑ v ∈ range Gq.length, amp gl Gk ca Gq v G * amp gl Gk ca Gq v G' := by
  simp_rw [pd_eq_amp, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun v hv => ?_
  rw [sum_comm]
  have e : ∀ v' ∈ range Gq.length, ∑ n ∈ range nb,
      amp gl Gk ca Gq v G * dy gl.SC ((cs.getD n []).getD v 0) *
        (amp gl Gk ca Gq v' G' * dy gl.SC ((cs.getD n []).getD v' 0)) =
      amp gl Gk ca Gq v G * amp gl Gk ca Gq v' G' * (if v = v' then 1 else 0) := by
    intro v' hv'
    rw [← hc v (mem_range.mp hv) v' (mem_range.mp hv'), mul_sum]
    refine sum_congr rfl fun n _ => by ring
  rw [sum_congr rfl e, sum_eq_single v (fun v' _ h => by rw [if_neg (Ne.symm h), mul_zero])
    (fun h => absurd hv h), if_pos rfl, mul_one]

/-- With shift-closure as well, the closure sum is BerkeleyGW's `ρ_aa(G - G')`. -/
theorem cloP_eq_rho (gl : Gl) (Gk : List V3) (ca : List ℤ) (Gq : List V3) (cs : List (List ℤ))
    (nb : ℕ) (G G' : V3) (hc : Complete gl Gq cs nb) (hs : ShiftClosed Gk Gq G G') :
    ∑ v ∈ range Gq.length, amp gl Gk ca Gq v G * amp gl Gk ca Gq v G' =
      pd gl Gk ca Gk ca (G - G') := by
  rw [← pd_closure_amp gl Gk ca Gq cs nb G G' hc, pd_closure gl Gk ca Gq cs nb G G' hc hs]

/-! ### C2 core: Cauchy-Schwarz over the omitted bands -/

/-- **C2 core.** Kernels `F n j i` within `r j i` of a centre `c j i` on every omitted band
`n < K`, vectors `u n i` (`M_n(G_i)`) and weights `v i`: the tail
`Σ_n Σ_{i,j} u_i v_i u_j F_ji` is `Σ v_i T_ij c_ji` up to `Σ |v_i| √T_ii √T_jj r_ji`,
`T_ij = Σ_n u_n i u_n j`. -/
theorem tail_core (m K : ℕ) (u : ℕ → ℕ → ℝ) (v : ℕ → ℝ) (F : ℕ → ℕ → ℕ → ℝ) (c r : ℕ → ℕ → ℝ)
    (hr : ∀ j i, 0 ≤ r j i) (hF : ∀ n < K, ∀ j < m, ∀ i < m, |F n j i - c j i| ≤ r j i) :
    |∑ n ∈ range K, ∑ i ∈ range m, ∑ j ∈ range m, u n i * v i * u n j * F n j i -
        ∑ i ∈ range m, ∑ j ∈ range m, v i * (∑ n ∈ range K, u n i * u n j) * c j i| ≤
      ∑ i ∈ range m, ∑ j ∈ range m,
        |v i| * (√(∑ n ∈ range K, u n i * u n i) * √(∑ n ∈ range K, u n j * u n j)) * r j i := by
  rw [sum_comm]
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
  rw [sum_comm, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  have e2 : ∑ n ∈ range K, u n i * v i * u n j * F n j i - v i * (∑ n ∈ range K, u n i * u n j) * c j i =
      ∑ n ∈ range K, (u n i * u n j * v i) * (F n j i - c j i) := by
    rw [mul_sum, sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => by ring
  rw [e2]
  have hsq : ∀ k, ∑ n ∈ range K, |u n k| ^ 2 = ∑ n ∈ range K, u n k * u n k :=
    fun k => sum_congr rfl fun n _ => by rw [sq_abs, sq]
  calc _ ≤ ∑ n ∈ range K, |u n i * u n j * v i| * r j i :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hF n (mem_range.mp hn) j hj' i hi') (abs_nonneg _))
    _ = |v i| * r j i * ∑ n ∈ range K, |u n i| * |u n j| := by
        rw [mul_sum]; refine sum_congr rfl fun n _ => by rw [abs_mul, abs_mul]; ring
    _ ≤ |v i| * r j i * (√(∑ n ∈ range K, |u n i| ^ 2) * √(∑ n ∈ range K, |u n j| ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)
          (mul_nonneg (abs_nonneg _) (hr j i))
    _ = _ := by rw [hsq, hsq]; ring

theorem sum_prod_expand (N L : ℕ) (f : ℕ → ℕ → ℝ) (A B : ℕ → ℝ) :
    ∑ n ∈ range N, (∑ v ∈ range L, A v * f n v) * (∑ v ∈ range L, B v * f n v) =
      ∑ v ∈ range L, ∑ v' ∈ range L, A v * B v' * ∑ n ∈ range N, f n v * f n v' := by
  simp_rw [sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun v' _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun n _ => by ring

/-! ### The omitted bands as a real completion of the computed ones

The computed state `st` holds the run's bands at every `k - q` (dyadic rows, as in
SigmaSpec). The omitted bands are NOT dyadic data: a completion `cp` gives, per `q_t`,
`K t` real coefficient rows `C t n` on the `k - q` sphere and their energies `ε t n` (Ry).
`CompleteK κ` asks computed + omitted rows to resolve `κ` times the identity. With
`κ = 1` this is completeness; a real completion exists iff `κ I - Rᵀ R` is positive
semidefinite for the computed rows `R` (not formalised; a dyadic completion of dyadic rows generally does not exist, and binary64
eigenvector rows have `‖R‖₂` slightly above `1`, so `κ` is a rigorous bound on `‖R‖₂²`).
For `κ > λ_max(RᵀR)` an exact completion needs at least `N` rows, so `cp` is an abstract
scaled-frame completion, not the omitted eigenvectors (REVIEW-28 F3). For the further dyadic
rows of a larger state these are the old notions (`completeK_of_complete`, `sig{T,A}all_of_state`). -/

/-- The omitted bands at every `k - q` point. -/
structure Compl where
  K : ℕ → ℕ
  C : ℕ → ℕ → ℕ → ℝ
  ε : ℕ → ℕ → ℝ

section compl

variable (gl : Gl) (st : St)

/-- The all-band pair sum `Σ_v A_v(G) A_v(G')` at `q_t` (computable from state `a`). -/
noncomputable def cloP (t a : ℕ) (G G' : V3) : ℝ :=
  ∑ v ∈ range (st.kq.getD t default).Gq.length,
    amp gl st.Gk (st.ck.getD a []) (st.kq.getD t default).Gq v G *
      amp gl st.Gk (st.ck.getD a []) (st.kq.getD t default).Gq v G'

/-- The pair sum over the computed bands. -/
noncomputable def parP (t a : ℕ) (G G' : V3) : ℝ :=
  ∑ n ∈ range (nbq st t), xS gl st t a n G * xS gl st t a n G'

/-- **The omitted-band pair sum**, computable: `κ` times all-band minus computed. -/
noncomputable def tailK (κ : ℝ) (t a : ℕ) (G G' : V3) : ℝ :=
  κ * cloP gl st t a G G' - parP gl st t a G G'

/-- Computed plus omitted rows resolve `κ` times the identity on the `k - q` sphere. -/
def CompleteK (κ : ℝ) (cp : Compl) (t : ℕ) : Prop :=
  ∀ v < (st.kq.getD t default).Gq.length, ∀ v' < (st.kq.getD t default).Gq.length,
    ∑ n ∈ range (nbq st t), dy gl.SC (((st.kq.getD t default).cq.getD n []).getD v 0) *
        dy gl.SC (((st.kq.getD t default).cq.getD n []).getD v' 0) +
      ∑ n ∈ range (cp.K t), cp.C t n v * cp.C t n v' = if v = v' then κ else 0

/-- `M_n(G)` of omitted band `n` at `q_t`. -/
noncomputable def mR (cp : Compl) (t a n : ℕ) (G : V3) : ℝ :=
  ∑ v ∈ range (st.kq.getD t default).Gq.length,
    amp gl st.Gk (st.ck.getD a []) (st.kq.getD t default).Gq v G * cp.C t n v

/-- `x = E - ε_n` (eV) of omitted band `n`. -/
noncomputable def xR (cp : Compl) (t a n iw : ℕ) : ℝ :=
  RYD * (dy gl.SEn (st.Ek.getD a 0) - cp.ε t n) + iw

theorem xR_one (cp : Compl) (t a n : ℕ) : xR gl st cp t a n 1 = xR gl st cp t a n 0 + 1 := by
  unfold xR; push_cast; ring

/-- The quadratic form of `quad` for an arbitrary pair-density function `u`. -/
noncomputable def quadR (vc : V3 → ℝ) (t : ℕ) (u : V3 → ℝ) (F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t),
    u (gs (gl.qs.getD t default) i) * vS gl vc (gl.qs.getD t default) i *
      u (gs (gl.qs.getD t default) j) * F j i

/-- **Closure** (completeness only; no shift-closure): the omitted-band pair sums are
`tailK`. -/
theorem tailK_eq (κ : ℝ) (cp : Compl) (t a : ℕ) (G G' : V3) (hc : CompleteK gl st κ cp t) :
    ∑ n ∈ range (cp.K t), mR gl st cp t a n G * mR gl st cp t a n G' = tailK gl st κ t a G G' := by
  set L := (st.kq.getD t default).Gq.length
  set A := amp gl st.Gk (st.ck.getD a []) (st.kq.getD t default).Gq
  have h1 : ∑ n ∈ range (cp.K t), mR gl st cp t a n G * mR gl st cp t a n G' =
      ∑ v ∈ range L, ∑ v' ∈ range L, A v G * A v' G' * ∑ n ∈ range (cp.K t), cp.C t n v * cp.C t n v' :=
    sum_prod_expand _ _ (cp.C t) _ _
  have h2 : parP gl st t a G G' = ∑ v ∈ range L, ∑ v' ∈ range L, A v G * A v' G' *
      ∑ n ∈ range (nbq st t), dy gl.SC (((st.kq.getD t default).cq.getD n []).getD v 0) *
        dy gl.SC (((st.kq.getD t default).cq.getD n []).getD v' 0) := by
    unfold parP xS
    simp_rw [pd_eq_amp]
    exact sum_prod_expand _ _ (fun n v => dy gl.SC (((st.kq.getD t default).cq.getD n []).getD v 0)) _ _
  have h3 : κ * cloP gl st t a G G' = ∑ v ∈ range L, ∑ v' ∈ range L, A v G * A v' G' *
      (if v = v' then κ else 0) := by
    unfold cloP
    rw [mul_sum]
    refine sum_congr rfl fun v hv => ?_
    rw [sum_eq_single v (fun v' _ h => by rw [if_neg (Ne.symm h), mul_zero]) (fun h => absurd hv h),
      if_pos rfl]
    ring
  unfold tailK
  rw [h1, h2, h3, ← sum_sub_distrib]
  refine sum_congr rfl fun v hv => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun v' hv' => ?_
  rw [← hc v (mem_range.mp hv) v' (mem_range.mp hv')]
  ring

variable (E : ℕ → ℕ → ℕ → ℝ)

/-- The omitted bands' theory correlation (every omitted band empty). -/
noncomputable def tailT (vc : V3 → ℝ) (cp : Compl) (a iw : ℕ) : ℝ :=
  ∑ t ∈ range gl.qs.length, ∑ n ∈ range (cp.K t), quadR gl vc t (mR gl st cp t a n)
    (fun j i => thK false (ITq gl E t j i) (OTq gl vc t j i) (xR gl st cp t a n iw))

/-- **The theory Σ, completion appended**: computed bands plus the rows of `cp`. -/
noncomputable def SigTall (vc : V3 → ℝ) (cp : Compl) (a iw : ℕ) : ℝ :=
  SigT gl E vc st a iw + tailT gl st E vc cp a iw

variable (vb oq : V3 → ℝ)

/-- The omitted bands' contribution with BerkeleyGW's rule: `ACq + Pq` (`specK`). -/
noncomputable def tailS (cp : Compl) (a iw : ℕ) : ℝ :=
  ∑ t ∈ range gl.qs.length, ∑ n ∈ range (cp.K t), quadR gl vb t (mR gl st cp t a n)
    (fun j i => specK (Iq gl E vb oq t j i) (Oq gl vb t j i) (xR gl st cp t a n iw))

/-- **The spec's Σ, completion appended.** Its static remainder `CORall` is NOT zero in general (`CorResidual.sigAall_static_split`, `cor_all_decomp`). -/
noncomputable def SigAall (cp : Compl) (a iw : ℕ) : ℝ :=
  SigA gl E vb oq st a iw + tailS gl st E vb oq cp a iw

end compl

section main

variable (gl : Gl) (st : St) (E : ℕ → ℕ → ℕ → ℝ) (vc : V3 → ℝ)

/-- The centre `Σ_t Σ_{i,j} v_i T_ij c_{t,j,i}`. -/
noncomputable def cenK (κ : ℝ) (a : ℕ) (c : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ t ∈ range gl.qs.length, ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t),
    vS gl vc (gl.qs.getD t default) i *
      tailK gl st κ t a (gs (gl.qs.getD t default) i) (gs (gl.qs.getD t default) j) * c t j i

/-- The radius `Σ_t Σ_{i,j} |v_i| √T_ii √T_jj r_{t,j,i}`. -/
noncomputable def radK (κ : ℝ) (a : ℕ) (r : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ t ∈ range gl.qs.length, ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t),
    |vS gl vc (gl.qs.getD t default) i| *
      (√(tailK gl st κ t a (gs (gl.qs.getD t default) i) (gs (gl.qs.getD t default) i)) *
        √(tailK gl st κ t a (gs (gl.qs.getD t default) j) (gs (gl.qs.getD t default) j))) * r t j i

/-- `tail_core` at every q-point, for a completion. -/
theorem tail_sum (κ : ℝ) (cp : Compl) (a : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℝ) (c r : ℕ → ℕ → ℕ → ℝ)
    (hc : ∀ t < gl.qs.length, CompleteK gl st κ cp t) (hr : ∀ t j i, 0 ≤ r t j i)
    (hF : ∀ t < gl.qs.length, ∀ n < cp.K t, ∀ j < nG gl t, ∀ i < nG gl t,
      |F t n j i - c t j i| ≤ r t j i) :
    |∑ t ∈ range gl.qs.length, ∑ n ∈ range (cp.K t), quadR gl vc t (mR gl st cp t a n) (F t n) -
        cenK gl st vc κ a c| ≤ radK gl st vc κ a r := by
  unfold cenK radK
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t ht => ?_)
  have ht' := mem_range.mp ht
  have hT : ∀ G G', tailK gl st κ t a G G' =
      ∑ n ∈ range (cp.K t), mR gl st cp t a n G * mR gl st cp t a n G' :=
    fun G G' => (tailK_eq gl st κ cp t a G G' (hc t ht')).symm
  simp only [hT]
  exact tail_core (nG gl t) (cp.K t) (fun n i => mR gl st cp t a n (gs (gl.qs.getD t default) i))
    (fun i => vS gl vc (gl.qs.getD t default) i) (F t) (c t) (r t) (hr t) (hF t ht')

/-- **C2, theory Σ, generic per-mode enclosure** (e.g. `c = 0`, `r = |I|/2` for a mode whose
validity is undecided, `thK_empty_abs`). -/
theorem sigT_tail_enclose (κ : ℝ) (cp : Compl) (a iw : ℕ) (c r : ℕ → ℕ → ℕ → ℝ)
    (hc : ∀ t < gl.qs.length, CompleteK gl st κ cp t) (hr : ∀ t j i, 0 ≤ r t j i)
    (hK : ∀ t < gl.qs.length, ∀ n < cp.K t, ∀ j < nG gl t, ∀ i < nG gl t,
      |thK false (ITq gl E t j i) (OTq gl vc t j i) (xR gl st cp t a n iw) - c t j i| ≤ r t j i) :
    |SigTall gl st E vc cp a iw - SigT gl E vc st a iw - cenK gl st vc κ a c| ≤
      radK gl st vc κ a r := by
  unfold SigTall
  rw [add_sub_cancel_left]
  exact tail_sum gl st vc κ cp a _ c r hc hr hK

/-- **C2 (main, theory).** The theory Σ with `cp` appended lies in the computed theory Σ plus
`Σ v T cK ± Σ |v| √T √T rK`, given only `D` (every omitted band has `x ≤ -D`, `D > 0`),
completeness (up to `κ`), and each mode's `w̃`. -/
theorem sigT_all_bands (κ : ℝ) (cp : Compl) (a iw : ℕ) (D : ℕ → ℝ)
    (hc : ∀ t < gl.qs.length, CompleteK gl st κ cp t) (hD : ∀ t, 0 < D t)
    (hx : ∀ t < gl.qs.length, ∀ n < cp.K t, xR gl st cp t a n iw ≤ -D t) :
    |SigTall gl st E vc cp a iw - SigT gl E vc st a iw -
        cenK gl st vc κ a (fun t j i => cK (ITq gl E t j i) (OTq gl vc t j i) (D t))| ≤
      radK gl st vc κ a (fun t j i => rK (ITq gl E t j i) (OTq gl vc t j i) (D t)) :=
  sigT_tail_enclose gl st E vc κ cp a iw _ _ hc (fun t _ _ => rK_nonneg _ _ _ (hD t))
    fun t ht n hn _ _ _ _ => thK_tail_mode (hD t) (hx t ht n hn)

/-- **C2, theory, the energy step** `Σ(E + 1 eV) - Σ(E)` (for the linearised Eqp1). -/
theorem sigT_diff_all_bands (κ : ℝ) (cp : Compl) (a : ℕ) (D : ℕ → ℝ)
    (hc : ∀ t < gl.qs.length, CompleteK gl st κ cp t) (hD : ∀ t, 1 < D t)
    (hx : ∀ t < gl.qs.length, ∀ n < cp.K t, xR gl st cp t a n 0 ≤ -D t) :
    |(SigTall gl st E vc cp a 1 - SigTall gl st E vc cp a 0) -
        (SigT gl E vc st a 1 - SigT gl E vc st a 0) -
        cenK gl st vc κ a (fun t j i => cKd (ITq gl E t j i) (OTq gl vc t j i) (D t))| ≤
      radK gl st vc κ a (fun t j i => rKd (ITq gl E t j i) (OTq gl vc t j i) (D t)) := by
  unfold SigTall
  have e : ∀ X Y A B : ℝ, (X + A - (Y + B)) - (X - Y) = A - B := fun _ _ _ _ => by ring
  rw [e]
  have hq : tailT gl st E vc cp a 1 - tailT gl st E vc cp a 0 =
      ∑ t ∈ range gl.qs.length, ∑ n ∈ range (cp.K t), quadR gl vc t (mR gl st cp t a n) (fun j i =>
        thK false (ITq gl E t j i) (OTq gl vc t j i) (xR gl st cp t a n 0 + 1) -
          thK false (ITq gl E t j i) (OTq gl vc t j i) (xR gl st cp t a n 0)) := by
    unfold tailT
    rw [← sum_sub_distrib]; refine sum_congr rfl fun t _ => ?_
    rw [← sum_sub_distrib]; refine sum_congr rfl fun n _ => ?_
    unfold quadR
    rw [← sum_sub_distrib]; refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]; refine sum_congr rfl fun j _ => ?_
    rw [xR_one]; ring
  rw [hq]
  exact tail_sum gl st vc κ cp a _ _ _ hc (fun t _ _ => rKd_nonneg _ _ _ (hD t))
    fun t ht n hn _ _ _ _ => thK_diff_mode (hD t) (hx t ht n hn)

variable (vb oq : V3 → ℝ)

/-- **C2 (main, BerkeleyGW's Σ, completion appended).** `SigAall` (`SigA` plus the omitted
rows' `ACq + Pq`, under `CompleteK κ`) lies in the run's Σ plus `Σ v T cS ± Σ |v| √T √T rS`;
`cS`'s `IeU/4` is the omitted rows' `ACq`; added to the run's `COR` it gives `CORall` = closure
scale + shift-closure defect + `Gch` coverage, not `0` (`CorResidual.cor_all_decomp`, F4). -/
theorem sigA_all_bands (κ : ℝ) (cp : Compl) (a iw : ℕ) (D : ℕ → ℝ)
    (hc : ∀ t < gl.qs.length, CompleteK gl st κ cp t) (hD : ∀ t, 1 / 2 < D t)
    (hx : ∀ t < gl.qs.length, ∀ n < cp.K t, xR gl st cp t a n iw ≤ -D t) :
    |SigAall gl st E vb oq cp a iw - SigA gl E vb oq st a iw -
        cenK gl st vb κ a (fun t j i => cS (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t))| ≤
      radK gl st vb κ a (fun t j i => rS (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t)) := by
  unfold SigAall
  rw [add_sub_cancel_left]
  exact tail_sum gl st vb κ cp a _ _ _ hc (fun t _ _ => rS_nonneg _ _ _ (by linarith [hD t]))
    fun t ht n hn _ _ _ _ => specK_tail_mode (hD t) (hx t ht n hn)

/-- **C2, BerkeleyGW's Σ, the energy step** (`D > 3/2`). -/
theorem sigA_diff_all_bands (κ : ℝ) (cp : Compl) (a : ℕ) (D : ℕ → ℝ)
    (hc : ∀ t < gl.qs.length, CompleteK gl st κ cp t) (hD : ∀ t, 3 / 2 < D t)
    (hx : ∀ t < gl.qs.length, ∀ n < cp.K t, xR gl st cp t a n 0 ≤ -D t) :
    |(SigAall gl st E vb oq cp a 1 - SigAall gl st E vb oq cp a 0) -
        (SigA gl E vb oq st a 1 - SigA gl E vb oq st a 0) -
        cenK gl st vb κ a (fun t j i => cSd (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t))| ≤
      radK gl st vb κ a (fun t j i => rSd (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t)) := by
  unfold SigAall
  have e : ∀ X Y A B : ℝ, (X + A - (Y + B)) - (X - Y) = A - B := fun _ _ _ _ => by ring
  rw [e]
  have hq : tailS gl st E vb oq cp a 1 - tailS gl st E vb oq cp a 0 =
      ∑ t ∈ range gl.qs.length, ∑ n ∈ range (cp.K t), quadR gl vb t (mR gl st cp t a n) (fun j i =>
        specK (Iq gl E vb oq t j i) (Oq gl vb t j i) (xR gl st cp t a n 0 + 1) -
          specK (Iq gl E vb oq t j i) (Oq gl vb t j i) (xR gl st cp t a n 0)) := by
    unfold tailS
    rw [← sum_sub_distrib]; refine sum_congr rfl fun t _ => ?_
    rw [← sum_sub_distrib]; refine sum_congr rfl fun n _ => ?_
    unfold quadR
    rw [← sum_sub_distrib]; refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]; refine sum_congr rfl fun j _ => ?_
    rw [xR_one]; ring
  rw [hq]
  exact tail_sum gl st vb κ cp a _ _ _ hc (fun t _ _ => rSd_nonneg _ _ _ (by linarith [hD t]))
    fun t ht n hn _ _ _ _ => specK_diff_mode (hD t) (hx t ht n hn)

end main

/-! ### The computed bands: truncation -/

/-- The first `nb` bands at one `k - q` point. -/
def truncKQ (nb : ℕ) (kq : KQ) : KQ := ⟨kq.Gq, kq.cq.take nb, kq.Eq.take nb⟩

/-- The state with only the first `nb` bands at every `k - q` (what the run computed). -/
def trunc (nb : ℕ) (st : St) : St := ⟨st.Gk, st.ck, st.Ek, st.kq.map (truncKQ nb)⟩

theorem trunc_kq (nb t : ℕ) (st : St) :
    (trunc nb st).kq.getD t default = truncKQ nb (st.kq.getD t default) := by
  simp only [trunc, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases st.kq[t]? with
  | none => simp only [Option.getD_none, Option.map_none, truncKQ]; cases nb <;> rfl
  | some k => simp

theorem getD_take {α : Type*} (l : List α) (n i : ℕ) (d : α) (h : i < n) :
    (l.take n).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

section trunc

variable (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vc : V3 → ℝ) (oq : V3 → ℝ) (st : St) (nb : ℕ)

theorem xS_trunc {t a n : ℕ} (G : V3) (h : n < nb) : xS gl (trunc nb st) t a n G = xS gl st t a n G := by
  unfold xS; rw [trunc_kq]; simp only [truncKQ, getD_take _ _ _ _ h]; rfl

theorem xT_trunc {t a n : ℕ} (iw : ℕ) (h : n < nb) : xT gl (trunc nb st) t a n iw = xT gl st t a n iw := by
  unfold xT; rw [trunc_kq]; simp only [truncKQ, getD_take _ _ _ _ h]; rfl

theorem wxS_trunc {t a n : ℕ} (iw : ℕ) (h : n < nb) : wxS gl (trunc nb st) t a n iw = wxS gl st t a n iw := by
  rw [wxS_eq, wxS_eq, xT_trunc gl st nb iw h]

theorem nbq_trunc {t : ℕ} (h : nb ≤ nbq st t) : nbq (trunc nb st) t = nb := by
  unfold nbq at h ⊢; rw [trunc_kq]; simp only [truncKQ, List.length_take]; omega

theorem Xq_trunc (t a : ℕ) (h : gl.nocc ≤ nb) : Xq gl vc (trunc nb st) t a = Xq gl vc st t a := by
  unfold Xq; dsimp only; rw [trunc_kq]; simp only [truncKQ]
  congr 1
  refine sum_congr rfl fun n1 hn1 => ?_
  rw [getD_take _ _ _ _ (lt_of_lt_of_le (mem_range.mp hn1) h)]; rfl

theorem PT_trunc {t a n : ℕ} (iw : ℕ) (h : n < nb) :
    PT gl E vc (trunc nb st) t a n iw = PT gl E vc st t a n iw := by
  unfold PT quad; simp only [xS_trunc gl st nb _ h, xT_trunc gl st nb iw h]

theorem ACq_trunc {t a n : ℕ} (h : n < nb) :
    ACq gl E vc oq (trunc nb st) t a n = ACq gl E vc oq st t a n := by
  unfold ACq quad; simp only [xS_trunc gl st nb _ h]

theorem Pq_trunc {t a n : ℕ} (iw : ℕ) (h : n < nb) :
    Pq gl E vc oq (trunc nb st) t a n iw = Pq gl E vc oq st t a n iw := by
  unfold Pq quad; simp only [xS_trunc gl st nb _ h, wxS_trunc gl st nb iw h]

theorem CSq_trunc (t a : ℕ) : CSq gl E vc oq (trunc nb st) t a = CSq gl E vc oq st t a := rfl

end trunc

theorem quad_add (gl : Gl) (vb : V3 → ℝ) (st : St) (t a n1 : ℕ) (F G : ℕ → ℕ → ℝ) :
    quad gl vb st t a n1 (fun j i => F j i + G j i) =
      quad gl vb st t a n1 F + quad gl vb st t a n1 G := by
  simp only [quad, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

theorem xT_one (gl : Gl) (st : St) (t a n : ℕ) : xT gl st t a n 1 = xT gl st t a n 0 + 1 := by
  unfold xT; push_cast; ring

theorem TZ_lt_half : TZ < 1 / 2 := by unfold TZ; norm_num

/-! ### The completion defined by a larger dyadic state: the old notions -/

section ofState

variable (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vc : V3 → ℝ) (st : St)

/-- The theory Σ with all bands is the truncated one plus the omitted-band correlation. -/
theorem sigT_split (a iw nb : ℕ) (hnb : ∀ t < gl.qs.length, nb ≤ nbq st t) (hocc : gl.nocc ≤ nb) :
    SigT gl E vc st a iw = SigT gl E vc (trunc nb st) a iw +
      ∑ t ∈ range gl.qs.length, ∑ n ∈ Ico nb (nbq st t), PT gl E vc st t a n iw := by
  unfold SigT
  rw [← sum_add_distrib]
  refine sum_congr rfl fun t ht => ?_
  have ht' := mem_range.mp ht
  have hP : ∑ n ∈ range nb, PT gl E vc (trunc nb st) t a n iw = ∑ n ∈ range nb, PT gl E vc st t a n iw :=
    sum_congr rfl fun n hn => PT_trunc gl E vc st nb iw (mem_range.mp hn)
  rw [nbq_trunc st nb (hnb t ht'), Xq_trunc gl vc st nb t a hocc, hP,
    ← sum_range_add_sum_Ico _ (hnb t ht')]
  ring

variable (vb oq : V3 → ℝ)

/-- The spec's Σ with all bands is the truncated spec Σ plus the omitted bands' `ACq + Pq`. -/
theorem sigA_split (a iw nb : ℕ) (hnb : ∀ t < gl.qs.length, nb ≤ nbq st t) (hocc : gl.nocc ≤ nb) :
    SigA gl E vb oq st a iw = SigA gl E vb oq (trunc nb st) a iw +
      ∑ t ∈ range gl.qs.length, ∑ n ∈ Ico nb (nbq st t),
        (ACq gl E vb oq st t a n + Pq gl E vb oq st t a n iw) := by
  unfold SigA
  rw [← sum_add_distrib]
  refine sum_congr rfl fun t ht => ?_
  have ht' := mem_range.mp ht
  have hP : ∑ n ∈ range nb, (ACq gl E vb oq (trunc nb st) t a n + Pq gl E vb oq (trunc nb st) t a n iw) =
      ∑ n ∈ range nb, (ACq gl E vb oq st t a n + Pq gl E vb oq st t a n iw) :=
    sum_congr rfl fun n hn => by
      rw [ACq_trunc gl E vb oq st nb (mem_range.mp hn), Pq_trunc gl E vb oq st nb iw (mem_range.mp hn)]
  rw [nbq_trunc st nb (hnb t ht'), Xq_trunc gl vb st nb t a hocc, CSq_trunc, hP,
    ← sum_range_add_sum_Ico _ (hnb t ht')]
  ring

/-- On an omitted (empty) band away from `TOL_Zero`, `ACq + Pq` is the quadratic form of `specK`. -/
theorem acq_pq_tail {t a n iw : ℕ} (hn : ¬ n < gl.nocc) (hx : TZ ≤ |xT gl st t a n iw|) :
    ACq gl E vb oq st t a n + Pq gl E vb oq st t a n iw =
      quad gl vb st t a n (fun j i => specK (Iq gl E vb oq t j i) (Oq gl vb t j i) (xT gl st t a n iw)) := by
  have hw : wxS gl st t a n iw = xT gl st t a n iw := by rw [wxS_eq, if_neg (not_lt.mpr hx)]
  unfold ACq Pq specK
  rw [if_neg hn, sub_zero, hw, ← quad_smul, ← quad_smul, ← quad_smul, ← quad_add]
  congr 1; funext j i; ring

/-- The completion given by the dyadic rows `n ≥ nb` of a larger state `st'`. -/
noncomputable def complOf (st' : St) (nb : ℕ) : Compl :=
  ⟨fun t => nbq st' t - nb,
   fun t n v => dy gl.SC ((((st'.kq.getD t default).cq).getD (nb + n) []).getD v 0),
   fun t n => dy gl.SEn (((st'.kq.getD t default).Eq).getD (nb + n) 0)⟩

theorem mR_complOf (st' : St) (nb t a n : ℕ) (G : V3) :
    mR gl (trunc nb st') (complOf gl st' nb) t a n G = xS gl st' t a (nb + n) G := by
  unfold mR xS complOf
  rw [trunc_kq, pd_eq_amp]; rfl

theorem xR_complOf (st' : St) (nb t a n iw : ℕ) :
    xR gl (trunc nb st') (complOf gl st' nb) t a n iw = xT gl st' t a (nb + n) iw := rfl

theorem quadR_complOf (st' : St) (nb t a n : ℕ) (F : ℕ → ℕ → ℝ) :
    quadR gl vc t (mR gl (trunc nb st') (complOf gl st' nb) t a n) F = quad gl vc st' t a (nb + n) F := by
  unfold quadR quad nG
  simp only [mR_complOf]

/-- Completeness of a larger dyadic state is `CompleteK 1` of its completion. -/
theorem completeK_of_complete (st' : St) (nb t : ℕ) (hnb : nb ≤ nbq st' t)
    (hc : Complete gl (st'.kq.getD t default).Gq (st'.kq.getD t default).cq (nbq st' t)) :
    CompleteK gl (trunc nb st') 1 (complOf gl st' nb) t := by
  intro v hv v' hv'
  rw [nbq_trunc st' nb hnb]
  simp only [trunc_kq, truncKQ] at hv hv' ⊢
  have e1 : ∑ n ∈ range nb, dy gl.SC (((List.take nb (st'.kq.getD t default).cq).getD n []).getD v 0) *
      dy gl.SC (((List.take nb (st'.kq.getD t default).cq).getD n []).getD v' 0) =
      ∑ n ∈ range nb, dy gl.SC (((st'.kq.getD t default).cq.getD n []).getD v 0) *
        dy gl.SC (((st'.kq.getD t default).cq.getD n []).getD v' 0) :=
    sum_congr rfl fun n hn => by rw [getD_take _ _ _ _ (mem_range.mp hn)]
  rw [e1]
  have e2 : ∑ n ∈ range ((complOf gl st' nb).K t), (complOf gl st' nb).C t n v * (complOf gl st' nb).C t n v' =
      ∑ n ∈ Ico nb (nbq st' t), dy gl.SC (((st'.kq.getD t default).cq.getD n []).getD v 0) *
        dy gl.SC (((st'.kq.getD t default).cq.getD n []).getD v' 0) := by
    rw [sum_Ico_eq_sum_range]; rfl
  rw [e2, sum_range_add_sum_Ico _ hnb, hc v hv v' hv']

/-- **Consistency (theory).** For the completion by a larger dyadic state, `SigTall` is that
state's `SigT`. -/
theorem sigTall_of_state (st' : St) (a iw nb : ℕ) (hnb : ∀ t < gl.qs.length, nb ≤ nbq st' t)
    (hocc : gl.nocc ≤ nb) :
    SigTall gl (trunc nb st') E vc (complOf gl st' nb) a iw = SigT gl E vc st' a iw := by
  rw [sigT_split gl E vc st' a iw nb hnb hocc]
  unfold SigTall tailT
  congr 1
  refine sum_congr rfl fun t ht => ?_
  rw [sum_Ico_eq_sum_range]
  refine sum_congr rfl fun n _ => ?_
  rw [quadR_complOf, PT]
  have : decide (nb + n < gl.nocc) = false := decide_eq_false (by omega)
  rw [this]; rfl

/-- **Consistency (spec).** For the completion by a larger dyadic state whose omitted bands
are away from `TOL_Zero`, `SigAall` is that state's `SigA`. -/
theorem sigAall_of_state (st' : St) (a iw nb : ℕ) (hnb : ∀ t < gl.qs.length, nb ≤ nbq st' t)
    (hocc : gl.nocc ≤ nb)
    (hx : ∀ t < gl.qs.length, ∀ n, nb ≤ n → n < nbq st' t → TZ ≤ |xT gl st' t a n iw|) :
    SigAall gl (trunc nb st') E vb oq (complOf gl st' nb) a iw = SigA gl E vb oq st' a iw := by
  rw [sigA_split gl E st' vb oq a iw nb hnb hocc]
  unfold SigAall tailS
  congr 1
  refine sum_congr rfl fun t ht => ?_
  rw [sum_Ico_eq_sum_range]
  refine sum_congr rfl fun n hn => ?_
  have h1 : nb ≤ nb + n := Nat.le_add_right _ _
  have h2 : nb + n < nbq st' t := by
    have := mem_range.mp hn; change n < nbq st' t - nb at this; omega
  rw [quadR_complOf, acq_pq_tail gl E st' vb oq (by omega) (hx t (mem_range.mp ht) _ h1 h2)]
  rfl

end ofState

end GW.Bridge
