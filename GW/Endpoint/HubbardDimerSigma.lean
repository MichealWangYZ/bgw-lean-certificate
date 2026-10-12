/-
A3 dimer, part 2 (Task 3): the single-pole G0W0 self-energy `sigmaSinglePole`
is DERIVED from G0 and W_c, instead of being taken as a definition.

Route (no contour integrals): everything is done in the time domain with
finite sums of exponentials.

* `G0time`: the time-ordered HF Green's function
      G0_ij(τ) = -i Σ_k φ_k(i) φ_k(j) [θ(τ)(1 - f_k) - θ(-τ) f_k] e^{-i ε_k τ}
  (equal-time value taken from the τ → 0⁻ side; a single point, irrelevant
  for the integrals).
* `WcTime`: the time-ordered single-pole screened interaction
      W_c,ij(τ) = -i R_ij e^{-i Ω |τ|}.
* `sigmaTime`: Σ_c,ij(τ) = i G0_ij(τ) W_c,ij(τ) (pointwise in the site
  indices; this is `Σ = i G W` with the contact interaction's site locality
  left general: any `R`).
* `ftDamped η f ω = ∫_ℝ e^{iωτ - η|τ|} f(τ) dτ`, the Fourier transform with
  the standard symmetric convergence factor, a genuine Lebesgue (Bochner)
  integral over the real line.

Proved (all real `ω` off the poles, limit `η → 0⁺`):
* `ftDamped_twoSided`: exact value of the damped transform of
  `θ(τ) Σ c_p e^{-i a_p τ} + θ(-τ) Σ d_q e^{-i b_q τ}` for every `η > 0`:
  `Σ c_p i/(ω - a_p + iη) + Σ d_q (-i)/(ω - b_q - iη)`
  (from Mathlib's `integral_exp_mul_complex_Ioi`/`_Iic`).
* `ftDamped_twoSided_limit`: its `η → 0⁺` limit.
* `sigmaSinglePole_eq_limit`: for ANY residue matrix `R`, pole `Ω` and
  orbital list, the limit of `ftDamped η (i G0 W_c)` is `sigmaSinglePole`.
* `sigmaC_eq_limit`: the dimer instance, with exactly the objects of
  `HubbardDimer.lean` (`resW`, `hRPA`, `phiB/phiA`, `epsB/epsA`), so the
  `sigmaC` that feeds `sigmaC_orbital`, `qp_removal`, `qp_addition` is the
  transform of `i G0 W_c`.
* Consistency of the time-domain inputs with the frequency-domain objects
  already in `HubbardDimer.lean`: `WcTime_limit` (the transform of `WcTime` is
  the proved RPA `Wc`), `G0time_limit` + `g0HF_resolvent` (the transform of
  `G0time` is the resolvent `(ω - F)⁻¹` of the HF Fock matrix).

What this does NOT say: it is the T = 0, time-ordered, single-pole case; the
convergence factor is put on Σ(τ) (equivalently on the product G0 W_c); the
limit is taken for real ω away from the poles, not as a distribution.
-/
import GW.Endpoint.HubbardDimer
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace GW.Endpoint.HubbardDimer

open Complex MeasureTheory Set Filter Topology Matrix

/-! ### Damped Fourier transform of two-sided exponential sums -/

/-- `∫_ℝ e^{iωτ - η|τ|} f(τ) dτ`. -/
noncomputable def ftDamped (η : ℝ) (f : ℝ → ℂ) (ω : ℝ) : ℂ :=
  ∫ τ : ℝ, Complex.exp (I * ω * τ - η * ((|τ| : ℝ) : ℂ)) * f τ

/-- `Σ_p c_p e^{-i a_p τ}` for a list of pairs `(c_p, a_p)`. -/
noncomputable def expSum (l : List (ℂ × ℝ)) (τ : ℝ) : ℂ :=
  (l.map fun p => p.1 * Complex.exp (-(I * p.2 * τ))).sum

/-- `θ(τ) expSum lp τ + θ(-τ) expSum ln τ` (value at `τ = 0` from the left). -/
noncomputable def twoSided (lp ln : List (ℂ × ℝ)) (τ : ℝ) : ℂ :=
  if 0 < τ then expSum lp τ else expSum ln τ

theorem list_sum_mul_left {α : Type*} (c : ℂ) (l : List α) (f : α → ℂ) :
    c * (l.map f).sum = (l.map fun x => c * f x).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [mul_add, ih]

theorem list_sum_map_add {α : Type*} (l : List α) (f g : α → ℂ) :
    (l.map f).sum + (l.map g).sum = (l.map fun x => f x + g x).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ← ih]; ring

theorem ofReal_list_sum {α : Type*} (l : List α) (f : α → ℝ) :
    (((l.map f).sum : ℝ) : ℂ) = (l.map fun x => (f x : ℂ)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

/-- Integral of a finite exponential sum over a set, term by term. -/
theorem setIntegral_expList {S : Set ℝ} (k : ℂ × ℝ → ℂ) (l : List (ℂ × ℝ))
    (hk : ∀ p ∈ l, IntegrableOn (fun τ : ℝ => Complex.exp (k p * τ)) S) :
    IntegrableOn (fun τ : ℝ => (l.map fun p => p.1 * Complex.exp (k p * τ)).sum) S ∧
      ∫ τ in S, (l.map fun p => p.1 * Complex.exp (k p * τ)).sum =
        (l.map fun p => p.1 * ∫ τ in S, Complex.exp (k p * τ)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := (hk p List.mem_cons_self).const_mul p.1
    obtain ⟨ih1, ih2⟩ := ih (fun q hq => hk q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, List.sum_cons]
    exact ⟨hp.add ih1, by rw [integral_add hp ih1, integral_const_mul, ih2]⟩

/-- Right half-line: `∫_0^∞ e^{(i(ω-a) - η)τ} dτ = i/(ω - a + iη)`. -/
theorem integral_Ioi_osc {η : ℝ} (hη : 0 < η) (ω a : ℝ) :
    IntegrableOn (fun τ : ℝ => Complex.exp ((I * (ω - a) - η) * τ)) (Ioi 0) ∧
      ∫ τ in Ioi (0 : ℝ), Complex.exp ((I * (ω - a) - η) * τ) = I / (ω - a + I * η) := by
  have hre : (I * ((ω : ℂ) - a) - η).re < 0 := by simp; linarith
  refine ⟨integrableOn_exp_mul_complex_Ioi hre 0, ?_⟩
  rw [integral_exp_mul_complex_Ioi hre 0]
  have hk : (I * ((ω : ℂ) - a) - η) = I * (ω - a + I * η) := by linear_combination (-(η : ℂ)) * I_sq
  have hne : ((ω : ℂ) - a + I * η) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  rw [hk]; simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring_nf; simp only [I_sq, show I ^ 3 = -I by rw [pow_succ, I_sq]; ring]; ring

/-- Left half-line: `∫_{-∞}^0 e^{(i(ω-b) + η)τ} dτ = -i/(ω - b - iη)`. -/
theorem integral_Iic_osc {η : ℝ} (hη : 0 < η) (ω b : ℝ) :
    IntegrableOn (fun τ : ℝ => Complex.exp ((I * (ω - b) + η) * τ)) (Iic 0) ∧
      ∫ τ in Iic (0 : ℝ), Complex.exp ((I * (ω - b) + η) * τ) = -I / (ω - b - I * η) := by
  have hre : 0 < (I * ((ω : ℂ) - b) + η).re := by simp; linarith
  refine ⟨integrableOn_exp_mul_complex_Iic hre 0, ?_⟩
  rw [integral_exp_mul_complex_Iic hre 0]
  have hk : (I * ((ω : ℂ) - b) + η) = I * (ω - b - I * η) := by linear_combination (η : ℂ) * I_sq
  have hne : ((ω : ℂ) - b - I * η) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  rw [hk]; simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring_nf; simp only [I_sq, show I ^ 3 = -I by rw [pow_succ, I_sq]; ring]; ring

/-- **Damped transform of a two-sided exponential sum**, exact for every `η > 0`. -/
theorem ftDamped_twoSided {η : ℝ} (hη : 0 < η) (lp ln : List (ℂ × ℝ)) (ω : ℝ) :
    ftDamped η (twoSided lp ln) ω =
      (lp.map fun p => p.1 * (I / (ω - p.2 + I * η))).sum +
        (ln.map fun p => p.1 * (-I / (ω - p.2 - I * η))).sum := by
  set g : ℝ → ℂ := fun τ => Complex.exp (I * ω * τ - η * ((|τ| : ℝ) : ℂ)) * twoSided lp ln τ
  set kp : ℂ × ℝ → ℂ := fun p => I * (ω - p.2) - η
  set kn : ℂ × ℝ → ℂ := fun p => I * (ω - p.2) + η
  have eR : EqOn g (fun τ : ℝ => (lp.map fun p => p.1 * Complex.exp (kp p * τ)).sum) (Ioi 0) := by
    intro τ hτ
    simp only [g, twoSided, if_pos (show (0 : ℝ) < τ from hτ), abs_of_pos (show (0 : ℝ) < τ from hτ),
      expSum, list_sum_mul_left]
    congr 1; apply List.map_congr_left; intro p _
    rw [mul_left_comm, ← Complex.exp_add]; congr 2; simp only [kp]; ring
  have eL : EqOn g (fun τ : ℝ => (ln.map fun p => p.1 * Complex.exp (kn p * τ)).sum) (Iic 0) := by
    intro τ hτ
    have hτ' : τ ≤ 0 := hτ
    simp only [g, twoSided, if_neg (not_lt.mpr hτ'), abs_of_nonpos hτ', expSum, list_sum_mul_left]
    congr 1; apply List.map_congr_left; intro p _
    rw [mul_left_comm, ← Complex.exp_add]; congr 2; simp only [kn]; push_cast; ring
  obtain ⟨iR, vR⟩ := setIntegral_expList (S := Ioi 0) kp lp
    (fun p _ => (integral_Ioi_osc hη ω p.2).1)
  obtain ⟨iL, vL⟩ := setIntegral_expList (S := Iic 0) kn ln
    (fun p _ => (integral_Iic_osc hη ω p.2).1)
  have hR : IntegrableOn g (Ioi 0) := iR.congr_fun eR.symm measurableSet_Ioi
  have hL : IntegrableOn g (Iic 0) := iL.congr_fun eL.symm measurableSet_Iic
  unfold ftDamped
  rw [← intervalIntegral.integral_Iic_add_Ioi hL hR, setIntegral_congr_fun measurableSet_Ioi eR,
    setIntegral_congr_fun measurableSet_Iic eL, vR, vL, add_comm]
  congr 1
  · congr 1; apply List.map_congr_left; intro p _; rw [(integral_Ioi_osc hη ω p.2).2]
  · congr 1; apply List.map_congr_left; intro p _; rw [(integral_Iic_osc hη ω p.2).2]

/-- **`η → 0⁺` limit** of the damped transform, for real `ω` off every pole that
carries a nonzero coefficient. -/
theorem ftDamped_twoSided_limit (lp ln : List (ℂ × ℝ)) (ω : ℝ)
    (hp : ∀ p ∈ lp, p.1 ≠ 0 → ω - p.2 ≠ 0) (hn : ∀ p ∈ ln, p.1 ≠ 0 → ω - p.2 ≠ 0) :
    Tendsto (fun η => ftDamped η (twoSided lp ln) ω) (𝓝[>] 0)
      (𝓝 ((lp.map fun p => p.1 * (I / (ω - p.2))).sum +
        (ln.map fun p => p.1 * (-I / (ω - p.2))).sum)) := by
  have hev : (fun η : ℝ => (lp.map fun p => p.1 * (I / (ω - p.2 + I * η))).sum +
      (ln.map fun p => p.1 * (-I / (ω - p.2 - I * η))).sum) =ᶠ[𝓝[>] 0]
      fun η => ftDamped η (twoSided lp ln) ω := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact (ftDamped_twoSided hη lp ln ω).symm
  refine Tendsto.congr' hev (Tendsto.mono_left ?_ nhdsWithin_le_nhds)
  have hc : Continuous fun η : ℝ => (η : ℂ) := continuous_ofReal
  refine Tendsto.add (tendsto_list_sum lp fun p hpl => ?_) (tendsto_list_sum ln fun p hpl => ?_)
  · by_cases hz : p.1 = 0
    · simp [hz]
    have h0 : ((ω : ℂ) - p.2) ≠ 0 := by exact_mod_cast hp p hpl hz
    simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.div
      ((continuous_const.add (continuous_const.mul hc)).tendsto 0) (by simpa using h0))
      : Tendsto (fun η : ℝ => p.1 * (I / ((ω : ℂ) - p.2 + I * η))) (𝓝 0) _)
  · by_cases hz : p.1 = 0
    · simp [hz]
    have h0 : ((ω : ℂ) - p.2) ≠ 0 := by exact_mod_cast hn p hpl hz
    simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.div
      ((continuous_const.sub (continuous_const.mul hc)).tendsto 0) (by simpa using h0))
      : Tendsto (fun η : ℝ => p.1 * (-I / ((ω : ℂ) - p.2 - I * η))) (𝓝 0) _)

/-! ### Time-domain G0, W_c and Σ_c = i G0 W_c -/

/-- An orbital entry `(φ, ε, occupied?)`, as in `sigmaSinglePole`. -/
abbrev Orb := (Fin 2 → ℝ) × ℝ × Bool

/-- Occupation number `f ∈ {0, 1}`. -/
noncomputable def occR (o : Orb) : ℝ := if o.2.2 then 1 else 0

/-- Time-ordered T = 0 Green's function of the orbitals `orbs`:
`G0_ij(τ) = -i Σ_k φ_k(i) φ_k(j) [θ(τ)(1 - f_k) - θ(-τ) f_k] e^{-i ε_k τ}`. -/
noncomputable def G0time (orbs : List Orb) (τ : ℝ) (i j : Fin 2) : ℂ :=
  -I * (orbs.map fun o =>
    ((o.1 i * o.1 j * (if 0 < τ then 1 - occR o else -occR o) : ℝ) : ℂ) *
      Complex.exp (-(I * o.2.1 * τ))).sum

/-- Time-ordered single-pole screened interaction `W_c,ij(τ) = -i R_ij e^{-iΩ|τ|}`. -/
noncomputable def WcTime (R : Matrix (Fin 2) (Fin 2) ℝ) (Ω τ : ℝ) (i j : Fin 2) : ℂ :=
  -I * R i j * Complex.exp (-(I * Ω * ((|τ| : ℝ) : ℂ)))

/-- `Σ_c,ij(τ) = i G0_ij(τ) W_c,ij(τ)`. -/
noncomputable def sigmaTime (R : Matrix (Fin 2) (Fin 2) ℝ) (Ω : ℝ) (orbs : List Orb) (τ : ℝ)
    (i j : Fin 2) : ℂ :=
  I * G0time orbs τ i j * WcTime R Ω τ i j

theorem list_sum_mul_right {α : Type*} (d : ℂ) (l : List α) (f : α → ℂ) :
    (l.map f).sum * d = (l.map fun x => f x * d).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [add_mul, ih]

theorem I_mul_negI (x : ℂ) : I * (-I * x) = x := by
  ring_nf; rw [I_sq]; ring

theorem negI_mul_I_div (x y : ℂ) : -I * x * (I / y) = x / y := by
  rw [div_eq_mul_inv, div_eq_mul_inv]; ring_nf; rw [I_sq]; ring

theorem I_mul_negI_div (x y : ℂ) : I * x * (-I / y) = x / y := by
  rw [div_eq_mul_inv, div_eq_mul_inv]; ring_nf; rw [I_sq]; ring

theorem WcTime_eq (R : Matrix (Fin 2) (Fin 2) ℝ) (Ω : ℝ) (i j : Fin 2) :
    (fun τ => WcTime R Ω τ i j) = twoSided [(-I * R i j, Ω)] [(-I * R i j, -Ω)] := by
  funext τ
  unfold WcTime twoSided expSum
  split_ifs with h
  · simp [abs_of_pos h]
  · simp only [abs_of_nonpos (not_lt.mp h), List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    push_cast; ring_nf

theorem G0time_eq (orbs : List Orb) (i j : Fin 2) :
    (fun τ => G0time orbs τ i j) =
      twoSided (orbs.map fun o => (-I * ((o.1 i * o.1 j * (1 - occR o) : ℝ) : ℂ), o.2.1))
        (orbs.map fun o => (I * ((o.1 i * o.1 j * occR o : ℝ) : ℂ), o.2.1)) := by
  funext τ
  unfold G0time twoSided expSum
  split_ifs with h
  · rw [List.map_map, list_sum_mul_left]
    congr 1; apply List.map_congr_left; intro o _
    simp only [Function.comp, if_pos h]; ring
  · rw [List.map_map, list_sum_mul_left]
    congr 1; apply List.map_congr_left; intro o _
    simp only [Function.comp, if_neg h]; push_cast; ring

/-- `Σ_c(τ) = i G0(τ) W_c(τ)` is again a two-sided exponential sum:
particles propagate forward with `e^{-i(ε_k + Ω)τ}`, holes backward with
`e^{-i(ε_k - Ω)τ}`. -/
theorem sigmaTime_eq (R : Matrix (Fin 2) (Fin 2) ℝ) (Ω : ℝ) (orbs : List Orb) (i j : Fin 2) :
    (fun τ => sigmaTime R Ω orbs τ i j) =
      twoSided (orbs.map fun o => (-I * ((R i j * o.1 i * o.1 j * (1 - occR o) : ℝ) : ℂ), o.2.1 + Ω))
        (orbs.map fun o => (I * ((R i j * o.1 i * o.1 j * occR o : ℝ) : ℂ), o.2.1 - Ω)) := by
  funext τ
  unfold sigmaTime G0time WcTime twoSided expSum
  split_ifs with h
  · rw [I_mul_negI, list_sum_mul_right, List.map_map, abs_of_pos h]
    congr 1; apply List.map_congr_left; intro o _
    simp only [Function.comp, if_pos h]
    rw [show -(I * ((o.2.1 + Ω : ℝ) : ℂ) * τ) = -(I * o.2.1 * τ) + -(I * Ω * τ) by push_cast; ring,
      Complex.exp_add]
    push_cast; ring
  · rw [I_mul_negI, list_sum_mul_right, List.map_map, abs_of_nonpos (not_lt.mp h)]
    congr 1; apply List.map_congr_left; intro o _
    simp only [Function.comp, if_neg h]
    rw [show -(I * ((o.2.1 - Ω : ℝ) : ℂ) * τ) = -(I * o.2.1 * τ) + -(I * Ω * ((-τ : ℝ) : ℂ)) by
      push_cast; ring, Complex.exp_add]
    push_cast; ring

/-! ### The single-pole self-energy is the transform of `i G0 W_c` -/

/-- **Task 3, general form.** For any residue matrix `R`, pole `Ω` and orbital
list, and real `ω` off the physical poles (`ε_k - Ω` for occupied, `ε_k + Ω` for
empty orbitals), the damped Fourier transform of `Σ_c(τ) = i G0(τ) W_c(τ)`
converges, as `η → 0⁺`, to `sigmaSinglePole R Ω orbs ω`. -/
theorem sigmaSinglePole_eq_limit (R : Matrix (Fin 2) (Fin 2) ℝ) (Ω : ℝ) (orbs : List Orb)
    (ω : ℝ) (hoff : ∀ o ∈ orbs, if o.2.2 then ω - o.2.1 + Ω ≠ 0 else ω - o.2.1 - Ω ≠ 0)
    (i j : Fin 2) :
    Tendsto (fun η => ftDamped η (fun τ => sigmaTime R Ω orbs τ i j) ω) (𝓝[>] 0)
      (𝓝 ((sigmaSinglePole R Ω orbs ω i j : ℝ) : ℂ)) := by
  rw [sigmaTime_eq]
  convert ftDamped_twoSided_limit _ _ ω ?_ ?_ using 2
  · rw [List.map_map, List.map_map, list_sum_map_add]
    simp only [sigmaSinglePole, Matrix.of_apply, ofReal_list_sum]
    congr 1; apply List.map_congr_left; intro o _
    simp only [Function.comp, negI_mul_I_div, I_mul_negI_div, occR]
    split_ifs <;> push_cast <;> ring
  · simp only [List.mem_map]
    rintro p ⟨o, ho, rfl⟩ hz
    have := hoff o ho
    cases hb : o.2.2
    · rw [hb] at this; simp only [Bool.false_eq_true, if_false] at this
      intro h; apply this; dsimp only at h; linarith
    · exfalso; apply hz; simp [occR, hb]
  · simp only [List.mem_map]
    rintro p ⟨o, ho, rfl⟩ hz
    have := hoff o ho
    cases hb : o.2.2
    · exfalso; apply hz; simp [occR, hb]
    · rw [hb] at this; simp only [if_true] at this
      intro h; apply this; dsimp only at h; linarith

/-- The orbitals of the G0W0@HF dimer, exactly as in `sigmaC`. -/
noncomputable def dimerOrbs (t U : ℝ) : List Orb := [(phiB, epsB t U, true), (phiA, epsA t U, false)]

/-- **Task 3, dimer.** The `sigmaC` used by `sigmaC_orbital`, `qp_removal` and
`qp_addition` is the `η → 0⁺` limit of the damped Fourier transform of
`i G0(τ) W_c(τ)`, with G0 the HF Green's function and W_c the RPA single pole
(`resW`, `hRPA`), for every real `ω` other than the two physical poles
`epsB - h` and `epsA + h`. -/
theorem sigmaC_eq_limit (t U ω : ℝ) (h1 : ω ≠ epsB t U - hRPA t U) (h2 : ω ≠ epsA t U + hRPA t U)
    (i j : Fin 2) :
    Tendsto (fun η => ftDamped η (fun τ => sigmaTime (resW t U) (hRPA t U) (dimerOrbs t U) τ i j) ω)
      (𝓝[>] 0) (𝓝 ((sigmaC t U ω i j : ℝ) : ℂ)) := by
  apply sigmaSinglePole_eq_limit
  intro o ho
  simp only [dimerOrbs, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl
  · simp only [if_true]; intro h; apply h1; linarith
  · simp only [if_false, Bool.false_eq_true]; intro h; apply h2; linarith

/-- Orbital matrix element of the transformed `i G0 W_c` in orbital `φ`. -/
noncomputable def sigmaOrbitalFT (t U : ℝ) (φ : Fin 2 → ℝ) (η E : ℝ) : ℂ :=
  ∑ i, (φ i : ℂ) * ∑ j, ftDamped η (fun τ => sigmaTime (resW t U) (hRPA t U) (dimerOrbs t U) τ i j) E *
    (φ j : ℂ)

theorem sigmaOrbitalFT_limit (t U : ℝ) (φ : Fin 2 → ℝ) (E : ℝ) (h1 : E ≠ epsB t U - hRPA t U)
    (h2 : E ≠ epsA t U + hRPA t U) :
    Tendsto (fun η => sigmaOrbitalFT t U φ η E) (𝓝[>] 0)
      (𝓝 ((φ ⬝ᵥ (sigmaC t U E *ᵥ φ) : ℝ) : ℂ)) := by
  simp only [dotProduct, Matrix.mulVec, ofReal_sum, ofReal_mul]
  exact tendsto_finset_sum _ fun i _ => tendsto_const_nhds.mul
    (tendsto_finset_sum _ fun j _ => (sigmaC_eq_limit t U E h1 h2 i j).mul tendsto_const_nhds)

/-- **Plug-in form.** The removal and addition self-energies `sigBB`, `sigAA`
entering `qp_removal` / `qp_addition` are the `η → 0⁺` limits of the orbital
matrix elements of the damped transform of `i G0 W_c` (off the two poles). -/
theorem sigBB_sigAA_eq_limit (t U E : ℝ) (h1 : E ≠ epsB t U - hRPA t U)
    (h2 : E ≠ epsA t U + hRPA t U) :
    Tendsto (fun η => sigmaOrbitalFT t U phiB η E) (𝓝[>] 0) (𝓝 (sigBB t U E : ℂ)) ∧
      Tendsto (fun η => sigmaOrbitalFT t U phiA η E) (𝓝[>] 0) (𝓝 (sigAA t U E : ℂ)) := by
  obtain ⟨hB, hA, -, -⟩ := sigmaC_orbital t U E
  exact ⟨hB ▸ sigmaOrbitalFT_limit t U phiB E h1 h2, hA ▸ sigmaOrbitalFT_limit t U phiA E h1 h2⟩

/-- The time-domain `W_c` transforms to the RPA `Wc` proved in `HubbardDimer.lean`. -/
theorem WcTime_limit {t U ω : ℝ} (ht : 0 < t) (hU : 0 ≤ U) (h1 : ω ≠ hRPA t U)
    (h2 : ω ≠ -hRPA t U) (i j : Fin 2) :
    Tendsto (fun η => ftDamped η (fun τ => WcTime (resW t U) (hRPA t U) τ i j) ω) (𝓝[>] 0)
      (𝓝 ((Wc t U ω i j : ℝ) : ℂ)) := by
  rw [WcTime_eq]
  convert ftDamped_twoSided_limit _ _ ω ?_ ?_ using 2
  · rw [Wc_single_pole ht hU h1 h2]
    simp only [Matrix.of_apply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [negI_mul_I_div]
    rw [show -I * ((resW t U i j : ℝ) : ℂ) * (-I / ((ω : ℂ) - ((-hRPA t U : ℝ) : ℂ))) =
        -(I * ((resW t U i j : ℝ) : ℂ) * (-I / ((ω : ℂ) - ((-hRPA t U : ℝ) : ℂ)))) by ring,
      I_mul_negI_div]
    push_cast; ring
  · simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p rfl _; exact sub_ne_zero.mpr h1
  · simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p rfl _; intro h; apply h2; dsimp only at h; linarith

/-- The time-domain G0 transforms to `Σ_k φ_k φ_k^T / (ω - ε_k)`. -/
theorem G0time_limit (orbs : List Orb) (ω : ℝ) (hoff : ∀ o ∈ orbs, ω - o.2.1 ≠ 0) (i j : Fin 2) :
    Tendsto (fun η => ftDamped η (fun τ => G0time orbs τ i j) ω) (𝓝[>] 0)
      (𝓝 (((orbs.map fun o => o.1 i * o.1 j / (ω - o.2.1)).sum : ℝ) : ℂ)) := by
  rw [G0time_eq]
  convert ftDamped_twoSided_limit _ _ ω ?_ ?_ using 2
  · rw [List.map_map, List.map_map, list_sum_map_add, ofReal_list_sum]
    congr 1; apply List.map_congr_left; intro o _
    simp only [Function.comp, negI_mul_I_div, I_mul_negI_div]
    push_cast; ring
  · simp only [List.mem_map]; rintro p ⟨o, ho, rfl⟩ _; exact hoff o ho
  · simp only [List.mem_map]; rintro p ⟨o, ho, rfl⟩ _; exact hoff o ho

/-- The frequency-domain HF Green's function of the dimer. -/
noncomputable def g0HF (t U ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => ((dimerOrbs t U).map fun o => o.1 i * o.1 j / (ω - o.2.1)).sum

/-- ... and it is the resolvent of the HF Fock matrix: `(ω - F) G0(ω) = 1`. -/
theorem g0HF_resolvent {t U ω : ℝ} (h1 : ω ≠ epsB t U) (h2 : ω ≠ epsA t U) :
    (ω • (1 : Matrix (Fin 2) (Fin 2) ℝ) - fock t U) * g0HF t U ω = 1 := by
  have e1 : ω - epsB t U ≠ 0 := sub_ne_zero.mpr h1
  have e2 : ω - epsA t U ≠ 0 := sub_ne_zero.mpr h2
  have hs := s2_mul
  rw [fock_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g0HF, dimerOrbs, phiB, phiA, h0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
      Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply] <;>
    field_simp <;> simp only [epsA, epsB] at * <;> ring_nf <;> simp only [s2_sq] <;> ring_nf

end GW.Endpoint.HubbardDimer
