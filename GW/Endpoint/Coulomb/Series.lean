/-
G2-coulomb (1/n): the two expansions behind the Taylor remainders.

With `z = 1 + α + β`, `α² ≤ 4β`, `β ≤ t²`, `0 ≤ t < 1` (for `z = |c+y|²/|c|²`,
`α = 2⟨c,y⟩/|c|²`, `β = |y|²/|c|²`, `t ≥ |y|/|c|`):

* `cW α β n` (Chebyshev-type, `W₀ = 1`, `W₁ = -α`, `W_{n+2} = -α W_{n+1} - β W_n`) are the
  graded pieces of `1/z`; `|W_n| ≤ (n+1) tⁿ` (`cW_bound`) and
  `|1/z - Σ_{n≤N} W_n| ≤ φ_N(t)` (`cW_taylor`);
* `lV α β n` (Legendre-type, `(n+2) V_{n+2} = -(2n+3)(α/2) V_{n+1} - (n+1) β V_n`) are the
  graded pieces of `z^{-1/2}`; `|V_n| ≤ (n+1) tⁿ` (`lV_bound`) and
  `|z^{-1/2} - Σ_{n≤N} V_n| ≤ φ_N(t)` (`lV_taylor`, by the fundamental theorem of calculus
  along `λ ↦ (λα, λ²β)`),

where `φ_N(t) = ((N+2) t^{N+1} + (N+1) t^{N+2}) / (1-t)²`.
-/
import Mathlib

namespace GW.Endpoint.Coulomb

open Finset

/-- The remainder bound `φ_N(t)`. -/
noncomputable def phiB (N : ℕ) (t : ℝ) : ℝ :=
  ((N + 2) * t ^ (N + 1) + (N + 1) * t ^ (N + 2)) / (1 - t) ^ 2

/-- Chebyshev-type sequence (graded pieces of `1/(1+α+β)`). -/
def cW (α β : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => -α
  | (n + 2) => -α * cW α β (n + 1) - β * cW α β n

/-- Legendre-type sequence (graded pieces of `(1+α+β)^{-1/2}`). -/
noncomputable def lV (α β : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => -α / 2
  | (n + 2) => (-(2 * n + 3) * (α / 2) * lV α β (n + 1) - (n + 1) * β * lV α β n) / (n + 2)

theorem cW_inv (α β : ℝ) (n : ℕ) :
    cW α β (n + 1) ^ 2 + α * cW α β (n + 1) * cW α β n + β * cW α β n ^ 2 = β ^ (n + 1) := by
  induction n with
  | zero => simp [cW]; ring
  | succ n ih =>
    have h2 : cW α β (n + 1 + 1) = -α * cW α β (n + 1) - β * cW α β n := rfl
    rw [h2, pow_succ β (n + 1), ← ih]; ring

theorem lV_inv (α β : ℝ) (hβ : 0 ≤ β) (hα : α ^ 2 ≤ 4 * β) (n : ℕ) :
    lV α β (n + 1) ^ 2 + α * lV α β (n + 1) * lV α β n + β * lV α β n ^ 2 ≤ β ^ (n + 1) := by
  induction n with
  | zero => simp [lV]; nlinarith
  | succ n ih =>
    have h2 : lV α β (n + 2) =
        (-(2 * n + 3) * (α / 2) * lV α β (n + 1) - (n + 1) * β * lV α β n) / (n + 2) := rfl
    set a := lV α β (n + 1)
    set b := lV α β n
    have hn : (0 : ℝ) < n + 2 := by positivity
    have key : (lV α β (n + 2)) ^ 2 + α * lV α β (n + 2) * a + β * a ^ 2 =
        β * (a ^ 2 + α * a * b + β * b ^ 2) - (2 * n + 3) * (a * α + 2 * b * β) ^ 2 / (4 * (n + 2) ^ 2) := by
      rw [h2]; field_simp; ring
    rw [key, pow_succ β (n + 1)]
    have : 0 ≤ (2 * (n : ℝ) + 3) * (a * α + 2 * b * β) ^ 2 / (4 * (n + 2) ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_left ih hβ
    push_cast at *
    nlinarith

/-- The common step: from the quadratic invariant to linear growth. -/
theorem step_bound {α β t x y : ℝ} (ht : 0 ≤ t) (hβt : β ≤ t ^ 2) (hα : α ^ 2 ≤ 4 * β) (n : ℕ)
    (hinv : x ^ 2 + α * x * y + β * y ^ 2 ≤ β ^ (n + 1)) (hy : |y| ≤ (n + 1) * t ^ n) :
    |x| ≤ (n + 2) * t ^ (n + 1) := by
  have hβ : 0 ≤ β := by nlinarith [sq_nonneg α]
  have h1 : (x + α / 2 * y) ^ 2 ≤ (t ^ (n + 1)) ^ 2 := by
    have : (x + α / 2 * y) ^ 2 = x ^ 2 + α * x * y + β * y ^ 2 - (β - α ^ 2 / 4) * y ^ 2 := by ring
    rw [this]
    have h3 : 0 ≤ (β - α ^ 2 / 4) * y ^ 2 := mul_nonneg (by linarith) (sq_nonneg y)
    have h4 : β ^ (n + 1) ≤ (t ^ 2) ^ (n + 1) := pow_le_pow_left₀ hβ hβt _
    calc _ ≤ β ^ (n + 1) := by linarith
      _ ≤ (t ^ 2) ^ (n + 1) := h4
      _ = (t ^ (n + 1)) ^ 2 := by ring
  have h2 : |x + α / 2 * y| ≤ t ^ (n + 1) := by
    rw [← abs_of_nonneg (pow_nonneg ht (n + 1))]; exact sq_le_sq.mp h1
  have hα2 : |α / 2| ≤ t := by
    rw [← abs_of_nonneg ht]; apply sq_le_sq.mp; nlinarith [sq_abs α]
  have h5 : |α / 2 * y| ≤ t * ((n + 1) * t ^ n) := by
    rw [abs_mul]; exact mul_le_mul hα2 hy (abs_nonneg _) ht
  calc |x| = |(x + α / 2 * y) - α / 2 * y| := by ring_nf
    _ ≤ |x + α / 2 * y| + |α / 2 * y| := abs_sub _ _
    _ ≤ t ^ (n + 1) + t * ((n + 1) * t ^ n) := add_le_add h2 h5
    _ = (n + 2) * t ^ (n + 1) := by ring

theorem cW_bound {α β t : ℝ} (ht : 0 ≤ t) (hβt : β ≤ t ^ 2) (hα : α ^ 2 ≤ 4 * β) :
    ∀ n, |cW α β n| ≤ (n + 1) * t ^ n := by
  intro n
  induction n with
  | zero => simp [cW]
  | succ n ih =>
    have := step_bound ht hβt hα n (le_of_eq (cW_inv α β n)) ih
    push_cast; linarith

theorem lV_bound {α β t : ℝ} (ht : 0 ≤ t) (hβt : β ≤ t ^ 2) (hα : α ^ 2 ≤ 4 * β) :
    ∀ n, |lV α β n| ≤ (n + 1) * t ^ n := by
  have hβ : 0 ≤ β := by nlinarith [sq_nonneg α]
  intro n
  induction n with
  | zero => simp [lV]
  | succ n ih =>
    have := step_bound ht hβt hα n (lV_inv α β hβ hα n) ih
    push_cast; linarith

/-- `(1+α+β) Σ_{n≤N} W_n = 1 - W_{N+1} + β W_N`. -/
theorem cW_sum (α β : ℝ) (N : ℕ) :
    (1 + α + β) * ∑ n ∈ range (N + 1), cW α β n = 1 - cW α β (N + 1) + β * cW α β N := by
  induction N with
  | zero => simp [cW]
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih]
    have h2 : cW α β (N + 2) = -α * cW α β (N + 1) - β * cW α β N := rfl
    rw [h2]; ring

/-- `z ≥ (1-t)²`. -/
theorem z_lower {α β t : ℝ} (ht : 0 ≤ t) (hβt : β ≤ t ^ 2) (hα : α ^ 2 ≤ 4 * β) :
    (1 - Real.sqrt β) ^ 2 ≤ 1 + α + β := by
  have hβ : 0 ≤ β := by nlinarith [sq_nonneg α]
  have hs := Real.sq_sqrt hβ
  have : |α| ≤ 2 * Real.sqrt β := by
    rw [← abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt β)]
    apply sq_le_sq.mp; nlinarith
  have := neg_abs_le α
  nlinarith

theorem phiB_mono {N : ℕ} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) : phiB N s ≤ phiB N t := by
  unfold phiB
  have ht0 : 0 ≤ t := le_trans hs hst
  apply div_le_div₀ (add_nonneg (mul_nonneg (by positivity) (pow_nonneg ht0 _))
    (mul_nonneg (by positivity) (pow_nonneg ht0 _))) _ (by nlinarith) _
  · gcongr
  · have : 0 ≤ 1 - t := by linarith
    gcongr

/-- **Taylor remainder of `1/z`.** -/
theorem cW_taylor {α β t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hβt : β ≤ t ^ 2) (hα : α ^ 2 ≤ 4 * β) (N : ℕ) :
    |1 / (1 + α + β) - ∑ n ∈ range (N + 1), cW α β n| ≤ phiB N t := by
  have hβ : 0 ≤ β := by nlinarith [sq_nonneg α]
  set s := Real.sqrt β
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = β := Real.sq_sqrt hβ
  have hst : s ≤ t := by rw [← abs_of_nonneg hs0, ← abs_of_nonneg ht]; exact sq_le_sq.mp (by linarith)
  have hs1 : s < 1 := lt_of_le_of_lt hst ht1
  have hz := z_lower ht hβt hα
  have hz0 : 0 < 1 + α + β := lt_of_lt_of_le (by nlinarith) hz
  have hsum := cW_sum α β N
  have e : 1 / (1 + α + β) - ∑ n ∈ range (N + 1), cW α β n =
      (cW α β (N + 1) - β * cW α β N) / (1 + α + β) := by
    field_simp; linarith
  rw [e, abs_div, abs_of_pos hz0]
  have b1 := cW_bound hs0 (le_of_eq hss.symm) hα (N + 1)
  have b0 := cW_bound hs0 (le_of_eq hss.symm) hα N
  have hnum : |cW α β (N + 1) - β * cW α β N| ≤ (N + 2) * s ^ (N + 1) + (N + 1) * s ^ (N + 2) := by
    calc _ ≤ |cW α β (N + 1)| + |β * cW α β N| := abs_sub _ _
      _ ≤ ((N + 1 : ℕ) + 1) * s ^ (N + 1) + s ^ 2 * ((N + 1) * s ^ N) := by
          apply add_le_add b1; rw [abs_mul, abs_of_nonneg hβ]
          calc β * |cW α β N| ≤ β * ((N + 1) * s ^ N) := mul_le_mul_of_nonneg_left b0 hβ
            _ = s ^ 2 * ((N + 1) * s ^ N) := by rw [hss]
      _ = _ := by push_cast; ring
  calc _ ≤ ((N + 2) * s ^ (N + 1) + (N + 1) * s ^ (N + 2)) / (1 - s) ^ 2 := by
        apply div_le_div₀ (by positivity) hnum (by nlinarith) hz
    _ = phiB N s := rfl
    _ ≤ phiB N t := phiB_mono hs0 hst ht1

/-! ### The Legendre-type remainder -/

/-- `2 z S' + z' S = 2 (N+1) λ^N (λ β V_N - V_{N+1})` for the λ-scaled partial sum. -/
theorem lV_ode (α β l : ℝ) (N : ℕ) :
    (α + 2 * l * β) * (∑ n ∈ range (N + 1), l ^ n * lV α β n) +
      2 * (1 + l * α + l ^ 2 * β) * (∑ n ∈ range (N + 1), (n : ℝ) * l ^ (n - 1) * lV α β n) =
    2 * (N + 1) * l ^ N * (l * β * lV α β N - lV α β (N + 1)) := by
  induction N with
  | zero => simp [lV]; ring
  | succ N ih =>
    rw [sum_range_succ (fun n => l ^ n * lV α β n), sum_range_succ (fun n => (n : ℝ) * l ^ (n - 1) * lV α β n),
      Nat.add_sub_cancel]
    have hn : (N : ℝ) + 2 ≠ 0 := by positivity
    have hv2 : ((N : ℝ) + 2) * lV α β (N + 1 + 1) =
        -(2 * N + 3) * (α / 2) * lV α β (N + 1) - (N + 1) * β * lV α β N := by
      show ((N : ℝ) + 2) * ((-(2 * N + 3) * (α / 2) * lV α β (N + 1) - (N + 1) * β * lV α β N) / (N + 2)) = _
      field_simp; ring
    push_cast
    linear_combination ih + 2 * l ^ (N + 1) * hv2

theorem hasDerivAt_psum (α β : ℝ) (N : ℕ) (l : ℝ) :
    HasDerivAt (fun l => ∑ n ∈ range (N + 1), l ^ n * lV α β n)
      (∑ n ∈ range (N + 1), (n : ℝ) * l ^ (n - 1) * lV α β n) l := by
  apply HasDerivAt.sum
  intro n _
  have := (hasDerivAt_pow n l).mul_const (lV α β n)
  simpa using this

/-- **Taylor remainder of `z^{-1/2}`.** -/
theorem lV_taylor {α β t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hβt : β ≤ t ^ 2) (hα : α ^ 2 ≤ 4 * β) (N : ℕ) :
    |1 / Real.sqrt (1 + α + β) - ∑ n ∈ range (N + 1), lV α β n| ≤ phiB N t := by
  have hβ : 0 ≤ β := by nlinarith [sq_nonneg α]
  set s := Real.sqrt β
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = β := Real.sq_sqrt hβ
  have hst : s ≤ t := by rw [← abs_of_nonneg hs0, ← abs_of_nonneg ht]; exact sq_le_sq.mp (by linarith)
  have hs1 : s < 1 := lt_of_le_of_lt hst ht1
  -- along the ray: z(l) = 1 + l α + l² β ≥ (1 - l s)² ≥ (1 - s)² > 0 for l ∈ [0,1]
  set z : ℝ → ℝ := fun l => 1 + l * α + l ^ 2 * β
  have hzl : ∀ l ∈ Set.Icc (0 : ℝ) 1, (1 - s) ^ 2 ≤ z l := by
    intro l ⟨h0, h1⟩
    have hls : l * s ≤ s := by nlinarith
    have := z_lower (α := l * α) (β := l ^ 2 * β) (t := l * s) (by positivity)
      (by rw [mul_pow, hss]) (by nlinarith [sq_nonneg l])
    have hsq : Real.sqrt (l ^ 2 * β) = l * s := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq h0]
    rw [hsq] at this
    have : (1 - s) ^ 2 ≤ (1 - l * s) ^ 2 := by nlinarith
    simp only [z]; linarith
  have hzpos : ∀ l ∈ Set.Icc (0 : ℝ) 1, 0 < z l := fun l hl =>
    lt_of_lt_of_le (by nlinarith) (hzl l hl)
  set S : ℝ → ℝ := fun l => ∑ n ∈ range (N + 1), l ^ n * lV α β n
  set S' : ℝ → ℝ := fun l => ∑ n ∈ range (N + 1), (n : ℝ) * l ^ (n - 1) * lV α β n
  set R : ℝ → ℝ := fun l => 2 * (N + 1) * l ^ N * (l * β * lV α β N - lV α β (N + 1))
  -- derivative of √z · S
  have hd : ∀ l ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun l => Real.sqrt (z l) * S l)
      (R l / (2 * Real.sqrt (z l))) l := by
    intro l hl
    rw [Set.uIcc_of_le zero_le_one] at hl
    have hz : HasDerivAt z (α + 2 * l * β) l := by
      have := ((hasDerivAt_id l).mul_const α).const_add 1 |>.add ((hasDerivAt_pow 2 l).mul_const β)
      convert this using 1; simp [z]
    have hsq := hz.sqrt (ne_of_gt (hzpos l hl))
    have := hsq.mul (hasDerivAt_psum α β N l)
    refine this.congr_deriv ?_
    have hr := lV_ode α β l N
    have hsz : Real.sqrt (z l) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hzpos l hl))
    have hsz2 : Real.sqrt (z l) * Real.sqrt (z l) = z l := Real.mul_self_sqrt (le_of_lt (hzpos l hl))
    have e : (α + 2 * l * β) / (2 * Real.sqrt (z l)) * S l + Real.sqrt (z l) * S' l =
        ((α + 2 * l * β) * S l + 2 * (Real.sqrt (z l) * Real.sqrt (z l)) * S' l) / (2 * Real.sqrt (z l)) := by
      field_simp; ring
    show (α + 2 * l * β) / (2 * Real.sqrt (z l)) * S l + Real.sqrt (z l) * S' l = R l / (2 * Real.sqrt (z l))
    rw [e, hsz2]
    simp only [z, R, S, S']
    rw [hr]
  have hcont : ContinuousOn (fun l => R l / (2 * Real.sqrt (z l))) (Set.uIcc 0 1) := by
    apply ContinuousOn.div
    · exact (by fun_prop : Continuous R).continuousOn
    · exact (by fun_prop : Continuous fun l => 2 * Real.sqrt (z l)).continuousOn
    · intro l hl; rw [Set.uIcc_of_le zero_le_one] at hl
      exact ne_of_gt (by have := Real.sqrt_pos.mpr (hzpos l hl); linarith)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable)
  have h0 : Real.sqrt (z 0) * S 0 = 1 := by
    simp only [z, S]; rw [sum_range_succ']; simp [lV]
  have h1 : Real.sqrt (z 1) * S 1 = Real.sqrt (1 + α + β) * ∑ n ∈ range (N + 1), lV α β n := by
    simp [z, S]
  rw [h0, h1] at hftc
  -- bound the integrand
  set K := (N + 1) * ((N + 2) * s ^ (N + 1) + (N + 1) * s ^ (N + 2)) / (1 - s)
  have hbd : ∀ l ∈ Set.uIoc (0 : ℝ) 1, ‖R l / (2 * Real.sqrt (z l))‖ ≤ K * l ^ N := by
    intro l hl
    rw [Set.uIoc_of_le zero_le_one] at hl
    have hl' : l ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hl.1, hl.2⟩
    have hsz : 1 - s ≤ Real.sqrt (z l) := by
      rw [show 1 - s = Real.sqrt ((1 - s) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
      exact Real.sqrt_le_sqrt (hzl l hl')
    have b1 := lV_bound hs0 (le_of_eq hss.symm) hα (N + 1)
    have b0 := lV_bound hs0 (le_of_eq hss.symm) hα N
    have hnum : |l * β * lV α β N - lV α β (N + 1)| ≤ (N + 2) * s ^ (N + 1) + (N + 1) * s ^ (N + 2) := by
      calc _ ≤ |l * β * lV α β N| + |lV α β (N + 1)| := abs_sub _ _
        _ ≤ s ^ 2 * ((N + 1) * s ^ N) + ((N + 1 : ℕ) + 1) * s ^ (N + 1) := by
            apply add_le_add _ b1
            rw [abs_mul, abs_mul, abs_of_nonneg hl'.1, abs_of_nonneg hβ]
            calc l * β * |lV α β N| ≤ 1 * β * ((N + 1) * s ^ N) := by
                  apply mul_le_mul (mul_le_mul_of_nonneg_right hl'.2 hβ) b0
                    (abs_nonneg _) (by positivity)
              _ = s ^ 2 * ((N + 1) * s ^ N) := by rw [hss]; ring
        _ = _ := by push_cast; ring
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (show (0:ℝ) < 2 * Real.sqrt (z l) by
      have := Real.sqrt_pos.mpr (hzpos l hl'); linarith)]
    simp only [R]
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (N + 1)),
      abs_of_nonneg (pow_nonneg hl'.1 N)]
    have hden : 0 < 2 * (1 - s) := by linarith
    calc 2 * (↑N + 1) * l ^ N * |l * β * lV α β N - lV α β (N + 1)| / (2 * Real.sqrt (z l))
        ≤ 2 * (↑N + 1) * l ^ N * ((N + 2) * s ^ (N + 1) + (N + 1) * s ^ (N + 2)) / (2 * (1 - s)) := by
          have hlN := pow_nonneg hl'.1 N
          apply div_le_div₀ (mul_nonneg (by positivity) (le_trans (abs_nonneg _) hnum)) _ hden (by linarith)
          exact mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = K * l ^ N := by
          have hs1' : 1 - s ≠ 0 := by linarith
          simp only [K]; field_simp; ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc hbd)
    ((by fun_prop : Continuous fun l : ℝ => K * l ^ N).intervalIntegrable (μ := MeasureTheory.volume) 0 1)
  have hK0 : 0 ≤ K := by
    have : 0 < 1 - s := by linarith
    simp only [K]; positivity
  have hKint : ∫ l in (0 : ℝ)..1, K * l ^ N = K / (N + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]; simp; field_simp
  rw [hKint, hftc, Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ K / (N + 1) by positivity)] at hint
  -- |√z S - 1| ≤ K/(N+1)  ⇒  |1/√z - S| ≤ K/((N+1)(1-s))
  have hz := z_lower ht hβt hα
  have hsqz : 1 - s ≤ Real.sqrt (1 + α + β) := by
    rw [show 1 - s = Real.sqrt ((1 - s) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt hz
  have hsq0 : 0 < Real.sqrt (1 + α + β) := lt_of_lt_of_le (by linarith) hsqz
  have e : 1 / Real.sqrt (1 + α + β) - ∑ n ∈ range (N + 1), lV α β n =
      -(Real.sqrt (1 + α + β) * ∑ n ∈ range (N + 1), lV α β n - 1) / Real.sqrt (1 + α + β) := by
    field_simp
  rw [e, abs_div, abs_neg, abs_of_pos hsq0]
  calc _ ≤ K / (N + 1) / (1 - s) := div_le_div₀ (by positivity) hint (by linarith) hsqz
    _ = phiB N s := by
        have hs1' : 1 - s ≠ 0 := by linarith
        simp only [K, phiB]; field_simp; ring
    _ ≤ phiB N t := phiB_mono hs0 hst ht1

end GW.Endpoint.Coulomb
