/-
G2-coulomb (2/n): integration over the standard triangle `T2 = {s ≥ 0, s₁ + s₂ ≤ 1}`.

* `integral_T2_monomial`: `∫_{T2} s₁^a s₂^b = a! b! / (a+b+2)!` (Fubini + Beta recursion);
* `integral_T2_split`: the 4-way midpoint subdivision
  `∫_{T2} g = ¼ Σ_c ∫_{T2} g ∘ φ_c` (`φ₀ s = s/2`, `φ₁ s = (½,0) + s/2`, `φ₂ s = (0,½) + s/2`,
  `φ₃ s = (½,½) - s/2`), for `g` integrable on `T2`;
* `IsPoly d g` (`g` is a real polynomial of total degree `≤ d` in `(s₁, s₂)`) and
  `rule_exact`: a cubature rule whose exactness on all monomials of degree `≤ d` is checked
  by `ruleOK` (exact rationals, kernel) integrates every `IsPoly d` function exactly.
-/
import Mathlib
import GW.Endpoint.Coulomb.CheckDefs

namespace GW.Endpoint.Coulomb

open MeasureTheory Set Finset

/-- The standard triangle. -/
def T2 : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

theorem T2_closed : IsClosed T2 := by
  apply IsClosed.inter (isClosed_le continuous_const continuous_fst)
  exact IsClosed.inter (isClosed_le continuous_const continuous_snd)
    (isClosed_le (continuous_fst.add continuous_snd) continuous_const)

theorem T2_sub : T2 ⊆ Icc (0 : ℝ × ℝ) 1 := by
  intro p ⟨h1, h2, h3⟩
  exact ⟨⟨h1, h2⟩, ⟨by show p.1 ≤ 1; linarith, by show p.2 ≤ 1; linarith⟩⟩

theorem T2_compact : IsCompact T2 := isCompact_Icc.of_isClosed_subset T2_closed T2_sub

theorem T2_meas : MeasurableSet T2 := T2_closed.measurableSet

theorem integrableOn_T2 {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g T2) : IntegrableOn g T2 :=
  hg.integrableOn_compact T2_compact

/-! ### Beta integrals and the monomial moments -/

theorem beta_nat (a c : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ c = (a.factorial * c.factorial : ℝ) / (a + c + 1).factorial := by
  induction c generalizing a with
  | zero =>
    simp only [pow_zero, mul_one, integral_pow]
    rw [Nat.add_zero, Nat.factorial_succ]; push_cast
    field_simp
  | succ c ih =>
    have e : ∀ x : ℝ, x ^ a * (1 - x) ^ (c + 1) = x ^ a * (1 - x) ^ c - x ^ (a + 1) * (1 - x) ^ c := by
      intro x; ring
    simp_rw [e]
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), ih a, ih (a + 1)]
    simp only [show a + 1 + c + 1 = a + c + 1 + 1 by ring, show a + (c + 1) + 1 = a + c + 1 + 1 by ring]
    rw [Nat.factorial_succ (a + c + 1), Nat.factorial_succ a, Nat.factorial_succ c]
    push_cast
    have h1 : ((a + c + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- Fubini on `T2`. -/
theorem integral_T2_iter {g : ℝ × ℝ → ℝ} (hg : IntegrableOn g T2) :
    ∫ p in T2, g p = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 - x), g (x, y) := by
  rw [← integral_indicator T2_meas]
  have hi : Integrable (T2.indicator g) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hg.integrable_indicator T2_meas
  rw [Measure.volume_eq_prod, integral_prod _ hi]
  have hx : ∀ x : ℝ, ∫ y, T2.indicator g (x, y) =
      (Icc (0 : ℝ) 1).indicator (fun x => ∫ y in (0 : ℝ)..(1 - x), g (x, y)) x := by
    intro x
    by_cases h : x ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem h]
      have : (fun y => T2.indicator g (x, y)) = (Icc (0 : ℝ) (1 - x)).indicator (fun y => g (x, y)) := by
        funext y
        by_cases hy : y ∈ Icc (0 : ℝ) (1 - x)
        · rw [indicator_of_mem hy, indicator_of_mem]
          exact ⟨h.1, hy.1, by linarith [hy.2]⟩
        · rw [indicator_of_not_mem hy, indicator_of_not_mem]
          intro ⟨_, h2, h3⟩; exact hy ⟨h2, by linarith⟩
      rw [this, integral_indicator measurableSet_Icc, intervalIntegral.integral_of_le (by linarith [h.2]),
        integral_Icc_eq_integral_Ioc]
    · rw [indicator_of_not_mem h]
      have : (fun y => T2.indicator g (x, y)) = fun _ => 0 := by
        funext y
        rw [indicator_of_not_mem]
        intro ⟨h1, h2, h3⟩; exact h ⟨h1, by linarith⟩
      rw [this, integral_zero]
  simp_rw [hx]
  rw [integral_indicator measurableSet_Icc, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc]

/-- **Monomial moments of `T2`.** -/
theorem integral_T2_monomial (a b : ℕ) :
    ∫ p in T2, p.1 ^ a * p.2 ^ b = (a.factorial * b.factorial : ℝ) / (a + b + 2).factorial := by
  rw [integral_T2_iter (integrableOn_T2 (by fun_prop))]
  have : ∀ x : ℝ, ∫ y in (0 : ℝ)..(1 - x), x ^ a * y ^ b = x ^ a * (1 - x) ^ (b + 1) / (b + 1) := by
    intro x
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp; ring
  simp_rw [this]
  rw [intervalIntegral.integral_div, beta_nat]
  rw [show a + (b + 1) + 1 = a + b + 2 by ring, Nat.factorial_succ b]
  push_cast
  have : ((a + b + 2).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-! ### The 4-way subdivision -/

/-- The four child maps. -/
noncomputable def phiC : Fin 4 → ℝ × ℝ → ℝ × ℝ
  | 0 => fun s => (s.1 / 2, s.2 / 2)
  | 1 => fun s => (1 / 2 + s.1 / 2, s.2 / 2)
  | 2 => fun s => (s.1 / 2, 1 / 2 + s.2 / 2)
  | 3 => fun s => (1 / 2 - s.1 / 2, 1 / 2 - s.2 / 2)

/-- The images of the child maps. -/
def SC : Fin 4 → Set (ℝ × ℝ)
  | 0 => {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1 / 2}
  | 1 => {p | 1 / 2 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
  | 2 => {p | 0 ≤ p.1 ∧ 1 / 2 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
  | 3 => {p | p.1 ≤ 1 / 2 ∧ p.2 ≤ 1 / 2 ∧ 1 / 2 ≤ p.1 + p.2}

theorem SC_closed (c : Fin 4) : IsClosed (SC c) := by
  have hf : Continuous fun p : ℝ × ℝ => p.1 := continuous_fst
  have hs : Continuous fun p : ℝ × ℝ => p.2 := continuous_snd
  have ha : Continuous fun p : ℝ × ℝ => p.1 + p.2 := continuous_fst.add continuous_snd
  fin_cases c <;> simp only [SC]
  · exact (isClosed_le continuous_const hf).inter ((isClosed_le continuous_const hs).inter
      (isClosed_le ha continuous_const))
  · exact (isClosed_le continuous_const hf).inter ((isClosed_le continuous_const hs).inter
      (isClosed_le ha continuous_const))
  · exact (isClosed_le continuous_const hf).inter ((isClosed_le continuous_const hs).inter
      (isClosed_le ha continuous_const))
  · exact (isClosed_le hf continuous_const).inter ((isClosed_le hs continuous_const).inter
      (isClosed_le continuous_const ha))

theorem SC_meas (c : Fin 4) : MeasurableSet (SC c) := (SC_closed c).measurableSet

/-- `σ ∈ T2 ↔ φ_c σ ∈ SC c`. -/
theorem mem_SC_iff (c : Fin 4) (s : ℝ × ℝ) : phiC c s ∈ SC c ↔ s ∈ T2 := by
  fin_cases c <;> simp only [phiC, SC, T2, mem_setOf_eq] <;> constructor <;>
    (intro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith)

/-- Change of variables through a child map: `∫_{T2} g ∘ φ_c = 4 ∫_{SC c} g`. -/
theorem integral_child (g : ℝ × ℝ → ℝ) (c : Fin 4) :
    ∫ s in T2, g (phiC c s) = 4 * ∫ p in SC c, g p := by
  -- φ_c s = v + r • s
  obtain ⟨v, r, hr, hφ⟩ : ∃ v : ℝ × ℝ, ∃ r : ℝ, |r| = 1 / 2 ∧ ∀ s, phiC c s = v + r • s := by
    fin_cases c
    · exact ⟨0, 1 / 2, by norm_num, fun s => by simp [phiC, Prod.ext_iff]; constructor <;> ring⟩
    · exact ⟨(1 / 2, 0), 1 / 2, by norm_num, fun s => by simp [phiC, Prod.ext_iff]; constructor <;> ring⟩
    · exact ⟨(0, 1 / 2), 1 / 2, by norm_num, fun s => by simp [phiC, Prod.ext_iff]; constructor <;> ring⟩
    · exact ⟨(1 / 2, 1 / 2), -1 / 2, by norm_num, fun s => by simp [phiC, Prod.ext_iff]; constructor <;> ring⟩
  rw [← integral_indicator T2_meas, ← integral_indicator (SC_meas c)]
  have e : (T2.indicator fun s => g (phiC c s)) = fun s => (SC c).indicator g (v + r • s) := by
    funext s
    by_cases h : s ∈ T2
    · rw [indicator_of_mem h, indicator_of_mem, hφ]
      rw [← hφ]; exact (mem_SC_iff c s).mpr h
    · rw [indicator_of_not_mem h, indicator_of_not_mem]
      rw [← hφ]; exact fun h' => h ((mem_SC_iff c s).mp h')
  rw [e]
  have := Measure.integral_comp_smul (μ := (volume : Measure (ℝ × ℝ)))
    (fun x => (SC c).indicator g (v + x)) r
  simp only at this
  rw [this, integral_add_left_eq_self (fun x => (SC c).indicator g x) v]
  simp only [Module.finrank_prod, Module.finrank_self, abs_inv, abs_pow, hr, smul_eq_mul]
  norm_num

theorem null_fst (a : ℝ) : volume {p : ℝ × ℝ | p.1 = a} = 0 := by
  have : {p : ℝ × ℝ | p.1 = a} = {a} ×ˢ (Set.univ : Set ℝ) := by ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod]; simp

theorem null_snd (a : ℝ) : volume {p : ℝ × ℝ | p.2 = a} = 0 := by
  have : {p : ℝ × ℝ | p.2 = a} = (Set.univ : Set ℝ) ×ˢ {a} := by ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod]; simp

theorem null_sum (a : ℝ) : volume {p : ℝ × ℝ | p.1 + p.2 = a} = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_apply
    (measurableSet_eq_fun (measurable_fst.add measurable_snd) measurable_const)]
  have : ∀ x : ℝ, Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 + p.2 = a} = {a - x} := by
    intro x; ext y; simp; constructor <;> intro h <;> linarith
  simp [this]

theorem aedisj_of_sub {s t u : Set (ℝ × ℝ)} (h : s ∩ t ⊆ u) (hu : volume u = 0) : AEDisjoint volume s t :=
  measure_mono_null h hu

theorem T2_cover : ∀ s ∈ T2, ∃ c : Fin 4, s ∈ SC c := by
  intro p ⟨h1, h2, h3⟩
  by_cases a : 1 / 2 ≤ p.1
  · exact ⟨1, a, h2, h3⟩
  by_cases b : 1 / 2 ≤ p.2
  · exact ⟨2, h1, b, h3⟩
  by_cases c : p.1 + p.2 ≤ 1 / 2
  · exact ⟨0, h1, h2, c⟩
  exact ⟨3, by show p.1 ≤ 1 / 2; linarith, by show p.2 ≤ 1 / 2; linarith, by show 1 / 2 ≤ p.1 + p.2; linarith⟩

/-- The inverse child maps. -/
theorem SC_surj (c : Fin 4) : ∀ s ∈ SC c, ∃ s' ∈ T2, phiC c s' = s := by
  intro s hs
  fin_cases c
  · refine ⟨(2 * s.1, 2 * s.2), ?_, ?_⟩
    · have := (mem_SC_iff 0 (2 * s.1, 2 * s.2)).mp; apply this
      simp only [phiC]; convert hs using 1; ext <;> simp <;> ring
    · simp only [phiC]; ext <;> simp <;> ring
  · refine ⟨(2 * s.1 - 1, 2 * s.2), ?_, ?_⟩
    · apply (mem_SC_iff 1 _).mp
      simp only [phiC]; convert hs using 1; ext <;> simp <;> ring
    · simp only [phiC]; ext <;> simp <;> ring
  · refine ⟨(2 * s.1, 2 * s.2 - 1), ?_, ?_⟩
    · apply (mem_SC_iff 2 _).mp
      simp only [phiC]; convert hs using 1; ext <;> simp <;> ring
    · simp only [phiC]; ext <;> simp <;> ring
  · refine ⟨(1 - 2 * s.1, 1 - 2 * s.2), ?_, ?_⟩
    · apply (mem_SC_iff 3 _).mp
      simp only [phiC]; convert hs using 1; ext <;> simp <;> ring
    · simp only [phiC]; ext <;> simp <;> ring

/-- **The 4-way subdivision.** -/
theorem integral_T2_split {g : ℝ × ℝ → ℝ} (hg : IntegrableOn g T2) :
    ∫ s in T2, g s = (1 / 4) * ∑ c : Fin 4, ∫ s in T2, g (phiC c s) := by
  simp_rw [integral_child]
  rw [Fin.sum_univ_four]
  have hT : T2 = ((SC 0 ∪ SC 1) ∪ SC 2) ∪ SC 3 := by
    ext p; simp only [T2, SC, mem_union, mem_setOf_eq]
    constructor
    · intro ⟨h1, h2, h3⟩
      by_cases a : 1 / 2 ≤ p.1
      · left; left; right; exact ⟨a, h2, h3⟩
      by_cases b : 1 / 2 ≤ p.2
      · left; right; exact ⟨h1, b, h3⟩
      by_cases c : p.1 + p.2 ≤ 1 / 2
      · left; left; left; exact ⟨h1, h2, c⟩
      right; exact ⟨by linarith, by linarith, by linarith⟩
    · rintro (((⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) | ⟨h1, h2, h3⟩) | ⟨h1, h2, h3⟩) <;>
        refine ⟨?_, ?_, ?_⟩ <;> linarith
  have hsub : ∀ c, SC c ⊆ T2 := by
    intro c p hp
    fin_cases c <;> simp only [SC, T2, mem_setOf_eq] at hp ⊢ <;>
      (obtain ⟨h1, h2, h3⟩ := hp; refine ⟨?_, ?_, ?_⟩ <;> linarith)
  have hI : ∀ c, IntegrableOn g (SC c) := fun c => hg.mono_set (hsub c)
  have d01 : AEDisjoint volume (SC 0) (SC 1) :=
    aedisj_of_sub (u := {p | p.1 + p.2 = 1 / 2}) (fun p ⟨⟨_, _, h3⟩, ⟨h1', h2', _⟩⟩ => by
      simp only [mem_setOf_eq]; linarith) (null_sum _)
  have d02 : AEDisjoint volume (SC 0) (SC 2) :=
    aedisj_of_sub (u := {p | p.1 + p.2 = 1 / 2}) (fun p ⟨⟨_, _, h3⟩, ⟨h1', h2', _⟩⟩ => by
      simp only [mem_setOf_eq]; linarith) (null_sum _)
  have d03 : AEDisjoint volume (SC 0) (SC 3) :=
    aedisj_of_sub (u := {p | p.1 + p.2 = 1 / 2}) (fun p ⟨⟨_, _, h3⟩, ⟨_, _, h3'⟩⟩ => by
      simp only [mem_setOf_eq]; linarith) (null_sum _)
  have d12 : AEDisjoint volume (SC 1) (SC 2) :=
    aedisj_of_sub (u := {p | p.1 = 1 / 2}) (fun p ⟨⟨h1, _, _⟩, ⟨_, h2', h3'⟩⟩ => by
      simp only [mem_setOf_eq]; linarith) (null_fst _)
  have d13 : AEDisjoint volume (SC 1) (SC 3) :=
    aedisj_of_sub (u := {p | p.1 = 1 / 2}) (fun p ⟨⟨h1, _, _⟩, ⟨h1', _, _⟩⟩ => by
      simp only [mem_setOf_eq]; linarith) (null_fst _)
  have d23 : AEDisjoint volume (SC 2) (SC 3) :=
    aedisj_of_sub (u := {p | p.2 = 1 / 2}) (fun p ⟨⟨_, h2, _⟩, ⟨_, h2', _⟩⟩ => by
      simp only [mem_setOf_eq]; linarith) (null_snd _)
  rw [hT, integral_union_ae _ (SC_meas 3).nullMeasurableSet ((hI 0).union (hI 1) |>.union (hI 2))
      (hI 3),
    integral_union_ae _ (SC_meas 2).nullMeasurableSet ((hI 0).union (hI 1)) (hI 2),
    integral_union_ae d01 (SC_meas 1).nullMeasurableSet (hI 0) (hI 1)]
  · ring
  · exact AEDisjoint.union_left d02 d12
  · exact AEDisjoint.union_left (AEDisjoint.union_left d03 d13) d23

/-! ### Polynomials and exact cubature -/

/-- `g` is a real polynomial of total degree `≤ d` in the two coordinates. -/
def IsPoly (d : ℕ) (g : ℝ × ℝ → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin 2) ℝ, p.totalDegree ≤ d ∧ ∀ s, g s = MvPolynomial.eval ![s.1, s.2] p

theorem IsPoly.mono {d e : ℕ} {g} (h : IsPoly d g) (hde : d ≤ e) : IsPoly e g := by
  obtain ⟨p, hp, hg⟩ := h; exact ⟨p, hp.trans hde, hg⟩

theorem IsPoly.const (d : ℕ) (a : ℝ) : IsPoly d fun _ => a :=
  ⟨MvPolynomial.C a, by simp, fun s => by simp⟩

theorem IsPoly.fst : IsPoly 1 fun s => s.1 :=
  ⟨MvPolynomial.X 0, by simp [MvPolynomial.totalDegree_X], fun s => by simp⟩

theorem IsPoly.snd : IsPoly 1 fun s => s.2 :=
  ⟨MvPolynomial.X 1, by simp [MvPolynomial.totalDegree_X], fun s => by simp⟩

theorem IsPoly.add {d : ℕ} {f g} (hf : IsPoly d f) (hg : IsPoly d g) : IsPoly d fun s => f s + g s := by
  obtain ⟨p, hp, hf⟩ := hf; obtain ⟨q, hq, hg⟩ := hg
  exact ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun s => by simp [hf, hg]⟩

theorem IsPoly.neg {d : ℕ} {f} (hf : IsPoly d f) : IsPoly d fun s => -f s := by
  obtain ⟨p, hp, hf⟩ := hf
  exact ⟨-p, by rw [MvPolynomial.totalDegree_neg]; exact hp, fun s => by simp [hf]⟩

theorem IsPoly.sub {d : ℕ} {f g} (hf : IsPoly d f) (hg : IsPoly d g) : IsPoly d fun s => f s - g s := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem IsPoly.mul {d e : ℕ} {f g} (hf : IsPoly d f) (hg : IsPoly e g) : IsPoly (d + e) fun s => f s * g s := by
  obtain ⟨p, hp, hf⟩ := hf; obtain ⟨q, hq, hg⟩ := hg
  exact ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (add_le_add hp hq), fun s => by simp [hf, hg]⟩

theorem IsPoly.const_mul {d : ℕ} {f} (a : ℝ) (hf : IsPoly d f) : IsPoly d fun s => a * f s := by
  simpa using (IsPoly.const 0 a).mul hf

theorem IsPoly.sum {d : ℕ} {ι : Type*} (s : Finset ι) {f : ι → ℝ × ℝ → ℝ} (hf : ∀ i ∈ s, IsPoly d (f i)) :
    IsPoly d fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPoly.const d 0
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf _ (Finset.mem_insert_self _ _)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- An affine function of `s` is `IsPoly 1`. -/
theorem IsPoly.affine (a b c : ℝ) : IsPoly 1 fun s => a + b * s.1 + c * s.2 :=
  ((IsPoly.const 1 a).add (IsPoly.fst.const_mul b)).add (IsPoly.snd.const_mul c)

/-- The node as a point. -/
noncomputable def GNode.pt (n : GNode) : ℝ × ℝ := ((n.a : ℝ) / n.m, (n.b : ℝ) / n.m)

theorem fact_eq (n : ℕ) : fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fact, Nat.factorial_succ, ih]

/-- The rule applied to `g`. -/
noncomputable def ruleSum (WC : ℕ) (r : List GNode) (g : ℝ × ℝ → ℝ) : ℝ :=
  (r.map fun n => ((n.W : ℝ) / WC) * g n.pt).sum

theorem ruleOK_nodes {d WC M : ℕ} {r : List GNode} (h : ruleOK d WC M r = true) : ∀ n ∈ r, n.pt ∈ T2 := by
  intro n hn
  simp only [ruleOK, nodesOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hm, ha⟩, -⟩ := h.1.1.1 n hn
  have hm' : (0 : ℝ) < n.m := by exact_mod_cast hm
  refine ⟨by simp only [GNode.pt]; positivity, by simp only [GNode.pt]; positivity, ?_⟩
  simp only [GNode.pt]
  rw [← add_div, div_le_one hm']; exact_mod_cast ha

theorem ruleOK_mono {d WC M : ℕ} {r : List GNode} (h : ruleOK d WC M r = true) (i j : ℕ) (hij : i + j ≤ d) :
    ruleSum WC r (fun s => s.1 ^ i * s.2 ^ j) = (i.factorial * j.factorial : ℝ) / (i + j + 2).factorial := by
  simp only [ruleOK, nodesOK, ruleRow, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨⟨hn, hM⟩, hW⟩, hmono⟩ := h
  have := hmono i (by omega) j (by omega)
  simp only [fact_eq] at this
  have hc : ((((i + j + 2).factorial : ℤ) *
      (r.map fun n => n.W * ((n.a ^ i * n.b ^ j * (M / n.m) ^ (i + j) : ℕ) : ℤ)).sum : ℤ) : ℝ) =
      (((WC * i.factorial * j.factorial * M ^ (i + j) : ℕ) : ℤ) : ℝ) := by rw [← this]
  rw [Int.cast_mul, Int.cast_list_sum, List.map_map, Int.cast_natCast, Int.cast_natCast] at hc
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hW' : (0 : ℝ) < WC := by exact_mod_cast hW
  have hf : (0 : ℝ) < (i + j + 2).factorial := by exact_mod_cast Nat.factorial_pos _
  have hterm : ∀ n ∈ r, ((Int.cast ∘ fun n : GNode => n.W * ((n.a ^ i * n.b ^ j * (M / n.m) ^ (i + j) : ℕ) : ℤ)) n : ℝ) =
      (M : ℝ) ^ (i + j) * WC * (((n.W : ℝ) / WC) * ((n.pt.1) ^ i * (n.pt.2) ^ j)) := by
    intro n hn'
    obtain ⟨⟨hm0, -⟩, hdvd⟩ := hn n hn'
    have hm0' : (0 : ℝ) < n.m := by exact_mod_cast hm0
    obtain ⟨q, hq⟩ : n.m ∣ M := Nat.dvd_of_mod_eq_zero hdvd
    have hMq : M / n.m = q := by rw [hq, Nat.mul_div_cancel_left _ hm0]
    simp only [Function.comp, GNode.pt]
    rw [hMq, Int.cast_mul, Int.cast_natCast]
    rw [show (M : ℝ) = n.m * q by exact_mod_cast hq]
    push_cast
    field_simp; ring
  rw [List.map_congr_left hterm, List.sum_map_mul_left] at hc
  rw [ruleSum]
  have hMp : (0 : ℝ) < (M : ℝ) ^ (i + j) := by positivity
  rw [eq_div_iff (ne_of_gt hf)]
  have hc' : ((r.map fun n => ((n.W : ℝ) / WC) * ((n.pt.1) ^ i * (n.pt.2) ^ j)).sum) * (i + j + 2).factorial *
      ((M : ℝ) ^ (i + j) * WC) = (i.factorial * j.factorial) * ((M : ℝ) ^ (i + j) * WC) := by
    push_cast at hc
    linear_combination hc
  have := mul_right_cancel₀ (ne_of_gt (by positivity : (0:ℝ) < (M : ℝ) ^ (i + j) * WC)) hc'
  simpa using this

theorem ruleSum_add (WC : ℕ) (r : List GNode) (f g : ℝ × ℝ → ℝ) :
    ruleSum WC r (fun s => f s + g s) = ruleSum WC r f + ruleSum WC r g := by
  simp only [ruleSum]; induction r with
  | nil => simp
  | cons n r ih => simp [ih]; ring

theorem ruleSum_const_mul (WC : ℕ) (r : List GNode) (a : ℝ) (f : ℝ × ℝ → ℝ) :
    ruleSum WC r (fun s => a * f s) = a * ruleSum WC r f := by
  simp only [ruleSum]; induction r with
  | nil => simp
  | cons n r ih => simp [ih]; ring

theorem ruleSum_sum (WC : ℕ) (r : List GNode) {ι : Type*} (s : Finset ι) (f : ι → ℝ × ℝ → ℝ) :
    ruleSum WC r (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, ruleSum WC r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ruleSum]
  | @insert a s ha ih => simp_rw [Finset.sum_insert ha]; rw [ruleSum_add, ih]

theorem ruleSum_congr (WC : ℕ) {r : List GNode} {f g : ℝ × ℝ → ℝ} (h : ∀ n ∈ r, f n.pt = g n.pt) :
    ruleSum WC r f = ruleSum WC r g := by
  simp only [ruleSum]; congr 1; exact List.map_congr_left fun n hn => by rw [h n hn]

/-- **Exact cubature** for polynomials of total degree `≤ d`. -/
theorem rule_exact {d WC M : ℕ} {r : List GNode} (h : ruleOK d WC M r = true) {g : ℝ × ℝ → ℝ}
    (hg : IsPoly d g) : ∫ s in T2, g s = ruleSum WC r g := by
  obtain ⟨p, hp, hgp⟩ := hg
  have hexp : ∀ s : ℝ × ℝ, g s = ∑ m ∈ p.support, p.coeff m * (s.1 ^ m 0 * s.2 ^ m 1) := by
    intro s
    rw [hgp, MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Fin.prod_univ_two]; simp
  have hg' : g = fun s => ∑ m ∈ p.support, p.coeff m * (s.1 ^ m 0 * s.2 ^ m 1) := funext hexp
  rw [hg']
  rw [integral_finset_sum _ (fun m _ => (integrableOn_T2 (by fun_prop)))]
  rw [ruleSum_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [integral_const_mul, ruleSum_const_mul, integral_T2_monomial]
  have hdeg : m 0 + m 1 ≤ d := by
    have := MvPolynomial.le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at this
    omega
  rw [ruleOK_mono h _ _ hdeg]

theorem ruleSum_abs_le (WC : ℕ) (r : List GNode) (f : ℝ × ℝ → ℝ) (E : ℝ) (hE : ∀ n ∈ r, |f n.pt| ≤ E) :
    |ruleSum WC r f| ≤ ((r.map fun n => |(n.W : ℝ) / WC|).sum) * E := by
  simp only [ruleSum]
  induction r with
  | nil => simp
  | cons n r ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := hE n List.mem_cons_self
    have h2 := ih (fun m hm => hE m (List.mem_cons_of_mem _ hm))
    have hE0 : 0 ≤ E := le_trans (abs_nonneg _) h1
    calc _ ≤ |(n.W : ℝ) / WC * f n.pt| + |(r.map fun n => ((n.W : ℝ) / WC) * f n.pt).sum| := abs_add _ _
      _ ≤ |(n.W : ℝ) / WC| * E + ((r.map fun n => |(n.W : ℝ) / WC|).sum) * E := by
          rw [abs_mul]; exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2
      _ = _ := by ring

theorem volume_T2 : (volume : Measure (ℝ × ℝ)).real T2 = 1 / 2 := by
  have := integral_T2_monomial 0 0
  simp at this
  rw [this]; norm_num

theorem volume_T2_lt : volume T2 < ⊤ := T2_compact.measure_lt_top

end GW.Endpoint.Coulomb
