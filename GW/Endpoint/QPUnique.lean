/-
Approximation layer A1: the logic of the uniqueness certificate
`bgw/endpoint/qp_unique.py` for a root of the quasiparticle equation
`f(E) = Emf + Sigma(E) - E = 0` in an energy window `[W₀, W₁]`.

The Python certificate establishes, in rigorous interval arithmetic, the
hypotheses below for the spec-A GPP self-energy of each O1 state:

* on the root bracket `[a, b]` every GPP branch condition is decided, so `f`
  is continuous there, and an enclosure of `f'` on `(a, b)` is negative;
* `f a > 0 > f b`;
* the rest of the window is covered by intervals on which `f` has no zero
  (the interval value of `f` excludes `0`, or, at a jump of `f` across `0`
  where one GPP branch switches, both single-branch values exclude `0`),
  i.e. `f E ≠ 0` for `E` in the window outside `(a, b)`. `f` need not be
  continuous outside `[a, b]`.

This file proves that these hypotheses give exactly one root in the window,
and that it lies in every sub-bracket with certified endpoint signs. That the
Python evaluation establishes the hypotheses for BerkeleyGW's `Sigma` is NOT
proved here (it is the interval-arithmetic correspondence, a recorded gap).
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

namespace GW.Endpoint

open Set

/-- A continuous function on `[a, b]` with a negative derivative on `(a, b)`
is strictly decreasing on `[a, b]`. -/
theorem strictAntiOn_Icc_of_hasDerivAt_neg {f f' : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x ∧ f' x < 0) :
    StrictAntiOn f (Icc a b) :=
  strictAntiOn_of_deriv_neg (convex_Icc a b) hc fun x hx => by
    rw [interior_Icc] at hx
    rw [(hd x hx).1.deriv]
    exact (hd x hx).2

/-- The uniqueness certificate: exactly one root of `f` in `[W₀, W₁]`. -/
theorem qp_root_unique {f f' : ℝ → ℝ} {W₀ W₁ a b : ℝ}
    (hWa : W₀ ≤ a) (hab : a ≤ b) (hbW : b ≤ W₁)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x ∧ f' x < 0)
    (ha : 0 < f a) (hb : f b < 0)
    (hcov : ∀ E ∈ Icc W₀ W₁, E ∉ Ioo a b → f E ≠ 0) :
    ∃! E, E ∈ Icc W₀ W₁ ∧ f E = 0 := by
  obtain ⟨E, hE, hfE⟩ :=
    intermediate_value_Icc' hab hc ⟨hb.le, ha.le⟩
  have hanti := strictAntiOn_Icc_of_hasDerivAt_neg hc hd
  refine ⟨E, ⟨⟨hWa.trans hE.1, hE.2.trans hbW⟩, hfE⟩, ?_⟩
  rintro E' ⟨hE'W, hfE'⟩
  have hE' : E' ∈ Icc a b := by
    by_contra h
    exact hcov E' hE'W (fun h' => h (Ioo_subset_Icc_self h')) hfE'
  exact hanti.injOn hE' hE (hfE'.trans hfE.symm)

/-- The root lies in every sub-bracket `[c, d] ⊆ [a, b]` with `f c > 0 > f d`
(the bisection output of `qp_cert.certify_root`). -/
theorem qp_root_mem_subbracket {f f' : ℝ → ℝ} {a b c d E : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x ∧ f' x < 0)
    (hfc : 0 < f c) (hfd : f d < 0)
    (hE : E ∈ Icc a b) (hfE : f E = 0) :
    E ∈ Icc c d := by
  have hanti := strictAntiOn_Icc_of_hasDerivAt_neg hc hd
  have hcI : c ∈ Icc a b := ⟨hac, hcd.trans hdb⟩
  have hdI : d ∈ Icc a b := ⟨hac.trans hcd, hdb⟩
  constructor
  · by_contra h
    push_neg at h
    have := hanti hE hcI h
    linarith
  · by_contra h
    push_neg at h
    have := hanti hdI hE h
    linarith

/-- A continuous function on `[a, b]` with a positive derivative on `(a, b)`
is strictly increasing on `[a, b]`. -/
theorem strictMonoOn_Icc_of_hasDerivAt_pos {f f' : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x ∧ 0 < f' x) :
    StrictMonoOn f (Icc a b) :=
  strictMonoOn_of_deriv_pos (convex_Icc a b) hc fun x hx => by
    rw [interior_Icc] at hx
    rw [(hd x hx).1.deriv]
    exact (hd x hx).2

/-- The hypotheses the certificate checks on one root bracket `[a, b]`:
continuity, a derivative of one fixed sign on `(a, b)`, and endpoint values of
opposite sign. -/
structure IsolatingBracket (f f' : ℝ → ℝ) (a b : ℝ) : Prop where
  le : a ≤ b
  cont : ContinuousOn f (Icc a b)
  deriv : (∀ x ∈ Ioo a b, HasDerivAt f (f' x) x ∧ f' x < 0) ∨
    (∀ x ∈ Ioo a b, HasDerivAt f (f' x) x ∧ 0 < f' x)
  sign : f a * f b < 0

/-- An isolating bracket contains exactly one root. -/
theorem IsolatingBracket.existsUnique {f f' : ℝ → ℝ} {a b : ℝ}
    (h : IsolatingBracket f f' a b) : ∃! E, E ∈ Icc a b ∧ f E = 0 := by
  have hinj : InjOn f (Icc a b) := by
    rcases h.deriv with hd | hd
    · exact (strictAntiOn_Icc_of_hasDerivAt_neg h.cont hd).injOn
    · exact (strictMonoOn_Icc_of_hasDerivAt_pos h.cont hd).injOn
  have hs := h.sign
  have hex : ∃ E ∈ Icc a b, f E = 0 := by
    rcases lt_or_le (f a) 0 with ha | ha
    · have hb : 0 < f b := by
        by_contra hb; push_neg at hb; nlinarith
      exact intermediate_value_Icc h.le h.cont ⟨ha.le, hb.le⟩
    · have hb : f b < 0 := by
        by_contra hb; push_neg at hb; nlinarith
      exact intermediate_value_Icc' h.le h.cont ⟨hb.le, ha⟩
  obtain ⟨E, hE, hfE⟩ := hex
  exact ⟨E, ⟨hE, hfE⟩, fun E' ⟨hE', hfE'⟩ => hinj hE' hE (hfE'.trans hfE.symm)⟩

/-- The complete root enumeration certified by `qp_unique.py`: finitely many
ordered, disjoint isolating brackets inside the window, and no zero of `f` in
the window outside their interiors. Then the zeros of `f` in the window are
exactly `n` points, one in each bracket, in increasing order. -/
theorem qp_roots_enumerated {f f' : ℝ → ℝ} {W₀ W₁ : ℝ} {n : ℕ} (a b : Fin n → ℝ)
    (hbr : ∀ i, IsolatingBracket f f' (a i) (b i))
    (hin : ∀ i, W₀ ≤ a i ∧ b i ≤ W₁)
    (hord : ∀ i j : Fin n, i < j → b i < a j)
    (hcov : ∀ E ∈ Icc W₀ W₁, (∀ i, E ∉ Ioo (a i) (b i)) → f E ≠ 0) :
    ∃ r : Fin n → ℝ, StrictMono r ∧ (∀ i, r i ∈ Icc (a i) (b i)) ∧
      {E | E ∈ Icc W₀ W₁ ∧ f E = 0} = range r := by
  choose r hr huniq using fun i => (hbr i).existsUnique
  refine ⟨r, fun i j hij => ?_, fun i => (hr i).1, ?_⟩
  · exact lt_of_le_of_lt (hr i).1.2 (lt_of_lt_of_le (hord i j hij) (hr j).1.1)
  ext E
  constructor
  · rintro ⟨hEW, hfE⟩
    by_contra hnot
    refine hcov E hEW (fun i hi => hnot ⟨i, ?_⟩) hfE
    exact (huniq i E ⟨Ioo_subset_Icc_self hi, hfE⟩).symm
  · rintro ⟨i, rfl⟩
    exact ⟨⟨(hin i).1.trans (hr i).1.1, (hr i).1.2.trans (hin i).2⟩, (hr i).2⟩

end GW.Endpoint
