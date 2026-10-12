/-
BRIDGE-Q0 Q2: what SigmaSpec's `q = 0` rule computes in terms of the `q → 0` limit of
`EpsQ0.lean`, and the composed theorem without the `E0` input.

SigmaSpec at `q = 0` (`Sig.epsS`, BerkeleyGW `fixwings.f90` with `q0flag`): the `eps⁻¹`
block is EpsSpec's at the finite `q0` (mapped by one symmetry op), the wings are zeroed,
the head is kept, and the head/`G = 0` Coulomb is the mini-BZ average `vb(0)`
(`⟨8π/|q|²⟩` over the `q = 0` cell).

* **Head** (`head_avg`, `head_avg_spec`): the theory's `q = 0` cell integrand of the singular
  part is `v(q) g(q)` with `v = 8π/|q|²` and `g` the head-dependent factor (the linear
  `eps⁻¹_head(q)`, or the whole GPP head-mode kernel). If `g` has a DIRECTION-INDEPENDENT
  limit `g0` with `|g(q) - g0| ≤ K |q|` (isotropy: for cubic Si the macroscopic
  `ε_M(u)` of `EpsQ0.schur_head` is the same for every `u`; this is a hypothesis, checked
  numerically in `bgw/bridge_q0/q0.py`), then `|⟨v g⟩ - g0 ⟨v⟩| ≤ K ⟨v |q|⟩`, where
  `⟨v |q|⟩ = ⟨8π/|q|⟩` is the `oneoverq`-type average of the cell; and SigmaSpec's value
  `⟨v⟩ g(q0)` is within `K (⟨v|q|⟩ + ⟨v⟩ |q0|)` of the theory's cell integral.
  Without isotropy the limit `g0(u)` depends on `u` and the cell integral is its
  angular average against the cell's solid-angle measure; `g(q0)` then picks the
  single direction `q0/|q0|`.
* **Wings** (`thK_odd`, `sum_odd_zero`, `integral_odd_zero`, `wing_avg_zero`): to leading
  order in `|q|` the `q = 0` wing modes have `I(-u) = -I(u)` and `Ω²(-u) = -Ω²(u)`
  (`EpsQ0.parity_inv` for `I`; the HL `Ω²_{0G} ∝ (q̂·G)/|q|` for `Ω²`) and an even weight
  (`M_{aa}(q, 0) = 1`), and the GPP kernel is odd in `(I, Ω²)` (`thK_odd`: `w̃² = Ω²/I`
  is even). So the leading wing integrand is odd in `q`, and its average over any
  inversion-symmetric measure (the mini-BZ cell, `Measure.IsNegInvariant`; or a finite
  set of directions closed under `u ↦ -u` with even weights, e.g. the 48 ops) is `0`.
  NOT covered (a named approximation): the next order, i.e. the even `O(1)` parts of the
  wings (from `M_{an}(q,0) = O(q)` for `n ≠ a` and from `O(q)` corrections), which
  BerkeleyGW also drops. They carry the cell weight `1/N_q`, like the body.
* **The theory's `q = 0` wings do not enter `SigT`** (`omT_wing`, `thK_zeroO`): with the
  theory's own convention `OmT = 0` on the `q = 0` wings (Bloch.lean), every wing mode of
  `SigT` is `0` whatever the wing values of `eps⁻¹`, and SigmaSpec's zeroed wings give `0`
  too (`specMode_zeroI`). So `sigA_eq_theory_q0` drops BRIDGE's `q = 0` wing hypothesis
  (`WingFree`'s first part, false for the raw `eps0mat`, whose row wing reaches 29)
  and asks `ModeOK` only off the `q = 0` wings.
* **Composition** (`sigA_eps_eq_theory_q0`): SigmaSpec with `eps⁻¹` the inverse of
  EpsSpec's eps on EVERY block, the `q = 0` block included (EpsSpec at `q0 ≠ 0`, an
  ordinary `EpsBlock.OK` block), equals the theory `SigT` built from the theory RPA eps
  (at `q0` on the `q = 0` block) plus `COR`. The input `E0` of BRIDGE-EPS is gone.
  Both inverses are Mathlib's totalized `Matrix.inv` (`0` for a singular matrix); they are
  genuine inverses only when `det eps ≠ 0`, which is not established for these blocks.
  `epsSpec_q0_scaled` + `EpsQ0.q0_error` then bound the head and the body of that block
  (the scaled wings too, though they do not enter) against a supplied invertible `Ẽ0`
  (in `bgw/bridge_q0/q0.py`, the computed one). That `Ẽ0` is the `q → 0` limit only if
  the physical ray satisfies `KPRay.OK`, with the k·p slope a hypothesis
  (`EpsQ0.q0_limit`, `chiSc_tendsto`); no theorem here composes the two.
  What remains between this `SigT` and a `q → 0` theory is named, not bounded here:
  the single direction `q0/|q0|` (the body limit depends on it at `O(1)`), the finite
  `|q0|` (bounded entrywise by `q0_error`, but not propagated through the nonlinear GPP),
  and the next-order even wing terms.

REVIEW-28 F1: the composed theorem below takes the screening blocks `bs` independently of the
Sigma data `gl`, `st`; it is a conditional identity, not a statement about one system. The
one-system version is `GW.Bridge.Common.sigA_compat` (`GW/Bridge/Common.lean`). On the
Si-EPM run the Epsilon and Sigma k-grids are disjoint, so with any screening block off `Z`
its compatibility hypothesis `Compat` fails whenever a block the Σ q-list reads is derived
(`Compat` requires `k0` and every `k0 - q_t`
to be grid points). Its time-reversal hypothesis `MF.TR` cannot hold at a self-paired
point with a nonzero sphere vector, such as X or L (`MF.tr_fixed`). For O1 its hypotheses
are unsatisfiable if every block outside `Z` has a `neg` that fixes `k0`
(`hyps_unsat_of_selfpaired`; this follows from the trusted premise that `neg` encodes
`-k`, on a grid that stores X/L once), or, for arbitrary plans, if no grid index stores
the negated sphere list of `k0` (`hnp`, `hyps_unsat_of_unpaired`); storing X/L once does
not by itself give either premise (`docs/reviews/R28-F1.md`).
-/
import GW.Bridge.EpsQ0
import GW.Bridge.EpsCompare
import Mathlib.MeasureTheory.Group.Integral

set_option linter.unusedSectionVars false

namespace GW.Bridge

open Finset MeasureTheory GW.Endpoint.Kernel.Sig GW.Endpoint.Kernel.Eps

/-! ### The GPP kernel is odd in `(I, Ω²)` -/

theorem wTilde_neg (I O : ℝ) : wTilde (-I) (-O) = wTilde I O := by
  unfold wTilde; rw [neg_div_neg_eq]

/-- **The GPP kernel is odd.** `w̃` is invariant under `(I, Ω²) ↦ (-I, -Ω²)` (`w̃² = Ω²/I`
is even) and the kernel is linear in the prefactor `Ω²` at fixed `w̃`. -/
theorem thK_odd (occ : Bool) (I O x : ℝ) : thK occ (-I) (-O) x = -thK occ I O x := by
  unfold thK
  rw [wTilde_neg]
  cases occ <;> simp [GW.GPP.occupiedTerm, GW.GPP.emptyTerm, neg_div]

theorem thK_zeroO (occ : Bool) (I x : ℝ) : thK occ I 0 x = 0 := by
  unfold thK; cases occ <;> simp [GW.GPP.occupiedTerm, GW.GPP.emptyTerm]

/-! ### Averages of odd functions vanish -/

/-- A finite, inversion-closed set of directions with even weights. -/
theorem sum_odd_zero {V : Type*} [AddCommGroup V] (Dset : Finset V)
    (hD : ∀ d ∈ Dset, -d ∈ Dset) (w f : V → ℝ) (hw : ∀ d, w (-d) = w d)
    (hf : ∀ d, f (-d) = -f d) : ∑ d ∈ Dset, w d * f d = 0 := by
  refine sum_involution (fun d _ => -d) (fun d _ => by rw [hw, hf]; ring) (fun d _ h hd => ?_)
    (fun d hd => hD d hd) (fun d _ => neg_neg d)
  apply h
  have hd' : -d = d := hd
  have : f d = -f d := by rw [← hf, hd']
  rw [show f d = 0 by linarith, mul_zero]

/-- An inversion-symmetric measure (the mini-BZ cell): the average of an odd function is `0`. -/
theorem integral_odd_zero {V : Type*} [MeasurableSpace V] [AddGroup V] [MeasurableNeg V]
    (μ : Measure V) [μ.IsNegInvariant] (f : V → ℝ) (hf : ∀ q, f (-q) = -f q) :
    ∫ q, f q ∂μ = 0 := by
  have h := integral_neg_eq_self f μ
  simp only [hf, integral_neg] at h
  linarith

/-- **The leading `q = 0` wing term averages to zero.** The integrand
`w(q) · thK occ (I q) (Ω² q) x` with an even weight `w` (`M_aa v M_G` at leading order)
and odd `I`, `Ω²` is odd, so its average over an inversion-symmetric measure is `0`. -/
theorem wing_avg_zero {V : Type*} [MeasurableSpace V] [AddGroup V] [MeasurableNeg V]
    (μ : Measure V) [μ.IsNegInvariant] (occ : Bool) (x : ℝ) (w I O : V → ℝ)
    (hw : ∀ q, w (-q) = w q) (hI : ∀ q, I (-q) = -I q) (hO : ∀ q, O (-q) = -O q) :
    ∫ q, w q * thK occ (I q) (O q) x ∂μ = 0 :=
  integral_odd_zero μ _ fun q => by rw [hw, hI, hO, thK_odd]; ring

/-- The same over a finite inversion-closed set of directions (e.g. the images of `q0` under
the 48 ops, each op one direction) with even weights. -/
theorem wing_sum_zero {V : Type*} [AddCommGroup V] (Dset : Finset V)
    (hD : ∀ d ∈ Dset, -d ∈ Dset) (occ : Bool) (x : ℝ) (w I O : V → ℝ)
    (hw : ∀ q, w (-q) = w q) (hI : ∀ q, I (-q) = -I q) (hO : ∀ q, O (-q) = -O q) :
    ∑ d ∈ Dset, w d * thK occ (I d) (O d) x = 0 :=
  sum_odd_zero Dset hD w (fun q => thK occ (I q) (O q) x) hw fun q => by
    simp only [hI, hO, thK_odd]

/-! ### The head: the mini-BZ average of the singular part -/

/-- **Head average with isotropy.** On the (normalised) cell measure `μ`, with `v ≥ 0`
(`8π/|q|²`) and `|g(q) - g0| ≤ K n(q)` (`n = |q|`; `g0` the direction-independent
limit), `|⟨v g⟩ - g0 ⟨v⟩| ≤ K ⟨v n⟩` (`⟨v n⟩ = ⟨8π/|q|⟩`, the `oneoverq`-type average). -/
theorem head_avg {α : Type*} [MeasurableSpace α] (μ : Measure α) (v n g : α → ℝ) (g0 K : ℝ)
    (hv : ∀ q, 0 ≤ v q) (hg : ∀ q, |g q - g0| ≤ K * n q)
    (hvg : Integrable (fun q => v q * g q) μ) (hv1 : Integrable v μ)
    (hvn : Integrable (fun q => v q * n q) μ) :
    |∫ q, v q * g q ∂μ - g0 * ∫ q, v q ∂μ| ≤ K * ∫ q, v q * n q ∂μ := by
  have e : ∫ q, v q * g q ∂μ - g0 * ∫ q, v q ∂μ = ∫ q, v q * (g q - g0) ∂μ := by
    rw [← integral_const_mul, ← integral_sub hvg (hv1.const_mul g0)]
    congr 1; funext q; ring
  rw [e, ← integral_const_mul]
  have hb : Integrable (fun q => K * (v q * n q)) μ := hvn.const_mul K
  calc |∫ q, v q * (g q - g0) ∂μ| = ‖∫ q, v q * (g q - g0) ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ q, K * (v q * n q) ∂μ := norm_integral_le_of_norm_le hb (Filter.Eventually.of_forall
        fun q => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv q)]
          calc v q * |g q - g0| ≤ v q * (K * n q) := mul_le_mul_of_nonneg_left (hg q) (hv q)
            _ = K * (v q * n q) := by ring)

/-- **SigmaSpec's head against the theory's cell integral.** SigmaSpec uses `⟨v⟩ g(q0)`
(the Coulomb average times the head at the one direction `q0`); the theory has `⟨v g⟩`.
Under the hypotheses of `head_avg` and `|g(q0) - g0| ≤ K |q0|`, they differ by at most
`K (⟨v |q|⟩ + ⟨v⟩ |q0|)`. -/
theorem head_avg_spec {α : Type*} [MeasurableSpace α] (μ : Measure α) (v n g : α → ℝ)
    (g0 K gq0 nq0 : ℝ) (hv : ∀ q, 0 ≤ v q) (hg : ∀ q, |g q - g0| ≤ K * n q)
    (hq0 : |gq0 - g0| ≤ K * nq0)
    (hvg : Integrable (fun q => v q * g q) μ) (hv1 : Integrable v μ)
    (hvn : Integrable (fun q => v q * n q) μ) :
    |∫ q, v q * g q ∂μ - (∫ q, v q ∂μ) * gq0| ≤
      K * ∫ q, v q * n q ∂μ + (∫ q, v q ∂μ) * (K * nq0) := by
  have h1 := head_avg μ v n g g0 K hv hg hvg hv1 hvn
  have hV : 0 ≤ ∫ q, v q ∂μ := integral_nonneg hv
  have h2 : |(∫ q, v q ∂μ) * gq0 - g0 * ∫ q, v q ∂μ| ≤ (∫ q, v q ∂μ) * (K * nq0) := by
    rw [show (∫ q, v q ∂μ) * gq0 - g0 * ∫ q, v q ∂μ = (∫ q, v q ∂μ) * (gq0 - g0) by ring,
      abs_mul, abs_of_nonneg hV]
    exact mul_le_mul_of_nonneg_left hq0 hV
  calc |∫ q, v q * g q ∂μ - (∫ q, v q ∂μ) * gq0|
      = |(∫ q, v q * g q ∂μ - g0 * ∫ q, v q ∂μ) - ((∫ q, v q ∂μ) * gq0 - g0 * ∫ q, v q ∂μ)| := by
        ring_nf
    _ ≤ |∫ q, v q * g q ∂μ - g0 * ∫ q, v q ∂μ| + |(∫ q, v q ∂μ) * gq0 - g0 * ∫ q, v q ∂μ| :=
        abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

/-! ### The `q = 0` wings do not enter the theory -/

/-- A `q = 0` wing position `(j, i)`. -/
def Wing (qd : QD) (j i : ℕ) : Prop :=
  qd.qh = 0 ∧ ((j = qd.z ∧ i ≠ qd.z) ∨ (i = qd.z ∧ j ≠ qd.z))

/-- The `q = 0` sphere has its `G = 0` exactly at `z`. -/
def ZeroAt (qd : QD) : Prop := ∀ j < qd.Gs.length, (gs qd j = 0 ↔ j = qd.z)

theorem vec_zero {qd : QD} (h : qd.qh = 0) : vec qd 0 = 0 := by
  funext c; fin_cases c <;> simp [vec, h]

theorem dotB_zero_left (gl : Gl) (w : Fin 3 → ℝ) : dotB gl 0 w = 0 := by simp [dotB]

/-- The theory `Ω²` vanishes on the `q = 0` wings. -/
theorem omT_wing (gl : Gl) (vc : V3 → ℝ) {qd : QD} (hz : ZeroAt qd) {j i : ℕ}
    (hj : j < qd.Gs.length) (hi : i < qd.Gs.length) (hw : Wing qd j i) :
    OmT gl vc qd j i = 0 := by
  obtain ⟨h0, hw⟩ := hw
  unfold OmT
  rcases hw with ⟨rfl, hne⟩ | ⟨rfl, hne⟩
  · have e1 : gs qd qd.z = 0 := (hz _ hj).mpr rfl
    have e2 : gs qd i ≠ 0 := fun h => hne ((hz _ hi).mp h)
    rw [if_pos ⟨h0, e1⟩, if_neg e2, mul_zero]
  · have e1 : gs qd qd.z = 0 := (hz _ hi).mpr rfl
    have e2 : gs qd j ≠ 0 := fun h => hne ((hz _ hj).mp h)
    rw [if_neg (fun h => e2 h.2), e1, vec_zero h0, dotB_zero_left, mul_zero, mul_zero]

/-- SigmaSpec's zeroed wing: `I = 0` drops the mode. -/
theorem specMode_zeroI (occ : Bool) (O x : ℝ) : specMode occ 0 O x = 0 := by
  have hk : ¬ keepM 0 O := fun h => by
    have := h.1.1; rw [abs_zero] at this; linarith [TS_pos]
  simp [specMode, schM, ssxM, hk]

theorem epsS_wing (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ) {qd : QD} {j i : ℕ}
    (hw : Wing qd j i) : IeS gl E vb oq qd j i = 0 := by
  obtain ⟨h0, hw'⟩ := hw
  have hji : j ≠ i := by rcases hw' with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> [exact fun e => h e.symm; exact h]
  simp only [IeS, epsS, if_pos h0, if_pos hw', if_neg hji, sub_zero]

/-- Off the `q = 0` wings, with the `q ≠ 0` wing factors `1`, SigmaSpec's `eps⁻¹` is `epsT`. -/
theorem epsS_off (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ) {qd : QD}
    (hq : qd.qh ≠ 0 → oq qd.qh * qlen gl qd / (8 * Real.pi) = 1 ∧
      oq qd.qh / (vb (key qd (gs qd 0)) * qlen gl qd) = 1) {j i : ℕ} (hw : ¬ Wing qd j i) :
    epsS gl E vb oq qd j i = epsT E qd j i := by
  have e : epsS gl E vb oq qd j i =
      if qd.qh = 0 then
        (if (j = qd.z ∧ i ≠ qd.z) ∨ (i = qd.z ∧ j ≠ qd.z) then 0 else epsT E qd j i)
      else if j = qd.z ∧ i ≠ qd.z then epsT E qd j i * (oq qd.qh * qlen gl qd / (8 * Real.pi))
      else if i = qd.z ∧ j ≠ qd.z then
        epsT E qd j i * (oq qd.qh / (vb (key qd (gs qd 0)) * qlen gl qd))
      else epsT E qd j i := rfl
  rw [e]
  by_cases h0 : qd.qh = 0
  · rw [if_pos h0, if_neg (fun h => hw ⟨h0, h⟩)]
  · rw [if_neg h0, (hq h0).1, (hq h0).2, mul_one]
    split_ifs <;> rfl

/-- **`sigA_eq_theory` without the `q = 0` wing hypothesis.** The `q = 0` wing values of
`E` are arbitrary; `ModeOK` is asked only off the `q = 0` wings; `ZeroAt` locates the
`G = 0` channel at the `q = 0` points. -/
theorem sigA_eq_theory_q0 (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ) (st : St)
    (vc : V3 → ℝ) (a iw : ℕ) (hC : ∀ k, vb k = vc k)
    (hWq : ∀ t < gl.qs.length, (gl.qs.getD t default).qh ≠ 0 →
      oq (gl.qs.getD t default).qh * qlen gl (gl.qs.getD t default) / (8 * Real.pi) = 1 ∧
      oq (gl.qs.getD t default).qh / (vb (key (gl.qs.getD t default)
        (gs (gl.qs.getD t default) 0)) * qlen gl (gl.qs.getD t default)) = 1)
    (hZ : ∀ t < gl.qs.length, (gl.qs.getD t default).qh = 0 → ZeroAt (gl.qs.getD t default))
    (hX : ∀ t < gl.qs.length, ∀ n1 < nbq st t, TZ ≤ |xT gl st t a n1 iw|)
    (hM : ∀ t < gl.qs.length, ∀ n1 < nbq st t, ∀ j < nG gl t, ∀ i < nG gl t,
      ¬ Wing (gl.qs.getD t default) j i →
      ModeOK (decide (n1 < gl.nocc)) (ITq gl E t j i) (OTq gl vb t j i) (xT gl st t a n1 iw)) :
    SigA gl E vb oq st a iw = SigT gl E vc st a iw + COR gl E vb oq st a := by
  have hv : vb = vc := funext hC
  subst hv
  unfold SigA SigT COR
  rw [← sum_add_distrib]
  refine sum_congr rfl fun t ht => ?_
  have ht' := mem_range.mp ht
  have hP : ∀ n1 ∈ range (nbq st t), Pq gl E vb oq st t a n1 iw = PT gl E vb st t a n1 iw := by
    intro n1 hn1
    have hn1' := mem_range.mp hn1
    rw [Pq_eq_quad, PT]
    apply quad_congr
    intro j hj i hi
    have hx : wxS gl st t a n1 iw = xT gl st t a n1 iw := by
      rw [wxS_eq, if_neg (not_lt.mpr (hX t ht' n1 hn1'))]
    by_cases hw : Wing (gl.qs.getD t default) j i
    · have hI : Iq gl E vb oq t j i = 0 := epsS_wing gl E vb oq hw
      have hO : OTq gl vb t j i = 0 := omT_wing gl vb (hZ t ht' hw.1) hj hi hw
      rw [hI, specMode_zeroI, hO, thK_zeroO]
    · have hI : Iq gl E vb oq t j i = ITq gl E t j i := by
        simp only [Iq, ITq, IeS, IT, epsS_off gl E vb oq (hWq t ht') hw]
      have hO : Oq gl vb t j i = OTq gl vb t j i := by simp only [Oq, OTq, om2S_eq]
      rw [hI, hO, hx]
      exact mode_eq (hM t ht' n1 hn1' j hj i hi hw)
  rw [sum_congr rfl fun n1 hn1 => by rw [hP n1 hn1], sum_add_distrib]
  ring

/-! ### The composition: EpsSpec on every block, the `q = 0` block included -/

/-- **The composed theorem without `E0`.** Every irreducible block, the `q0` block of the
`q = 0` point included, is EpsSpec's (`Z = ∅`), each an `EpsBlock.OK` block
(`q0 ≠ 0`, so `qne` holds there too). Then BerkeleyGW's `SigA` equals the theory `SigT`
built from the inverse theory RPA eps of every block, plus `COR`, under `hC`, the `q ≠ 0`
wing factors, `ZeroAt` at `q = 0`, `hX` and `ModeOK` off the `q = 0` wings. "Inverse" is
Mathlib's totalized `Matrix.inv`; it is a genuine inverse only when `det eps ≠ 0`, which
`hOK` does not give. -/
theorem sigA_eps_eq_theory_q0 {κ : Type*} [Fintype κ] [DecidableEq κ] (gl : Gl)
    (vb oq : V3 → ℝ) (st : St) (vc : V3 → ℝ) (a iw : ℕ) (bs : ℕ → EpsBlock κ)
    (hOK : ∀ iq, (bs iq).OK) (hC : ∀ k, vb k = vc k)
    (hWq : ∀ t < gl.qs.length, (gl.qs.getD t default).qh ≠ 0 →
      oq (gl.qs.getD t default).qh * qlen gl (gl.qs.getD t default) / (8 * Real.pi) = 1 ∧
      oq (gl.qs.getD t default).qh / (vb (key (gl.qs.getD t default)
        (gs (gl.qs.getD t default) 0)) * qlen gl (gl.qs.getD t default)) = 1)
    (hZ : ∀ t < gl.qs.length, (gl.qs.getD t default).qh = 0 → ZeroAt (gl.qs.getD t default))
    (hX : ∀ t < gl.qs.length, ∀ n1 < nbq st t, TZ ≤ |xT gl st t a n1 iw|)
    (hM : ∀ t < gl.qs.length, ∀ n1 < nbq st t, ∀ j < nG gl t, ∀ i < nG gl t,
      ¬ Wing (gl.qs.getD t default) j i →
      ModeOK (decide (n1 < gl.nocc)) (ITq gl (Etheory ∅ 0 bs) t j i) (OTq gl vb t j i)
        (xT gl st t a n1 iw)) :
    SigA gl (Espec ∅ 0 bs) vb oq st a iw =
      SigT gl (Etheory ∅ 0 bs) vc st a iw + COR gl (Etheory ∅ 0 bs) vb oq st a := by
  rw [Espec_eq_Etheory ∅ 0 bs (fun iq _ => hOK iq)]
  exact sigA_eq_theory_q0 gl _ vb oq st vc a iw hC hWq hZ hX hM

/-! ### The `q0` block against the `q → 0` limit -/

/-- **EpsSpec's `q0` block is a point of the k·p ray.** If a ray `D` reproduces EpsSpec's
`χ` at `t0` on the sphere (`hmatch`), EpsSpec's eps at `q0` is `epsM (vT) (chiRay D gs t0)`,
so `EpsQ0.q0_error` applies to it with `v = vT`, `χ = chiRay D gs t0`, relative to a
supplied invertible `Ẽ0`. `hmatch` pins `D` only at `t0`; that `Ẽ0` is the `q → 0` limit
(`EpsQ0.q0_limit`) needs `KPRay.OK` for the physical ray, with the k·p slope a hypothesis,
and is not composed here. -/
theorem epsSpec_q0_scaled {τ γ : Type*} (inp : Input) (D : KPRay τ γ)
    (gs' : Fin inp.Gs.length → γ) (t0 : ℝ)
    (hmatch : ∀ i j, chi inp (gsI inp i) (gsI inp j) = D.chi t0 (gs' i) (gs' j)) :
    epsMatR inp = epsM (vT inp) (chiRay D gs' t0) := by
  ext i j
  have h := hmatch i j
  simp only [gsI] at h
  simp only [epsMatR, epsR, epsM, Matrix.of_apply, Matrix.sub_apply, one_fin_apply,
    Matrix.diagonal_mul, chiRay, vT, gsI, h]

/-- The Coulomb head of the `q0` block: `t0² · 8π/|q0|² = 8π/|u|²` for `q0 = t0 u`. -/
theorem vT_head (inp : Input) (z : Fin inp.Gs.length) {t0 c : ℝ} (ht : t0 ≠ 0)
    (hq : qG2 inp (gsI inp z) = t0 ^ 2 * c) (hc : c ≠ 0) :
    vSc z t0 (vT inp) z = 8 * Real.pi / c := by
  apply coulomb_head ht
  simp only [vT, vC, hq]; field_simp; ring

end GW.Bridge
