/- ARCHIVED (2026-10-01): Specification.md v0.1 demo lineage, superseded by GW.Endpoint.Kernel.SigmaSpec and GW.Bridge; kept, not extended, outside the fast gate. See docs/CODEMAP.md.
Domain-carrying denominator types for the S1 pole cancellation.

This module is **additive**. It introduces no new axiom, weakens nothing, and
restates nothing: every theorem below is proved *from* the existing unbundled
theorems of `GW.GPP.PoleCancellation`, `GW.GPP.BerkeleyGWMap` and
`GW.GPP.FiniteSelfEnergy`, which remain the primary statements.

## Why two types and not one

An external review asked for a single bundled "admissible pole configuration"
carrying `w`, `x` and the three nonvanishing proofs, so that the side conditions
of

```text
-A/(x^2 - w^2) + A/(2*w*(x - w)) = A/(2*w*(x + w))
```

cannot be forgotten at a use site. That works for the *algebraic* identity, and
`AdmissiblePole` below is exactly that type.

It does **not** work for the analytic S1 statements. Continuity at `x = w` and
the punctured limit at `x = w` quantify over a whole neighbourhood of `x`, and
the merged expression is continuous *at* `x = w`, a point which is by
construction excluded from `AdmissiblePole`. Bundling `x` with `w` therefore
makes those theorems unstateable over the bundle. The honest design is a
two-level one:

* `PoleEnergy` - carries only `w ≠ 0`. This is the domain of the analytic
  facts (extension value, continuity, punctured limit) and of the
  Coulomb-hole rewrite, all of which hold for every real `x`.
* `AdmissiblePole` - extends `PoleEnergy` with an offset `x` avoiding both
  poles. This is the domain of the algebraic cancellation and of the
  BerkeleyGW branch-agreement identity.

`PoleEnergy.eventually_admissible` records the exact relationship: near the
removable pole the smaller domain is eventually inhabited, which is why the
limit statement lives one level up.

## What the bundle deliberately does not model

`AdmissiblePole` is the domain of the **raw split** expression, and it is
strictly smaller than the domain of the public checked evaluator of
`GW.GPP.FiniteSelfEnergy`. That evaluator accepts an occupied term at `x = w`
with `w > 0` on purpose (Specification.md S2: the intended continuous
extension). `Term.check_ok_rawSplitAdmissible_false` below exhibits a term that
the evaluator accepts and that admits no `AdmissiblePole`. So this type must not
be used as the evaluator's domain type.

Lean division remains total here. The bundle does not change that; it only
makes the hypotheses that give the expressions their intended meaning travel
with the data.
-/
import GW.GPP.PoleCancellation
import GW.GPP.BerkeleyGWMap
import GW.GPP.FiniteSelfEnergy

namespace GW.GPP

open Filter Topology

/-! ## A nonvanishing pole energy -/

/-- A GPP pole energy bundled with its nonvanishing proof. `w` is an energy in
eV (Specification.md S2); this type carries `w ≠ 0` only, not positivity, which
is a separate requirement of the checked evaluator. -/
structure PoleEnergy where
  /-- The pole energy `w`, in eV. -/
  w : ℝ
  /-- The domain condition carried by the type. -/
  w_ne_zero : w ≠ 0

namespace PoleEnergy

/-- Build a pole energy from strict positivity, the condition the public
checked evaluator of S2 actually enforces. -/
def ofPos {w : ℝ} (hw : 0 < w) : PoleEnergy := ⟨w, ne_of_gt hw⟩

@[simp] theorem ofPos_w {w : ℝ} (hw : 0 < w) : (ofPos hw).w = w := rfl

theorem sq_pos (p : PoleEnergy) : 0 < p.w ^ 2 := by
  have := p.w_ne_zero
  positivity

/-- The two excluded offsets are distinct; this is what makes `x = w` a
*removable* singularity of the raw split expression. -/
theorem pole_ne_negPole (p : PoleEnergy) : p.w ≠ -p.w :=
  GW.GPP.pole_ne_pole p.w p.w_ne_zero

/-- The merged denominator at the removable point does not vanish. -/
theorem denom_ne_zero_at_pole (p : PoleEnergy) : 2 * p.w * (p.w + p.w) ≠ 0 :=
  occupied_denom_ne_zero_at_pole p.w p.w_ne_zero

/-! ### The analytic S1 facts, which hold for every real offset -/

/-- **Extension value**, with the domain carried by the type. -/
theorem merged_at_pole (p : PoleEnergy) (A : ℝ) :
    occupiedTerm A p.w p.w = A / (4 * p.w ^ 2) :=
  occupiedTerm_at_pole A p.w p.w_ne_zero

/-- **Continuity at the removable point**, with the domain carried by the
type. This statement is available only at this level: its point of interest
`x = w` is excluded from `AdmissiblePole` by construction. -/
theorem continuousAt_merged (p : PoleEnergy) (A : ℝ) :
    ContinuousAt (fun x : ℝ => occupiedTerm A x p.w) p.w :=
  continuousAt_occupiedTerm A p.w p.w_ne_zero

/-- **Punctured limit of the raw split expression**, with the domain carried by
the type. -/
theorem tendsto_raw (p : PoleEnergy) (A : ℝ) :
    Tendsto (fun x : ℝ => rawOccupied A x p.w) (𝓝[≠] p.w) (𝓝 (A / (4 * p.w ^ 2))) :=
  tendsto_rawOccupied_nhdsWithin_ne A p.w p.w_ne_zero

/-- The Coulomb-hole rewrite of the transcribed BerkeleyGW 4.0 `sch`
accumulation needs `w ≠ 0` and nothing else, so it also lives at this level. -/
theorem ch_term_eq (p : PoleEnergy) (ieps x : ℝ) :
    (1 / 2 : ℝ) * (p.w / (x - p.w) * ieps) = p.w ^ 2 * ieps / (2 * p.w * (x - p.w)) :=
  BGW4.ch_term_eq ieps x p.w p.w_ne_zero

/-- The transcribed unoccupied branch equals the S1 empty branch. -/
theorem emptyBranch_eq (p : PoleEnergy) (ieps x : ℝ) :
    BGW4.emptyBranch ieps x p.w = emptyTerm (BGW4.omega2 ieps p.w) x p.w :=
  BGW4.emptyBranch_eq_emptyTerm ieps x p.w p.w_ne_zero

/-- The transcribed generic occupied branch at full occupation equals the S1
raw split expression. Also only needs `w ≠ 0`. -/
theorem occupiedGeneric_eq_raw (p : PoleEnergy) (ieps x : ℝ) :
    BGW4.occupiedGeneric ieps x p.w = rawOccupied (BGW4.omega2 ieps p.w) x p.w :=
  BGW4.occupiedGeneric_eq_rawOccupied ieps x p.w p.w_ne_zero

end PoleEnergy

/-! ## An admissible pole configuration -/

/-- An **admissible pole configuration**: a pole energy `w` together with an
energy offset `x = E - eps` that avoids both the removable pole `x = w` and the
surviving pole `x = -w`. Every side condition of the S1 algebraic cancellation
is a field, so no use site can forget one. -/
structure AdmissiblePole extends PoleEnergy where
  /-- The energy offset `x = E - eps`, in eV. -/
  x : ℝ
  /-- Avoids the removable pole of the raw split expression. -/
  x_ne_pole : x ≠ w
  /-- Avoids the surviving pole shared by both expressions. -/
  x_ne_negPole : x ≠ -w

namespace AdmissiblePole

/-- Explicit constructor from loose hypotheses. This is the *only* place the
three conditions have to be discharged; every consumer below gets them for
free. -/
def mk' {x w : ℝ} (hw : w ≠ 0) (hp : x ≠ w) (hm : x ≠ -w) : AdmissiblePole :=
  { w := w, w_ne_zero := hw, x := x, x_ne_pole := hp, x_ne_negPole := hm }

@[simp] theorem mk'_x {x w : ℝ} (hw : w ≠ 0) (hp : x ≠ w) (hm : x ≠ -w) :
    (mk' hw hp hm).x = x := rfl

@[simp] theorem mk'_w {x w : ℝ} (hw : w ≠ 0) (hp : x ≠ w) (hm : x ≠ -w) :
    (mk' hw hp hm).w = w := rfl

theorem x_sub_w_ne_zero (c : AdmissiblePole) : c.x - c.w ≠ 0 :=
  sub_ne_zero.mpr c.x_ne_pole

theorem x_add_w_ne_zero (c : AdmissiblePole) : c.x + c.w ≠ 0 := fun h =>
  c.x_ne_negPole (by linarith)

/-- The raw split denominator `x^2 - w^2` is nonzero on this domain, so the
totalized Lean division there is the intended mathematical quotient. -/
theorem raw_denom_ne_zero (c : AdmissiblePole) : c.x ^ 2 - c.w ^ 2 ≠ 0 := by
  have h : c.x ^ 2 - c.w ^ 2 = (c.x - c.w) * (c.x + c.w) := by ring
  rw [h]
  exact mul_ne_zero c.x_sub_w_ne_zero c.x_add_w_ne_zero

/-- The screened-exchange denominator `2*w*(x - w)` is nonzero on this domain. -/
theorem sx_denom_ne_zero (c : AdmissiblePole) : 2 * c.w * (c.x - c.w) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero c.w_ne_zero) c.x_sub_w_ne_zero

/-- The merged denominator `2*w*(x + w)` is nonzero on this domain. -/
theorem merged_denom_ne_zero (c : AdmissiblePole) : 2 * c.w * (c.x + c.w) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero c.w_ne_zero) c.x_add_w_ne_zero

/-! ### The bundled expressions -/

/-- The raw split occupied contribution evaluated on an admissible
configuration. -/
noncomputable def raw (c : AdmissiblePole) (A : ℝ) : ℝ := rawOccupied A c.x c.w

/-- The merged occupied contribution evaluated on an admissible
configuration. -/
noncomputable def merged (c : AdmissiblePole) (A : ℝ) : ℝ := occupiedTerm A c.x c.w

/-- The empty (Coulomb-hole only) contribution on an admissible
configuration. -/
noncomputable def emptyValue (c : AdmissiblePole) (A : ℝ) : ℝ := emptyTerm A c.x c.w

@[simp] theorem raw_eq (c : AdmissiblePole) (A : ℝ) :
    c.raw A = rawOccupied A c.x c.w := rfl

@[simp] theorem merged_eq (c : AdmissiblePole) (A : ℝ) :
    c.merged A = occupiedTerm A c.x c.w := rfl

@[simp] theorem emptyValue_eq (c : AdmissiblePole) (A : ℝ) :
    c.emptyValue A = emptyTerm A c.x c.w := rfl

/-- **Algebraic cancellation, hypothesis-free at the use site.** The three side
conditions are supplied by the type. -/
theorem raw_eq_merged (c : AdmissiblePole) (A : ℝ) : c.raw A = c.merged A :=
  rawOccupied_eq_occupiedTerm A c.x c.w c.w_ne_zero c.x_ne_pole c.x_ne_negPole

/-- On this domain the merged value vanishes exactly when the coefficient does.
A statement of this shape is only meaningful once the denominator is known to be
nonzero, which is precisely what the bundle carries. -/
theorem merged_eq_zero_iff (c : AdmissiblePole) (A : ℝ) :
    c.merged A = 0 ↔ A = 0 := by
  rw [merged_eq, occupiedTerm, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h c.merged_denom_ne_zero
  · intro h
    exact Or.inl h

theorem merged_ne_zero (c : AdmissiblePole) {A : ℝ} (hA : A ≠ 0) : c.merged A ≠ 0 :=
  fun h => hA ((c.merged_eq_zero_iff A).mp h)

/-- **BerkeleyGW branch agreement, hypothesis-free at the use site.** -/
theorem branches_agree (c : AdmissiblePole) (ieps : ℝ) :
    BGW4.occupiedGeneric ieps c.x c.w = BGW4.occupiedNearPole ieps c.x c.w :=
  BGW4.branches_agree ieps c.x c.w c.w_ne_zero c.x_ne_pole c.x_ne_negPole

/-- The transcribed near-pole branch equals the merged S1 expression. -/
theorem occupiedNearPole_eq_merged (c : AdmissiblePole) (ieps : ℝ) :
    BGW4.occupiedNearPole ieps c.x c.w = c.merged (BGW4.omega2 ieps c.w) :=
  BGW4.occupiedNearPole_eq_occupiedTerm ieps c.x c.w c.w_ne_zero c.x_ne_pole
    c.x_ne_negPole

/-- The source comment's formula, read with the comment's own `delw`, is the
merged value. Needs only `w ≠ 0` and `x ≠ -w`, both carried here. -/
theorem commentFormula_eq_merged (c : AdmissiblePole) (ieps : ℝ) :
    BGW4.omega2 ieps c.w / (4 * c.w ^ 2) / (1 + BGW4.delwComment c.x c.w) =
      c.merged (BGW4.omega2 ieps c.w) :=
  BGW4.commentFormula_eq_occupiedTerm ieps c.x c.w c.w_ne_zero c.x_ne_negPole

/-- **Exact branch mismatch at partial occupation**, on the bundled domain.
Bundling does not hide the occupation asymmetry of the source: the mismatch is
still present whenever `occ ≠ 1`. -/
theorem branch_mismatch (c : AdmissiblePole) (occ ieps : ℝ) :
    BGW4.occupiedGenericOcc occ ieps c.x c.w - BGW4.occupiedNearPoleOcc occ ieps c.x c.w =
      (1 - occ) * (BGW4.omega2 ieps c.w / (2 * c.w * (c.x + c.w))
        + BGW4.omega2 ieps c.w / ((c.x - c.w) * (c.x + c.w))) :=
  BGW4.branch_mismatch occ ieps c.x c.w c.w_ne_zero c.x_ne_pole c.x_ne_negPole

end AdmissiblePole

/-! ## Bridges to the unbundled statements

The bundled and unbundled forms are inter-derivable. These theorems are the
evidence that nothing was weakened: the bundled identity alone recovers the
original hypothesis-carrying statement, and any bundle is the bundle of its own
components. -/

/-- Bundle-to-loose bridge: `AdmissiblePole.raw_eq_merged` alone reproves the
original unbundled cancellation statement. -/
theorem rawOccupied_eq_occupiedTerm_of_bundled (A x w : ℝ) (hw : w ≠ 0)
    (hp : x ≠ w) (hm : x ≠ -w) : rawOccupied A x w = occupiedTerm A x w :=
  (AdmissiblePole.mk' hw hp hm).raw_eq_merged A

/-- Loose-to-bundle bridge: any admissible configuration is the bundle of its
own components, so the two forms quantify over the same data. -/
theorem AdmissiblePole.eta (c : AdmissiblePole) :
    AdmissiblePole.mk' c.w_ne_zero c.x_ne_pole c.x_ne_negPole = c := rfl

/-- The smaller domain sits inside the larger one as expected. -/
theorem AdmissiblePole.toPoleEnergy_w (c : AdmissiblePole) :
    c.toPoleEnergy.w = c.w := rfl

/-- Near the removable pole the admissible domain is eventually inhabited. This
is the precise reason the punctured-limit theorem must be stated at the
`PoleEnergy` level rather than over `AdmissiblePole`. -/
theorem PoleEnergy.eventually_admissible (p : PoleEnergy) :
    ∀ᶠ x : ℝ in 𝓝[≠] p.w, x ≠ p.w ∧ x ≠ -p.w := by
  have hne : ∀ᶠ x : ℝ in 𝓝[≠] p.w, x ≠ p.w := self_mem_nhdsWithin
  have hneg : ∀ᶠ x : ℝ in 𝓝[≠] p.w, x ≠ -p.w := by
    have hmem : {(-p.w : ℝ)}ᶜ ∈ 𝓝 (p.w : ℝ) :=
      isOpen_compl_singleton.mem_nhds (by simpa using p.pole_ne_negPole)
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Filter.eventually_of_mem hmem fun _ hx => hx)
  filter_upwards [hne, hneg] with x hx hx' using ⟨hx, hx'⟩

/-- On a punctured neighbourhood of the removable pole the raw and merged
expressions agree pointwise, derived here through the bundle. -/
theorem PoleEnergy.eventuallyEq_raw_merged (p : PoleEnergy) (A : ℝ) :
    (fun x : ℝ => rawOccupied A x p.w) =ᶠ[𝓝[≠] p.w]
      fun x : ℝ => occupiedTerm A x p.w := by
  filter_upwards [p.eventually_admissible] with x hx
  exact (AdmissiblePole.mk' p.w_ne_zero hx.1 hx.2).raw_eq_merged A

/-! ## Bridge to the exact rational evaluator (S2)

The bundle is the domain of the *raw split* expression. It is strictly smaller
than the domain of the public checked evaluator, which deliberately accepts an
occupied term at `x = w`. The decidable test below makes that gap explicit and
executable. -/

/-- Decidable rational-level test: is the S1 **raw split** expression defined
for this term's data at energy `E`? This is a stricter test than `Term.check`:
it additionally rejects the removable point `x = w`, and unlike `Term.check` it
does not require `omega > 0`. -/
def Term.rawSplitAdmissible (t : Term) (E : ℚ) : Bool :=
  (t.omega != 0) && (t.offset E != t.omega) && (t.offset E != -t.omega)

theorem Term.rawSplitAdmissible_iff (t : Term) (E : ℚ) :
    t.rawSplitAdmissible E = true ↔
      t.omega ≠ 0 ∧ t.offset E ≠ t.omega ∧ t.offset E ≠ -t.omega := by
  simp [Term.rawSplitAdmissible, and_assoc]

/-- A term whose raw split expression is defined yields an admissible pole
configuration over the reals, obtained by casting the exact rational data. -/
noncomputable def Term.toAdmissiblePole (t : Term) (E : ℚ)
    (h : t.rawSplitAdmissible E = true) : AdmissiblePole :=
  AdmissiblePole.mk' (x := ((E : ℝ) - (t.epsilon : ℝ))) (w := (t.omega : ℝ))
    (by
      have hw := ((t.rawSplitAdmissible_iff E).mp h).1
      exact_mod_cast hw)
    (by
      have hp := ((t.rawSplitAdmissible_iff E).mp h).2.1
      have : ((t.offset E : ℚ) : ℝ) ≠ ((t.omega : ℚ) : ℝ) := by exact_mod_cast hp
      simpa [Term.offset] using this)
    (by
      have hm := ((t.rawSplitAdmissible_iff E).mp h).2.2
      have : ((t.offset E : ℚ) : ℝ) ≠ ((-t.omega : ℚ) : ℝ) := by exact_mod_cast hm
      simpa [Term.offset] using this)

@[simp] theorem Term.toAdmissiblePole_w (t : Term) (E : ℚ)
    (h : t.rawSplitAdmissible E = true) :
    (t.toAdmissiblePole E h).w = (t.omega : ℝ) := rfl

@[simp] theorem Term.toAdmissiblePole_x (t : Term) (E : ℚ)
    (h : t.rawSplitAdmissible E = true) :
    (t.toAdmissiblePole E h).x = (E : ℝ) - (t.epsilon : ℝ) := rfl

/-- For an occupied term on the raw-split domain, the real model value of S2 is
the bundled merged value. -/
theorem Term.valueReal_eq_merged (t : Term) (E : ℚ)
    (h : t.rawSplitAdmissible E = true) (hocc : t.occupied = true) :
    t.valueReal (E : ℝ) = (t.toAdmissiblePole E h).merged (t.coefficient : ℝ) := by
  simp [Term.valueReal, hocc]

/-- ... and therefore also the bundled raw split value. -/
theorem Term.valueReal_eq_raw (t : Term) (E : ℚ)
    (h : t.rawSplitAdmissible E = true) (hocc : t.occupied = true) :
    t.valueReal (E : ℝ) = (t.toAdmissiblePole E h).raw (t.coefficient : ℝ) := by
  rw [t.valueReal_eq_merged E h hocc, AdmissiblePole.raw_eq_merged]

/-- The bundle's conditions imply the evaluator's surviving-denominator
condition, for either branch. -/
theorem Term.rawSplitAdmissible_denom_ne_zero (t : Term) (E : ℚ)
    (h : t.rawSplitAdmissible E = true) : t.denom E ≠ 0 := by
  obtain ⟨hw, hp, hm⟩ := (t.rawSplitAdmissible_iff E).mp h
  have hsub : t.offset E - t.omega ≠ 0 := sub_ne_zero.mpr hp
  have hadd : t.offset E + t.omega ≠ 0 := fun hz => hm (by linarith)
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  cases hocc : t.occupied
  · simpa [Term.denom, hocc] using mul_ne_zero (mul_ne_zero h2 hw) hsub
  · simpa [Term.denom, hocc] using mul_ne_zero (mul_ne_zero h2 hw) hadd

/-- **The gap, exhibited.** The probe `A = 4, w = 1, eps = 0` at `E = 1` sits
exactly at the removable pole. The public checked evaluator accepts it and
returns the continuous extension value `A/(4*w^2) = 1`, while it admits no
`AdmissiblePole`: the raw split expression is undefined there. The bundled type
is therefore NOT the evaluator's domain type. -/
theorem Term.check_ok_rawSplitAdmissible_false :
    (Term.mk 4 1 0 true).check 1 = .ok 1 ∧
      (Term.mk 4 1 0 true).rawSplitAdmissible 1 = false := by
  constructor
  · norm_num [Term.check, Term.denom, Term.offset]
  · norm_num [Term.rawSplitAdmissible, Term.offset]

/-- The empty branch at the removable point is rejected by both notions, so the
bundle and the evaluator agree there. -/
theorem Term.check_error_rawSplitAdmissible_false :
    (Term.mk 4 1 0 false).check 1 = .error (.zeroDenominator (Term.mk 4 1 0 false)) ∧
      (Term.mk 4 1 0 false).rawSplitAdmissible 1 = false := by
  constructor
  · norm_num [Term.check, Term.denom, Term.offset]
  · norm_num [Term.rawSplitAdmissible, Term.offset]

end GW.GPP
