/-
Specification.md, section S1: the scalar screened-exchange / Coulomb-hole
cancellation for a single occupied generalized-plasmon-pole contribution, and
the removable singularity of the merged expression at `x = w`.

All statements here are about real numbers. Nothing in this file claims anything
about BerkeleyGW source code, floating-point arithmetic, or physical accuracy.

Lean division is total: `a / 0 = 0`. The expressions below are therefore
*defined* everywhere as Lean terms, but only the hypotheses stated in each
theorem make them the intended mathematical objects. A value produced with a
vanishing denominator is never a physically defined quantity; the public
checked evaluator in `GW.GPP.FiniteSelfEnergy` rejects such inputs.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace GW.GPP

open Filter Topology

/-! ## Definitions (S1)

`A` is the (real, possibly negative) coefficient in eV^3, `w` the pole energy in
eV, and `x = E - eps` the energy offset in eV. -/

/-- The raw split occupied contribution: Coulomb-hole-like term plus
screened-exchange-like term, before cancellation. Undefined (in the
mathematical sense) at `x = w` and `x = -w`. -/
noncomputable def rawOccupied (A x w : ℝ) : ℝ :=
  -A / (x ^ 2 - w ^ 2) + A / (2 * w * (x - w))

/-- The merged occupied contribution. Its only genuine pole is `x = -w`. -/
noncomputable def occupiedTerm (A x w : ℝ) : ℝ := A / (2 * w * (x + w))

/-- The empty (unoccupied) contribution: Coulomb hole only, no screened-exchange
cancellation, so `x = w` really is a pole of this branch. -/
noncomputable def emptyTerm (A x w : ℝ) : ℝ := A / (2 * w * (x - w))

/-! ## Algebraic cancellation -/

/-- Cancellation in an arbitrary field of characteristic zero. -/
theorem raw_eq_occupied_field {K : Type*} [Field K] [CharZero K]
    (A x w : K) (hw : w ≠ 0) (hp : x - w ≠ 0) (hm : x + w ≠ 0) :
    -A / (x ^ 2 - w ^ 2) + A / (2 * w * (x - w)) = A / (2 * w * (x + w)) := by
  have hsq : x ^ 2 - w ^ 2 ≠ 0 := by
    have : x ^ 2 - w ^ 2 = (x - w) * (x + w) := by ring
    rw [this]
    exact mul_ne_zero hp hm
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  field_simp
  ring

/-- **Algebraic cancellation (S1).** For real `A, x, w` with `w ≠ 0`, `x ≠ w`
and `x ≠ -w`, the raw split occupied expression equals the merged one. -/
theorem rawOccupied_eq_occupiedTerm (A x w : ℝ) (hw : w ≠ 0) (hp : x ≠ w)
    (hm : x ≠ -w) : rawOccupied A x w = occupiedTerm A x w := by
  have hp' : x - w ≠ 0 := sub_ne_zero.mpr hp
  have hm' : x + w ≠ 0 := fun h => hm (by linarith [h])
  simpa [rawOccupied, occupiedTerm] using raw_eq_occupied_field A x w hw hp' hm'

/-- The two excluded points are distinct exactly because `w ≠ 0`; this is what
makes `x = w` a *removable* singularity of the raw expression. -/
theorem pole_ne_pole (w : ℝ) (hw : w ≠ 0) : (w : ℝ) ≠ -w := by
  intro h
  apply hw
  linarith

/-! ## Removable singularity at `x = w` -/

/-- **Extension value (S1).** The merged expression at the removable point. -/
theorem occupiedTerm_at_pole (A w : ℝ) (_hw : w ≠ 0) :
    occupiedTerm A w w = A / (4 * w ^ 2) := by
  unfold occupiedTerm
  congr 1
  ring

/-- The merged denominator does not vanish at `x = w` when `w ≠ 0`. -/
theorem occupied_denom_ne_zero_at_pole (w : ℝ) (hw : w ≠ 0) :
    2 * w * (w + w) ≠ 0 := by
  have : 2 * w * (w + w) = 4 * w ^ 2 := by ring
  rw [this]
  positivity

/-- **Continuity (S1).** The merged occupied expression is continuous at the
removable point `x = w` whenever `w ≠ 0`. -/
theorem continuousAt_occupiedTerm (A w : ℝ) (hw : w ≠ 0) :
    ContinuousAt (fun x : ℝ => occupiedTerm A x w) w := by
  unfold occupiedTerm
  exact ContinuousAt.div continuousAt_const
    (by fun_prop) (occupied_denom_ne_zero_at_pole w hw)

/-- On a punctured neighbourhood of `w` that also excludes `-w`, the raw split
expression agrees with the merged one. Since `w ≠ 0` the point `-w` is at
positive distance from `w`, so `{-w}ᶜ` is already a neighbourhood of `w`. -/
theorem rawOccupied_eventuallyEq_occupiedTerm (A w : ℝ) (hw : w ≠ 0) :
    (fun x : ℝ => rawOccupied A x w) =ᶠ[𝓝[≠] w] fun x : ℝ => occupiedTerm A x w := by
  have hne : ∀ᶠ x : ℝ in 𝓝[≠] w, x ≠ w := self_mem_nhdsWithin
  have hneg : ∀ᶠ x : ℝ in 𝓝[≠] w, x ≠ -w := by
    have hmem : {(-w : ℝ)}ᶜ ∈ 𝓝 (w : ℝ) :=
      isOpen_compl_singleton.mem_nhds (by simpa using pole_ne_pole w hw)
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Filter.eventually_of_mem hmem fun _ hx => hx)
  filter_upwards [hne, hneg] with x hx hx'
  exact rawOccupied_eq_occupiedTerm A x w hw hx hx'

/-- **Punctured limit (S1).** The raw split expression, which is not defined at
`x = w`, tends to the merged value `A / (4 * w ^ 2)` along the punctured
neighbourhood filter at `w`. This is a genuine limit statement, not an
evaluation of the merged formula at a point. -/
theorem tendsto_rawOccupied_nhdsWithin_ne (A w : ℝ) (hw : w ≠ 0) :
    Tendsto (fun x : ℝ => rawOccupied A x w) (𝓝[≠] w) (𝓝 (A / (4 * w ^ 2))) := by
  have hmerged : Tendsto (fun x : ℝ => occupiedTerm A x w) (𝓝[≠] w)
      (𝓝 (occupiedTerm A w w)) :=
    (continuousAt_occupiedTerm A w hw).continuousWithinAt.tendsto
  rw [occupiedTerm_at_pole A w hw] at hmerged
  exact hmerged.congr' (rawOccupied_eventuallyEq_occupiedTerm A w hw).symm

/-! ## The empty branch really is singular at `x = w`

No cancellation happens for an unoccupied state: the empty branch keeps the
`x - w` denominator. We record the fact that its denominator vanishes there, so
the checked evaluator must reject the point (rather than return Lean's
totalized `a / 0 = 0`). -/

theorem empty_denom_zero_at_pole (w : ℝ) : 2 * w * (w - w) = 0 := by ring

end GW.GPP
