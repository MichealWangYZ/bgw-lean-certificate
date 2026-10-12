/- ARCHIVED (2026-10-01): Specification.md v0.1 demo lineage, superseded by GW.Endpoint.Kernel.SigmaSpec and GW.Bridge; kept, not extended, outside the fast gate. See docs/CODEMAP.md.
Specification.md, section S2: the finite scalar model with exact rational
inputs, the real-valued mathematical model obtained by casting, and a checked
executable evaluator whose success implies domain validity.

Units are a documented input contract (S2), not a type-level theorem here:
`E`, `epsilon`, `omega`, `sigmaX` and the result are in eV, so `coefficient` is
in eV^3. `omega` is a pole ENERGY (hbar * angular frequency). `coefficient` may
have either sign; occupancy is binary; the term list keeps multiplicity.

Lean's rational and real division is total (`a / 0 = 0`). The `*Unchecked`
definitions below therefore always elaborate, but a value obtained from a zero
denominator is NOT a physically defined quantity. The public entry point is
`Data.sigmaChecked`, which validates every term before dividing.
-/
import GW.GPP.PoleCancellation
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.List.Basic
import Mathlib.Tactic.FieldSimp

namespace GW.GPP

/-! ## Exact rational input data -/

/-- One contribution: coefficient `A` (eV^3), pole energy `omega` (eV), state
energy `epsilon` (eV), and binary occupancy. -/
structure Term where
  coefficient : ℚ
  omega : ℚ
  epsilon : ℚ
  occupied : Bool
deriving Repr, DecidableEq, Inhabited

/-- A finite model: an external static contribution `sigmaX` (eV) plus a finite
list of terms. The list is *not* deduplicated; repeated entries contribute
repeatedly. An empty list yields `sigmaX`. -/
structure Data where
  sigmaX : ℚ
  terms : List Term
deriving Repr, Inhabited

/-- The energy offset `x = E - eps` of S2. -/
def Term.offset (t : Term) (E : ℚ) : ℚ := E - t.epsilon

/-- The surviving denominator of the selected branch, computed *before* any
division: `2*w*(x+w)` when occupied (merged SX+CH), `2*w*(x-w)` when empty
(CH only). -/
def Term.denom (t : Term) (E : ℚ) : ℚ :=
  2 * t.omega * (if t.occupied then t.offset E + t.omega else t.offset E - t.omega)

/-! ## Unchecked rational evaluation

These helpers perform no validation and rely on Lean's totalized division. They
are exposed only so the finite computation is inspectable; do not read their
output as physical when a denominator vanishes. -/

/-- Unchecked rational value of one term. -/
def Term.valueUnchecked (t : Term) (E : ℚ) : ℚ := t.coefficient / t.denom E

/-- Unchecked rational finite sum `sigmaX + sum_t K(t,E)`. -/
def Data.sigmaUnchecked (D : Data) (E : ℚ) : ℚ :=
  D.sigmaX + (D.terms.map fun t => t.valueUnchecked E).sum

/-! ## Real-valued mathematical model

Obtained by casting the rational data into ℝ and using the S1 branches. -/

/-- Real model value of one term: the merged occupied expression or the empty
(Coulomb-hole) expression, as selected by the occupancy flag. -/
noncomputable def Term.valueReal (t : Term) (E : ℝ) : ℝ :=
  if t.occupied then occupiedTerm (t.coefficient : ℝ) (E - (t.epsilon : ℝ)) (t.omega : ℝ)
  else emptyTerm (t.coefficient : ℝ) (E - (t.epsilon : ℝ)) (t.omega : ℝ)

/-- Real model finite sum. -/
noncomputable def Data.sigmaReal (D : Data) (E : ℝ) : ℝ :=
  (D.sigmaX : ℝ) + (D.terms.map fun t => t.valueReal E).sum

/-! ## Rational-to-real correspondence -/

/-- Casting the rational denominator gives the real denominator of the selected
branch. -/
theorem Term.denom_cast (t : Term) (E : ℚ) :
    ((t.denom E : ℚ) : ℝ) =
      2 * (t.omega : ℝ) *
        (if t.occupied then ((E : ℝ) - (t.epsilon : ℝ)) + (t.omega : ℝ)
         else ((E : ℝ) - (t.epsilon : ℝ)) - (t.omega : ℝ)) := by
  cases h : t.occupied <;> simp [Term.denom, Term.offset, h]

/-- **Rational-to-real term correspondence (S2).** -/
theorem Term.valueUnchecked_cast (t : Term) (E : ℚ) :
    ((t.valueUnchecked E : ℚ) : ℝ) = t.valueReal (E : ℝ) := by
  cases h : t.occupied <;>
    simp [Term.valueUnchecked, Term.valueReal, Term.denom, Term.offset,
      occupiedTerm, emptyTerm, h]

/-- Cast of a finite rational term sum is the real term sum. -/
theorem list_sum_valueUnchecked_cast (ts : List Term) (E : ℚ) :
    (((ts.map fun t => t.valueUnchecked E).sum : ℚ) : ℝ) =
      (ts.map fun t => t.valueReal (E : ℝ)).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [Rat.cast_add, ih, Term.valueUnchecked_cast]

/-- **Rational-to-real finite-sum correspondence (S2).** -/
theorem Data.sigmaUnchecked_cast (D : Data) (E : ℚ) :
    ((D.sigmaUnchecked E : ℚ) : ℝ) = D.sigmaReal (E : ℝ) := by
  simp [Data.sigmaUnchecked, Data.sigmaReal, list_sum_valueUnchecked_cast]

/-! ## Checked public evaluator -/

/-- Why a term was rejected. Rejection is a domain restriction of this scalar
model, not a claim about every BerkeleyGW branch. -/
inductive EvalError where
  /-- Pole energy is zero or negative; `w` must be a strictly positive energy. -/
  | nonpositiveOmega (t : Term)
  /-- The surviving denominator of the selected branch vanishes. -/
  | zeroDenominator (t : Term)
deriving Repr, DecidableEq, Inhabited

/-- Checked value of one term. Validity is tested before any division and does
not depend on the coefficient, so a term with `A = 0` is rejected exactly when
its data is invalid. An occupied term at `x = w` with `w > 0` is accepted: that
is the intended continuous extension of S1, not a pole. -/
def Term.check (t : Term) (E : ℚ) : Except EvalError ℚ :=
  if t.omega ≤ 0 then .error (.nonpositiveOmega t)
  else if t.denom E = 0 then .error (.zeroDenominator t)
  else .ok (t.coefficient / t.denom E)

/-- Checked values of a whole list, failing on the first invalid term. -/
def checkedValues : List Term → ℚ → Except EvalError (List ℚ)
  | [], _ => .ok []
  | t :: ts, E =>
    match t.check E with
    | .error e => .error e
    | .ok v =>
      match checkedValues ts E with
      | .error e => .error e
      | .ok vs => .ok (v :: vs)

/-- **Public entry point.** Returns `sigmaX + sum_t K(t,E)` only if every term
has a strictly positive pole energy and a nonzero surviving denominator. -/
def Data.sigmaChecked (D : Data) (E : ℚ) : Except EvalError ℚ :=
  match checkedValues D.terms E with
  | .error e => .error e
  | .ok vs => .ok (D.sigmaX + vs.sum)

/-! ## Soundness of the checked evaluator -/

theorem Term.check_ok_omega_pos {t : Term} {E v : ℚ} (h : t.check E = .ok v) :
    0 < t.omega := by
  unfold Term.check at h
  by_cases h1 : t.omega ≤ 0
  · simp [h1] at h
  · exact lt_of_not_ge h1

theorem Term.check_ok_denom_ne_zero {t : Term} {E v : ℚ} (h : t.check E = .ok v) :
    t.denom E ≠ 0 := by
  unfold Term.check at h
  by_cases h1 : t.omega ≤ 0
  · simp [h1] at h
  · by_cases h2 : t.denom E = 0
    · simp [h1, h2] at h
    · exact h2

theorem Term.check_ok_eq {t : Term} {E v : ℚ} (h : t.check E = .ok v) :
    v = t.valueUnchecked E := by
  unfold Term.check at h
  by_cases h1 : t.omega ≤ 0
  · simp [h1] at h
  · by_cases h2 : t.denom E = 0
    · simp [h1, h2] at h
    · rw [if_neg h1, if_neg h2] at h
      have hv := Except.ok.inj h
      simp [Term.valueUnchecked, ← hv]

theorem checkedValues_ok_valid {ts : List Term} {E : ℚ} {vs : List ℚ}
    (h : checkedValues ts E = .ok vs) :
    ∀ t ∈ ts, 0 < t.omega ∧ t.denom E ≠ 0 := by
  induction ts generalizing vs with
  | nil => intro t ht; cases ht
  | cons t ts ih =>
    intro u hu
    rw [checkedValues] at h
    cases hc : t.check E with
    | error e => rw [hc] at h; exact absurd h (by simp)
    | ok v =>
      rw [hc] at h
      cases hr : checkedValues ts E with
      | error e => rw [hr] at h; exact absurd h (by simp)
      | ok ws =>
        rcases List.mem_cons.mp hu with rfl | hmem
        · exact ⟨Term.check_ok_omega_pos hc, Term.check_ok_denom_ne_zero hc⟩
        · exact ih hr u hmem

theorem checkedValues_ok_eq {ts : List Term} {E : ℚ} {vs : List ℚ}
    (h : checkedValues ts E = .ok vs) :
    vs = ts.map fun t => t.valueUnchecked E := by
  induction ts generalizing vs with
  | nil => rw [checkedValues] at h; simpa using h.symm
  | cons t ts ih =>
    rw [checkedValues] at h
    cases hc : t.check E with
    | error e => rw [hc] at h; exact absurd h (by simp)
    | ok v =>
      rw [hc] at h
      cases hr : checkedValues ts E with
      | error e => rw [hr] at h; exact absurd h (by simp)
      | ok ws =>
        rw [hr] at h
        have : v :: ws = vs := by simpa using h
        rw [← this, List.map_cons, ih hr, Term.check_ok_eq hc]

/-- **Domain validity (S2).** Successful checked evaluation implies every pole
energy is strictly positive and every selected denominator is nonzero. -/
theorem Data.sigmaChecked_ok_valid {D : Data} {E s : ℚ}
    (h : D.sigmaChecked E = .ok s) :
    ∀ t ∈ D.terms, 0 < t.omega ∧ t.denom E ≠ 0 := by
  unfold Data.sigmaChecked at h
  cases hr : checkedValues D.terms E with
  | error e => rw [hr] at h; exact absurd h (by simp)
  | ok vs => exact checkedValues_ok_valid hr

/-- Successful checked evaluation returns exactly the unchecked rational sum. -/
theorem Data.sigmaChecked_ok_eq_unchecked {D : Data} {E s : ℚ}
    (h : D.sigmaChecked E = .ok s) : s = D.sigmaUnchecked E := by
  unfold Data.sigmaChecked at h
  cases hr : checkedValues D.terms E with
  | error e => rw [hr] at h; exact absurd h (by simp)
  | ok vs =>
    rw [hr] at h
    have hs : D.sigmaX + vs.sum = s := by simpa using h
    rw [← hs, Data.sigmaUnchecked, checkedValues_ok_eq hr]

/-- **Checked evaluation soundness (S2).** A successful checked evaluation
returns precisely the real finite sum after casting. -/
theorem Data.sigmaChecked_ok_eq_real {D : Data} {E s : ℚ}
    (h : D.sigmaChecked E = .ok s) : (s : ℝ) = D.sigmaReal (E : ℝ) := by
  rw [Data.sigmaChecked_ok_eq_unchecked h, Data.sigmaUnchecked_cast]

/-- The empty list returns the static contribution alone. -/
theorem Data.sigmaChecked_nil (sx E : ℚ) :
    Data.sigmaChecked ⟨sx, []⟩ E = .ok sx := by
  simp [Data.sigmaChecked, checkedValues]

/-- An occupied term exactly at the removable pole `x = w` with `w > 0` is
accepted and returns the continuous extension value `A / (4 * w ^ 2)`. -/
theorem Term.check_occupied_at_pole {t : Term} {E : ℚ} (hocc : t.occupied = true)
    (hw : 0 < t.omega) (hx : t.offset E = t.omega) :
    t.check E = .ok (t.coefficient / (4 * t.omega ^ 2)) := by
  have hd : t.denom E = 4 * t.omega ^ 2 := by
    simp only [Term.denom, hocc, hx, if_true]
    ring
  have hne : t.denom E ≠ 0 := by
    rw [hd]; positivity
  unfold Term.check
  rw [if_neg (not_le.mpr hw), if_neg hne, hd]

end GW.GPP
