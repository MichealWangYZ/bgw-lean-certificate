/- ARCHIVED (2026-10-01): Specification.md v0.1 demo lineage, superseded by GW.Endpoint.Kernel.SigmaSpec and GW.Bridge; kept, not extended, outside the fast gate. See docs/CODEMAP.md.
Specification.md, section S3: the mandatory synthetic fixture, its exact
rational values, rejection cases, reordering, and mutant checks.

These are finite sample computations about specific inputs. They are NOT
theorems about arbitrary inputs; the general statements live in
`GW.GPP.PoleCancellation` and `GW.GPP.FiniteSelfEnergy`. The fixture is
artificial: it is not a material, a BerkeleyGW export, or a measurement.

Kernel note: rational arithmetic does not reduce under `decide` in this
toolchain (`Rat.mul`/`Rat.inv` get stuck), so the sample facts below are proved
with `norm_num` and `simp only` on the defining equations. `native_decide` is
never used.
-/
import GW.GPP.FiniteSelfEnergy
import Mathlib.Tactic.NormNum

namespace GW.Examples

open GW.GPP

/-! ## The synthetic three-term fixture (S3) -/

/-- Evaluation energy `E = 1` eV. -/
def fixtureEnergy : ℚ := 1

/-- `A = 8`, `w = 2`, `eps = 0`, occupied. Expected value `2/3`. -/
def term1 : Term := { coefficient := 8, omega := 2, epsilon := 0, occupied := true }

/-- `A = 6`, `w = 3`, `eps = -1`, empty. Expected value `-1`. -/
def term2 : Term := { coefficient := 6, omega := 3, epsilon := -1, occupied := false }

/-- `A = -4`, `w = 1`, `eps = 0`, occupied: exactly at the removable occupied
pole `x = w = 1`. Its raw split expression is undefined; the merged value `-1`
is used. -/
def term3 : Term := { coefficient := -4, omega := 1, epsilon := 0, occupied := true }

/-- The fixture: `sigmaX = -1/2` eV plus the three terms above. -/
def fixture : Data := { sigmaX := -1/2, terms := [term1, term2, term3] }

/-- A model with no dynamic terms and the same nonzero static contribution. -/
def emptyFixture : Data := { sigmaX := -1/2, terms := [] }

/-- Probe term of the JSON schema: `A = 4`, `w = 1`, `eps = 0`, occupied. At
`E = 1` it sits exactly on the removable occupied pole. -/
def probe : Term := { coefficient := 4, omega := 1, epsilon := 0, occupied := true }

/-- Per-term checked values of the fixture, as actually computed. -/
def fixtureTermValues : Except EvalError (List ℚ) :=
  checkedValues fixture.terms fixtureEnergy

/-! ## Exact per-term values -/

theorem term1_value : term1.check fixtureEnergy = .ok (2/3) := by
  norm_num [Term.check, Term.denom, Term.offset, term1, fixtureEnergy]

theorem term2_value : term2.check fixtureEnergy = .ok (-1) := by
  norm_num [Term.check, Term.denom, Term.offset, term2, fixtureEnergy]

theorem term3_value : term3.check fixtureEnergy = .ok (-1) := by
  norm_num [Term.check, Term.denom, Term.offset, term3, fixtureEnergy]

theorem fixtureTermValues_eq : fixtureTermValues = .ok [2/3, -1, -1] := by
  simp only [fixtureTermValues, fixture, checkedValues, term1_value, term2_value,
    term3_value]

/-- The fixture total of S3. -/
theorem fixture_sigma : fixture.sigmaChecked fixtureEnergy = .ok (-11/6) := by
  have h : checkedValues [term1, term2, term3] fixtureEnergy = .ok [2/3, -1, -1] :=
    fixtureTermValues_eq
  simp only [Data.sigmaChecked, h, fixture]
  norm_num

/-- An empty term list returns the nonzero static contribution alone. -/
theorem emptyFixture_sigma : emptyFixture.sigmaChecked fixtureEnergy = .ok (-1/2) :=
  Data.sigmaChecked_nil _ _

/-- Term 3 is exactly at the removable occupied pole, and is accepted because
`w > 0`: this is the intended continuous extension, not a division by zero. -/
theorem term3_at_removable_pole : term3.offset fixtureEnergy = term3.omega := by
  norm_num [Term.offset, term3, fixtureEnergy]

/-- The probe value at the removable occupied pole, `A = 4`, `x = w = 1`, is
`A / (4 w^2) = 1`. -/
theorem probe_at_pole : probe.check fixtureEnergy = .ok 1 := by
  norm_num [Term.check, Term.denom, Term.offset, probe, fixtureEnergy]

/-- The same value also follows from the general continuous-extension theorem
`Term.check_occupied_at_pole`, rather than from a one-off computation. -/
theorem probe_at_pole_general :
    probe.check fixtureEnergy = .ok (probe.coefficient / (4 * probe.omega ^ 2)) :=
  Term.check_occupied_at_pole (by rfl) (by norm_num [probe])
    (by norm_num [Term.offset, probe, fixtureEnergy])

/-! ## Reordering and multiplicity

The sum is over a finite list with multiplicity: reordering must not change the
total, and a repeated entry must contribute twice. -/

def reorderedFixture : Data := { sigmaX := -1/2, terms := [term3, term1, term2] }

theorem reordered_sigma :
    reorderedFixture.sigmaChecked fixtureEnergy = fixture.sigmaChecked fixtureEnergy := by
  have h : checkedValues [term3, term1, term2] fixtureEnergy = .ok [-1, 2/3, -1] := by
    simp only [checkedValues, term1_value, term2_value, term3_value]
  rw [fixture_sigma]
  simp only [Data.sigmaChecked, h, reorderedFixture]
  norm_num

def duplicatedFixture : Data := { sigmaX := -1/2, terms := [term1, term1] }

theorem duplicated_sigma :
    duplicatedFixture.sigmaChecked fixtureEnergy = .ok (-1/2 + 2/3 + 2/3) := by
  have h : checkedValues [term1, term1] fixtureEnergy = .ok [2/3, 2/3] := by
    simp only [checkedValues, term1_value]
  simp only [Data.sigmaChecked, h, duplicatedFixture]
  norm_num

/-! ## Rejection cases

Validity is checked before dividing, so Lean's totalized `a / 0 = 0` never
escapes as a physical value. -/

def probeZeroOmega : Term := { probe with omega := 0 }
def probeNegativeOmega : Term := { probe with omega := -1 }
def probeEmptyBranch : Term := { probe with occupied := false }
def probeZeroCoeffZeroOmega : Term := { probe with coefficient := 0, omega := 0 }
def probeZeroCoeffEmptyBranch : Term :=
  { probe with coefficient := 0, occupied := false }

/-- Zero pole energy is rejected. -/
theorem reject_zero_omega :
    probeZeroOmega.check fixtureEnergy = .error (.nonpositiveOmega probeZeroOmega) := by
  norm_num [Term.check, probeZeroOmega, probe]

/-- Negative pole energy is rejected. -/
theorem reject_negative_omega :
    probeNegativeOmega.check fixtureEnergy =
      .error (.nonpositiveOmega probeNegativeOmega) := by
  norm_num [Term.check, probeNegativeOmega, probe]

/-- The surviving occupied pole `x = -w` is rejected. Here `E = -1`, `eps = 0`,
`w = 1`, so `x + w = 0`. -/
theorem reject_occupied_pole :
    probe.check (-1) = .error (.zeroDenominator probe) := by
  norm_num [Term.check, Term.denom, Term.offset, probe]

/-- The empty branch has no screened-exchange cancellation, so `x = w` is a
genuine pole of that branch and is rejected. -/
theorem reject_empty_pole :
    probeEmptyBranch.check fixtureEnergy = .error (.zeroDenominator probeEmptyBranch) := by
  norm_num [Term.check, Term.denom, Term.offset, probeEmptyBranch, probe, fixtureEnergy]

/-- Invalid data is rejected even when the coefficient is zero: a vanishing
numerator does not make a vanishing denominator meaningful. -/
theorem reject_zero_coefficient_zero_omega :
    probeZeroCoeffZeroOmega.check fixtureEnergy =
      .error (.nonpositiveOmega probeZeroCoeffZeroOmega) := by
  norm_num [Term.check, probeZeroCoeffZeroOmega, probe]

theorem reject_zero_coefficient_pole :
    probeZeroCoeffEmptyBranch.check fixtureEnergy =
      .error (.zeroDenominator probeZeroCoeffEmptyBranch) := by
  norm_num [Term.check, Term.denom, Term.offset, probeZeroCoeffEmptyBranch, probe,
    fixtureEnergy]

/-- One invalid term rejects the whole model. -/
def fixtureWithInvalidTerm : Data := { sigmaX := -1/2, terms := [term1, probeZeroOmega] }

theorem reject_model_with_invalid_term :
    fixtureWithInvalidTerm.sigmaChecked fixtureEnergy =
      .error (.nonpositiveOmega probeZeroOmega) := by
  simp only [Data.sigmaChecked, fixtureWithInvalidTerm, checkedValues, term1_value,
    reject_zero_omega]

/-! ## Mutants

Each mutated fixture must differ from the specified total `-11/6`. -/

def mutantBranch : Data :=
  { sigmaX := -1/2, terms := [{ term1 with occupied := false }, term2, term3] }
def mutantCoefficient : Data :=
  { sigmaX := -1/2, terms := [{ term1 with coefficient := 9 }, term2, term3] }
def mutantSign : Data :=
  { sigmaX := -1/2, terms := [term1, term2, { term3 with coefficient := 4 }] }
def mutantMissingTerm : Data := { sigmaX := -1/2, terms := [term1, term2] }
def mutantStatic : Data := { sigmaX := 0, terms := [term1, term2, term3] }

/-- Branch mutant: term 1 marked empty instead of occupied. -/
theorem mutant_branch_ne :
    mutantBranch.sigmaChecked fixtureEnergy ≠ .ok (-11/6) := by
  have hv : ({ term1 with occupied := false } : Term).check fixtureEnergy = .ok (-2) := by
    norm_num [Term.check, Term.denom, Term.offset, term1, fixtureEnergy]
  have h : checkedValues [{ term1 with occupied := false }, term2, term3] fixtureEnergy
      = .ok [-2, -1, -1] := by
    simp only [checkedValues, hv, term2_value, term3_value]
  simp only [Data.sigmaChecked, h, mutantBranch]
  norm_num

/-- Coefficient mutant. -/
theorem mutant_coefficient_ne :
    mutantCoefficient.sigmaChecked fixtureEnergy ≠ .ok (-11/6) := by
  have hv : ({ term1 with coefficient := 9 } : Term).check fixtureEnergy = .ok (3/4) := by
    norm_num [Term.check, Term.denom, Term.offset, term1, fixtureEnergy]
  have h : checkedValues [{ term1 with coefficient := 9 }, term2, term3] fixtureEnergy
      = .ok [3/4, -1, -1] := by
    simp only [checkedValues, hv, term2_value, term3_value]
  simp only [Data.sigmaChecked, h, mutantCoefficient]
  norm_num

/-- Sign mutant: the negative coefficient of term 3 flipped positive. -/
theorem mutant_sign_ne : mutantSign.sigmaChecked fixtureEnergy ≠ .ok (-11/6) := by
  have hv : ({ term3 with coefficient := 4 } : Term).check fixtureEnergy = .ok 1 := by
    norm_num [Term.check, Term.denom, Term.offset, term3, fixtureEnergy]
  have h : checkedValues [term1, term2, { term3 with coefficient := 4 }] fixtureEnergy
      = .ok [2/3, -1, 1] := by
    simp only [checkedValues, term1_value, term2_value, hv]
  simp only [Data.sigmaChecked, h, mutantSign]
  norm_num

/-- Missing-term mutant. -/
theorem mutant_missing_term_ne :
    mutantMissingTerm.sigmaChecked fixtureEnergy ≠ .ok (-11/6) := by
  have h : checkedValues [term1, term2] fixtureEnergy = .ok [2/3, -1] := by
    simp only [checkedValues, term1_value, term2_value]
  simp only [Data.sigmaChecked, h, mutantMissingTerm]
  norm_num

/-- Static-contribution mutant: `sigmaX` really enters the total. -/
theorem mutant_static_ne : mutantStatic.sigmaChecked fixtureEnergy ≠ .ok (-11/6) := by
  have h : checkedValues [term1, term2, term3] fixtureEnergy = .ok [2/3, -1, -1] := by
    simp only [checkedValues, term1_value, term2_value, term3_value]
  simp only [Data.sigmaChecked, h, mutantStatic]
  norm_num

/-! ## Transfer to the real model

The rational fixture result is exactly the real finite-sum model at `E = 1`.
This uses the general soundness theorem, not a separate real computation. -/

theorem fixture_sigmaReal : fixture.sigmaReal ((fixtureEnergy : ℚ) : ℝ) = ((-11/6 : ℚ) : ℝ) :=
  (Data.sigmaChecked_ok_eq_real fixture_sigma).symm

end GW.Examples
