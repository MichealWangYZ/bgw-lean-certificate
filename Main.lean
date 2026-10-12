/- ARCHIVED (2026-10-01): Specification.md v0.1 demo lineage, superseded by GW.Endpoint.Kernel.SigmaSpec and GW.Bridge; kept, not extended, outside the fast gate. See docs/CODEMAP.md.
Command line front end for the GPP pole-cancellation demo.

Every printed number and boolean below is produced by an actual call to the
checked evaluator `GW.GPP.Data.sigmaChecked` / `GW.GPP.Term.check`; nothing is
hardcoded from `Specification.md`. The executable, the Lean compiler, and the
runtime are a separate trust boundary from the kernel-checked proofs: a
successful run does not verify the compiler or the runtime.
-/
import GW
import Lean.Data.Json

open GW.GPP GW.Examples

namespace GW.Demo

/-- Canonical rational rendering: `2/3`, `-11/6`, and `2` (never `2/1`). This is
the `Rat` `ToString` instance, which already normalises. -/
def fmtRat (q : ℚ) : String := toString q

/-- Did the checked evaluator reject this input? -/
def rejected (r : Except EvalError ℚ) : Bool :=
  match r with
  | .error _ => true
  | .ok _ => false

/-- Extract a value that the demo expects to be accepted, failing loudly (and
with a nonzero exit code) if the evaluator rejected it. -/
def expectOk (name : String) (r : Except EvalError ℚ) : IO ℚ :=
  match r with
  | .ok v => pure v
  | .error e => throw <| IO.userError s!"unexpected rejection in {name}: {reprStr e}"

/-- Render a rejection for the human-readable report. -/
def showResult (r : Except EvalError ℚ) : String :=
  match r with
  | .ok v => fmtRat v
  | .error (.nonpositiveOmega t) =>
      s!"rejected: pole energy w = {fmtRat t.omega} is not strictly positive"
  | .error (.zeroDenominator t) =>
      s!"rejected: surviving denominator of the " ++
        (if t.occupied then "occupied" else "empty") ++ " branch is zero"

/-- The five rejection / acceptance probes of the JSON schema, each computed. -/
def probeAtPole : Except EvalError ℚ := probe.check fixtureEnergy
def probeZeroOmegaResult : Except EvalError ℚ := probeZeroOmega.check fixtureEnergy
def probeNegativeOmegaResult : Except EvalError ℚ := probeNegativeOmega.check fixtureEnergy
def probeOccupiedPoleResult : Except EvalError ℚ := probe.check (-1)
def probeEmptyPoleResult : Except EvalError ℚ := probeEmptyBranch.check fixtureEnergy

/-- Stable JSON schema required by T-001 section C. -/
def jsonReport : IO String := do
  let values ← match checkedValues fixture.terms fixtureEnergy with
    | .ok vs => pure vs
    | .error e => throw <| IO.userError s!"unexpected rejection in fixture: {reprStr e}"
  let sigma ← expectOk "fixture sigma" (fixture.sigmaChecked fixtureEnergy)
  let atPole ← expectOk "occupied_at_pole" probeAtPole
  let emptySum ← expectOk "empty_sum" (emptyFixture.sigmaChecked fixtureEnergy)
  pure <| (Lean.Json.mkObj [
    ("fixture", .str "synthetic-three-term-v1"),
    ("terms", .arr (values.map fun v => Lean.Json.str (fmtRat v)).toArray),
    ("sigma", .str (fmtRat sigma)),
    ("occupied_at_pole", .str (fmtRat atPole)),
    ("reject_zero_omega", .bool (rejected probeZeroOmegaResult)),
    ("reject_negative_omega", .bool (rejected probeNegativeOmegaResult)),
    ("reject_occupied_pole", .bool (rejected probeOccupiedPoleResult)),
    ("reject_empty_pole", .bool (rejected probeEmptyPoleResult)),
    ("empty_sum", .str (fmtRat emptySum))
  ]).compress

def describeTerm (t : Term) : String :=
  s!"A = {fmtRat t.coefficient} eV^3, w = {fmtRat t.omega} eV, eps = " ++
    s!"{fmtRat t.epsilon} eV, " ++ (if t.occupied then "occupied" else "empty")

def humanReport : IO Unit := do
  IO.println "GPP pole-cancellation demo (synthetic-three-term-v1)"
  IO.println "Artificial exact-rational fixture from Specification.md S3."
  IO.println "Not a material, not a BerkeleyGW export, not a measurement."
  IO.println ""
  IO.println s!"E = {fmtRat fixtureEnergy} eV, sigmaX = {fmtRat fixture.sigmaX} eV"
  IO.println "Per-term checked values (eV):"
  for t in fixture.terms do
    IO.println s!"  {describeTerm t}"
    IO.println s!"    K = {showResult (t.check fixtureEnergy)}"
  let sigma ← expectOk "fixture sigma" (fixture.sigmaChecked fixtureEnergy)
  IO.println s!"Sigma = {fmtRat sigma} eV"
  IO.println ""
  IO.println "Empty term list (static contribution only):"
  IO.println s!"  Sigma = {showResult (emptyFixture.sigmaChecked fixtureEnergy)} eV"
  IO.println ""
  IO.println "Removable occupied pole, A = 4 eV^3, x = w = 1 eV:"
  IO.println s!"  merged value = {showResult probeAtPole} eV"
  IO.println "  the raw split expression is undefined there; the merged branch"
  IO.println "  is its continuous extension (GW.GPP.tendsto_rawOccupied_nhdsWithin_ne)."
  IO.println ""
  IO.println "Rejection cases (checked before any division):"
  IO.println s!"  w = 0            -> {showResult probeZeroOmegaResult}"
  IO.println s!"  w = -1           -> {showResult probeNegativeOmegaResult}"
  IO.println s!"  occupied x = -w  -> {showResult probeOccupiedPoleResult}"
  IO.println s!"  empty x = w      -> {showResult probeEmptyPoleResult}"

def usage : String :=
  "usage: gpp_demo [--json]\n\n" ++
  "  (no flag)  human-readable report of the synthetic three-term fixture\n" ++
  "  --json     stable machine-readable report for the supervisor oracle\n"

end GW.Demo

open GW.Demo in
def main (args : List String) : IO UInt32 := do
  match args with
  | [] => do
    humanReport
    pure 0
  | ["--json"] => do
    IO.println (← jsonReport)
    pure 0
  | _ => do
    (← IO.getStderr).putStr s!"gpp_demo: unknown arguments: {String.intercalate " " args}\n{usage}"
    pure 1
