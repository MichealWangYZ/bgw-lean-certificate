import GW.GPP.FiniteSelfEnergy
import GW.GPP.PoleDomain

open GW.GPP

def rejected {alpha : Type} : Except EvalError alpha -> Bool
  | .error _ => true
  | .ok _ => false

def equalsOk (result : Except EvalError Rat) (expected : Rat) : Bool :=
  match result with
  | .ok value => value == expected
  | .error _ => false

def main : IO Unit := do
  let first : Term := { coefficient := 8, omega := 2, epsilon := 0, occupied := true }
  let second : Term := { coefficient := 6, omega := 3, epsilon := -1, occupied := false }
  let third : Term := { coefficient := -4, omega := 1, epsilon := 0, occupied := true }
  let terms := [first, second, third]
  let evaluate := fun ts => (Data.mk ((-1 : Rat) / 2) ts).sigmaChecked 1
  let expected : Rat := (-11 : Rat) / 6
  let probe : Term := { coefficient := 4, omega := 1, epsilon := 0, occupied := true }
  let tests : List (Prod String Bool) := [
    ("fixture", equalsOk (evaluate terms) expected),
    ("reordered", equalsOk (evaluate terms.reverse) expected),
    ("multiplicity", equalsOk (evaluate (terms ++ terms)) ((-19 : Rat) / 6)),
    ("empty sum", equalsOk (evaluate []) ((-1 : Rat) / 2)),
    ("removable pole", equalsOk (probe.check 1) 1),
    ("occupied surviving pole", rejected (probe.check (-1))),
    ("empty surviving pole", rejected ({ probe with occupied := false }.check 1)),
    ("zero omega", rejected ({ probe with omega := 0 }.check 1)),
    ("negative omega", rejected ({ probe with omega := -1 }.check 1)),
    ("zero coefficient cannot hide occupied pole", rejected ({ probe with coefficient := 0 }.check (-1))),
    ("zero coefficient cannot hide empty pole", rejected ({ probe with coefficient := 0, occupied := false }.check 1)),
    ("zero coefficient cannot hide zero omega", rejected ({ probe with coefficient := 0, omega := 0 }.check 1)),
    ("invalid tail cannot be omitted", rejected (evaluate (terms ++ [{ probe with omega := 0 }]))),
    ("occupancy mutant", !equalsOk (evaluate [{ first with occupied := false }, second, third]) expected),
    ("coefficient mutant", !equalsOk (evaluate [{ first with coefficient := 1 }, second, third]) expected),
    ("sign mutant", !equalsOk (evaluate [{ first with coefficient := -8 }, second, third]) expected),
    ("missing term mutant", !equalsOk (evaluate [first, second]) expected),
    -- The raw-split domain (`GW/GPP/PoleDomain.lean`) is STRICTLY SMALLER than
    -- the checked evaluator's domain: it also excludes the removable pole.
    ("raw-split domain accepts a generic occupied term", first.rawSplitAdmissible 1),
    ("raw-split domain accepts a generic empty term", second.rawSplitAdmissible 1),
    ("raw-split domain rejects the removable pole", !probe.rawSplitAdmissible 1),
    ("evaluator still accepts the removable pole", equalsOk (probe.check 1) 1),
    ("raw-split domain rejects the surviving pole", !probe.rawSplitAdmissible (-1)),
    ("raw-split domain rejects zero omega", !({ probe with omega := 0 }.rawSplitAdmissible 1)),
    ("raw-split domain ignores the coefficient", { probe with coefficient := 0 }.rawSplitAdmissible 2),
    ("raw-split domain ignores occupancy", { probe with occupied := false }.rawSplitAdmissible 2),
    ("raw-split domain admits negative omega the evaluator rejects",
      { probe with omega := -1 }.rawSplitAdmissible 3 && rejected ({ probe with omega := -1 }.check 3)),
    ("fixture term 3 is exactly at the removable pole", !third.rawSplitAdmissible 1)
  ]
  for (label, passed) in tests do
    unless passed do
      throw (IO.userError s!"FAILED: {label}")
  IO.println s!"PASS: {tests.length} independent Lean runtime edge and mutation checks"
