"""SCIENTIFIC GATE: soundness of the T-005 occupation analyzer.

Origin: an independent audit on branch `audit/checker-soundness-20260914`
found three ways the checker reported success on invalid input. On the
reviewed base `374459f` five of these eight were RED. They are green here
because `bgw/branch_boundary/analyze.py` was repaired, not because the tests
were weakened -- the repair is in the analyzer and these assertions are
unchanged in substance.

What they cover, and why each is a silent pass rather than an ordinary bug:

* **F1 non-finite input.** `abs(nan - x) > 0` is False, so a NaN passed the
  delta-consistency check; `max(0.0, nan)` is 0.0, so it then vanished from
  the reported maximum. An invalid observation produced perfect-looking
  metrics.
* **F2 correlated oracle.** The report compared `gen_value - np_value` against
  the driver's own `closed_form` column, so scaling all four together left
  every error metric at zero. The oracle is now recomputed from `occ`, `ieps`,
  `wt`, `wxt` -- and the driver's column is checked separately as an output.
* **F3 coverage.** The report looped over OCCCHK, so a deleted row silently
  dropped a point and a duplicated `(point, occ)` was silently overwritten.

These tests import the production analyzer, never a replacement. Inputs are
synthetic local-kernel candidates, not BerkeleyGW material data.

Live under `tests/` rather than in a parallel audit tree, on the audit's own
recommendation: a second test framework outside the gate is a place for
regressions to rot unnoticed.
"""
from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "audit_boundary_analyze", ROOT / "bgw/branch_boundary/analyze.py"
)
assert SPEC is not None and SPEC.loader is not None
analyze = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(analyze)

OCC_COLUMNS = (
    "point occ ieps wt wxt gen_value np_value delta closed_form"
).split()
CHECK_COLUMNS = "point ratio_ref max_rel_spread".split()
OCCUPATIONS = (1.0, 0.75, 0.5, 0.25)


def fixture() -> dict:
    """Four nonsingular points, with all candidate values exactly binary64.

    x=3*w and Omega2=w*w*ieps give
      generic = ieps*(1/4 - occ/8), near = ieps*occ/8,
      delta = ieps*(1-occ)/4.
    Hence no tolerance/roundoff ambiguity is needed to construct these cases.
    """
    rows, checks = [], []
    for i, scale in enumerate((1.0, 2.0, 4.0, 8.0), start=1):
        point = f"P{i}"
        for occ in OCCUPATIONS:
            generic = scale * (0.25 - occ / 8.0)
            near = scale * occ / 8.0
            rows.append(dict(
                point=point, occ=occ, ieps=scale, wt=scale, wxt=3.0*scale,
                gen_value=generic, np_value=near, delta=generic-near,
                closed_form=scale*(1.0-occ)/4.0,
            ))
        checks.append(dict(point=point, ratio_ref=scale/4.0, max_rel_spread=0.0))
    return {"OCC": rows, "OCCCHK": checks}


def table(data: dict) -> str:
    lines = []
    for tag, columns in (("OCC", OCC_COLUMNS), ("OCCCHK", CHECK_COLUMNS)):
        lines.append("# COLUMNS " + tag + " " + " ".join(columns))
        for row in data[tag]:
            lines.append(tag + " " + " ".join(str(row[name]) for name in columns))
    return "\n".join(lines) + "\n"


def report(data: dict) -> dict:
    return analyze.occupation_report(analyze.parse_text(table(data)))


def mutate(kind: str) -> dict:
    data = copy.deepcopy(fixture())
    target = next(r for r in data["OCC"] if r["point"] == "P2" and r["occ"] == 0.5)
    if kind == "nonfinite":
        for key in ("gen_value", "delta", "closed_form"):
            target[key] = float("nan")
    elif kind == "counterfeit_oracle":
        for row in data["OCC"]:
            if row["point"] == "P2":
                for key in ("gen_value", "np_value", "delta", "closed_form"):
                    row[key] *= 2.0
        next(r for r in data["OCCCHK"] if r["point"] == "P2")["ratio_ref"] *= 2.0
    elif kind == "orphan_point":
        data["OCCCHK"] = [r for r in data["OCCCHK"] if r["point"] != "P2"]
    elif kind == "duplicate_occupation":
        data["OCC"].append(copy.deepcopy(target))
    elif kind == "moving_inputs":
        target["ieps"] *= 2.0
    else:
        raise ValueError(f"unknown mutation: {kind}")
    return data


class ExistingBehaviorControls(unittest.TestCase):
    def test_unmodified_synthetic_kernel_data_agree(self):
        output = report(fixture())
        self.assertEqual(set(output), {"P1", "P2", "P3", "P4"})
        for point in output.values():
            self.assertEqual(point["max_relative_spread"], 0.0)
            self.assertEqual(point["max_relative_closed_form_error"], 0.0)
        for row in fixture()["OCC"]:
            self.assertEqual(row["delta"], analyze.closed_form(
                row["occ"], row["ieps"], row["wt"], row["wxt"]))

    def test_existing_arity_check_rejects_truncation(self):
        text = table(fixture())
        row = next(line for line in text.splitlines() if line.startswith("OCC "))
        with self.assertRaises(ValueError):
            analyze.parse_text(text.replace(row, row.rsplit(" ", 1)[0], 1))

    def test_existing_delta_consistency_check_rejects_mutation(self):
        data = fixture()
        data["OCC"][2]["delta"] += 1.0
        with self.assertRaises(ValueError):
            report(data)


class RequiredFailClosedBehavior(unittest.TestCase):
    def test_nonfinite_observation_is_rejected(self):
        with self.assertRaises(ValueError):
            report(mutate("nonfinite"))

    def test_data_supplied_oracle_cannot_hide_100_percent_error(self):
        data = mutate("counterfeit_oracle")
        row = next(r for r in data["OCC"] if r["point"] == "P2" and r["occ"] == 0.5)
        independent = analyze.closed_form(row["occ"], row["ieps"], row["wt"], row["wxt"])
        self.assertEqual(abs(row["delta"]-independent)/abs(independent), 1.0)
        try:
            output = report(data)
        except ValueError:
            return  # Rejecting corrupted evidence is also acceptable.
        self.assertGreaterEqual(output["P2"]["max_relative_closed_form_error"], 0.5,
                                "reported zero despite a 100% equation mismatch")

    def test_orphan_occupation_point_is_rejected_not_silently_omitted(self):
        with self.assertRaises(ValueError):
            report(mutate("orphan_point"))

    def test_duplicate_point_occupation_is_rejected(self):
        with self.assertRaises(ValueError):
            report(mutate("duplicate_occupation"))

    def test_linearity_requires_fixed_kernel_inputs(self):
        with self.assertRaises(ValueError):
            report(mutate("moving_inputs"))


if __name__ == "__main__":
    unittest.main()
