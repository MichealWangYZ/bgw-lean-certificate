# Codex Review of T-003-R1

Date: 2026-09-11. Outcome: validator repairs pass independent review;
one source-explanation finding remains. T-003 is not yet accepted.
No new Claude job or weighted-mismatch work was dispatched in this review.

## Remaining Finding: F3 Static-Sentinel Explanation

`bgw/occupation_audit/REPORT.md:161-165` still makes two false statements.

1. The generic-branch `ssx` does not tend to zero with a large positive pole.
   The pinned source recomputes `wtilde2 = wtilde**2` and then
   `Omega2 = wtilde2 * I_eps_array` at `Sigma/mtxel_cor.f90:1810-1812`.
   Its generic expression at lines 1828-1834 therefore gives, at fixed finite
   `x = wxt` and `ieps`,

   ```text
   ssx = w^2 * ieps / (x^2 - w^2) -> -ieps
   sch / 2 = w * ieps / (2 * (x - w)) -> -ieps / 2
   -occ * ssx + sch / 2 -> (occ - 1/2) * ieps
   ```

   The last expression is the mapped local occupied-loop contribution with
   common matrix-element/Coulomb factors stripped, not a full self-energy.
   The default sexcut factor of 4 does not suppress this limit. The preceding
   setup stores `I_eps_array` before applying the invalid-mode policy and
   does not zero it when selecting the sentinel. Confusing the earlier setup
   plasma frequency with the kernel's recomputed `Omega2` causes the error.
   At `w=1e12, x=10, ieps=-1/4, occ=1`, exact rational evaluation gives
   `ssx` approximately `0.25` and local contribution approximately `-0.125`,
   not the CH-only value of approximately `+0.125`.

2. Near-pole selection does not require `abs(x-w) <= 0.5`. That is one route;
   the generic branch also fails when `delwr >= limitone`. For example,
   `w=1e12, x=w+1e6` gives `wdiffr=1e12` and `delwr=1e12`, selecting branch 2
   despite the energy difference exceeding 0.5. The complete predicate must
   remain in the explanation. Ordinary band energies are still far from
   this region, so this does not overturn the stated ordinary-energy
   generic-branch conclusion. This example is algebra, not an executed
   material witness.

Fix the report and add a focused regression for these source-algebra claims
before final acceptance. Preserve original provenance and worker handoffs;
record any follow-up revision separately. No physical rerun or Lean change
is needed for this finding.

## Independent Verification

- `bash scripts/verify.sh`: exit 0, completed 2026-09-11 17:09:25 UTC;
  85 Python tests, 60 named / 126 exhaustive theorem audits, 17 Lean runtime
  cases. Existing BerkeleyGW saved-export verification passed.
- Executed the actual checker CLI against all nine original review cases:
  baseline passes; all eight invalid/incomplete cases now exit 1.
- Additional positive count mutation (`branch2 = [76461, 3703]`) exits 1.
- Explicit one-record subset passes and reports full-fixture validation false.
- Supervisor fresh records with their own fresh control/probe tallies pass.
- The three reported residual/mismatch numbers and branch2 counts are
  preserved in the independently generated JSON outputs.
- All 21 entries in `PROVENANCE-R1.txt` match their actual files.
- No BerkeleyGW build/run, implementation edit, Lean edit, or fixture edit
  was performed in this review.

Evidence: `artifacts/t003-r1-codex-review/` contains CLI mutation outcomes,
provenance verification, and both exact-rational sentinel counterexamples.
The full gate logs remain in `artifacts/verification.json` and `artifacts/tests.log`.

## Row-Sum Invariant Decision

Keep this as an enforced invariant for this frozen control/probe pair. Both
runs admit the same bands (`nvband=4`, `ncrit=0`); the branch and clamp
predicates use the same energies/poles and do not depend on `occ`. Reclassifying
occupation cannot change each row's total. This is not a universal invariant
for arbitrary Fermi-level changes or different material calculations.

The invariant is a consistency check, not authentication of every individual
count: coordinated changes preserving row sums need not be detected by it.
The saved provenance and independent run are separate evidence. The 48
exported records still do not constitute numerical validation of all 3702
qualifying events, and measured residual thresholds are not proved universal
rounding-error bounds. The charge-inconsistency caveat remains in force.
