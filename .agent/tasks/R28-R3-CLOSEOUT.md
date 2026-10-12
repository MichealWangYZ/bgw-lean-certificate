# R28-R3-CLOSEOUT: four findings, one closing patch

Base reviewed: `94393dec0b74bd4927263dbe9513d2aa63ea3737` (same tree as the
reported-gated `47a46c994d0c11424754d14a48303cb4eff9c276`).
Read `docs/reviews/R28-R3-INDEPENDENT.md` and the project instructions first.
This is the finite repair specification, not evidence that repairs are already
done and not an automatically running job.

## Deliver exactly these repairs

1. In `bgw/bridge_cor/cor.py`, replace both padded scalar Ry-to-eV radius
   reporting conversions (per-band fields in run_all and radius_eV in all_bands)
   with the existing interval arithmetic and the upper endpoint of
   `I.exact(radius) * RYD`. Reuse the interval-valued constant; do not use only
   `RYD_F`, increase the padding, or introduce a new interval library.
   Add an actual implementation regression in the existing bridge-cor tests.
   Include zero, ordinary finite positive radii, subnormals, and specifically
   radius = 2 * nextafter(0, 1). Compare against Fraction(radius) times the exact
   decimal 13.60569253. Show the old implementation fails the distinguishing case
   and the repaired implementation passes. Check both reporting call sites and
   confirm assemble still follows its existing interval path.
2. Correct the first B2 chain row in docs/BRIDGE.md: state the nonzero static-match
   hypotheses, distinguish the unconditional tail result, and describe
   fsum_moment with w nonzero as algebra rather than a formalized spectral integral.
3. Correct departure-table row 6: row wing O(1/|q|), column wing O(|q|), with the
   finite limits of t times the row wing and column wing divided by t. Do not
   assert mandatory divergence when the leading row-wing coefficient is zero.
4. Reconcile the README, ENDPOINT E1.4, R28-R3 gate/status record and current state
   summary with the final PR #31 gate comment and the October 7 spec-header edit.
   Label historical checkpoints as historical and the full-gate report as
   submitted evidence. Record the current closing patch's own validation scope;
   do not present the older gate as covering its changed executable code.

## Boundaries

No Lean theorem/definition edits, new science, new run or certificate, dependency
upgrade, changed physical assumptions, tuned tolerances or widened acceptance
budget. No generalisation of MF.TR, oscillator-strength derivation, RowDist proof,
or binary-decoder formalisation as a condition of closing this task.

Do not touch unrelated branches, merge main, change visibility/licensing, publish,
contact upstream maintainers, or launch another worker automatically. Preserve
existing work. Do not change public claims beyond making these descriptions
accurate. The static-remainder and finite-basis limitations remain disclosed.

The committed cor.json comes from a specific recorded run. Do not manufacture a
fresh-run or regeneration claim. Either regenerate only the permitted reporting
outputs from available pinned inputs and record the exact method, or explicitly
retain the older conservative reported values as historical output and explain
why the source repair does not invalidate them. Do not derive hidden unrounded
operands by inverting rounded output values.

## Validation and finite exit

Run the relevant bridge-cor regression suite, including the distinguishing
negative control, and applicable Python syntax checks. Run the normal fast gate
before committing and full gate before any merge as required by AGENTS.md;
record exact revisions, results, skips and actual environment limitations.
Regenerate registries only if the existing generator requires a change; never
hand-edit generated registry/digest files.

Update .agent/STATE.md and write the handoff with a four-row closure table and
pointers to the validation evidence. Return one reviewable closing patch and
STOP. Worker completion remains ready for review, not self-acceptance.

Acceptance is finite: when these four findings are resolved and their closing
diff plus applicable evidence are checked, the reviewer will sign off R28-R3
under its bounded claims. There is no additional requirement for another broad
review cycle or for solving the disclosed physics-bridge research questions.
If a genuinely new load-bearing defect is discovered during closeout, report its
specific evidence instead of silently expanding this task.
