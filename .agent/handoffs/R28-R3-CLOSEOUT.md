# R28-R3-CLOSEOUT handoff: the four findings of the independent R28-R3 review

Worker: the Claude supervisor session, at the owner's direction (2026-10-09).
- Task file: `.agent/tasks/R28-R3-CLOSEOUT.md`.
- Review: `docs/reviews/R28-R3-INDEPENDENT.md` (commit 743cd48).
- Branch: `r28-r3-closeout/work`, on `review/r28-r3-closeout`.
- Fix commit: e8ef424.

Status: **ready for review, not accepted.**

## Closure table

| Finding | Repair | Evidence |
| --- | --- | --- |
| R3-I1 `cor.py` radius conversion | Both reporting sites (`run_all` per-band `radius_*_eV`; `all_bands` `radius_eV`) call `radius_eV(r) = float((I.exact(r) * RYD).hi)`, with the existing interval-valued `RYD`. The padded scalar `r * RYD_F * (1 + 1e-12)` is removed. `assemble` is unchanged and still converts through `RYD` intervals. No other module reads these fields. | `tests/test_bridge_cor.py::IntervalSerialization`: <br>- outward against `Fraction(r) * 13.60569253` for 0, `s`, `2s`, `3s` (`s = nextafter(0, 1)`), other subnormals, the normal boundary and ordinary radii; <br>- the old form gives `27 s` at `2s`, below the exact `27.21138506 s`; <br>- a source check that both sites call `radius_eV`. <br>Negative control: with the old expression substituted back, `test_radius_eV_is_outward` fails 2 subtests (the subnormal cases). |
| R3-I1 committed `cor.json` | Kept as historical output, not regenerated. The pinned run directories (session scratch) no longer exist, and the task excludes a new run. All 30 committed radii are at least 9.9e-5 eV, so they are normal-range values. There the old form is outward: the 1e-12 relative pad exceeds its three binary64 roundings. The committed values therefore remain upper bounds. No hidden operand is reconstructed. | `test_old_padded_radius_was_outward_in_normal_range` (normal boundary plus 2000 log-uniform radii from 1e-307 to 1e3); `test_committed_radii_are_in_the_normal_range` |
| R3-I2 BRIDGE B2 row | The static value `-I` needs `I ≠ 0` and `Ω² ≠ 0` (`gppC_static`; the totalized `gppC 1 0 0 = 0`). The tail limit holds unconditionally (`gppC_tail`). `fsum_moment` is the algebraic substitution for `w ≠ 0`, with no formalized spectral integral. The same qualification is added to the BRIDGE frequency paragraph that cited `gppC_static`. | `docs/BRIDGE.md` B2 row and the `gppC_static` paragraph; Lean statements at `GW/Bridge/GPPModel.lean:75,106,122` |
| R3-I3 departure row 6 | The unscaled row wing is `O(1/abs(q))` and the column wing is `O(abs(q))`. The finite limits are `t · (row wing)` and `(column wing)/t` (`q0_limit`). The row wing diverges only if its leading coefficient is nonzero. | `docs/BRIDGE.md` row 6; `GW/Bridge/EpsQ0.lean:228-239` |
| R3-I4 stale status records | README, ENDPOINT E1.4, the R28-R3 record and handoff, and STATE (two places): <br>- The current full gate of the merged R28-R3 code is the PR #31 record at 47a46c9, labelled author/supervisor-reported. <br>- 214b656, e3ae6b4, 7435f99 and f9cf59a are labelled historical. <br>- This patch's executable change is stated as not covered by that gate. <br>- E1.4 records the 2026-10-07 spec-header edit; the old "deliberately not edited" wording is labelled historical. <br>- The old "A2 open" lines are marked superseded, not deleted. <br>- The reviewer's guide is regenerated. | the diff of e8ef424 |

## Validation of this patch

The gates ran in the warm worktree `.claude/worktrees/r28-r2-cold`, detached at e8ef424
with a clean tree:

- `bash scripts/verify.sh --gate fast`: PASS, 77 s.
  - registry check;
  - default-library build;
  - memoized audit;
  - 6 change-selected test modules, including `test_bridge_cor` and `test_python_compiles`.
- `bash scripts/verify.sh`: PASS, 06:18 to 06:35 UTC on 2026-10-09; `artifacts/verification.json` records `head` e8ef424 and `tracked_changes: false`.
  - No Lean source changed, so the build replayed the 47a46c9 build.
  - Exhaustive axiom audit: 34553 theorems, standard axioms only.
  - 699 scientific tests passed: the 694 before, plus the 5 new radius tests.
  - 15 workflow tests passed.
  - 2 environment skips: the pinned BerkeleyGW compiler is absent, and there is no supervisor fresh run.
- The commit after e8ef424 adds only this handoff and the STATE entry. It is checked by the fast gate.

These are author-run results, not an independent replay.

## Not done, by the task's boundaries

- no Lean edit;
- no new run or regenerated certificate;
- no merge, visibility change or publication;
- no change to registries, which the generator did not require.

## Next action

1. The reviewer checks the closing diff (`review/r28-r3-closeout..r28-r3-closeout/work`) and this evidence, and records the sign-off from `docs/reviews/R28-R3-INDEPENDENT.md` if it holds.
2. The owner decides the merge into main.
