# PR #4 review: proceed to a structural ring checkpoint — ARCHIVED (2026-10-01): LL review record; LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md.

Reviewed: `111e97ce793118e35093cd5d1890171741c3f0db`, PR #4, 2026-09-15.
Disposition: **PROCEED_WITH_CARRY for internal research**. Accept C1/R1 as the
bounded finite-ring baseline for the next experiment; do not merge or publish
by implication. This is an AI-assisted technical assessment, not human sign-off
or an independently rerun full Lean gate. No further repair-only round is requested.
The next assignment is [LL-C2A](../.agent/tasks/LL-C2A.md).

## Criteria fixed before reading the returned work

1. Preserve the three ring definitions/results and state the model's actual scope.
2. Remove the host-specific checkout dependency and supply fresh-checkout evidence.
3. Deliver real evidence and reject the previously demonstrated malformed tables.
4. Reuse the community API without speculative dependency/framework expansion.
5. Stop within R1 and leave a defensible next mathematical question.

These are progression criteria, not a demand that the whole project be finished.
A bounded residual does not automatically require another repair-only milestone.

## What was actually checked

Read the PR, the returned `.agent/handoffs/LL-C1-R1.md`, the changed source and
patches, and the committed artifacts. This is a review of the durable handoff,
not access to a live Claude process or a complete hidden session transcript.

Executed in the review container, against source reconstructed from connector
contents and verified against Git blob hashes:

- All **21** tests in `tests/test_ll_c1.py`: pass.
- `ll/make_comparison.py`: **18** exact comparisons and **7** detected mutants.
- Regenerated `comparison.json` has Git blob SHA
  `eaa8b402bc314aef4598e03c260b74e4e4e1f0dc`, matching the committed file exactly.
- Repeated the duplicate-row and invalid-index probes against the repaired checks;
  they reject both. An ordinary wrong value is still detected.
- Probed the standalone report writer separately; it still falsely succeeds on
  duplicate rows, impossible metadata, and forged symmetry metadata (see below).

Byte-checked inputs:

| File | Git blob SHA |
|---|---|
| `ll/ring_reference.py` | `641d536ad219738af480c7bae159721aef49e5bd` |
| `tests/test_ll_c1.py` | `977ad493159825f8b36d300d8897db8610f76dc3` |
| `ll/make_comparison.py` | `ade0a7fee3ec29ea489f82575e43deb51a518382` |
| `artifacts/ll-c1/lean_values.json` | `74d0b875b55586a345b106e64226f827df12104c` |

**Not executed here:** Lean build/audit, BerkeleyGW, or full fresh-clone bootstrap.
Lean/Lake were absent and the container could not resolve the raw GitHub host.
This was a byte-verified reconstruction of the files needed for the Python checks,
not a successful `git clone`. The worker's 248-test / 247-audit fresh-checkout
result remains reported evidence. Its declared reuse of a dependency olean cache
is not the same as inheriting project binaries. Independent Python checks do not
certify the Lean compiler, runtime, or the physical model.

## Findings against the criteria

**Core mathematics: preserved.** The ring results and `IsAut` definition did not
change; `sum_over_pi_succ` now uses pinned mathlib's `Fin.consEquiv`. The new loop
example is additive. The finite ring result was not replaced by a weaker target.

**Portability: demonstrated defect removed.** The pinned Git tree no longer
contains `.tools`, and the ignore rule covers the symlink as well as a directory.
The handoff reports a fresh source checkout and new toolchain installation; full
bootstrap reproduction was not independently possible in this environment.

**Evidence: substantially repaired.** Both claimed snapshots really exist now.
The production test path rejects duplicate names before constructing its dictionary,
binds N/i/j to the named fixture, checks bounds/types, and still compares exact
values. `ll/*.py` is now included in the existing source-stability hash coverage.

**Community alignment: implemented, not just promised.** The duplicate equivalence
was removed, the pinned dependency is unchanged, and `AGENTS.md` now contains
specific reuse and human-owned upstream communication rules. No need to import a
work-in-progress Physlib interface or change toolchains to continue privately.

**Stopping: appropriate.** This is a repair pass; it did not start arbitrary-k,
resummation, or an electronic bridge. Returning it for review was correct.

## Carry-forward items: real, but not reasons to halt the research route

### R1. The report writer bypasses the fixed validator

`ll/make_comparison.py:build` still constructs a dictionary directly and copies
`symmetry_factors` from the candidate into a field called
`symmetry_factors_from_paper`. Thus the repaired test path and the report writer
have diverged. Measured behavior:

| Input | Existing test checks | Standalone report CLI |
|---|---|---|
| Committed control | accept | exit 0, all exact |
| Wrong numerical value | reject | exit 1, not all exact |
| Wrong duplicate before the correct row | reject | **exit 0, all exact** |
| N=1 with i=j=999 | reject | **exit 0, all exact** |
| ring1 symmetry metadata changed to 999 | reject | **exit 0; labels 999 as from the paper** |

This does not invalidate the committed, validated numbers and does not demonstrate
escape from the complete fresh-generation gate. It DOES mean the standalone
report must not yet be used as a validating entry point. Share one small validator
between tests and report generation, check expected symmetry metadata independently,
and add narrow CLI regressions. Move the helper into an existing small `ll` module
or one tiny module if needed; do not import the whole test suite in production and
do not introduce a schema or provenance framework. Regenerate the report in the
existing gate so a checked result and a stale summary cannot silently diverge.

### R2. The loop witness and remaining docstrings need precise claims

The new `loopExample` has 3 sites but 2 interaction edges sharing the one internal
site. In the compressed reading, each site is a side of exactly one interaction;
this toy does not itself establish a *well-formed quartic Lin-Lindsey* counterexample.
Moreover Lean proves only its compressed count equals 1; the explicit half-edge
count 2 is explained in prose, not proved there. The general limitation is real,
but calling the whole source-correspondence counterexample kernel-checked is too strong.

Use the already-known valid small witness instead (or explicitly label the current
one an abstract incidence toy): sites I,J,a,b; interactions `(I,J),(a,b)`;
propagators `(I,a),(a,J),(b,b)`. Each site belongs to one interaction; internal
propagator degree is 2, and each external site has one propagator plus its fixed
external flag. Swapping the two flags of the loop is invisible to site/edge IDs.
A small compressed-cardinality proof plus explicitly labelled external half-edge
reasoning suffices for this carry item. The next task separately proves the lift
for the ring family; it does not need a universal loop theorem.

Also fix the `Aut` docstring that still identifies its count with Definition 3.8
without a qualifier. Replace the `example : True := trivial` used as a comment
holder with an ordinary comment. These are local claim corrections, not new theory.

## Why proceeding is justified

The remaining defect is on a secondary reporting path; the actual tested table is
valid and byte-reproducible. The modelling issue limits extrapolation, not the
three ring identities. Neither requires abandoning the route. Keep these as a short
opening cleanup inside C2A, then spend the work allowance on new mathematics.

C1 answered whether three finite graph instances can produce the right algebra.
It did not answer whether the representation scales or faithfully captures every
half-edge relabeling. Therefore split old C2 into **C2A: arbitrary finite ring +
proved ring-specific lift**, then a separately authorized **C2B: formal resummation**.
Do not spend another whole cycle polishing C1, and do not combine those two new
uncertainties into one unbounded job.

## Source and community boundaries

Primary mathematics: [Lin–Lindsey Part I v1](https://arxiv.org/abs/1809.02900v1),
PDF §3.2 and §4.7.1, printed pp. 42–43/Fig. 4.11 (re-inspected as page images).
This is the classical real Gibbs model. It is not electronic GW or BerkeleyGW.

Policies re-read on 2026-09-15: [mathlib contribution/AI guidance](https://leanprover-community.github.io/contribute/index.html)
and [Physlib AI policy](https://github.com/leanprover-community/physlib/blob/master/AI-POLICY.md).
Stay downstream; search pinned APIs before inventing abstractions. Human ownership,
reference verification and the target community's communication rules remain
requirements for any eventual upstream contribution. No upstream contact, bulk
patches, visibility changes, merge, or worker launch is implied by this review.
