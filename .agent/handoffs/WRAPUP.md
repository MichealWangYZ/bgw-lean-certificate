# WRAPUP handoff: freeze, code map, memoized audit, registries, fast gate, rules, gate

Worker: Claude (implementer). Branch `wrapup/work`, worktree `.claude/worktrees/wrapup`,
base 5026240 (`bridge/theory-to-bgw`) + task brief 88018aa. Status: **CHECKPOINT_READY**,
meaning ready for review. It is NOT accepted; Codex/owner owns acceptance. I made no Lean
statement changes, only comments/banners, the generated `GW.lean` import block and the
audit script. I added no sorry, axiom or native_decide.

## Commits (one per item, pushed to `origin/wrapup/work`)

| Item | Commit | Content |
| --- | --- | --- |
| 1 Freeze + state | a86324e | `.agent/STATE.md`: freeze section (date, scope, owner-only lift) and a 2026-10-01 state section (PR #27 merged at 709220e, the BRIDGE series table, current claims with their evidence kind, open decisions O1 15.4 vs -3.8 / RHO / `CompleteK` / more bands / merge). Older sections relabelled historical. `.agent/WAKEUP.md`: freeze paragraph. |
| 2 Code map | 3378938 | `docs/CODEMAP.md`; one-line ARCHIVED banners (63 files); `make_review.py` footer links CODEMAP; PROVENANCE-R6 re-signed |
| 3 Memoized audit | 9211c8d | `scripts/CheckAxioms.lean`: per-constant cache over the whole environment (Tarjan SCCs) |
| 4 Registries | fc1dd33 | `scripts/registry.py` (+ `--check`), generated `scripts/CheckAxiomsFast.lean`, regenerated `GW.lean`/`CheckAxioms`/`gates.py`/R6, registry step in `verify.py` |
| 5 Fast gate | 0471a28 | `verify.sh --gate fast`; `gates.py` FAST map; CODEMAP test section (timings, redundancy candidates) |
| 6 AGENTS.md | b46a826 | "Architecture and workflow" section |
| 7 Gate | (this commit) | full `verify.sh` result below, this handoff, STATE.md pointer |

## Item 1

Facts come from the BRIDGE* handoffs, `docs/BRIDGE.md`, `docs/ENDPOINT.md` and `git log`.
Every Lean theorem name cited in STATE.md was grepped and exists (`sigA_eq_theory_q0`,
`S3.o1_enclosure` in `Data/S3Check.lean`, `R.o1_fullQP_irr` in `Data/RIrr.lean`, etc.).
`origin/main` = 709220e was checked with `git fetch`. The "verify PASS at 3387327" is
taken from the brief and was not re-observed here; item 7 re-observes the gate.

## Item 2: how canonical vs archived was decided

The script (scratch, `graph.py`) parsed every `import` of `GW/**/*.lean` and of the
`*Main.lean` files. It then computed the closure of the 25 `GWKernelData` roots
(48 non-Data modules) and the closure of `GW/Bridge/*`.

* Canonical: the modules in either closure, plus the A3 modules `docs/ENDPOINT.md`
  names (ManyBody.*, HubbardDimer*), plus `CertInterval` and `UnfoldPhase`.
* ARCHIVED: modules nothing canonical imports. These are `GW.BGW.*`,
  `GPP.{FiniteSelfEnergy,BerkeleyGWMap,PoleDomain}`, `Examples`, `LL.{RingHalfEdge,Wick}`,
  `Main` and `LL*Main`.
* RETAINED: older-lineage modules the bridge imports. These are `GW.GPP.PoleCancellation`
  and `GW.LL.{Diagram,Ring,StructuralRing,Screening,Electronic}`. They get no banner.
  This is listed as open question 1 in CODEMAP.

Python was classified the same way from its imports. Canonical `bgw/endpoint` and
`bgw/bridge_*` import nothing archived, with one recorded exception:
`bgw/endpoint/mutate_lean.py` loads `bgw/m4_gpp/mutate.py`. `bgw/export/*.in` are shared
input decks.

How the banners were placed:
* Each banner is merged into the first docstring/title line, because historical handoffs
  and audits cite `file:line` (e.g. `audits/checker_soundness/REPORT.md` →
  `analyze.py:291`).
* Files whose bytes recorded evidence pins (sha256 found by grepping every candidate's
  hash across the repo) are NOT bannered. They are listed in CODEMAP: `M2Screening`,
  `M3Chi`, `M4GPP`, `M5Sigma` (mutation/replay logs; M4/M5 are also generated and
  compared by tests), several `bgw/m*` scripts, `ll/ring_reference.py`, and the
  branch_boundary README/f90.
* The banners rebuilt only the archived modules and their dependents (lake build 221 s).
  `GWKernelData` was untouched (`--no-build` rc 0). None of the 48 kernel-data upstream
  modules was edited.

Generator link:
* `make_review.py` footer now names `docs/CODEMAP.md`.
* `docs/review/index.html` was NOT regenerated. Regenerating it needs
  `artifacts/axioms.log` (from verify) and the BerkeleyGW tree, and a trial regeneration
  showed that the committed HTML already lags the source: it was generated at 1a5cd73,
  and it reads `cert.py:103` where the source now has `:107`.

## Item 3: memoized audit, equivalence and timings

Algorithm:
* `memo[d]` = `collectAxioms d`, the axioms in the order a fresh
  `CollectAxioms.collect d` first visits them.
* Tarjan SCCs close in reverse topological order. Inside a closed component, `collect`'s
  DFS is replayed over the members. An edge to an earlier component appends that
  component's memo minus the axioms already collected.
* The docstring carries the argument for why this is exact. In short: an earlier
  component cannot reach back into the search stack, and everything visited in its reach
  was fully visited.

Same allowlist, same messages, same loop order (sorted names, throw at the first
forbidden axiom).

| Run (same build each pair) | old wall | new wall | peak RSS old / new | result |
| --- | --- | --- | --- | --- |
| pre-banner build (5026240 + item 1) | 48:44 (first ~13 min concurrent with my test runs) | 2:32 | 5.81 / 5.86 GB | whole logs **byte-identical**, sha256 4964e174…; 34285 AUDITED lines |
| post-banner build (item 2), clean sequential | **46:22** | **2:26** | 5.83 / 5.87 GB | byte-identical to each other and to the pre-banner logs |

The AUDITED lines are identical as ordered lists, not just as sets, and each line keeps
its axiom order. Eight distinct orders occur, e.g. `[propext, Quot.sound,
Classical.choice]` 6454 times and `[Quot.sound, propext]` 11 times.

Small-environment checks (PoleCancellation + LL.Electronic imports, 342 theorems):
* identical AUDITED lines;
* with `Quot.sound` removed from the allowlist, both versions fail at the same theorem
  (`_private.GW.LL.StructuralRing.0._proof_10`) with the same message, after the same
  16 AUDITED lines. Only the `run_cmd` line number in the error prefix differs.

The full-gate step comment in `verify.py` now says ~2.5 min instead of ~20 min.

## Item 4: registries

`python3 scripts/registry.py [--check]` handles each registry as follows.

| Registry | Rule | Regeneration diff on the current tree (reviewed) |
| --- | --- | --- |
| `GW.lean` imports | every default-library module, sorted. A module is default-library unless it is under `Kernel/Data/`, imports one transitively, or is `GW/Audit.lean`. The docstring is kept and gained a "GENERATED" note. | reordered; 21 modules that were previously only transitive (ManyBody.*, HubbardDimerExact/Fock) are now explicit. The module set is unchanged: `lake build` rebuilt only GW, Main and gpp_demo (15 s). |
| `scripts/CheckAxioms.lean` imports | GW, Main, then the `GWKernelData` roots in lakefile order; body verbatim | AuditData and CoulTamper/CoulAudit reordered; the per-stage comment lines were dropped (the same text is in `lakefile.toml`) |
| `scripts/CheckAxiomsFast.lean` | generated whole: imports GW and Main, then the same body | new |
| `scripts/gates.py` tuples | `tests/test_*.py`; WORKFLOW iff the docstring's first line starts with `WORKFLOW GATE` | sorted, so bridge_cor/disc and endpoint_a*/e* swap. The run order now puts `test_endpoint_a` before `e1`, the order that exposed `cert.STATS` before BRIDGE-FIX; it passes. `test_provenance_committed`'s docstring gained the `WORKFLOW GATE:` prefix so the rule keeps it in WORKFLOW. |
| PROVENANCE-R6 digests | re-hash listed paths only (as `make_manifest.py`); runs last | digests of the edited vouched files |

`GW/Audit.lean` is NOT generated:
* It is the curated S5 named list: 1316 names, a deliberate subset of the declared
  theorems. Per module, e.g. `Kernel.Sound` has 8 of 42 and `Coulomb.Leaf` 1 of 30.
* Generating it from all declared theorems would change what it means.
* `--check` verifies only that it imports exactly `GW`, names no theorem twice, and
  contains the 8 S5 required names.

`--check` is wired into `verify.py` as the first full-gate step and into the fast gate.
It also fails if a SCIENTIFIC test is in neither `FAST` nor `ARCHIVED_TESTS` (item 5).
It is idempotent: a second run reports "0 regenerated".

## Item 5: fast gate

`bash scripts/verify.sh --gate fast [--base REF] [--all-tests] [--jobs N]` runs:
* the registry check;
* `lake build GW` (no GWKernelData);
* `lake env lean scripts/CheckAxiomsFast.lean`, which checks that every default-library
  module appears as AUDIT_MODULE;
* the workflow tests;
* the FAST tests that cover the changed paths.

Tests run as parallel processes, one per module. The record goes to
`artifacts/verification-fast.json` and the logs to `artifacts/fast/`. Selection rules
are in `scripts/gates.py`, and unsure means all FAST modules.

| Case | Wall |
| --- | --- |
| no scientific change (the item-5 diff itself) | **66 s** (audit 61.5 s, 3571 theorems) |
| `--all-tests` (worst case) | **439 s** (e1 360 s ∥ a 196 s ∥ …), all 14 modules OK, no skips |

Both are under the 10 min target. Before this, serially, the canonical tests alone took
about 590 s (measured per module).

Redundancy candidates are listed in `docs/CODEMAP.md`, and no test was deleted. They are:
* x = 0 `∓I/2`: measure vs disc;
* x = w̃ discrepancy: bridge vs measure;
* invalid-mode static limit (×3);
* empty near-pole dropped (×2);
* `mode_eq` (×2);
* `wdiff_zero_possible` (×2);
* six independent fresh BerkeleyGW runs (a computation duplicate, not a claim duplicate).

## Item 6

`AGENTS.md` "Architecture and workflow" (about 30 lines) covers every point in the
brief. It records as fact that the no-nested-agents/no-overlapping-writers rule was not
kept: BRIDGE-DISC/-Q0/-COR ran in parallel and all wrote `GW.lean`, `GW/Audit.lean`,
`gates.py`, `PROVENANCE-R6` and `docs/BRIDGE.md` (merges f4124da, 3387327). The
proposed future form is marked "Proposed, not decided". Human review of
specification/transcription changes is a Recommendation, not a rule.

## Item 7: full gate

`bash scripts/verify.sh` at b46a826 (clean tree, `tracked_changes: false`) gave
**PASS (all)**. Wall time was **991 s (16.5 min)** with a warm `.lake/build`; GWKernelData
was already built. It ran from 2026-10-02 04:39:12 to 04:55:44 UTC, and
`artifacts/verification.json` has `status: passed` with 17 steps. The steps:
* registry check: OK;
* `lake build` and `lake build GWKernelData`: OK;
* `GW/Audit.lean`: 1316 named entries, 1311 "depends on axioms" and 5 "does not depend
  on any axioms", all within the allowlist;
* `CheckAxioms.lean` (memoized): AXIOM AUDIT PASSED, 34285 theorems, 304 runtime-only
  unsafe declarations, every project module audited;
* Lean demo, runtime checks, exact oracle, BerkeleyGW exports, LL evaluators: OK;
* scientific gate: 655 tests, OK, 2 skipped;
* workflow gate: 14 tests, OK.

The two skips are pre-existing environment skips, so these did NOT verify:
`test_branch_boundary...byte_for_byte` (the pinned arch.mk compiler is absent) and
`test_occupation_audit...supervisor_fresh_records_pass` (no supervisor fresh run).

The brief expected about 1 h warm. Most of the difference is the memoized audit (about
2.5 min instead of about 46).

## Failed attempts and corrections

* My first registry draft treated `import Lean.Util.CollectAxioms` / `Std.*` as part of
  the generated project import block, and would have dropped them from the audit body.
  Fixed: library imports are kept after the project imports.
* My first `select_fast` checked `NO_PYTHON_TEST` (`scripts/`) before `ARCHIVED_PATHS`,
  so `scripts/reference.py` was not reported as archived. The order is now swapped.
* `bgw/endpoint/cert.py`'s `inverse_cw` is actually in `iv.py`. I corrected this in
  CODEMAP before committing.
* Running `old_pre` concurrently with the test timing inflated its wall time (48:44).
  The clean sequential pair (46:22 vs 2:26) is the number to quote.

## Open questions (owner)

1. RETAINED modules (`GW.GPP.PoleCancellation` and the five `GW.LL` modules the bridge
   imports): canonical, or RETAINED as recorded?
2. E2 scripts (`sweep.py`, `e2_*.py`): this is a withdrawn layer, so I left them
   unbannered. Should they be archived?
3. `AGENTS.md` cites the archived `docs/LL-C1-REVIEW.md` for live policy. Should that
   text move?
4. The reading order still starts with `Specification.md` (the archived demo's
   contract). Should it point to `docs/ENDPOINT.md` §4?
5. Should `docs/review/index.html` be regenerated now that `artifacts/axioms.log` exists
   (requires `~/bgw-src`)?
6. Scientific open decisions are recorded in `.agent/STATE.md`. All of them are frozen.

## Next action

Codex/owner review of the seven commits. Merging `wrapup/work` (and its base
`bridge/theory-to-bgw`) into `main` needs an owner decision.
