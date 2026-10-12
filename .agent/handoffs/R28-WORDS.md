# R28-WORDS handoff: REVIEW-28 wording, records and earlier cleanup

Task: `.agent/tasks/R28-WORDS.md`. Branch `r28-words/work`, based on main `d783e18` plus the
brief commit `6c0e19d`. Status: **ready for review, not accepted.** This task changed
wording and records only. No Lean statement changed. No new Lean modules or tests.

## What was done, per target

**1. Adopt the review's scope.**
* `README.md` is rewritten. It had described the archived scalar demo. It now uses the
  reviewer's title and suggested public wording, and it links STATE, CODEMAP, ENDPOINT,
  BRIDGE, `docs/review/index.html` and the review. Its sections:
  * claim 1 (certified evaluation) with its trust boundaries;
  * the O1 wording;
  * claim 2 as conditional theory-to-specification identities, with F1–F4;
  * what is not claimed;
  * build/verify commands;
  * the existing credits and licence text, kept.
* `docs/BRIDGE.md`:
  * New section "Scope after REVIEW-28", placed before "The question". It states that
    the bridge consists of conditional theory-to-specification identities, and covers
    F1 (no common-system field), F2 (formal properties and consequences of the
    specified HL ansatz, conditional on its oscillator-strength prescription), F3
    (abstract scaled-frame completion) and F4 (static term kept).
  * Rows B2, B4, 3, 4, 16 and C-1 are qualified.
  * "What is and is not claimed" gets a bullet on F1, and the BRIDGE-EPS "not claimed"
    gets the same.
  * The BRIDGE-COR title, its scope box, the `sigA_all_bands` bullet, the κ paragraph
    (rank-N argument), the table headings, the "-3.8" paragraph (now the O1 wording)
    and its "Not claimed" list are corrected.
* `docs/ENDPOINT.md` did not claim more than the review allows about claim 2. It gets
  a short scope note near the top: the O1 wording, plus a pointer to the conditional
  bridge scope.
* `GW/Bridge/Cor.lean` docstrings only. "with ALL bands", "static remainder `0`" and
  "COR replaced by the enclosed dynamic tail" are replaced. They now say "completion
  appended", "static term kept, not shown to vanish (F4)" and "abstract scaled-frame
  completion, not the omitted eigenvectors (F3)". The line count is unchanged (801), so
  the review's `Cor.lean:350–520` / `:640–820` ranges still hold.

**2. Record the review.**
* `docs/reviews/REVIEW-28-adversarial.md`, `counterexamples.py`, `counterexamples.json`
  and `.agent/tasks/REVIEW-28.md` were already committed, unchanged, in `6c0e19d`.
  Nothing more was needed for them.
* New file `docs/reviews/README.md`. It records:
  * the reviewer (Codex, per the brief; the review text does not name its author), the
    revision and the date;
  * what was and was not replayed;
  * the decision;
  * a table of F1–F4 with severity and R28 task.
* I re-ran `counterexamples.py`: it exits 0, and its output equals the committed JSON.

**3. Earlier cleanup.**
* `THIRD_PARTY_NOTICES.md`: new subsection "Added since 2026-09-13", found by searching
  the tree:
  * the verbatim Fortran excerpts in `docs/review/index.html`, with all 11 ranges taken
    from `make_review.py`;
  * `bgw/branch_boundary/branch_boundary.f90` (`!>BGW` statements and their ranges);
  * 6 dump/instrument patches plus the earlier `bgw/export/instrument.patch`;
  * 4 derived input decks, each diffed against the shipped deck;
  * the Lean/Python transcriptions (`SigmaSpec`, `EpsSpec`, `CertSexcut`, `NearPole`,
    `Unfold`, `GW/BGW/M*`, `spec.py`, `cert.py`, …);
  * short Fortran quotes in `docs/BRIDGE.md`, the PROVENANCE/README/FINDINGS files and
    the named handoffs (T-005, T-005-R1, T-006-CAPABILITY-SCOUT, BGW-M1, BGW-M3-CHI,
    LEAN-CERT, BRIDGE-FIX);
  * output/derived data directories, including the generated `GW/Endpoint/Kernel/Data/*`.

  A heuristic search also flagged handoffs that turned out to cite only `file:line` or
  variable names: BGW-M4-R1, BGW-M5, BGW-E2 and `docs/ENDPOINT.md`. They are named as
  non-quoting.

  I also corrected a stale section: "License of this repository's own work: Not yet
  decided. No LICENSE file is present". It contradicted the file's own header and
  `LICENSE`. The section now cites the BSD-3-Clause decision, commit `bb30f9b`. This
  changes no licensing; it fixes a record. **Owner may want to confirm this edit.**
* `AGENTS.md`:
  * removed the April 29 ODMR sentence;
  * reading order is now STATE → CODEMAP → ENDPOINT/BRIDGE → task, with
    `Specification.md` labelled the archived demo contract;
  * added a claim-scope rule (no "formally verified the core physics");
  * added the scoped freeze lift to the freeze bullet;
  * copied the live rules of `docs/LL-C1-REVIEW.md` §5 (downstream aim, missing-semantics
    rule, no vendoring to claim alignment, the mathlib/Physlib human duties, credit and
    notices, policy links) and removed the dependence on the archived file.
* `CLAUDE.md` and `.agent/WAKEUP.md`: same reading order. WAKEUP also records the
  scoped lift.
* `docs/CODEMAP.md`:
  * the former RETAINED modules (`GW.GPP.PoleCancellation`, `GW.LL.{Diagram,Ring,
    StructuralRing,Screening,Electronic}`) are labelled CANONICAL, and the definitions
    and dependency rules are updated;
  * the E2 scripts are recorded as ARCHIVED (withdrawn layer);
  * the documents table adds README, STATE and `docs/reviews/`, and notes that the LL-C1
    policy now lives in `AGENTS.md`;
  * the Specification.md paragraph gives the new reading order;
  * the four "Open questions" are rewritten as labelled and applied;
  * the Bridge row gets a placeholder for R28 additions.
* E2 banners: the docstring line 2 of `bgw/endpoint/sweep.py`, `e2_analyze.py` and
  `e2_layer1.py` now starts with
  `ARCHIVED (2026-10-02): E2 convergence layer, withdrawn … See docs/CODEMAP.md. -- `.
  No line moved, and `ast.parse` is OK. They are not byte-pinned: none appears in any
  digest manifest.
* `GW/Bridge/Compare.lean`, comments only. The module header and the
  `sigA_eq_theory_complete` docstring now say that its `Complete` hypothesis is
  unsatisfiable on the stored dyadic rows (`cor.json` `completeness_check`), so the
  corollary never applies to the run's data. 6 comment lines were added, so the line
  numbers below line 31 shift. Nothing cites `Compare.lean:N`; I checked with
  `grep -rn "Compare.lean:[0-9]"`.

**4. `.agent/STATE.md`.** New top section "REVIEW-28 and the scoped freeze lift". It
holds the review facts, a table of F1–F4 and their tasks (status: dispatched or wording
done; none integrated or accepted), the freeze lift and its limits, the labels applied,
and the O1 wording. The "Current claims", BRIDGE-COR row and "Open decisions" bullets are
reworded to the conditional scope.

## Second pass: R28-F4 wording applied (supervisor request, after commit `1adf6e1`)

The supervisor reported that R28-F4 had finished. I applied the replacement texts of
`git show origin/r28-f4/work:docs/reviews/R28-F4.md`, items 1–15, adapted to text this
task had already rewritten:

* **`docs/BRIDGE.md`.**
  * The scope box F4 bullet now gives the corrected statement: `sigAall_static_split`,
    `cor_all_decomp`, `cor_all_eq_zero`, and the Si-EPM sizes.
  * Row 16 gets `cor_decomp_complete`; row C-1 gets the `CORall` clause and
    `cor_all_decomp`.
  * In BRIDGE-COR: the scope box (F4 placeholder removed), the `sigA_all_bands` bullet,
    the static-tail sentence (`2·CORall` = -4.4 / -7.5 meV, with its
    shift/`Gch`/scale split), the −3.8 paragraph (+1.21 meV residual, [-5.25, -4.72]
    without it, outside [-4.04, -3.51]), the theory-kernel bullet, and the "Not claimed"
    bullet.
  * The cross-check paragraph gets one sentence from R28-F4's prose: the 164-band
    cross-check validates the added bands, not a vanishing remainder.
* **`GW/Bridge/Cor.lean`.** Items 8–11, merged into this task's F3 wording. The text is
  comment-only, and the line count is still 801.
* **`GW/Bridge/Compare.lean`.** Item 12, comment-only; one more line.
* **`.agent/STATE.md`.** Items 13, 14 and 15, applied to the reworded bullets. The task
  table now records R28-F4 as finished per the supervisor, not integrated.
* **`README.md`, `docs/ENDPOINT.md`.** The O1 wording now uses item 15. The README's F4
  bullet states the decomposition.
* **`docs/reviews/README.md` and the `docs/CODEMAP.md` Bridge row.** These name
  `GW/Bridge/CorResidual.lean` (R28-F4).

`GW.Bridge.CorResidual` and its theorem names are referenced in comments and docs only.
The module is not on this branch: it exists after integration.

These were not touched, being outside my scope: `bgw/bridge_cor/cor.py`,
`tests/test_bridge_cor.py`, the BRIDGE-COR handoff and `EpsCompare.lean`. The supervisor
handles them.

Check after the second pass:
* the comment-stripped comparison with `HEAD` is still identical for both Lean files;
* `lake build GW.Bridge.Cor GW.Bridge.Compare GW.Bridge.EpsCompare` succeeds.

## Placeholders left for the supervisor (F1 and F3 only)

* `docs/BRIDGE.md` "Scope after REVIEW-28": F1 → `docs/reviews/R28-F1.md`, F3 →
  `R28-F3.md`. The BRIDGE-COR scope box (F3) has one too.
* `README.md` claim 3: F1, F3.
* `docs/CODEMAP.md` Bridge row: the F1/F3 additions.
* `docs/reviews/README.md` findings table: the R28-F1/F3 rows.
* `.agent/STATE.md` task table: the R28-F1/F3 status. Also the "CompleteK vs Complete"
  open decision, which points to `R28-F3.md`.

F2 has no Lean task, so its wording is final here. There is no placeholder for it.

## Byte-pinned or generated files not changed

* `bgw/weighted_audit/PROVENANCE-R6.txt` is generated. `THIRD_PARTY_NOTICES.md` is
  digest-pinned in it, so `registry.py --check` reports drift. The only differing line
  is the `THIRD_PARTY_NOTICES.md` digest (`868f96…` → `90e288…`), which was expected.
  I ran `python3 scripts/registry.py` locally for the gate, then ran
  `git checkout -- bgw/weighted_audit/PROVENANCE-R6.txt` before committing. **The
  supervisor regenerates it at integration.**
* `scripts/gates.py` is generated and outside my scope. The newly archived E2 scripts
  should be added to `ARCHIVED_PATHS`. Until then, editing them makes the fast-gate
  selection treat them as uncovered canonical paths.
* `Specification.md` needed no change; it is digest-pinned in PROVENANCE-R6.
* Not in my scope, possible follow-ups:
  * `GW/Bridge/GPPModel.lean` docstrings ("the HL f-sum constraint", "f-sum tail")
    and `Bloch.lean:62` ("HL f-sum parameter") would read better as "HL prescription"
    (F2);
  * `GW/Bridge/EpsCompare.lean` / `EpsQ0Sigma.lean` docstrings might get an F1 note;
  * `docs/review/index.html` / `make_review.py` were not checked for scope wording
    beyond a grep.

## Commands and results

* `python3 <scratch>/strip.py GW/Bridge/Cor.lean GW/Bridge/Compare.lean`: strips Lean
  comments and compares with `HEAD`. Result: "code identical: True" for both.
  `wc -l Cor.lean`: 801 before and after.
* `python3 docs/reviews/counterexamples.py`: exit 0, and the output equals
  `counterexamples.json`.
* `python3 scripts/registry.py --check`: FAILED, drift in PROVENANCE-R6 only (expected,
  see above).
* `python3 scripts/registry.py`, then `bash scripts/verify.sh --gate fast --jobs 4`:
  see the result line below.

**Fast gate: PASS**, 497.8 s wall (`artifacts/verification-fast.json`, untracked;
status `passed`, `not_verified` empty). It ran with the locally regenerated
PROVENANCE-R6, which was then restored to `HEAD`. Its steps:
* registry check;
* `lake build GW` (Cor/Compare rebuilt);
* the memoized default-library audit;
* 9 test modules, all exit 0: 3 workflow, plus `test_bridge_disc`,
  `test_bridge_measure`, `test_bridge_q0`, `test_endpoint_a`, `test_endpoint_a2` and
  `test_endpoint_e1`, selected by the change.

The run reported `archived_changed: PROVENANCE-R6.txt`; that was the local
regeneration. At the committed tree, `registry.py --check` reports the expected
PROVENANCE-R6 digest drift for `THIRD_PARTY_NOTICES.md`, so a fast gate on the committed
tree fails at the registry step until the supervisor regenerates it.

Pitfall: my gate log in the session scratchpad (`fast.log`) also picked up lines from
another R28 agent's run (`tests.test_r28_f4`, "4 test modules"). The agents share a
scratchpad path. The JSON in this worktree is the authoritative record of my run.

## Next action

1. The supervisor reviews the wording against the review and fills the placeholders
   from `docs/reviews/R28-F{1,3,4}.md`.
2. The supervisor regenerates the registries (PROVENANCE-R6 for the notices digest) and
   adds the E2 scripts to `gates.ARCHIVED_PATHS`.
3. Owner: confirm the `THIRD_PARTY_NOTICES.md` licence-section correction and the
   applied open-question labels.
