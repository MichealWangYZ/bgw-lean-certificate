# LL-C1-R1 handoff — repair of the reviewed checkpoint

```
Status: CHECKPOINT_READY
```

Not self-acceptance. I stopped here; C2 was not started, nothing was pushed,
`main` was not merged, and no licensing or visibility setting was touched.

## Base, result, versions, elapsed

* Reviewed base: `cf49853` (LL-C1). Task branch base:
  `review/ll-c1-r1-20260914` at `552cca8`.
* Work branch `ll-c1-r1/repair`, isolated worktree. Result commit **`0ef9ab9`**
  (a handoff commit follows).
* Lean 4.19.0 / Lake 5.0.0-6caaee8, mathlib `c44e0c8`, Python 3.12.3.
* **Elapsed active wall time: ~27 min** (`04:21:47Z` → `04:48:20Z`), against a
  3-hour allowance. The 45-minute no-new-evidence limit was never approached;
  no obstruction lasted more than a few minutes.

**All five findings were reproduced before anything was changed.** None was
taken on the review's word, and all five were real.

## A. Portable checkout — pass

`.tools` was tracked as mode `120000`, an absolute symlink to
`<repo>/.tools`. I introduced it in LL-C1 with a
careless `git add -A` in a worktree where I had created the link by hand.

Mechanism confirmed without touching the real installation (the review noted a
host where the target exists should record this as skipped): in a scratch
directory, `mkdir -p .tools` over a dangling symlink exits **1** with
`cannot create directory '.tools': File exists`. `scripts/bootstrap.sh` runs
under `set -euo pipefail`, so it aborts on its fifth line.

Repair: `git rm --cached .tools` (on-disk link preserved), and the ignore rule
changed from `.tools/` to `.tools`, since the trailing slash matches only a
directory and therefore did not cover the symlink that caused this.

**Verified from a genuinely fresh, independent checkout**, not from the old
worktree:

```
git clone --no-hardlinks --branch ll-c1-r1/repair <repo> /tmp/llc1r1-fresh
bash scripts/bootstrap.sh    # exit 0, 2m15s
bash scripts/verify.sh       # exit 0, 4m29s
```

`.tools` is absent from the checkout; `git ls-files -s` reports **no tracked
symlink of any mode**; bootstrap created its own `.tools` and installed elan
plus the Lean 4.19.0 toolchain (1.6 GB) from scratch.

**Dependency caches reused, stated exactly:** one — the user-level mathlib
olean cache `~/.cache/mathlib` (277 MB), which is what `lake exe cache get`
exists to consume (`No files to download` / `Decompressing 6641 file(s)`).
Everything else was obtained fresh: elan, the Lean toolchain, the mathlib
source clone, the project source, and the entire project build. No project
binary and no untracked project source was inherited.

## B. Honest, reproducible evidence — pass

The LL-C1 handoff said `artifacts/ll-c1/lean_values.json` and
`comparison.json` were "both committed on the branch". **They were not.**
`artifacts/` is ignored, so `git add -A` never staged them, and a fresh
checkout of `cf49853` does not contain them — which is also why
`tests/test_ll_c1.py` could not run standalone there.

Corrected by a note at the head of `.agent/handoffs/LL-C1.md` pointing here;
the body of that handoff is left as submitted, so the historical claim stays
visible rather than being quietly rewritten.

Both snapshots are now **deliberately committed** (`git add -f`, two small
files only; no other ignored artifact was added and no manifest scope widened).
`ll/make_comparison.py` regenerates the comparison from the Lean output by one
deterministic command; every `exact_match` and `detected` field is computed
while it runs.

```
lake build ll_c1_eval && ./.lake/build/bin/ll_c1_eval > artifacts/ll-c1/lean_values.json
python3 ll/make_comparison.py
```

In the fresh checkout, the Lean binary regenerated `lean_values.json`
**byte-identically** to the committed copy, and `make_comparison.py`
regenerated `comparison.json` byte-identically (`git status --porcelain
artifacts/ll-c1/` empty after both). Committed status: both tracked; both
reproducible; 18/18 exact, 7/7 mutants detected.

## C. Checker fixes and regressions — pass

Reproduced the review's probes first with its archival script:
`ordinary_wrong_value_control` → 1 failure (correctly caught);
`wrong_duplicate_before_correct_row` → 0 failures (**false pass**);
`out_of_bounds_external_indices` → 0 failures (**false pass**).

Both defects were mine and both are the same underlying mistake — *metadata
supplied by the artifact under test was never checked against anything*:

* rows were keyed straight into `{row["name"]: row for row in values}`, so a
  later correct row silently overwrote an earlier wrong duplicate;
* the row's own `N`, `i`, `j` were never read. The arithmetic used the Python
  reference's indices, so `i = j = 999` at `N = 1` was simply decoration.

`validate_rows` now rejects duplicates **before** dictionary construction,
enforces the exact fixture inventory and row count, and checks `N`, `i`, `j`
against the named fixture with bounds `0 ≤ i,j < N`. Type is checked with
`type(x) is not int`, not `isinstance` — `bool` is a subclass of `int` and
would otherwise pass as an index. Exact rational comparison is unchanged and
still catches an ordinary wrong value.

Eight regressions migrated into `tests/test_ll_c1.py` (scientific gate), not
left in the archival reproducer: real table validates; wrong duplicate
rejected; out-of-bounds rejected; metadata disagreeing with its fixture
rejected; `bool` rejected; `float` rejected; missing and extra fixtures
rejected; ordinary wrong value still caught. `tests/test_ll_c1.py` 13 → 21.

`ll/*.py` added to the existing `source_hashes()` coverage in
`scripts/verify.py` — the existing mechanism, no new registry.

**Scope of this finding:** it concerns the parser/evidence boundary. It does
not show the LL-C1 Lean outputs were wrong, and it does not show a corrupt
table survives the full fresh-generation gate. The fresh run above in fact
reproduced the values byte-for-byte.

## D. Mathematical scope narrowed — pass

`samePair`, the three ring data definitions and all ring identities are
**unchanged**; no bug required touching them.

Documentation now states that the compressed site/edge representation has a
*demonstrated interpretation for these loopless rings*, not a proved general
equivalence to all Lin–Lindsey half-edge diagrams.

The counterexample is machine-checked rather than only described:
`GW.LL.loopExample` carries a self-loop `(int 0, int 0)`, and
`GW.LL.loopExample_compressed_card : Fintype.card (Aut loopExample) = 1`. In an
explicit half-edge model the loop's two flags may be exchanged with all site
and edge identifiers fixed, giving 2. So the compressed model undercounts
there. None of `ring0/1/2` contains a loop, so this bounds the claim rather
than refuting anything — consistent with the review, and it is **not** a
`ROUTE_REFUTED` condition.

Also recorded in the source: the structure does not enforce well-formed quartic
incidence, so an arbitrary `FeynDiagram` is not thereby a physically valid
diagram; and the polynomial identities hold for **arbitrary** matrix entries,
whereas reading the stored-order disjunction as preserving the contracted
*value* is a different statement that does use symmetric `G` and `v`. No
general well-formedness hierarchy and no universal half-edge library was built.

I have not labelled the source-to-paper correspondence kernel-verified. It
rests on my reading of the PDF plus a Python cross-check; a general-ring task
can prove the lift explicitly.

## E. Reuse and community check — pass

The locally reimplemented `consEquiv` is replaced by pinned mathlib's
`Fin.consEquiv` (`Mathlib/Data/Fin/Tuple/Basic.lean:185`,
`def consEquiv (α : Fin (n+1) → Type*) : α 0 × (∀ i, α (succ i)) ≃ ∀ i, α i`),
specialised to the constant family. The single caller `sum_over_pi_succ`
compiles unchanged otherwise; no style sweep.

Why I missed it in LL-C1: I grepped `Mathlib/Logic/Equiv/Fin/*.lean` and one
`Data/Fin/Tuple` pattern for `def consEquiv` and concluded it was absent. The
definition was in `Data/Fin/Tuple/Basic.lean` the whole time. The lesson is
about the search, not the library.

Physlib check (~10 min, within budget). `AI-POLICY.md` requires that *"all
communication with human reviewers must be conducted by humans, not by an AI
agent"*, that the author *personally* verify bibliographic references
("that the work exists, that the cited statement is accurate, and that page
numbers are right"), that the author independently verify AI-implemented review
feedback before re-review, and states the human author is *"fully responsible
for every line of the PR, however it was produced"*. It is therefore **not a
demonstrated drop-in dependency** here: it is a policy plus a work-in-progress
library on a different toolchain, and adopting it would be a dependency
decision plus human obligations, not an import. No migration, adapter or
upstream contact was attempted, and none is recommended now.

## Verification

| Command | Exit | Result |
|---|---|---|
| `bash scripts/verify.sh` (repair worktree) | 0 | PASS |
| `bash scripts/bootstrap.sh` (fresh clone) | 0 | 2m15s |
| `bash scripts/verify.sh` (fresh clone) | 0 | 4m29s, PASS |
| `python3 ll/make_comparison.py` | 0 | 18/18 exact, 7/7 detected |
| `python3 audits/ll_c1_review/review_checks.py` | — | reproduced both false passes on the reviewed base |

Fresh-checkout gate: **248 tests** (234 scientific, 14 workflow), **118 named /
247 exhaustive** theorem audits, `AUDIT_MODULE GW.LL.Diagram` and
`GW.LL.Ring` both present, only `propext`, `Classical.choice`, `Quot.sound`.
No `sorry`, `admit`, `native_decide`, or custom axiom.

The exhaustive count moved 248 → 247. My reading: removing the local
`consEquiv` removed its two structure-field proofs (`left_inv`, `right_inv`)
and `loopExample_compressed_card` added one. Stated as inference, not measured
term by term.

`bgw/weighted_audit/PROVENANCE-R6.txt` digests were refreshed for the two
covered files this task changed (`scripts/verify.py`, `GW/Audit.lean`) using
the existing `scripts/make_manifest.py`, which only re-hashes already-listed
paths. Its claim scope was not enlarged.

## Generated vs committed artifacts

| Path | Status |
|---|---|
| `artifacts/ll-c1/lean_values.json` | **committed**, and regenerated byte-identically by `ll_c1_eval` |
| `artifacts/ll-c1/comparison.json` | **committed**, and regenerated byte-identically by `ll/make_comparison.py` |
| `artifacts/tests-*.log`, `axioms.log`, `named-axioms.log` | generated by the gate, ignored, not committed |

## Remaining assumptions and open items

1. The half-edge ↔ compressed correspondence is *demonstrated* for the three
   loopless rings, not proved. A general-ring task should prove the lift.
2. `FeynDiagram` does not enforce quartic well-formedness; the three rings are
   given explicitly and are valid.
3. Three rings say nothing about general `k`, formal series, skeleton theory,
   electronic GW, or BerkeleyGW.
4. The review's own limits stand: it did not rerun the Lean build or the gate,
   and its 18 values are Python recomputations.

## One recommendation

**Accept for independent review** — that is a recommendation, not an order, and
not self-acceptance.

If accepted, the next bounded task I would propose is unchanged from LL-C1: a
structural all-order ring theorem (`Aut(ring k) ≃ (Fin k → Bool)` for general
`k`, plus the general contraction identity), which would also be the natural
place to prove the half-edge lift that item D leaves open. It needs its own
explicit task and allowance; it is not authorized here, and it is not formal
resummation, skeleton theory, electronic GW, or BerkeleyGW verification.
