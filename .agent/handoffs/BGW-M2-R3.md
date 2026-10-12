# BGW-M2-R3 — close the remaining input-preservation holes

**Status: CHECKPOINT_READY. Not accepted by me.**

Base: `1eab8fa76830f6c9249dae10c1ec2cc14295db3b` (PR #17 head after R2).
Active time: ~40 min, mostly the native A/B rebuild and two Lean elaborations.

The recheck at `1eab8fa` confirmed findings 1 and 3 repaired and found two
remaining holes in finding 2. Both reproduced before repair. Snapshot, budgets,
Lean literals, theorem program and scientific scope are unchanged; no Lean
source changed at all in this pass.

## 1. A supplied input that is itself a symlink fell out of the baseline

`need` dereferences (it hashes bytes), but `tree_digests` skipped every
symlink. So with

```text
inputs/WFN       -> ../data/WFN      supplied by the caller
run-pristine/WFN -> inputs/WFN       created by this driver
```

`data/WFN` was in neither baseline. Reproduced with disposable fixtures: a
mocked native step writing through `run-pristine/WFN` changed `data/WFN` and
`reproduce` returned `0`.

`tree_digests(root, *, follow=True)` now dereferences; a dangling link
contributes nothing because `is_file()` is False for it. An input path that
**exists** but cannot be digested — dangling link, directory, device — is
refused before the build:

```
['WFN'] did not resolve to readable regular files under <dir>;
this driver cannot vouch for inputs it cannot digest
```

`os.path.lexists`, not `exists`, so a dangling link reaches that check. The
guard is scoped to paths that exist, because a genuinely absent `WFN` is
already `need`'s failure and scoping it this way keeps the reviewer's own
PR #19 probe — which mocks `need` out and supplies no wavefunctions — working
unchanged.

On the real fixture this widened the source baseline from **1980 to 2096
files**; those 116 are the dereferenced escaping symlinks.

## 2. The input comparison ignored additions

The source comparison counted new keys; the input comparison iterated over the
"before" map only. A new `inputs/unexpected.dat` was reported as unchanged.
`_differences(before, after)` is now one rule — modified, removed **and**
added — applied to both trees.

## 3. Docstring wording

`--full` "never writes inside TREE or DIR" overstated a detection-only
contract. It now says the driver issues no write of its own there and its
copies cannot reach back, but the run directories link at the supplied
wavefunctions, so what is established is that nothing changed on this run —
not that a write is impossible.

## 4. The meta-check no longer maintains a copy of `decides`

Raised as non-blocking durability. `_decides_without_inversion_guard()` now
parses `decides`' own source, removes the single `if` whose test is
`ref.inf_norm(ref.matsub(Xhat, Rh)) > binv`, and compiles the result. The
guard-free checker is therefore this head's decision rule minus exactly one
statement, and the derivation raises if that statement is not found exactly
once. The hand-written duplicate is deleted.

## Regressions added

| Test | Guards |
| --- | --- |
| `test_a_symlinked_supplied_input_is_still_covered` | finding 1; asserts the probe really corrupted the target before asserting detection |
| `test_a_new_file_in_the_inputs_directory_is_reported` | finding 2 |
| `test_an_input_the_driver_cannot_digest_is_refused` | the dangling-link refusal |

## Commands and results

```
python3 -m pytest tests/test_bgw_m2.py             49 passed  (was 46)
acceptance_regressions.py (review's PR #19, verbatim)   7 OK
python3 bgw/m2_screening/run_m2.py --full --proof  exit 0
python3 scripts/verify.py --gate all               exit 0
```

Gate: **446 scientific + 14 workflow**, **260 named / 698 exhaustive** audits.
Evidence regenerated at this head because `run_m2.py` changed and the replay
log pins its digest: `bgw/m2_screening/evidence/full-proof-replay.log` and
`proof-corruption.log` (literals exit 0, `--proof` exit 1).

## What is still not established

Unchanged. The driver **detects** modification of the supplied source and
inputs — now by content, through supplied symlinks, counting additions — and
does not prevent it. Everything else in M2's non-claims list stands.

## Recommended next decision

Accept or reject the M2 package. If accepted, the χ transition-sum provenance
for one nontrivial entry, with the tutorial's absorbed denominator weighting
written into the contract.
