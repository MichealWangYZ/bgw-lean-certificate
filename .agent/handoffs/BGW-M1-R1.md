# BGW-M1-R1 handoff — repair the delivered production evidence

```
Status: CHECKPOINT_READY
```

Not self-acceptance. No `main` merge, no stack cleanup, no visibility or
licensing change, no upstream contact, no paid resource, no BGW-M2, no new
scientific target. Commit/push and the private review PR are under the owner's
standing grant.

## Base, result, active time

* Base: PR #14 at `6c30d50`, branch `bgw-m1/production-screening`.
* **Active time ~10 min** (`19:55:49Z` → `20:05Z`) of the 2-hour allowance;
  access/baseline preflight ~5 min of its 20-minute cap. No no-progress rule
  fired; no obstruction needed a second approach.
* The reviewed 8×8 inverse certificate and its numerical result are preserved
  unchanged. `E`, `V`, `Rref` literals are untouched; the review reconstructed
  them independently and matched the Git blob, and
  `regenerate_certificate.py --check` still reproduces them from the dump.

## Every finding reproduced before repair

All measured against the **committed** slice, not a synthetic table.

| Finding | Reproduced |
| --- | --- |
| corrupted complete q=2 block **then** good q=2 block | ACCEPTED, and the corrupt values were silently discarded (`E00` = the good `3.104321`) |
| unterminated corrupted block **then** good block | ACCEPTED |
| good slice **plus** unexpected q=99 | ACCEPTED, blocks `[2, 99]` |
| duplicate-entry test placed the duplicate **after** `QEND` | confirmed at `tests/test_bgw_m1.py:90` — it exercised the outside-a-block branch |
| dump-hash test only asserted length 64 | confirmed, with a comment of mine rationalizing it |
| `patch -p1` per the documented command | failed: `can't find file to patch`, absolute headers |
| handoff said "~1 h 24 min" | `05:39:19Z → 06:03:02Z` is **23 min 43 s**; my figure was a subtraction error |

## 1. Input boundary repaired

`bgw/m1_screening/extract.py` now rejects, at block close or on sight:

* a **repeated q id** — the error message names the cause, that the Fortran
  instrumentation opens its output in **append mode**, so one file can hold two
  runs and silently keeping the last block would let a corrupted run be masked
  by a later good one;
* a `QSTART` while a block is still open;
* a `QEND` that does not match the open block, and data outside any block;
* an **in-block** duplicate label, a missing label, an out-of-range label, an
  inconsistent `nmtx`, a malformed `QSTART`, and an empty dump.

New `load_single(path, iq, expected_n, expected_q)` requires the inventory to be
**exactly** `{2}`, with `nmtx` and `q` matched against the specification rather
than against whatever the file contains. `matrices()` now refuses a block that
did not close validly.

Re-running the review's probes after the repair:

```
  control (unchanged)                ACCEPTED  <- correct
  corrupted q2 THEN good q2          rejected: q 2 appears twice; the dump is appended to...
  unterminated corrupt THEN good     rejected: QSTART 2 while q 2 is still open...
  good PLUS unexpected q=99          rejected: expected exactly q {2}, found [2, 99]
  duplicate EPSPRE INSIDE block      rejected: duplicate EPSPRE key (1, 1) inside q 2
  QEND with wrong id                 rejected: QEND 7 closes q 2
  data line outside any block        rejected: EPSPRE outside a q block
```

All migrated into `tests/test_bgw_m1.py` as `RunBoundaryIsRejected` (6 tests)
plus the in-block duplicate and out-of-range cases in `ExportIsExact`. Ordinary
wrong pre- and post-inversion values with consistent bits and decimals still
fail the comparison, and the unmodified control still passes.

**Freshness, not deletion:** the reproduction below ran in a *new* directory
rather than reusing one. No existing run data was truncated or removed.

Snapshot pinning: `SnapshotIsPinned` asserts the dump and basis slices equal
their **recorded constants** (`047557fe…`, `5060298f…`) via
`extract.require_sha256`, and a replaced snapshot is rejected. The expectation
is a constant in the test, never recomputed from the data under test.

Tests: **21 → 34**.

## 2. Provenance packet completed

`bgw/m1_screening/PROVENANCE.md` rewritten. Added the previously missing
linkage: `WFN`/`WFNq` SHA-256, the exact small-run `epsilon.inp` (content and
hash), the build identity (`arch.mk` hash, compiler path, `-O2`, OpenBLAS
0.3.34, flavor selection), the **built executable** SHA-256, the run log hash,
and committed log evidence including `Job Done`, `nmtx: 8` and the q line.

**Ordered retained basis recovered and committed.** The instrumentation now also
writes `GVEC` records — to a **separate file**, deliberately, so the reviewed
`m1_eps_dump_q2.txt` snapshot stays byte-identical. `data/m1_gvec_q2.txt` gives
all eight G vectors in crystal coordinates with `ekin = |q0+G|²` in Ry:

```
1 ( 0, 0,-1)  0.281206072713701      5 ( 0,-1,-1)  1.031088933283572
2 ( 0, 0, 0)  0.281206072713701      6 ( 0, 1, 0)  1.031088933283572
3 (-1,-1,-1)  1.031088933283572      7 ( 1, 0, 0)  1.031088933283572
4 (-1, 0,-1)  1.031088933283572      8 ( 1, 1, 0)  1.031088933283572
```

**Two** distinct `|q0+G|²` shells, which is precisely why `vcoul` takes two
distinct values and therefore why `E` is unsymmetric. A test ties the count of
distinct `ekin` values to the count of distinct `vcoul` values, so the basis and
the matrix corroborate each other.

**Patch fixed.** Regenerated with relative `a/Epsilon/epsinv.f90` and
`b/Epsilon/epsinv.f90` headers; new SHA-256
`046456cc941bc3bcbc00f5dd2304aaa2d26aa8c1a7a41fe439a862d2314cd77d`. Validated by
applying it with `-p1` to a **hash-checked** pristine copy and comparing the
result byte-for-byte against the instrumented tree (`IDENTICAL`). The
documented command now uses an absolute `$PATCH` because it `cd`s first, and it
records the real-flavor `make clean` step that the stale-`.mod` failure requires.

**Regeneration check added.** `bgw/m1_screening/regenerate_certificate.py --check`
recomputes `E`, `V` and `Rref` from the committed dump and compares them against
the Lean literals; it never edits the module, so drift fails rather than being
silently absorbed. Exit 0.

**Determinism verified.** A fresh run in a clean directory with the pinned
inputs reproduced `data/m1_eps_dump_q2.txt` **byte-identically** (same SHA-256).

**Instrumented ≠ pristine, stated plainly.** The log lines used as a
cross-check come from code paths the patch does not touch, but they are printed
*inside the instrumented run*. That shows the dump agrees with what the
surrounding un-patched code reports; it does **not** establish that the
instrumented and pristine executables agree. No separate pristine run at this
cutoff was performed, and `PROVENANCE.md` now says so.

**Durability, not overclaimed.** The `/tmp` paths are recorded as locations but
explicitly labelled *not durable provenance*; what is durable is the hash set
plus the committed slices. Retention beyond this session was not checked and is
not claimed. Nothing large was added to Git: the new committed files total
~11 KB.

## 3. Evidence claims corrected

Thresholds **unchanged**, as the brief requires, but now described accurately as
**input-dependent engineering rules**, not universal proved LAPACK bounds — the
proved statements in this milestone are the Lean theorems. The criterion in use
is labelled a **max-entry** normalized residual.

A standard ∞-norm residual `‖EX−I‖∞ / (‖E‖∞‖X‖∞)` is **added alongside** without
replacing the original comparison: measured `7.008168410280357e-17`. The review
reported `5.5620368e-17` for an ∞-norm variant; that differs from mine by
normalization choice, and I am recording my formula rather than claiming
agreement with a number I cannot reproduce from the stated definition. Either
way the conclusion is unchanged.

**Predeclaration disclosed honestly.** The rules were written before the
comparison in this session, but version history alone cannot establish that
ordering to a third party and no contemporaneous external record exists. No past
preregistration was fabricated; the rules are unchanged and were frozen before
the R1 reproduction.

**Time reconciled.** `~24 min`, not `~1 h 24 min`. The printed interval was
right and my figure was wrong — a subtraction error, not a budget overrun.
Corrected in place in `.agent/handoffs/BGW-M1.md` with the cause.

**M2 expectation corrected.** My BGW-M1 recommendation ("certify `E = I − V·chi`
upstream") was too strong. Exact formation `E* = I − V̂·χ̂` generally differs from
the **stored** `Ê` by rounding, and M1 certifies `Ê⁻¹`. A future BGW-M2 needs
independently exported `χ` (not `recover_chi`, which cannot close this
non-circularly), an explicit `E*`/`Ê` distinction, and either a certified
represented reference or a concrete rounding bound. Also recorded: the current
`Wref` is derived from `Rref` and `V` and has **not** been compared against an
exported production `W`. "Certified end to end" is not claimed.

## Commands and outcomes

```
patch -p1 < $PATCH  (hash-checked pristine copy)        applied, IDENTICAL
cp flavor_real.mk flavor.mk && make epsilon             exit 0
epsilon.real.x in a FRESH directory (cutoff 1.5)        exit 0, "Job Done"
   -> m1_eps_dump_q2 slice sha256 == 047557fe…          byte-identical
python3 bgw/m1_screening/regenerate_certificate.py --check   exit 0
python3 -m pytest tests/test_bgw_m1.py                  34 passed
python3 scripts/verify.py --gate all                    exit 0
```

Gate: **397 scientific + 14 workflow** tests (was 384 + 14); **240 named / 657
exhaustive** audits; `AUDIT_MODULE GW.BGW.M1Screening` present; axioms limited
to `propext`, `Classical.choice`, `Quot.sound`. No existing theorem, fixture,
target or GPP scope changed. The Lean certificate rebuilt and re-audited.

## What was reproduced versus rechecked

* **Freshly executed:** the BerkeleyGW rebuild, a new production run in a clean
  directory, the patch application, the full Lean build and exhaustive audit,
  the whole Python gate.
* **Rechecked against retained evidence:** nothing essential — the production
  case was genuinely re-run, and its dump matched the committed snapshot bit for
  bit.
* **Not done:** a separate pristine-executable run at this cutoff; any
  comparison against an exported production `W`.

## Remaining gaps

1. Formation of `E` from `chi` is still a declared input, and closing it is
   BGW-M2 with the `E*`/`Ê` distinction above — not a simple extension.
2. No pristine-versus-instrumented executable comparison at this cutoff.
3. `Wref` is derived, not compared against production `W`.
4. Predeclaration ordering cannot be independently established for the original
   comparison.

## One recommended next decision

**Accept or reject this repair, then scope BGW-M2 with the `E*` versus `Ê`
distinction written into its contract.** The cheapest thing that would retire
gap 2 at the same time is a single pristine-executable run at cutoff 1.5 with a
diff of the printed epsilon/epsilon-inverse lines — minutes of work, and it
converts the cross-check from "internally consistent" to "instrumentation
demonstrably neutral". I did not do it here because it is outside this brief's
required changes.
