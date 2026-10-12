# T-003 Independent Review

Status: needs repair, not accepted. Supervisor: Codex.
Review date: 2026-09-11. No weighted-mismatch follow-on was started.

## Findings

### F1: Successful checker exit does not enforce the record contract

Priority: high. `bgw/occupation_audit/check_occupation.py:151-168,222-247`.
Changing the first saved record's `sch` to 1.0 still returns exit 0, while
printing `all_sch_zero: false`. That value is inconsistent with branch 2's
explicit `sch = 0`, and it changes the reported accumulated local value.
Changing `ssx_pre` to 999999 also exits 0 with a reported clamp despite the
saved probe's unclamped contract. The only numerical exit gate uses `ssx_post`.

The checker also accepts `omega2 = 999999`, `efermi = 999999`, and an exported
`den_nearpole = 0` in the first record. These recorded quantities are ignored
or replaced by recomputation, so successful arithmetic comparison does not
validate the promised exported-source consistency. Derived intermediates need
appropriate measured residual checks, not exact equality to rounded Fortran.
The half-occupation source condition needs its own consistency check.

### F2: Tally and sample integrity are not enforced

Priority: medium. `check_occupation.py:59-84,178-216`.
Changing the qualifying event tally from 3702 to -1 still exits 0; the probe
only tests equality to zero. Repeating one record 48 times with the same record
ID also passes. Tally parsing permits duplicate or unknown rows and does not
require nonnegative counts or the complete control contract.

The CLI also accepts a one-record file by default. One valid record can prove
existence, but that mode must not be confused with validation of the saved
48-record export. The saved-fixture path needs an explicit coverage/integrity
contract; optional subset analysis should be clearly separate.

### F3: The default invalid-mode policy is stated incorrectly

Priority: medium. `bgw/occupation_audit/REPORT.md:108-114`, also original
worker handoff source deduction S9.
`Sigma/inread.f90:82` initializes `sig%invalid_gpp_mode = -1`; the only other
assignment reads the optional input keyword. In `Sigma/mtxel_cor.f90:779-797`,
case 0 chooses zero, but case default chooses `CMPLX(1d0/TOL_ZERO, 0d0)`.
Thus the report's assertion that the default maps invalid modes to zero is
false. Even for an explicit zero-mode policy, generic versus dropped behavior
depends on the predicate, as the report's next bullet itself acknowledges.
Correct the policy-specific exclusion argument; do not generalize it to all
invalid modes. This correction does not erase the directly observed witness.

## Independent Positive Checks

- `bash scripts/verify.sh`: PASS, completed 2026-09-11 15:18:58 UTC.
  60 named / 126 exhaustive theorem audits, 17 Lean cases, 53 Python tests.
- All 24 digest/path pairs in the submitted PROVENANCE.txt match the files,
  including source, instrumented binary, reused inputs, fixtures, and reports.
- Applying the saved instrumentation patch to the pristine source recreates
  the actual instrumented source byte-for-byte. No accepted tree was modified.
- Fresh control execution: exit 0, counts and sigma log match archived output.
- Fresh manual-Fermi probe: exit 0, counts, sigma log, and all 48 exported
  records match archived output byte-for-byte; 3702 qualifying events recur.
- Fresh smearing probe: terminates with SIGABRT (Python return code -6,
  conventionally shell exit 134) and the expected input-validation message.
- The unchanged checker passes the freshly generated 48 records when invoked
  with `--min-records 48`; measured maximum SX residual is
  4.2435598287864196e-19. Its adversarial failures remain separate findings.

All executions used the existing instrumented binary and copied upstream
inputs in fresh directories, not a clean compiler/toolchain build.

## Evidence

- `artifacts/t003-codex-review/checker-mutation-results.json`: reproducible
  positive result and eight accepted corrupt/incomplete-input cases.
- `artifacts/t003-codex-review/provenance-check.json`: 24/24 digest checks.
- `artifacts/t003-codex-review/runs/report.json`: fresh execution results.
- `artifacts/t003-codex-review/runs/{control,fermi,smear}/`: full fresh outputs.
- `artifacts/t003-codex-review/runs/checker.json`: fresh-record arithmetic check.
- `artifacts/verification.json`: independent gate logs and input hashes.

## Decision and Next Action

The executed half-occupation witness and smearing rejection are independently
reproduced, subject to the original physical caveat: the manual Fermi-level
probe is charge-inconsistent and does not establish a realistic material error.

T-003 as a complete audit/checker milestone is not accepted until F1-F3 are
repaired and regression-tested. Prepared `.agent/tasks/T-003-R1.md` for Claude;
it has not been dispatched. Codex did not implement the repairs during testing.
No Lean/specification change, new materials search, or weighted-mismatch study
is authorized by this review.
