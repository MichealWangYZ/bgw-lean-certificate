# Independent audit: occupation-checker false passes

Reviewed base: `374459f33088f1700ce57adf690da81b2461b382` (main as read on 2026-09-14).
This is a separate audit track, not a repetition of the earlier branch-boundary
physics review. No production code, Lean proof, accepted fixture, gate, or
acceptance record is changed by this branch.

## Execution and limits

Eight focused tests were executed: **three controls passed and five regression
assertions failed**. These are deliberately ordinary failing assertions, not
`expectedFailure` decorations or a green "we reproduced a bug" suite.

The tests import `bgw/branch_boundary/analyze.py` and feed its real parser and
`occupation_report` synthetic OCC/OCCCHK subtables. The local copy used for
execution was reconstructed from the GitHub connector's file contents and
verified byte-for-byte against Git blob
`1e16806f2746b5997de9c64286af6c6264bb463c` (SHA-256
`c06eec8ac02f4bbc57c642cc2635fdf473438e49104b84f3b092c0977bbfacba`).
The execution environment was Python 3.13.5.

This was **not** a full repository/toolchain build. The Lean audit, the full
Python suite, BerkeleyGW, and the standalone Fortran driver were not rerun.
The adversarial inputs are not material data. Nothing here establishes that
the saved measurements are wrong, or that edited committed fixtures would
escape the complete provenance, saved-summary, and optional recompile checks.
The demonstrated failures are at the parser/occupation-report boundary used
by those downstream checks.

Run from the repository root:

```sh
python3 -m unittest discover -s audits/checker_soundness -p 'test_*.py' -v
```

On the reviewed base, expect eight tests and exit 1 with five failures.
`evidence.json` records the measured outcomes without nonstandard JSON NaNs.
The audit tests live outside the normal gate intentionally and are not claimed
to be part of it. After repair, migrate the relevant tests into the scientific
suite rather than leave another parallel framework behind.

## F1: non-finite observations can report zero numerical error

Priority: high for the evidence checker.
Source: `bgw/branch_boundary/analyze.py:49-85,302-313`.

`parse_text` converts numeric fields with `float` but does not reject NaN.
The consistency check `abs(delta - recorded_delta) > 0` then fails to reject a
NaN difference. In the tested row order, `max(0.0, nan)` leaves the running
maximum at zero; the spread reduction likewise hides a later NaN.

Reproduction: replace the P2 half-occupation `gen_value`, `delta`, and
`closed_form` by NaN, leaving the other observations unchanged. The actual
analyzer returns:

- `max_relative_closed_form_error = 0.0`;
- `max_relative_spread = 0.0`;
- a non-finite half-occupation ratio.

That is not merely accepting an unusual input: it emits perfect-looking error
metrics despite an invalid observation. The finite reference row is retained,
so this probe does not depend on every field becoming NaN.

Small repair: reject non-finite OCC inputs before arithmetic, validate derived
metrics before returning them, and use strict JSON emission (`allow_nan=False`)
as a final guard. Any intentionally non-finite singular-point diagnostics in
other row types need an explicit separate status, not numerical success.

## F2: a data-supplied oracle hides a 100% equation error

Priority: high for independent verification; not a claim of a wrong GW result.
Source: `bgw/branch_boundary/analyze.py:291-325` and
`tests/test_branch_boundary.py`, `PartialOccupationTests`.

`occupation_report` compares `gen_value - np_value` to the same table's
`closed_form` column. It does not reconstruct the expected expression from
`occ`, `ieps`, `wt`, and `wxt`. The test method that independently calls
`analyze.closed_form` does so for P1 only; the other points rely on the reported
residual. These are source observations, not a claim that the full suite was
executed on our mutants.

The synthetic baseline uses four points with `x=3*w`. Their values are exactly
representable:

```text
generic = ieps * (1/4 - occ/8)
near    = ieps * occ/8
delta   = ieps * (1-occ)/4
```

Reproduction: for P2 only, double both candidate values, their difference, and
the supplied closed-form column, while keeping all physical inputs fixed.
The measured discrepancy has **100% relative error** against an expression
recomputed from those inputs. Nevertheless, both reported error metrics remain
zero. This is a correlated-error blind spot: checking a number against another
column produced by the same calculation is not an independent oracle.

A second probe changes `ieps` in just P2's half-occupation row while retaining
all outputs. The report still claims zero spread and zero closed-form error,
although the independently reconstructed equation now has 50% relative error.
The purported linearity test does not enforce fixed non-occupation inputs.

Small repair: recompute the expected discrepancy for every point and every
occupation. On the same nonsingular, positive-real, unclamped domain as the
mapped identity, a useful independently arranged expression is

```text
Delta = (1-occ) * ieps * wt / (2*(x-wt)).
```

This follows by combining the two fractions in the existing mismatch theorem;
it is not a post-clamp identity. Use exact rationals for the recorded binary64
inputs where practical. Check the supplied closed-form column separately as an
output, and require fixed `(ieps, wt, wxt)` within each point's occupation sweep.

## F3: occupation evidence can be omitted or duplicated silently

Priority: medium; coverage/integrity, not an observed numerical error.
Source: `bgw/branch_boundary/analyze.py:291-325`.

The report loops over OCCCHK, not over an independently validated inventory of
OCC points. Deleting P2's OCCCHK row leaves all sixteen OCC observations present,
but the report silently returns only P1, P3, and P4. Conversely, appending a
second P2 half-occupation row increases the observation count from sixteen to
seventeen without affecting the report: the occupation-keyed dictionary
silently overwrites the earlier entry.

Small repair: require matching point sets between OCC and OCCCHK, exactly one
OCCCHK row per point, and unique `(point, occ)` observations. The T-005 full
fixture should additionally enforce its declared four-point/four-occupation
inventory. A separately requested subset mode can use an explicit different
contract; it should not masquerade as full coverage.

## What passed, and what not to add

The unmodified synthetic data give the expected exact identity at every row.
The existing parser rejects a shortened row, and the existing delta-consistency
check rejects an ordinary finite one-column mutation. The checker is not
wholly ineffective: these particular correlated/non-finite/coverage cases
expose gaps its present checks do not cover.

The repair does not need a new orchestration system, schema generator,
provenance generation, or documentation gate. A small OCC validation function,
one independently reconstructed equation, and these bounded regressions are
sufficient for the demonstrated failures. Keep the Lean proofs unchanged;
these findings concern the path from numerical observations to reported
verification metrics, not the truth of those proofs.
