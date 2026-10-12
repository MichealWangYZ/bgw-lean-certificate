# LL-C2B handoff — formal screening for the ring family

```
Status: CHECKPOINT_READY
```

**Post-review addendum (C2B review, PR #9 — `ACCEPT_FOR_INTERNAL_PROGRESSION`).**
Four nonblocking corrections were raised; I reproduced all four independently
and applied all four. Two were false statements of mine, corrected in place
below with the cause. The other two tightened the evidence path: residual tests
now run on the validated candidate matrices rather than a Python recomputation,
and exact-value encoding is now checked as a rational literal rather than by
`Fraction`-convertibility, which silently accepts `bool` and `float`. No
theorem statement changed. C3/C4 remain unauthorized and unstarted.

Not self-acceptance. I stopped here: **C3/C4 were not started**, nothing was
pushed, `main` was not merged, no dependency or toolchain changed, no timer was
installed, and no upstream community was contacted.

## Base, result, versions, elapsed

* Task base: PR #6 at `ce92b80` (C2A head). Plan branch
  `plan/ll-c2b-formal-screening-20260915` at `029efaf`.
* Result: the single commit on `ll-c2b/formal-screening` that adds this file.
  Local only — not pushed, and the branch has no upstream.
* Work branch `ll-c2b/formal-screening`, in an isolated worktree
  (`.claude/worktrees/ll-c2b`). No existing work was overwritten.
* Lean 4.19.0 / mathlib `v4.19.0` (`c44e0c8`), Python 3.12.3. Unchanged.
* **Cumulative active wall time: ~21 min** (`22:41:59Z` -> `23:03Z`, measured
  with `date -u` at the start and at each checkpoint) against a 6-hour
  allowance. Preflight ~7 min (cap 30); opening cleanup ~8 min (cap 45). The
  toolchain bootstrap and two full gate runs are inside that figure; the
  mathlib dependency build was served from cache.
  The 90-minute no-new-evidence rule was never approached; no obligation needed
  a second approach.
* Toolchain was bootstrapped fresh in this worktree (`scripts/bootstrap.sh`,
  exit 0): its own `.tools/elan` and `.lake`. One disclosed reused dependency
  cache: `~/.cache/mathlib`, via `lake exe cache get`. No inherited binary, no
  machine-specific symlink, no untracked source is required.

## 1. Opening cleanup — the evidence-reader boundary (section 2)

### Both review residuals reproduced before being repaired

I did not take either finding on report.

**Residual 1 confirmed.** `tests/test_ll_c2a.py` really did read its own table:
`cls.rows = {r["name"]: r for r in cls.data["values"]}` (a wrong duplicate is
overwritten by the correct row), `cls.orders = cls.data["orders"]` (the
candidate chooses its own coverage; `test_orders_reach_at_least_three` only
demanded `max >= 3` and `0 in orders`), and no test read a row's `N`/`i`/`j`.

I reran the review's four inputs against a byte-faithful reimplementation of
that old reader and against the new one:

| Synthetic input | Old reader | New validator |
|---|---|---|
| Wrong duplicate before the correct row | ACCEPTED | rejected: `duplicate fixture rows: ['N2-pd']` |
| `i = j = 999` | ACCEPTED | rejected: `i is 999, fixture says 0` |
| Row declares `N = 999` | ACCEPTED | rejected: `N is 999, fixture says 2` |
| `orders = [0, 3]` hiding a wrong `k4` | ACCEPTED | rejected: `declared orders [0, 3] != specification's [0, 1, 2, 3, 4]` |

**Residual 2 confirmed, and my PR #6 claim was wrong.** I read the pinned
`.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Inverse.lean` directly.
`invOfUnit`, `coeff_invOfUnit`, `constantCoeff_invOfUnit`, `mul_invOfUnit`,
`invOfUnit_mul` and `isUnit_iff_constantCoeff` are all inside `section Ring` /
`variable [Ring R]`, lines 43-110. No commutativity anywhere. My earlier
conclusion that a matrix coefficient ring blocked the off-the-shelf route came
from reading typeclass headers around `def inv` and `def inv.aux` rather than
reading the whole `[Ring R]` section. It was a missed API, not a missing
foundation. C2B uses the library interface; nothing was built around it.

### What changed

`ll/evidence.py` is now the one validator for **all three** LL evidence paths.
The boundary rule, not just four patched examples: *expected fixtures, expected
orders and expected value keys are supplied by the caller from the
specification, never read out of the table under test.*

* Extracted `_check_orders`, `_check_inventory`, `_check_row_metadata` as the
  shared core.
* `validate_table(..., value_prefix, expected_orders)` — scalar columns; the
  C1 path (`validate_rows`, `ring0..ring2`) and the C2A path (`validate_c2a`,
  `k0..k4`) are thin wrappers over it with spec-owned constants
  `EXPECTED_C1_ORDERS`, `EXPECTED_C2A_ORDERS`.
* `validate_matrix_table(..., series_keys, expected_orders)` — full-matrix
  values, for C2B (`validate_c2b`, series `W` and `T`, degrees 0..4).
* Rejected: duplicate rows, missing/extra fixtures, wrong row count,
  non-`int` metadata (`type(x) is not int`, because `bool` subclasses `int`),
  metadata disagreeing with the fixture, out-of-range indices, missing value
  columns, value columns **outside** the checked coverage, declared coverage
  that is not the specification's, wrong matrix shape, and inexact entries.
* `ll/make_comparison.py` is unchanged and still routes through the same
  module; its C1 interface (`validate_rows`) was preserved deliberately.

Regressions added: `tests/test_ll_c2a.py::ReaderRejectsBadEvidence` (10 tests,
built from a synthetic reference-generated table so they neither need nor touch
a generated artifact) and `tests/test_ll_c2b.py::ReaderRejectsBadEvidence`
(10 tests). Ordinary wrong-value controls are kept in both, so structural
validation has not displaced the numerical comparison.

`audits/ll_c2a_review/checker_probe.py` now refuses to run, by its own design,
because `tests/test_ll_c2a.py` changed — its assertions are the table above and
are migrated into the current tests.

> **Correction (C2B review finding 1).** This handoff originally reported that
> the probe prints its refusal and exits **0**, and recommended against wiring
> it into a gate. That was wrong: it exits **1**, with the refusal on stderr.
> I had run it as `... | tail -8; echo "exit=$?"`, so I read `tail`'s exit
> status, not the script's. Re-measured without the pipe: `exit=1`. The probe
> is correct as pushed and needs no change; the defect was in my measurement.
> Cause worth keeping: `$?` after a pipeline is the last command's status.

## 2. The mathematics (sections 3-4): `GW/LL/Screening.lean`

Over a characteristic-zero field `K`, arbitrary finite `N`, coefficient ring
`R = Matrix (Fin N) (Fin N) K` (noncommutative), `B = bubble G = G (*) G`:

```
AL = (1/2) • (v * B)                 AR = (1/2) • (B * v)
PL = 1 + X * C AL                    PR = 1 + X * C AR
SL = PowerSeries.invOfUnit PL 1      SR = PowerSeries.invOfUnit PR 1
W  = SL * C v
```

The `1/2` is the C2A symmetry factor `2^k` (`card_aut_ring`) distributed one
bubble at a time. Characteristic zero is a standing assumption on every
statement in the file, so that `1/2` is the physical weight rather than Lean's
totalized division — the qualification `docs/LL-C2A-REVIEW.md` asked for.

### 2.1 Both inverse identities, from the library

`constantCoeff_PL`, `constantCoeff_PR` (`= 1`), then all four of
`PL_mul_SL`, `SL_mul_PL`, `PR_mul_SR`, `SR_mul_PR`, each discharged by
`mul_invOfUnit` / `invOfUnit_mul` with the constant-unit hypothesis supplied
explicitly. Neither direction is assumed from the other.

### 2.2 The screening equations, with the orderings kept apart

```
C_v_mul_PR      : C v * PR = PL * C v          -- the bridge; both sides are ½ v B v
PL_mul_W        : PL * W = C v
W_mul_PR        : W * PR = C v                 -- P_R on the right, NOT P_L
W_eq_C_v_mul_SR : W = C v * SR
```

`v * AR = AL * v` is the only place the two orderings meet, and it is proved,
not assumed. No step anywhere commutes `v` with `B`. The fixtures include a
witness with `v B != B v`, and a mutant that substitutes `A_R` on the left is
one of the four required detections below.

### 2.3 Coefficients: closed form proved equal to the library inverse

`Wcoeff G v k = (-1/2)^k • (v * (B * v)^k)` is defined with no reference to
`W`, `SL` or `invOfUnit`. `Wexp = mk (Wcoeff G v)`. Then:

```
PL_mul_Wexp : PL * Wexp = C v            -- by coefficient extensionality
Wexp_eq_W   : Wexp = W                   -- left-multiply by SL
coeff_W (k) : coeff k W = Wcoeff G v k   -- the bridge, for EVERY k
```

This is the "connected by a checked theorem, not compared at a few orders"
requirement: `coeff_W` is a theorem quantified over `k`, obtained from a
uniqueness argument, not from agreement on a table. The recurrences follow:

```
coeff_W_zero  : coeff 0 W = v
coeff_W_succ  : coeff (k+1) W = -(AL * coeff k W)
coeff_W_succ' : coeff (k+1) W = -(coeff k W * AR)
```

### 2.4 Back to the diagrams

`hadamardSeries G U` multiplies each coefficient entrywise by `G`.
`hadamardSeries_add` proves it additive. `hadamardSeries_not_multiplicative`
exhibits an explicit `N = 2` failure over `ℚ`
(`G = !![1,1;1,0]`, `A = B = !![1,1;1,1]`: the `(0,1)` entry is `2` one way and
`1` the other), so there is no ring-hom API to transport it through a matrix
product and none is used.

`T = mk fun k => Matrix.of fun i j => contribution (ring k) G v i j` is defined
from C2A's graph data, independently of `W`. Then the identity:

```
T_eq_neg_hadamardSeries_W : T G v = -hadamardSeries G (W G v)
```

proved from C2A's `contribution_ring`, carrying the sign, the `2^k` weight and
the matrix order. Concretely `(-1)^(k+1) · G_ij · (v(Bv)^k)_ij / 2^k` on one
side against `-G_ij · (-1/2)^k · (v(Bv)^k)_ij` on the other.

`Tcoeff` is a **computable** coefficient (via C2A's `contributionOf (2^k)`) with
`coeff_T_eq_Tcoeff : coeff k T = Tcoeff G v k` as its named bridge, plus
`Tcoeff_eq_neg_hadamard_Wcoeff`. These two bridges are what let the executable
table below stand for series coefficients.

### 2.5 Degree convention (section 4.3)

`T` and `W` count bubbles: the Fock term is the constant coefficient. A ring of
order `k` has `k + 1` interactions, so `Tcoupling = X * T` and
`Wcoupling = X * W` count interactions. Proved:
`constantCoeff_Tcoupling = 0`, `constantCoeff_Wcoupling = 0`,
`coeff_succ_Tcoupling : coeff (k+1) Tcoupling = contribution (ring k)`,
`coeff_one_Wcoupling : coeff 1 Wcoupling = v`.

`G` is a fixed input throughout. This is **not** the expansion of a
self-consistent `G(z)`, and the Hartree contribution is not derived here.

### 2.6 What is deliberately NOT claimed (section 4.4)

Every equality above is in `PowerSeries R`. Nothing is evaluated at `z = 1`, no
radius or convergence is asserted, and no infinite-dimensional or cutoff-free
statement follows. A formal unit with constant coefficient `I` can specialize to
a singular matrix. The model's full quartic perturbation series and this
selected geometric ring series are different series; the divergence of the
former says nothing here.

## 3. Executable evidence (section 5)

`LLC2BMain.lean` -> `ll_c2b_eval` emits, for three fixtures (two `N=2`, one
`N=3`, one with non-integer rationals, at least one with `v B != B v`), the full
`W_k` and `T_k` matrices at degrees 0..4 as exact rationals.

`ll/screening_reference.py` is independent — it reads no artifact and imports no
expected-answer column — and reaches the coefficients by **four** routes:

1. the closed form `(-1/2)^k v (Bv)^k`;
2. the left recurrence `W_{k+1} = -A_L W_k`;
3. the right recurrence `W_{k+1} = -W_k A_R`;
4. **generic** formal-series inversion (`S_0 = I`, `S_n = -Σ_{m=1..n} P_m S_{n-m}`,
   which does not know `P_L` has only two terms) followed by a Cauchy-product
   convolution with `C(v)`; and the mirrored `W = C(v) S_R`.

`all_routes_agree` raises on any disagreement. `screening_residual` checks
`P_L W - C(v)` and `W P_R - C(v)` coefficientwise; all vanish through degree 4.

> **Correction (C2B review finding 2).** This originally said degree 5 was left
> unasserted because constraining it "would be a convergence claim". That is
> wrong — it is finite algebra. Truncating `W` after `W_4` merely drops the
> coefficient that cancels it, so the degree-5 residual of `P_L W` is exactly
> `A_L W_4`, and exactly `-W_5`. On the `N2-pd` witness that is
> `[[137700, 7208775/32], [7208775/32, 1474175/4]]`, which I reproduced and
> which matches the reviewer's independently computed matrix. The test now
> asserts that equality, plus the cancellation and a nonvacuity check, instead
> of asserting only the matrix's size.

Mutants, all detected against the Lean values at the noncommuting witness:
wrong sign; missing factor `1/2`; `A_R` applied on the left (an ordering error
that commutativity would hide); and the bubble-vs-coupling degree shift. A plain
wrong value is a separate control, as are malformed coverage and inventory.

`tests/test_ll_c2b.py`: 27 tests.

## 4. Commands and outcomes

```
bash scripts/bootstrap.sh                              exit 0
lake build                                             exit 0
lake env lean GW/LL/Screening.lean                     exit 0, no output
./.lake/build/bin/ll_c2b_eval                          exit 0
python3 scripts/make_manifest.py bgw/weighted_audit/PROVENANCE-R6.txt
                                       4 refreshed, 0 missing, 56 scanned
python3 scripts/verify.py --gate all                   exit 0
```

Gate result: **PASS (all)**.

* Scientific gate: **290 tests**, OK (1 skipped, pre-existing).
* Workflow gate: **14 tests**, OK.
* Theorem audits: **191 named** (`GW/Audit.lean`, 24 new C2B entries) /
  **550 exhaustive** (`scripts/CheckAxioms.lean`).
* `AUDIT_MODULE GW.LL.Screening` is present; `verify.py` derives the required
  module set from `GW/**.lean`, so the new module could not have escaped it.
* Axioms across both audits: only `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, custom axiom, `native_decide` or unsafe shortcut in any
  new file. No existing theorem was weakened, restated or deleted.

First gate run failed (exit 1) on one workflow test: `PROVENANCE-R6.txt`
digests for `scripts/verify.py`, `GW.lean`, `GW/Audit.lean` and
`scripts/gates.py` were stale after I edited them. Refreshed with the existing
idempotent tool and reran green. The manifest was **not** extended to cover the
new C2B files: that tool never adds entries by design, and deciding what a
provenance manifest vouches for is a human act.

## 5. Committed versus generated

Committed: `GW/LL/Screening.lean`, `LLC2BMain.lean`, `ll/screening_reference.py`,
`tests/test_ll_c2b.py`, and edits to `GW.lean`, `GW/Audit.lean`, `lakefile.toml`,
`ll/evidence.py`, `scripts/gates.py`, `scripts/verify.py`,
`tests/test_ll_c2a.py`, `bgw/weighted_audit/PROVENANCE-R6.txt`.

**Generated, not committed:** `artifacts/ll-c2b/screening_values.json` and the
gate logs. `artifacts/` is gitignored and the gate regenerates this table before
testing it, exactly as for C2A. I am stating this rather than implying the file
ships — an earlier LL-C1 handoff of mine claimed committed artifacts that
`git add -A` had never staged.

## 6. Failed attempts and obstructions

No mathematical obstruction arose; no obligation required a second approach.
Four mechanical failures, all fixed, none reaching a committed claim:

1. `Wcoeff_succ`: `rw [pow_succ]` left
   `v (Bv)^k B v = v B v (Bv)^k` — the two sides peel the power from opposite
   ends. Replaced by an explicit `pow_succ'` helper rather than tactic-poking.
2. `T_eq_neg_hadamardSeries_W`: `ext k` already descends through `Matrix`, so a
   following `funext i j` failed. Used `ext k i j`.
3. `hadamardSeries_not_multiplicative`: `congrArg (fun U => constantCoeff _ U 0 1)`
   left the coefficient-ring metavariable unsolved. Named the type explicitly
   and added `constantCoeff_hadamardSeries`.
4. The stale-manifest gate failure in section 4.

Also recorded honestly: the *initial* C2B design I sketched in PR #6 — avoid an
inverse operator and state a two-sided series relation — was a workaround for an
obstacle that did not exist. It is not what this checkpoint implements.

## 7. What this teaches about C2B's successors

* The compressed-versus-half-edge and formal-versus-analytic boundaries held up.
  The thing that keeps going wrong is neither: it is **acceptance checkers that
  read their expectations out of the candidate**. That is now three consecutive
  occurrences (C1 report path, C2A test path, and the C2B path pre-empted here).
  The structural fix is the one applied: expectations are parameters supplied by
  the caller, and there is exactly one validator to route them through.
* The next real mathematical step is a choice between generalizing beyond rings
  (skeleton/2PI structure, where the compressed representation is NOT known to
  be faithful — C2A's fidelity is ring-specific and `selfLoopWitness` is the
  standing counterexample) and a narrow electronic bridge. Nothing in C2B makes
  either easier or harder than the roadmap already says.
* Anything that wants `Σ_k` as a number rather than a coefficient needs analysis
  that is not in this repository and is not implied by anything proved here.

## 8. Recommended next decision

**Review this checkpoint, then choose C3 scope.** I recommend the narrow
electronic bridge over general skeleton work: the ring family is now complete
end-to-end (graph data -> arbitrary-order contraction -> symmetry factor ->
half-edge fidelity -> screened resummation), which is a natural place to test
whether any of it transfers to the electronic setting, whereas skeleton theory
would restart the representation question that C2A only settled for rings.

Not authorized and not started: C3, C4, merge, push, visibility or licensing
changes, upstream contact. A human technical owner, not an AI review, remains
required for any eventual community contribution.
