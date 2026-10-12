# First Demo: What We Can Show — ARCHIVED (2026-10-01): Specification.md v0.1 demo lineage, superseded by GW.Endpoint.Kernel.SigmaSpec and GW.Bridge; kept, not extended, outside the fast gate. See docs/CODEMAP.md.

The project now has a compiled Lean proof of a scalar occupied-state GPP pole
cancellation, its punctured limit, and an exact finite self-energy evaluator
whose successful outputs agree with a real-valued mathematical model.

```text
Split:   -A/(x^2-w^2) + A/(2*w*(x-w))
Merged:   A/(2*w*(x+w))
Limit at x=w: A/(4*w^2)
```

The equality requires `w != 0` and `x != +/-w`. The limit statement is separate:
it does not evaluate the split formula at a zero denominator. The executable
uses the occupied continuous extension and rejects remaining singular inputs.

## Evidence

- 60 named theorems; 126 declarations audited including generated/private ones.
- No proof dependency beyond Lean's stated foundational allowlist.
- 17 independent Lean runtime cases and 25 Python tests.
- Synthetic terms `2/3, -1, -1`, plus static `-1/2`, give `-11/6 eV` in both
  the Lean executable and an independently written exact-rational oracle.
- Deliberate branch, coefficient, sign, and omitted-term changes are detected.

## Why the Rewrite Matters Numerically

For `A=4 eV^3`, `w=1 eV`, and representable binary64 `x` near `1+1e-8 eV`,
the split evaluation returns zero while the exact value is close to one. The
merged expression has about `2.5e-17 eV` absolute error in this example.
The exact oracle receives the same binary64 input, so this measures evaluation
error rather than mixing it with decimal-input rounding.

See `artifacts/pole-cancellation.png`, `artifacts/numerical-demo.json`, and
`artifacts/numerical-demo.log`. This experiment is not a formal float bound.
It concerns the unprotected split, not a demonstrated defect in BerkeleyGW,
whose inspected path includes a near-pole branch and additional cutoffs.

## Source-Linked Demo

T-002 maps a checksummed BerkeleyGW 4.0 CPU kernel to the exact-real formulas.
The saved Si-EPM run has 48 nonzero mode comparisons (including 32 near-pole
records) and 48 zero placeholders checked separately. Max measured S1 residuals
are `6.25e-16` for the general sample and `2.51e-19` for the near-pole sample,
in normalized dimensionless local contributions, not a total energy error.

Fresh pristine/instrumented runs each satisfy 24 upstream assertions and match
all four saved text outputs on this host. Reproduction depends on upstream
BLAS threading; no portable bitwise guarantee or physical gauge equivalence
is claimed. See `artifacts/t002-codex-reproduction/report.json`.

## What the Agent Workflow Demonstrated

Codex created the contract and a bounded task. Claude implemented the Lean files
and returned a detailed handoff. Codex checked the code, corrected stale handoff
claims, improved serialization, and independently accepted the result.
All restart context lives in project files. A fresh session can pick it up.

Shared wakeup instructions are prepared, but no timer is active. The proposal is
one Codex supervisor schedule, with Claude dispatched only for bounded jobs.

## Scope of the Claim

This is a proof about an explicit scalar mathematical model inspired by the
BerkeleyGW GPP formulas. The methods-paper correspondence is documented in
`SOURCE_MAP.md`, with a restricted BerkeleyGW 4.0 source/run comparison now
documented. Physical approximation error, upstream coefficient correctness,
full unitful material sums, floating-point bounds, fractional occupation, and
quasiparticle roots remain separate work.

Run the complete gate with `bash scripts/verify.sh`. The detailed acceptance
records are `.agent/handoffs/CODEX-ACCEPTANCE.md` (T-001) and
`.agent/handoffs/CODEX-T-002-ACCEPTANCE.md` (T-002).
