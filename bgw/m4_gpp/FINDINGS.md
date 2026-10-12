# BGW-M4 feasibility findings — reported run, unresolved screening bridge

> **BGW-M4-R1 outcome (2026-09-22), superseding the interpretation below.**
> The input bridge is now established for all 8448 surviving GPP records
> that read the M2 block. Each consumed operand equals M2's `Xhat` bits under
> the traced map: symmetry, umklapp, ±1 phase, and `fixwings`'s wing
> normalization. The "2/64 matches with sign flips" below came from an
> identity-label comparison. Sigma reaches M2's block even at rq = (0,0,½)
> through symmetry 38 with umklapp (0,0,1), and rescales the G = 0 wings.
> The runner's reading "fails structurally" was wrong. Codex's hedged reading
> of it was right: the mismatch showed only that the identification was
> unjustified. The raw feasibility artifacts lived in `/tmp` and are gone, so
> their counts cannot be replayed. See `PROVENANCE.md` and
> `.agent/handoffs/BGW-M4-R1.md`. The text below is retained unedited.

**Status: input continuity is unresolved; M4 is not accepted.**
The existing feasibility run is reported below. This documentation revision
performs no new run, changes no instrumentation, and starts no Lean or
certificate implementation. It does not retroactively authorize the run or
provide permission for further execution.

The proposed bounded endpoint and acceptance contract are in
[BGW-M4-PREFLIGHT.md](../../.agent/handoffs/BGW-M4-PREFLIGHT.md). This file
preserves the reported observations and distinguishes them from an established
M2-to-Sigma correspondence.

## What the feasibility runner reported

The runner built `sigma.real.x` from the pinned tree and used the M2/M3
screening file (`epsmat` SHA-256 prefix `4512f63a4a9c28e8...`, 61181 bytes,
`nmtx = 8`, `epsilon_cutoff 1.5`) with `WFN_inner`, `RHO`, `VXC`, and
`sigma.inp` from the T-002 artifacts. This identifies the file, not a proof
that every array Sigma consumed is covered by M2's certificate.

```text
sigma.real.x     exit 0, "Job Done"
```

The existing patch `bgw/m4_gpp/mtxel_cor_m4_dump.patch` instruments
`Sigma/mtxel_cor.f90` at the GPP parameter formation point, exporting per
`(ig, igp)` the `epstemp`, phases, `epsggp`, `I_epsggp`, `Omega2`, `wtilde2`,
G vectors, and q vector.

The runner reported pristine/instrumented A/B outputs `eqp0.dat`, `eqp1.dat`,
`sigma_hp.log`, and `ch_converge.dat` as byte-identical. These statements
record the existing feasibility report; this documentation review did not
independently replay Sigma or validate its raw runtime evidence.

## Reported arithmetic observations

The report counts 15147 exported records and 459 unique `(q, ig, igp)` keys.
For the relation checks it reports:

| Relation | Reported result |
| --- | --- |
| `wtilde2 == fl(Omega2 / I_epsggp)` | 187/187 exact |
| `I_epsggp == delta - fl(ph_g * ph_gp * epstemp)` | 187/187 exact |
| observed phases | all `(1.0, 1.0)` |

These support the tractability of the checked local arithmetic, conditional
on its actual operands. They are not a certificate for every exported record,
a general IEEE-754 theorem, or evidence that those operands are covered by M2.
The numerator's primitive-operand reconstruction is also not established by
exporting `Omega2 = wpmtx` alone.

The patch exports after the quotient and before a subsequent
`if (abs(wtilde2) .lt. TOL_Small) cycle`. Therefore an exported parameter is not
by itself evidence of a surviving, usable real GPP mode. A future target must
have explicit branch-survival evidence. All-one observed phases also cannot
demonstrate sensitivity to every nontrivial phase-handling error.

## Reported mismatch in the attempted direct identification

The feasibility comparison used Sigma's q = `(0, 0, 0.5)` and M2's certified
`Xhat`, under the attempted identity G labelling. It reported:

```text
exact matches            2 / 64
max absolute difference  1.343e-01
```

Some entries reportedly differ in sign. The report's scan found the closest
comparison at Sigma's q = `(0.5, 0, 0)`: 16 entries with overlapping G labels
agreed to `2.22e-16`. That consumer block's reported G set is not M2's; it
contains `(-1, 0, 0)`, absent from the pinned M2 basis:

```text
{(0,0,-1), (0,0,0), (-1,-1,-1), (-1,0,-1),
 (0,-1,-1), (0,1,0), (1,0,0), (1,1,0)}
```

The runner attributed the mismatch to Sigma mapping required `q = k - k'`
values to available screening q points, rotating/relabeling G vectors and
applying `gmap` phases. That is the mechanism to trace, not a completed
source-to-consumer certificate.

**Correction to the earlier interpretation:** the failed direct comparison
establishes that the attempted array identification has not been justified.
Partial numerical agreement does not prove that the consumer is an image of
the exact M2-certified block. Nor does the mismatch establish that BerkeleyGW
is wrong, that the problem cannot be an indexing/provenance mistake, or that
a general symmetry formalization is required. The precise finite mapping,
including any conjugation, transpose, shift, or normalization, remains open.

## Next work order, after separate execution authorization

First establish one finite M2-to-Sigma input connection. Then, for that one
usable nonzero off-diagonal target, independently reconstruct `Omega2` and
`wtilde2` and bound the production values against the mapped M2 exact screening
reference, including M2's inherited error. The full scope, deterministic
target-selection rule, numerical acceptance conditions, and mutation
requirements are defined in the linked preflight.

The required input condition remains:

> Establish that the actual consumed q block, basis ordering, transformations,
> and decoded values are covered by the existing M2 certificate. Matching the
> input file, cutoff, or matrix dimensions alone is insufficient.

If that connection cannot be established within the single finite target,
**STOP as `BLOCKED`**, name the missing obligation, and retain the evidence.
Do not proceed by accepting arbitrary `epstemp` as a new input boundary.

The earlier alternatives of removing transformations by re-running and
re-certifying a full q set, dropping the M2 connection, or building general
symmetry machinery are not fallbacks in this milestone. Do not alter the
screening matrix or Sigma arithmetic to make a comparison pass.

## Evidence still needed; no execution authorized here

The current report does not supply a checked target identity/mapping,
primitive-to-`Omega2` reference, branch-survival witness, fixed numerical
budgets, or concrete Lean endpoints. The proposed milestone is therefore not
implementation-ready or accepted. These gaps are not additional M3 acceptance
requirements.

No claim is made about the GPP approximation's accuracy, the frequency
integral, `Sigma = iGW`, self-consistency, quasiparticle energies, ground-state
input generation, or the square-root-dependent Coulomb-hole/`Term` mapping.
Screened exchange may admit a rational expression, but remains out of scope.

**Current patch: documentation only. Preserve M1–M3 and their repairs; no new
runs, instrumentation, implementation, or merges are authorized.**
