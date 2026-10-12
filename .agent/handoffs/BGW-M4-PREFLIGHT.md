# BGW-M4 proposed scope — one certified screening-to-GPP connection

**Status: DOCUMENTATION ONLY. Proposed endpoint; input bridge unresolved.**
**This patch does not authorize new runs, instrumentation, Lean implementation,
or an M4 acceptance claim.**

Reviewed snapshot: PR #25 head `523809d1e948aaccec80058f1a1cf5992f22ffea`.
The PR targets `bgw-m3/chi-transition-sum`, whose reviewed head is
`6bcdeeeced9e3f581ea78cdc2aeb9dff7f7f7fc8`, not `main`. Preserve the existing
M1–M3 stack and PR #23/#24 repairs. Consolidation/review comes before further
execution; this document neither performs nor authorizes a merge.

## In ordinary language: what Claude should work on next

We checked screening matrix A, but Sigma reads array B. The feasibility report
attributes the difference to rotations, relabelling, and phases. We have not
established the exact connection. This is a verification gap, not evidence
that BerkeleyGW's physics or numerical calculation is wrong.

After separate execution authorization, the bounded work order would be:

1. **Trace one usable example from A to B.** Identify one nonzero off-diagonal
   parameter on the ordinary real-flavor path that survives the relevant
   branch checks. Establish the source q block, G indices, and every actual
   index/phase/conjugation/normalization operation connecting it to M2. Do not
   change Sigma or the screening input to force a match. If the connection
   cannot be established within this finite instance, stop as `BLOCKED`.
2. **Independently reconstruct its two parameters.** Reconstruct `Omega2` from
   the primitive density/Coulomb/geometric operands and `wtilde2` from that
   numerator and the traced screening denominator. Exported production values
   are comparison targets, not their own reference answers.
3. **Include the earlier uncertainty.** Carry M2's screening-error bound
   through the selected mapping and the new arithmetic, then check the final
   bound in Lean. A deliberately wrong mapping must be rejected even when its
   downstream division is internally consistent.

**Finish line:** one production squared GPP pole is connected to the already
certified finite screening calculation, with a checked numerical error bound.
Stop there, before a pole square root or any self-energy evaluation.

## What changed since the original preflight

The original preflight at `60fd851605f291e6fb6f5debc8f63a80b78809ba` asserted
that the two parameters were literally the fields of `FiniteSelfEnergy.Term`
and that the existing method transferred unchanged to that endpoint. Those
claims are retracted. The units/square-root correction at `bcffe56`, the later
branch-dependent refinement, and the feasibility report supersede them.

`Term` contracts a pole energy `omega` in eV and a coefficient in eV^3.
Its denominator is `2*omega*(x +/- omega)`. The squared GPP parameters cannot
simply be assigned to those fields. Units and all conversion/weighting factors
must be traced rather than inferred from variable names.

The real path takes `sqrt(wtilde2)`, and the resulting pole survives linearly
in the Coulomb-hole/merged `Term` expression. A rounded floating-point square
root can be decoded as a rational, but treating that value as a fresh input
does not certify its relation to the intended pole. The existing rational
reference construction does not close that missing error treatment.

The displayed screened-exchange expression is rational in `Omega2` and
`wtilde2`; therefore stopping at the parameters is a deliberate scope choice,
not a theorem that exact-rational methods cannot go further. Screened exchange
is not a stretch goal of this milestone.

The later `bgw/m4_gpp/FINDINGS.md` reports a completed Sigma feasibility run
and a mismatch in the attempted direct screening-array identification. PR #25
also contains `bgw/m4_gpp/mtxel_cor_m4_dump.patch`. It is no longer accurate to
call the entire PR a one-document addition or to say Sigma has never been run.
Those runtime results are runner-reported, not independently replayed by this
documentation review; their existence does not grant permission for more runs.

## Frozen input boundary and target

Use only the existing M2/M3 `epsmat`: SHA-256 prefix `4512f63a4a9c28e8`,
61181 bytes, with the complete digest taken from existing provenance. Preserve
the certified q index 2 block at `(0, 0, 1/2)`, its retained `nmtx = 8` basis,
and a compatible Sigma cutoff. The T-002 `epsmat` (`8bb0bafa...`, 175533 bytes)
is not a fallback.

File identity, a matching cutoff, an 8x8 shape, or approximate agreement does
not establish operand identity. Check the actual source-to-consumer map for
one target, including any rotation, reciprocal-lattice shift, G ordering,
phase, conjugation, transpose, or normalization actually used. Do not introduce
a general crystal-symmetry framework or certify other q blocks.

Freeze one nonzero off-diagonal target using a deterministic rule independent
of certificate residuals: the lexicographically first eligible source pair
in the pinned basis, then its runtime occurrence identifier. Record the rule,
selected identity, and eligibility evidence before assessing the error bounds.
Require nonzero numerator/denominators, a positive squared-pole reference,
and survival of the selected ordinary-real branch. An export before a later
`cycle` is not evidence of survival. If no eligible mapped target exists,
report `BLOCKED`; do not move to a target chosen for an easier residual.

Primitive density, Coulomb, and geometric numerical operands are explicit
external inputs. Their ground-state, wavefunction, FFT, or convergence
provenance is not part of M4. The finite expression forming this `Omega2`,
including units and constants, is part of M4: copying exported `wpmtx` into
`Omega2` is not independent reconstruction. If its reconstruction requires a
new technique outside this scope, record the obstruction rather than silently
promoting the final numerator to a trusted input.

## Precise scientific endpoint

Keep the decoded production inverse `Xhat` distinct from M2's exact screening
reference `Rstar`. Let `T` be the frozen finite source-to-consumer map, and let
`a,b` identify the selected consumer entry. Define, from independent inputs:

```text
sStar = T(Rstar)[a,b]
IStar = delta(a,b) - sStar
OStar = F_Omega(primitive operands)
PStar = OStar / IStar
```

Here `OStar` and `PStar` are the exact-rational `Omega2` and `wtilde2`
references. The measured production values are `Ohat`, `Ihat`, and `Phat`.
Provenance must bind the consumed screening operand to the corresponding
transformation of M2's production data; the error bound then connects it to
`T(Rstar)`. Do not restart from arbitrary `epstemp` as a new screening input.

The concrete Lean endpoints must establish:

```text
abs(Ohat - OStar) <= B_Omega
abs(Ihat - IStar) <= B_I
abs(Phat - Ohat/Ihat) <= B_div
abs(Phat - PStar) <= B_P
```

For a fixed acceptance rule, require `B_I <= abs(IStar)/2`, with
`d = abs(IStar) - B_I > 0`, and compose:

```text
B_I = B_map + B_formation + L_T * B_M2
B_P = B_div + B_Omega/d + abs(OStar)*B_I/(abs(IStar)*d)
```

Justify the transfer factor `L_T` for the actual finite map; do not assume a
unit factor without checking it. Check each component bound separately, so a
large inherited budget cannot conceal a failed local arithmetic obligation.
The positive-domain and nonzero-denominator results must also be checked.

Budgets must come from the frozen operands and operation trace, with any
engineering factors fixed before inspecting the certificate discrepancies.
Do not set a budget to the measured error plus a margin. The target, complete
numerator expression, map, and explicit rational budget values remain open;
no numerical tolerance is invented here. Their absence means this proposed
scope is not an implementation-ready certificate brief.

## Acceptance and stop condition

Acceptance requires all of the following for this one instance:

- A checked finite input bridge to the existing M2 block, not just a matching
  filename or quotient. Source/data-flow evidence remains separate from the
  mathematical statements that Lean checks.
- An independent primitive-to-`Omega2` reference and concrete Lean bounds
  composed against the mapped M2 exact screening reference. Endpoint theorems
  must not assume the missing mapping, correspondence, or transfer inequality.
- Focused discriminating mutations: a wrong mapping with self-consistent
  downstream arithmetic, a primitive/witness mismatch, and a local arithmetic
  violation. Each must fail the intended obligation; checksum rejection alone
  is insufficient. Valid controls must pass. All-one observed phases do not
  demonstrate rejection of general nontrivial phase errors.
- Committed finite evidence that regenerates the same certificate, integration
  with the existing verification gate, and preservation of earlier checks.
  Audit the concrete endpoints; no `sorry`, `admit`, new unsupported axioms,
  or `native_decide`. Runtime A/B reports are not Lean/compiler proofs.

Once these pass, **STOP**. This certifies one finite numerical instance, not
all screening entries or all microscopic provenance. In particular, do not
extend M3's `(1,1)` and `(1,2)` operand-level claims to every matrix entry.

If the map, primitive reconstruction, domain conditions, or bounds cannot be
closed within this scope, **STOP as `BLOCKED`**, identifying the failed
obligation and retaining the evidence. Do not substitute a matrix, re-run or
re-certify more q points, drop the M2 connection, or loosen the endpoint.

Out of scope: `sqrt(wtilde2)`, algebraic-number/interval infrastructure,
`FiniteSelfEnergy.Term`, screened exchange, Coulomb hole, finite self-energy
sums, quasiparticle energies, new materials/cutoffs/q grids, general symmetry
machinery, complex flavor, static/full-frequency alternatives, physical
accuracy/convergence, and compiler/BLAS/whole-program correctness.

**Current action remains documentation only. No new scientific execution,
implementation, merge, or milestone acceptance follows from this patch.**
