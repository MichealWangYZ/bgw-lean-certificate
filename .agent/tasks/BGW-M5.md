# BGW-M5 — one production GPP self-energy term, connected to the Lean GPP core

Authorized by the owner on 2026-09-22 ("Go ahead and implement", session
`89307ad5`, after the four-agent roadmap audit named "nothing past wtilde2" as
the largest scientific gap). Worker: Claude. Result is ready_for_review, never
self-accepted.

## Goal

Extend the BGW-M4-R1 target (source pair (1,2), consumer (2,1), irq 2, GPP
setup occurrence 1913) through the real-flavor GPP self-energy kernel
`sigma_gpp_cpu` (`Sigma/mtxel_cor.f90:1685-1931`) for ONE (band, frequency):

1. The production pole `wtilde = sqrt(wtilde2)`: bound its distance from the
   exact `sqrt(PStar)` in Lean. The rounded sqrt is checked by exact squaring,
   not assumed from an IEEE model.
2. The per-mode SX and CH values `ssx`, `sch` the kernel forms: bound each
   against exact references built from M4's `OStar`, `IStar`, `PStar` and
   the exact energy difference.
3. Prove the reference combination `-ssx* + sch*/2` equals the specification's
   merged occupied term `GW.GPP.occupiedTerm OStar x* sqrt(PStar)`, using the
   existing pole-cancellation theorem, so the Spec core is instantiated with
   production-certified parameters for the first time.

## Frozen selection rule (fixed before any data is seen)

Within the Sigma call that produced M4's setup occurrence, take the first
occupied band n1 (increasing index), frequency slot `iw = 2`
(evaluation at `E = e_lk`), and require the generic branch
(`wdiffr > gamma^2` and `delwr < 1/(4 TOL_Small)`) and no `sexcut` clamp.
If that record is not generic or is clamped, report BLOCKED; do not pick
another band for convenience.

## Inputs treated as external

Band energies `e_lk`, `e_n1kq`; matrix elements `aqsn`, `aqsm`; `vcoul(igp)`;
`occ`. They enter only the weighting identity, not the certified per-mode values.

## Acceptance

Write-only instrumentation with pristine/instrumented A/B identity; committed
export; generated Lean module with component bounds, the sqrt bound, the
occupiedTerm identity, branch/clamp predicates; discriminating mutations
(sqrt witness, wrong pole branch, energy, local arithmetic); gate passes.

## Out of scope

Sums over modes, bands, q or frequency; quasiparticle energies; other q blocks;
the empty-band CH-only path; complex flavor; physical accuracy.
