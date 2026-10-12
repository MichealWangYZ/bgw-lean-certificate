# Lin–Lindsey / BerkeleyGW: revisable checkpoint roadmap — ARCHIVED (2026-10-01): parked, superseded by docs/ENDPOINT.md; kept, not extended, outside the fast gate. See docs/CODEMAP.md.

Revised 2026-09-16 after BGW-M1-R1 at `353f9803ec4e51c572dcaa4e3fc785e4a21f49fa`.
Technical decision and limits: [M1-R1 acceptance](../.agent/handoffs/BGW-M1-R1-ACCEPTANCE.md).
> **Status 2026-09-22.** The dispatch text below (as of M1-R1) is historical.
> Since then, BGW-M2 (+R1–R3), M3 (+R1), M4-R1 and M5 have reached
> CHECKPOINT_READY on the stacked PRs #17 → #22 → #25. None is merged, and
> only M1 is accepted. The chain runs from one certified 8x8 screening
> inverse, through one GPP pole, to one production self-energy mode tied to
> `GW.GPP.occupiedTerm`. Missing: sums over modes/bands/q, the weights,
> quasiparticle energies, and any Lean link from the LL theory track to the
> BGW certificates. The live ledger is `.agent/STATE.md`.

At M1-R1: **Only [BGW-M2](../.agent/tasks/BGW-M2.md) was then authorized.** It is one
12-active-hour task with internal waypoints and mandatory earlier exits, not an
automatic sequence of future tasks. No process is launched by this document.
This current dispatch supersedes earlier M1-only pointers in historical state.

## Purpose: connect theory, a defined approximation, and a reference calculation

Build a checked chain from explicit many-body models and approximations to small
reference calculations capable of testing corresponding BerkeleyGW computations.
The finite classical Lin–Lindsey model is a theoretical entry point, not a silent
replacement for electronic GW. Neither production agreement nor an exact inverse
certificate proves the accuracy of a physical approximation.

Keep both goals visible: (1) formalize meaningful many-body-theory connections,
and (2) connect a reference calculation to a real production path. Choosing an
engineering interface now does not declare the general theory finished. Earlier
GPP/Fortran source-level diagnostics remain separate assets; a Git dependency is
not itself a proof of the missing physics connection.

## Status by scientific connection

| Stage | What the result establishes | What remains |
|---|---|---|
| C1/C2A | Selected classical ring data, arbitrary-order contractions, non-enumerative symmetry factors and ring-specific half-edge fidelity. | Not a universal diagram representation. |
| C2B | Graph-defined ring coefficients equal a library formal inverse with explicit matrix order and coupling degree. | Fixed G, formal coefficients; no convergence or self-consistency. |
| C3.1 | Conditional pairing-sum first-order Hartree/Fock algebra, a general recursion and the dressed ring-zero connection. | Actual Gaussian/Gibbs interpretation, general pairing correspondence and bare/bold/skeleton theory remain open. |
| C4.1 | Specified finite static electronic response and formal screening, with the sign-only non-transferability claim corrected. | No derivation of electronic chi, full frequency-dependent GW or GPP convolution. |
| BGW-M1 + R1 | Concrete inverse/derived-screening certificate for stored production E and matched production-inverse comparison; repaired run selection and small provenance packet. | E formation is input; pristine/instrumented neutrality is not yet tested independently; reviewer has not repeated the Lean/Fortran builds. |
| **BGW-M2** | **Authorized next:** independently exported chi,V -> exact E_star; explicit stored E_hat discrepancy; certified reference/propagation and comparison to actual production output; same-input pristine A/B. | Stop after this result or a precise terminal blocker. It still does not prove the origin of chi or the entire program. |

M1 is accepted for internal progression within its specified narrower boundary.
The original broad C3 and C4 roadmap rows are not complete. Do not rename local
conditional results to make those larger objectives appear finished.

## Why M2, and why a longer allowance

A real production boundary is now in hand. Extend it, rather than repeat the same
inverse on more q points or create another isolated formula. The useful new object
is the difference between E_star=I-V_hat*chi_hat in exact arithmetic and the stored
E_hat. Export chi independently; never recover it from E_hat for this verification.

A longer task permits acquisition, a pristine/instrumented comparison, concrete
proof work, numerical error accounting and integration in one run. Internal
waypoints are progress checks, not mandatory returns to the owner. They cannot be
used to weaken the final success criterion or hide a blocked connection.

M2 retains the same small complete real-flavor basis. It does not seek a new material,
a larger cutoff, a frequency convolution, all of Wick's theorem or a general
floating-point library. External solvers may generate certificates; Lean must
check the actual represented instance, not just a generic conditional statement.

The exact identity R_hat-R_star=-R_hat*(E_hat-E_star)*R_star connects formation
error to inversion. A declared finite error budget and an actual-output certificate
make that bridge useful without claiming universal compiler/Fortran correctness.
The derived W=R*V must remain distinguished from a separately exported production W.

## Review after M2, not automatic M3

Choose one substantive next direction based on the result:
- extend the electronic physical connection (formation of chi, or the frequency/
  GPP self-energy link); or
- close a theory connection (finite Gaussian moments/normalized expansion or a
  carefully bounded general pairing/skeleton result).

These are alternatives for a later decision, not two pre-authorized projects.
If M2 exposes a bad convention, inaccessible input or infeasible certificate,
review that evidence before commissioning more modules. Avoid endless parser/
prose-polish cycles when a scientific interface is already settled.

## Fixed boundaries

Arbitrary finite N is not an infinite-dimensional limit. Formal coefficients are
not automatically summable at unit coupling. Exact rational decoding of doubles
is not an unrounded physical system. The stored E_hat need not equal exact E_star;
certifying one inverse does not certify the other without a connection.

A pristine/instrumented A/B comparison supports neutrality on that selected input
and observed output, not all executions. Validate the complete selected matrix,
not only its printed diagonal. Do not discard complex parts or invert an arbitrary
sub-block instead of the complete retained system.

The current 34-test M1 suite and additional reviewer checks passed on the committed
data. Full Lean/Fortran reproduction remains worker-reported; next-task baseline
and comparison runs must be actually executed and recorded, not inherited as claims.

## Resources, stops and authorization

M2 has 12 cumulative active hours; access preflight 60 minutes, actual-data/A-B
waypoint by hour 3, one new actual-input Lean certificate by hour 6. At any time,
90 minutes without new evidence on one central obstruction or two materially
different unproductive approaches triggers a stop. See the task for exact rules.

Every run returns one of CHECKPOINT_READY, ROUTE_REFUTED, BLOCKED, BUDGET_STOP.
Success is all of the stated connected result, not just one waypoint. An exact
counterexample is not the same as an environment/tactic failure. Preserve partial
work on failure, report the precise missing decision, and do not reset the budget
across sessions. Finish earlier if done; never pad work to consume the allowance.

Private commits, pushes and result PRs are authorized under the owner's standing
grant. Merge/main cleanup, new paid resources, global toolchain changes, licensing/
visibility changes, upstream contact and automatic next tasks are not authorized.

## Sources and community alignment

Theoretical starting point: Lin–Lindsey Part I, arXiv:1809.02900v1: finite Gibbs
model/interaction in section 2.1, diagram structure and later skeleton/ring results.
The Gaussian-moment interpretation and general skeleton theorem remain open here.

Production source and docs must be read, not used as interchangeable authorities:
https://manual.berkeleygw.org/4.0/epsilon-overview/
https://manual.berkeleygw.org/4.0/epsilon-keywords/
https://berkeleygw.org/documentation/tutorial/tutorial-epsilon/

Reuse pinned mathlib's matrix, inverse, finite-sum and norm infrastructure. A missed
API is not a missing foundation. Model-specific downstream code is legitimate;
an unsolicited competing general library is not the default solution.

Stay downstream. No agent-generated upstream issues, bulk PRs or maintainer replies.
Any future upstream contribution requires human technical ownership, personal source
verification and compliance with the destination's current contribution policies.
Do not use theorem counts, proof length or quick worker completion as percentages
of completion of the scientific program.
