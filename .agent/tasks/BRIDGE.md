# BRIDGE — BerkeleyGW's GPP self-energy derived from many-body theory, then STOP

Base: `main` at `709220e` (PR #27 merged). Branch `bridge/theory-to-bgw`,
worktree `.claude/worktrees/bridge`.
Read `AGENTS.md`, `Specification.md`, `.agent/STATE.md`, `.agent/WAKEUP.md`,
`docs/ENDPOINT.md` first.

## 0. Provenance

Written by the supervising session (not the implementer) on the owner's request
"bridge them": derive the specification of BerkeleyGW's GPP Sigma independently
from theory, and prove the code-transcribed specification equals it up to named
approximations. The targets in section 2 may not be weakened during execution.
If a target is unreachable the exit is `BLOCKED` with the exact obstruction, not
a smaller target. Never mark the work accepted.

## 1. The scientific question

`GW/Endpoint/Kernel/SigmaSpec.lean` (and `EpsSpec.lean`) were transcribed FROM
BerkeleyGW's Fortran. A spec transcribed from the code certifies the code's
bugs. Is every formula in SigmaSpec what G0W0 theory with the Hybertsen–Louie
GPP says, and where it is not, what exactly is the departure?

The theory end already exists and must be reused, not redone:

* `GW/Endpoint/ManyBody/` — general finite fermion system, exact Sigma,
  `GWSecond.lean` (G0, chi0, W to second order in the time domain, `ftDamped`
  transform, `eta -> 0+` limit), `GWError.lean`.
* `GW/LL/Electronic.lean` — finite static RPA `W = (1 - v chi0)^{-1} v` (formal).
* `GW/GPP/PoleCancellation.lean`, `BerkeleyGWMap.lean`, `PoleDomain.lean` —
  scalar SX/CH identities for one pole and the transcription of one code path.
* `GW/Endpoint/HubbardDimerSigma.lean` — `ftDamped` and limits.

## 2. Targets (in order; each is a stage with its own handoff section)

**B1. GPP frequency integral (the core).** In a finite basis, define the G0W0
correlation self-energy with a screened interaction whose correlation part is a
finite sum of single poles, `W_c(omega) = sum_k B_k * 2 w_k / (omega^2 - w_k^2)`
(the GPP form, `w_k > 0`), via the time-domain product `i G0(tau) W_c(tau)` and the
existing damped Fourier transform / `eta -> 0+` limit (as in `GWSecond.lean`).
Prove the limit equals the closed form

  Sigma_c(E) = sum over occupied n, poles k of  B_k / (E - e_n + w_k)
             + sum over empty  n, poles k of  B_k / (E - e_n - w_k)

(with the correct signs/factors — derive them, do not assume these) and then
the Hybertsen–Louie SX/CH rewriting that BerkeleyGW uses (screened exchange on
occupied states + Coulomb hole over all states). Connect to the existing scalar
identities in `GW/GPP/PoleCancellation.lean`.

**B2. The GPP model itself.** Define the HL GPP `eps^{-1}_{GG'}(omega)` from the
static `eps^{-1}(0)` and the f-sum rule parameter `Omega^2_{GG'}`. Prove: static
match at `omega = 0`; the first-moment (f-sum) identity by construction; the
precise condition under which a mode is invalid (`wtilde^2 < 0`, and `I = 0`
cases), i.e. when no single positive pole matches both constraints. State, do
not hide, what BerkeleyGW does for invalid modes (`wtilde = 1/TOL_Zero`) as a
named departure.

**B3. Bloch / plane-wave specialisation.** Orbitals `(n, k)`, finite G sphere,
pair densities `M_nm(k, q, G)`, bare Coulomb `v(q+G) = 8 pi / (Omega |q+G|^2)`
(Ry units). Show the B1 formula with W built from `eps^{-1}` and `v` in this
basis is the sum over `q, n, G, G'` that BerkeleyGW writes.

**B4. The comparison theorem.** Prove that the per-state Sigma of
`Kernel/SigmaSpec.lean` (exchange, SX, CH, static remainder, per-mode kernel
`schS`/`ssxS`) equals the B3 theory formula, with EVERY departure appearing as
an explicit named hypothesis or explicit correction term. Expected departures
(verify each; add any others you find; each is either proved harmless or
listed): Coulomb mini-BZ averages `vb`/`oq` replacing `v`; the q -> 0 wing rule;
the invalid-mode rule; the near-pole branch and `sexcut` clamp; `TOL_Zero`
replacement of `wx`; drop thresholds; the static-remainder (exact static CH)
correction; finite band sum; the linearisation in Eqp1 (not part of Sigma).
Deliver `docs/BRIDGE.md` with the departure table: formula, theory, SigmaSpec,
status (proved equal / named approximation / DISCREPANCY).

A genuine discrepancy (SigmaSpec differs from theory in a way that is not a
documented BerkeleyGW approximation) is a result, not a failure: record it with a
minimal Lean witness and stop to report it.

## 3. Rules

* No `sorry`, `admit`, new axioms, `native_decide`, `ofReduceBool`,
  `implemented_by`. Axioms of every new theorem must be within
  `[propext, Classical.choice, Quot.sound]`; add the new modules to the axiom
  audit (`scripts/CheckAxioms.lean`) and to `GW.lean`/`GW/Audit.lean` as the
  existing pattern does, and re-sign `bgw/weighted_audit/PROVENANCE-R6.txt` if
  its digests change.
* Every numerical sanity claim gets an independent Python oracle (e.g. numeric
  contour/residue integration on random small instances) that never reads Lean
  output.
* Do NOT build the `GWKernelData` library (5 h, 10 GB). Import only the spec
  modules (`Kernel/SigmaSpec`, `EpsSpec`) and the default library.
* Write scope: new files under `GW/Bridge/`, `docs/BRIDGE.md`, `tests/` for the
  oracle, the audit/registration files above, `.agent/handoffs/BRIDGE.md`.
  Do not edit existing theorem statements.
* Commit per stage; push to `origin bridge/theory-to-bgw` is authorized. Do not
  open-merge to main. Never use bare `git stash`.
* Commit trailer: `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.

## 4. Exit

`CHECKPOINT_READY` (all of B1–B4), `PARTIAL` (list which stages), or `BLOCKED`
(exact obstruction). Handoff `.agent/handoffs/BRIDGE.md`: commands, results,
failed attempts, the departure table, next action.
