# LL-C4 — finite electronic RPA screening, then STOP

Base: C3 result `2abd10d` on `ll-c3/wick-hartree-fock` (PR #10).
Read `AGENTS.md`, `docs/LIN_LINDSEY_ROADMAP.md`, `docs/LL-C2B-REVIEW.md`,
`.agent/handoffs/LL-C3.md` first.

## 0. Provenance and the review gap — read first

**Written by the implementer, like LL-C3, and shipped without an intervening
review.** The owner authorized C4 directly and chose to skip the review round.
This is now the **second consecutive unreviewed checkpoint**. This project's own
history records that consecutive unreviewed passes are where errors enter. Two
compensations are therefore mandatory, not optional:

1. every numerical claim must be checked against an independently written
   oracle that never reads Lean output; and
2. every non-claim must be written down as an explicit theorem or an explicit
   sentence, not left to the reader's charity.

Targets below come from the roadmap's C4 row ("Explicit fermionic/sign/frequency
conventions; finite GW/GPP specification; reference calculation; matched-input
comparison") and from `docs/LL-C2B-REVIEW.md` section 6 ("choose an explicitly
specified finite electronic response/GW bridge"). They may not be weakened
during execution; an unreachable target means `BLOCKED`.

## 1. One scientific question

Does any of the C1–C3 machinery transfer to the **electronic** setting, and if
so exactly which part?

The suspicion to be settled precisely: the ring/screening algebra looks the same
in both settings, but the classical Gibbs model's objects are not the electronic
ones. A useful answer separates the two and proves both halves.

## 2. Declared conventions — stated before any result

The electronic quantities are **specified**, not derived from a many-body
Hamiltonian. This task fixes a finite static RPA model:

* a finite set of transitions, each with an occupied energy, an empty energy, a
  spectral weight, and a real matrix element vector;
* static (zero-frequency) polarizability
  `chi0 i j = sum_t weight_t * m_t i * m_t j / (occ_t - emp_t)`;
* dielectric `eps = 1 - v * chi0`, screened interaction `W = eps⁻¹ v`.

The spin/degeneracy factor lives in `weight_t` and is an input. **No claim is
made that this is BerkeleyGW's convention, nor that it is the only correct one.**
The repository contains no dielectric or screened-interaction fixture from a
BerkeleyGW run (`fixtures/` holds only synthetic GPP self-energy data), so a
matched-input comparison against a production path is **out of reach here** and
must not be claimed. That part of the C4 row remains open.

## 3. Fixed targets

### 3.1 The algebra transfers — proved by reuse, not by resemblance

Factor the geometric-inverse algebra used by C2B into a general form over an
arbitrary matrix `A`, using the pinned `PowerSeries.invOfUnit` interface:
`geoP A = 1 + X * C A`, `geoS`, `geoW A u`. Prove the two-sided inverse
identities and the coefficient formula `coeff k (geoW A u) = (-1)^k • (A^k * u)`.

Then prove **both** are instances:

* C2B's classical `GW.LL.W G v` is `geoW (AL G v) v`;
* the electronic `W` is `geoW (-(v * chi0)) v`, giving the Neumann series
  `coeff k = (v * chi0)^k * v`.

Do not restate C2B's theorems; connect to the existing ones.

### 3.2 The content does not transfer — proved, not asserted

Prove a structural obstruction, not a vague warning. The classical bubble
`bubble G = G ⊙ G` has nonnegative diagonal; a physical `chi0` built from
occupied-to-empty transitions with nonnegative weights has nonpositive diagonal.
State both, and exhibit a witness where both diagonals are nonzero, so the two
objects genuinely differ and C2B cannot be read as an electronic result.

### 3.3 Physical sanity of the specified `chi0`

Prove `chi0` is symmetric, and that it is negative semidefinite when every
transition has `occ < emp` and nonnegative weight. This is the check that the
sign conventions in section 2 are internally coherent.

### 3.4 The GPP bridge, at the dielectric level only

The repository already analyses a plasmon-pole self-energy kernel (`GW.GPP`).
Define the single-pole model for the inverse dielectric and prove the standard
parameter identification reproduces the static value at zero frequency, under
the domain condition that the pole frequency is nonzero.

State explicitly that connecting this to `GW.GPP.Data.sigmaChecked` requires the
frequency integral `Sigma = i G W`, which is **not** performed here.

## 4. Executable evidence

Exact rationals. An independently written Python oracle that builds `chi0`,
`eps` and `W` from the transition data and solves `eps W = v` by exact Gaussian
elimination — a genuinely different route from the Neumann series. Mutants that
must be detected: wrong transition sign (`emp - occ`), missing spectral weight,
`eps = 1 + v chi0`, Neumann series truncated one order early, and an ordinary
wrong value. Route the table through `ll/evidence.py` with specification-owned
fixtures, orders and series names; do not write a new reader.

## 5. Out of scope — stop rather than do these

Frequency dependence beyond the stated static model, the `Sigma = i G W`
integral, self-consistency, vertex corrections, real BerkeleyGW comparison,
convergence or thermodynamic limits, new general frameworks, dependency or
toolchain changes, licence/visibility changes, upstream contact, `main` merge.

## 6. Verification

Pinned Lean 4.19.0 / mathlib. No `sorry`, `admit`, custom axiom, `native_decide`
or unsafe shortcut. New modules in the exhaustive audit. Full existing gate
before `CHECKPOINT_READY`. All C1/C2A/C2B/C3 targets and fixtures unchanged.

## 7. Budget and stop contract

Allowance **6 cumulative active hours**; preflight cap 30 min. Earliest
applicable status wins: `CHECKPOINT_READY`, `ROUTE_REFUTED`, `BLOCKED` (incl. 90
active minutes with no new evidence, or two materially different failed
approaches to one obligation), `BUDGET_STOP`.

Write `.agent/handoffs/LL-C4.md` and STOP. Do not self-accept or continue to
another stage.
