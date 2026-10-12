# GPP Pole-Cancellation Demo: Specification v0.1

Status: provisional mathematical contract chosen for this demo. Physical source
mapping and conventions have not been signed off by the user. No BerkeleyGW
source checkout or exported material data was supplied.

## Claim and Scope

Prove one scalar algebraic rewrite and its removable-singularity limit, then
connect an exact rational finite evaluator to a real-valued mathematical model.
Use synthetic inputs, real coefficients, strictly positive pole energies,
binary occupancy, and a finite list with multiplicity. This models a restricted
local dynamic contribution with fixed input coefficients.

It does not verify BerkeleyGW, derive GW from diagrams, bound floating-point
roundoff, certify a material, or prove the accuracy of the GW approximation.
No complex poles, broadening, fractional occupations, long-wave limit, dielectric
matrix construction, root certification, or production-code export is included.

## S1: Single Occupied Contribution

Let `A, x, w` be real. Define

```text
raw(A,x,w) = -A / (x^2 - w^2) + A / (2*w*(x-w))
occupied(A,x,w) = A / (2*w*(x+w))
empty(A,x,w) = A / (2*w*(x-w))
```

For `w != 0`, `x != w`, and `x != -w`, prove `raw = occupied`.
For `w != 0`, prove continuity of `occupied` at `x = w`, its value
`A/(4*w^2)`, and the punctured limit of `raw` at that point with the same value.
The raw expression at `x=w` is not a physical value. At `x=-w` the occupied
denominator still vanishes and the public evaluator rejects it, even if `A=0`.
The empty branch has no screened-exchange cancellation and rejects `x=w`.

## S2: Finite Model and Units

Each term has coefficient `A`, pole energy `w`, state energy `eps`, and
`occupied : Bool`. Let `x = E - eps` and use the respective branch above.

```text
Sigma(D,E) = sigmaX + sum(t in D.terms, K(t,E))
```

The list retains repeated entries. An empty list returns `sigmaX`. `sigmaX` is
an external static constant. Occupied terms include the combined dynamic SX+CH
piece; empty terms include the CH piece. Coefficients absorb weights and matrix
factors; their provenance is external to the formal claim.

Use eV for `E`, `eps`, `w`, `sigmaX`, and `Sigma`; `A` consequently has units
eV^3. `w` means pole ENERGY (hbar times angular frequency). Use a common energy
zero. Shifting both `E` and `eps` preserves `x`. Units are a documented input
contract, not a type-level theorem in this demo. `A` may have either sign.

Inputs in the executable are exact rationals. The real model is obtained by
casting the rational data to reals. Prove that successful checked evaluation
returns precisely the real finite sum after casting, and that success implies
all pole energies are positive and all selected denominators are nonzero.
Validity must be checked even when `A=0`. Do not reject occupied `x=w` when
`w>0`: this is the intended continuous extension.

## S3: Mandatory Synthetic Fixture

```text
E = 1; sigmaX = -1/2
term 1: A=8,  w=2, eps=0,  occupied=true  ->  2/3
term 2: A=6,  w=3, eps=-1, occupied=false -> -1
term 3: A=-4, w=1, eps=0,  occupied=true  -> -1
Sigma = -11/6
```

Term 3 is exactly at the removable occupied pole. Its raw split expression is
undefined. Use the merged value. Tests must also cover zero/negative `w`, both
surviving poles, empty lists, a nonzero static contribution, reordered terms,
negative `A`, and branch/coeff/sign/missing-term mutants.

## S4: Numerical Experiment

Compare the raw split and merged expressions near `x=w=1`, `A=4`. Use an exact
rational oracle for the SAME binary64 input (via `Fraction.from_float`) to avoid
confusing input rounding with evaluation error. Label the result an experiment,
not a floating-point theorem. Include `x=w`, explain the raw singularity, and
report the finite merged value. No arbitrary energy tolerance is an acceptance
criterion for the formal theorem.

## S5: Trust Boundary and Acceptance

Required named theorems: algebraic cancellation; extension value; continuity;
punctured limit; rational-to-real term and finite-sum correspondence; checked
evaluation soundness and domain validity. Record exact names in `GW/Audit.lean`.
Build with pinned dependencies and audit every exported theorem. Fail acceptance
on missing audit entries or any dependency outside the foundational allowlist.

The Lean kernel checks elaborated proof terms. The compiler/runtime, console IO,
Python oracle, source-to-physics correspondence, and exact encoding of external
measurements are separate trust boundaries. A successful executable test alone
does not verify the compiler or runtime.

## Sources and Pending Correspondence

- Requested roadmap: ChatGPT conversation `6aa362f9-6b04-83e9-8d6c-72e201fc27dc`.
  Its text was read; the five original attached images were unavailable.
- Requested handoff design: conversation `328fef41-0fcc-832b-a9d5-e2fab5f12b92`.
  Use its final job-file/handoff approach; no TUI control is required.
- Deslippe et al., BerkeleyGW methods paper, arXiv:1111.4429:
  https://arxiv.org/abs/1111.4429 . Source mapping is recorded separately in
  `docs/SOURCE_MAP.md`; no imaginary source commit or line numbers are allowed.
- BerkeleyGW sigma tutorial:
  https://berkeleygw.org/documentation/tutorial/tutorial-sigma/ . Supports the
  occupied SX versus all-band CH distinction; it does not establish our entire
  scalar restriction or a match to a particular implementation version.

