# LL-C2B review — pass for internal progression — ARCHIVED (2026-10-01): LL review record; LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md.

Reviewed PR #8 at `63363c79ce73598810174f241e6907211b0c23d3`.
Base contract: `.agent/tasks/LL-C2B.md` from plan commit `029efaf`.

**Disposition: ACCEPT_FOR_INTERNAL_PROGRESSION.** No mathematical blocker or
repair-only round is requested. This is an AI-assisted source/executable review,
not a merge, human sign-off, upstream endorsement, or independently repeated Lean
kernel verification. Nothing in this review starts or authorizes a C3/C4 worker.

## 1. What was reviewed and what was actually executed

Read the complete `GW/LL/Screening.lean`, the executable `LLC2BMain.lean`, the
handoff, the Python reference/validator/tests, and integration changes. The diff
against the planning base changes 13 files, with no dependency/toolchain upgrade,
no change to the earlier graph theorems, and no general inverse implementation.

For execution, reconstructed these connector-returned sources and checked their
exact Git blob hashes before running them:

| Path | Git blob |
|---|---|
| `ll/screening_reference.py` | `56a312e2e0d7cfa559b25c030f82e12811bb58a0` |
| `ll/evidence.py` | `c4824ae1c1963248d08d1271780d1a08994ad7f0` |
| `tests/test_ll_c2b.py` | `efae546564bd53c46538e73b3916b8ecb5e25087` |
| `ll/ring_reference.py` | `641d536ad219738af480c7bae159721aef49e5bd` |
| `audits/ll_c2a_review/checker_probe.py` | `0cd0532410dbea20cdf66406ae2b4c77558ed5a1` |

Ran the **original 27 C2B tests on a clearly labelled synthetic control table**,
then on 10 separately corrupted tables. W was computed using SymPy exact matrices;
T was computed by the earlier direct graph-contraction reference. The control
passes all 27 tests. All 10 corrupted inputs fail. Also directly exercised the
shared C2A validator on the six historical inventory/metadata/coverage probes:
all rejected. These are checker tests, not a run of the Lean executable.

Independently compared 85 scalar entries of W and 85 scalar entries of the direct
Python graph contribution against the SymPy calculation at orders 0..4. Tested the
reference's generic inverse against a polynomial with noncommuting degree-one and
degree-two coefficients through degree six; both products give the identity to
that order. Additional nonsymmetric/nilpotent, singular-v, and zero-G examples
agree through degree six. These are useful finite checks, not substitutes for the
arbitrary-order theorem.

**NOT run:** Lean/Lake, the candidate executable, a full repository clone/gate,
or BerkeleyGW. Lean/Lake are absent here and direct source download failed on DNS.
The candidate screening table is generated, not committed; its exact-path fetch
returned 404, consistent with the handoff. No PR-triggered workflow runs were
returned by the connector for this commit. The worker's report of 290 scientific
and 14 workflow tests (one pre-existing skip), 191 named and 550 exhaustive audits,
and a green local gate therefore remains submitted evidence, not this reviewer's
independent full-build result.

Reproducer: `audits/ll_c2b_review/run_review.py` (optional reviewer dependency:
SymPy; no project dependency change). Run without Python optimization against the
reviewed source bytes:

```bash
python3 audits/ll_c2b_review/run_review.py --source . --out /tmp/ll-c2b-review
```

It writes synthetic inputs only to temporary paths, never to the project's
candidate-output location. Source mismatch raises an error rather than silently
passing. Committed observed results: `audits/ll_c2b_review/review_results.json`.

## 2. Mathematical contract: the requested connections are present

**Existing inverse API, not a substitute.** `SL` and `SR` call
`PowerSeries.invOfUnit` with unit 1. Constant-coefficient proofs feed the pinned
library's left and right inverse theorems. This is the noncommutative `[Ring R]`
interface that the prior review identified; no new inverse library was built.

**Matrix order is preserved.** The source defines AL=1/2(vB), AR=1/2(Bv), with
B the entrywise square of G. The proved identity v*AR=AL*v connects the two
polynomials. It yields PL*W=C(v), W*PR=C(v), and W=C(v)*SR. It does not silently
use W*PL=C(v), assume invertible v, or commute v and B.

**All-order coefficient identification is genuine.** `Wexp` is independently
assembled from the explicit coefficients. `PL_mul_Wexp` checks its coefficients;
`Wexp_eq_W` uses the existing inverse to identify the two series. `coeff_W` is
therefore a theorem for every order, not agreement at orders 0..4.

**The graph connection is not definitional.** `T` is built from the existing
`FeynDiagram.contribution (ring k)`. `T_eq_neg_hadamardSeries_W` invokes C2A's
`contribution_ring`, with the sign and the proved 2^k divisor. The entrywise map
is additive, not assumed multiplicative. A counterexample to general
multiplicativity is separately proved; it is not used as a proof shortcut.

**Executable definitions are connected.** The executable calls `Wcoeff` and
`Tcoeff`, not fresh formulas disconnected from the theorem. `coeff_W` and
`coeff_T_eq_Tcoeff` are the named equalities connecting them to the formal series.
Printing those theorem names in JSON is not itself verification; inspection of
the definitions and the equalities is what supports this correspondence.

**Degree and analytic boundaries are maintained.** The bubble-counting series
has Fock at degree zero. The coupling-counting series is multiplied by X, and
its constant/shifted coefficients are proved. G remains fixed. No evaluation at
z=1, convergence claim, self-consistency theorem, Hartree derivation, or electronic
GW claim appears in the mathematical result.

The primary paper's screened ring sum is on printed pp. 42–43, Fig. 4.11. Those
pages were re-inspected as images. The paper adds Hartree separately; the code is
correct not to identify the ring series alone with the complete GW ansatz.
Source: https://arxiv.org/pdf/1809.02900

## 3. The recurring reader defect is now closed on the reviewed paths

The expectations come from the caller/specification; the table cannot select its
own order inventory. C1/C2A scalar tables and C2B matrix tables share the inventory,
metadata and coverage checks. The actual C2A caller now invokes `validate_c2a`,
and C2B invokes `validate_c2b` before its main numerical comparisons.

| Synthetic input supplied to the original C2B suite | Observed result |
|---|---|
| Exact synthetic control | 27 tests pass |
| Ordinary wrong W coefficient | 1 numerical failure |
| Ordinary wrong T coefficient | 1 numerical failure |
| Incorrect duplicate before the correct row | rejected |
| Impossible external indices | rejected |
| False dimension | rejected |
| Candidate orders=[0,3] hiding a wrong order-four entry | rejected |
| Duplicate order | rejected |
| Missing or extra degree in a required series | rejected |
| Missing T series | rejected |

Some malformed tables cause class setup errors and consequently fewer than 27
individual tests run. That is expected rejection, not a skipped successful check.

No new false pass of a corrupted required numerical value or covered-order
inventory was demonstrated. There is no reason to send the mathematical task
back for another reader-repair-only round.

## 4. Nonblocking corrections and test precision

### A. The worker's report of an exit-zero archival refusal is incorrect

At the pushed commit the historical C2A probe raises `SystemExit` with a string
on a hash mismatch. Executing a byte-verified copy against a deliberately changed
test file returned **exit 1**, not 0, and printed the refusal to stderr.
The observation in the handoff/PR body should be corrected. No patch to that
archival script is warranted on this evidence; do not repair a nonexistent defect.
The exact refusal result is in this review's JSON.

### B. A truncated product's next coefficient is not analytically unknowable

The reference docstring and handoff say constraining degree five would be a
convergence claim. That is not right. For the truncated W through degree four,
the degree-five residual of (I+z*AL)W is explicitly AL*W4. On the N2-pd fixture
this review computes

```
[[137700,       7208775/32],
 [7208775/32,   1474175/4 ]]
```

It is a finite algebraic coefficient, usually nonzero. The full formal series
has an additional W5 which cancels it. The existing arbitrary-order theorem is
correct; this is imprecise prose and a weak test that only checks matrix size,
not an analytic defect. Clarify when that code is next touched.

### C. The residual tests currently exercise the reference, not the emitted table

`ScreeningEquations` calls `screening_residual`, which regenerates W internally.
Other tests already compare every emitted W/T entry with that reference, so this
does not make the overall comparison vacuous. It is nevertheless more direct to
compute residuals from the validated candidate table when revisiting those tests.
This is test localization/maintenance, not a progression blocker.

### D. Exact arithmetic versus strict serialization

`Fraction` accepts numeric bool/float inputs too. The validator consequently accepts
such encodings for matrix entries even though the prose says inexact entries are
rejected. An exact numerical comparison still checks the converted value; this
review did not show a wrong-value bypass. Narrow the prose or require the desired
rational-string/int encoding when useful. Do not create a schema framework or a new
milestone merely to police equivalent encodings.

## 5. How much progress this represents

The resummation was mathematically expected once the coefficients were known.
It is not a new physics approximation, but it is a newly completed formal connection
between graph-derived coefficients and an existing library inverse. Short proofs
using a suitable API are a success, not evidence that the milestone was meaningless.
The half-weight, matrix order, coefficient bridge and degree convention were all
real opportunities for an incorrect formalization; the inspected result addresses
them. The absence of a lengthy proof is not a reason to demand more code.

Conversely, C1+C2A+C2B still do not formalize the whole paper, derive general
Feynman rules from the Gibbs model, establish the skeleton theorem, or connect to
electronic BerkeleyGW. Do not convert a completed ring path into those claims.

## 6. Roadmap and stop decision

C2B stopped at the intended milestone. The next branch point in the existing
roadmap remains real: broader Lin–Lindsey diagram theory versus a narrow electronic
bridge. This review commissions neither, and no new worker is launched. There is
no need for another screening-polish or repair-only checkpoint.

For the original paper-formalization goal, a useful next C3 subtask would connect
finite Wick pairings and normalized first-order moments to Hartree/Fock, including
cancellation of disconnected terms and the 1/8 interaction normalization. That
would test an upstream semantic link not covered by the ring series. For prioritizing
BerkeleyGW delivery, choose an explicitly specified finite electronic response/GW
bridge instead. Do not silently treat these as the same project or solve both in
one allowance. The next build book should select one after owner direction.

Remain a small downstream project. Reuse pinned community APIs, keep any model-specific
adapter transparent, and do not create a parallel general diagram framework or
upstream-review burden. No agent-initiated upstream issues, PRs, reviewer replies,
publicity, license changes, visibility changes, or main merge are authorized here.
Current mathlib contribution policy: https://leanprover-community.github.io/contribute/index.html
