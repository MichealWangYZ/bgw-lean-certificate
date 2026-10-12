# PRs 10 and 11: retain the sub-results; restore the original completion criteria — ARCHIVED (2026-10-01): LL review record; LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md.

Reviewed revisions:
- PR 10: `2abd10d8b5b4f52ebc38808de8be7ba3440ee297` (base `52a24726`).
- PR 11: `7a2f4601eaaa676e6e215d05034f1399e79ff93a` (base is PR 10).

This is an AI-authored internal review, not human sign-off, a merge, a public
submission, or an independently repeated Lean build. No next worker is launched.

## Decision

**Keep PR 10 as a conditional, first-order Wick/Hartree–Fock sub-result (C3.1).**
The inspected algebra is useful and the independent finite checks agree. It does
not complete the original C3 roadmap row or prove Gaussian perturbation theory.

**Keep PR 11 as a finite static-response/formal-screening prototype (C4.1), with
changes requested to its scientific characterization and one mutation test.**
The diagonal-sign theorems are true, but they do not establish the claimed
structural obstruction to a properly signed/scaled correspondence. The prototype
does not complete the original C4 matched-input BerkeleyGW milestone.

No discovered problem requires throwing away the mathematical developments.
Do not, however, record “C3 and C4 complete” or advance to an undefined C5. The next
substantive task should close an existing interface, not add another self-contained
formula family with the interface declared out of scope.

## What the original project was for

The original discussion aimed to build a many-body-theory foundation, recover GW
as a selected approximation, implement a reference in Lean, and generate examples
that could check Fortran BerkeleyGW. Lin–Lindsey Part I was subsequently chosen as
a concrete, finite-dimensional theoretical entry point, not as a silent replacement
for the electronic/GW checking objective.

These are connected goals, not interchangeable deliverables. A proof about the
classical Gibbs model is not automatically an electronic-GW result. A validated
static matrix calculation is not automatically a GW self-energy calculation. A
Python reference tested against itself is not a production-code comparison.

Earlier GPP/Fortran source-level diagnostics are genuine downstream assets. This
review does not erase them or imply that the repository has never interacted with
BerkeleyGW. The new C4 path simply has not yet connected its electronic model to
those assets or to a matched production dielectric calculation.

## Evidence actually obtained

Read both task briefs and handoffs, the complete new `Wick.lean` and
`Electronic.lean` modules, both reference implementations and their tests, the
shared validator, PR diffs, and current project instructions/state. The new scopes
were self-authored by the implementer. The owner explicitly authorized both runs;
this review does not treat the lack of an intermediate review as unauthorized work.

In the review container, reconstructed and verified Git blob hashes for:

| Reference | Exact Git blob |
|---|---|
| `ll/wick_reference.py` | `c3a16b495c02bf86f71ed5738fbb77a4dcc5d623` |
| `ll/electronic_reference.py` | `7506e8aadcde818a2b9e9a2a9a7d6a5d22de9e41` |

Executed `run_review.py` against those exact bytes. Observed:

- All 15 arity-six recursive matchings coincide with an independent search over
  all 720 permutations for fixed-point-free involutions; no missing or duplicate
  permutation was found.
- 113 six-point moments and 17 normalized-correction entries across the three C3
  fixtures agree with an independent finite source-polynomial calculation using
  coefficients of `exp(t^T G t/2)`. This is not a proof of Gaussian integration in
  Lean. Hartree/Fock decomposition and five numerical mutants per fixture check out.
- 136 Neumann-coefficient/partial-sum entries across the C4 fixtures agree with
  SymPy exact matrix powers and sums. Static response and dielectric matrices also
  agree; the Python pivoting solve agrees with an adjugate/determinant calculation.
- A noncommuting two-dimensional witness disproves the sign-alone obstruction
  inference, while preserving both of the original diagonal-sign statements.
- The submitted early-truncation assertion passes both an early truncation and
  the correct intended truncation. It therefore does not diagnose that mutation.
- Twelve scalar plasmon-pole/static-value checks pass for nonzero pole frequencies.

**Not executed:** Lean/Lake, the candidate Lean executables, either original full
Python test suite, the repository verification gate, or BerkeleyGW. Lean/Lake were
absent here; a direct download probe failed with DNS resolution error (curl exit 6).
No PR-triggered workflow runs were returned for either reviewed commit. Worker
reports of 319/350 scientific tests and 592/631 exhaustive audits remain submitted
results, not independently reproduced counts. Generated candidate JSON/logs were
not used as if they were available. No synthetic data is represented as Lean output.

The supplied reproducer needs SymPy for the independent reviewer calculations;
this is not a new project dependency. It refuses mismatched reference-source hashes.

## PR 10: what is sound, what remains conditional

### The finite first-order algebra is substantive

`wick6_split` expands the six-point pairing sum into the direct external pairing
and the other twelve terms. `disconnected_cancels` cancels the normalized
subtraction. `firstOrder_eq_hartree_fock` then uses symmetric G and v to give

```
Delta G = - G [ (1/2) diag(v d) + (v hadamard G) ] G,
d_i = G_ii.
```

`dressed_ring0_eq_neg_fock` invokes the existing ring contribution; it is not just
an independently named formula of similar shape. The explicit nonzero Hartree
witness is useful. The source does not introduce an unproved Lean axiom to obtain
these algebraic equalities.

### The upstream interpretation is still not a theorem

`wickMoment` is defined by pairings. `firstOrder` is defined as the normalized
first-order subtraction. The code does not construct a Gaussian probability
measure, prove these are its moments, or derive the subtraction by differentiating
a normalized Gibbs expectation. The omitted interpretation is accurately disclosed,
but disclosure is not closure of that link. Symmetric matrices in an algebraic
theorem also need not satisfy the positivity/stability assumptions of an actual
Gibbs integral.

This is why “conditional first-order combinatorics” is the correct milestone
label. It is not a failed result; it is a smaller result than the whole original C3.

### Source check and task discrepancies

The `1/8` is correct: Lin–Lindsey Part I, section 2.1, **equation (2.4), printed
page 5**, defines the quartic interaction with exactly this prefactor. The task
and handoff's pointer to printed page 42 is wrong for this definition. Page 42
introduces the GW/ring construction. Source retrieved directly from the paper:
https://arxiv.org/pdf/1809.02900

The implementer says the PDF was not read. That is an avoidable source-check gap,
not a missing mathematical library, and should not remain a permanent “assumption”.
Record the correct reference; human verification is still required before any
upstream contribution under the project's community rules.

The self-authored brief also does not precisely match the delivered scope:

- Section 3.1 asks for a finite-list pairing-sum/recursive correspondence. The
  submitted completeness result is at arity six only; the module mentions
  `wickMoment_cons`, but no such declaration is present. For this first-order
  calculation the finite checks and explicit six-point expansion are sufficient;
  do not call the general-list obligation complete or build a new general library
  just to repair a comment.
- Section 4 asks for a fixture with nonsymmetric `v hadamard G`, while the stated
  closed-form contract assumes both v and G symmetric. Their Hadamard product is
  necessarily symmetric. That is an impossible test requirement under those
  assumptions, not an implementation failure. A noncommuting-matrix witness would
  have been a coherent alternative. Correct the brief explicitly.
- The handoff says a second-order two-point extension has 105 pairings at eight
  points. The two-point numerator at order U^2 has **ten** fields and 945 pairings;
  105 applies to the eight-field vacuum U^2 term. This is not an error in the
  first-order proof, but should not inform future planning uncorrected.

The nonzero Hartree result does not refute C2B's accepted scope. The paper and
C2B already separate the ring contribution from Hartree; neither claimed the
ring family alone was the entire self-energy.

## PR 11: useful algebra, but the main negative claim overreaches

### The declared response model is coherent

The specified static chi0 is a weighted sum of rank-one matrices with negative
energy denominators. Under occupied<empty and nonnegative weight, the source
proves symmetry and a nonpositive quadratic form. The general geometric inverse
really reuses the existing `PowerSeries.invOfUnit`, and the classical W is a
definitional instance. The finite telescoping residual is correctly distinguished
from convergence. These are useful, limited results.

### Opposite diagonal signs do not prove a transfer obstruction

The code proves B_ii >= 0 and chi0_ii <= 0, and supplies a strict witness. It does
NOT prove there is no correctly signed/scaled correspondence between the models.
The quantities entering the two screening polynomials are already

```
classical:   I + z (v B)/2
electronic:  I - z v chi0.
```

Thus chi0=-B/2 makes the screening kernels identical. The review executed this
within the PR's own admissible transition specification, including noncommutativity:

```
G = diag(2,3), v = [[2,1],[1,3]], B = diag(4,9).
transition 1: occ=0, emp=2, weight=4, m=(1,0)
transition 2: occ=0, emp=2, weight=9, m=(0,1)
chi0 = diag(-2,-9/2) = -B/2;  v B != B v.
```

All coefficient comparisons at degrees 0..5 agree, and the general algebraic
identification follows by direct substitution. This does not establish equivalence
of the underlying physical systems; it establishes that the stated sign argument
cannot establish their non-transferability. Preserve the true diagonal lemmas.
Replace “the content does not transfer — proved by structural obstruction” with
“direct identification B=chi0 is generally wrong; the physical correspondence,
including signs, degeneracies and matrix-element conventions, is not derived.”

This correction matters to the project's direction: do not use a difference of
convention as a theorem that the broader theoretical route cannot connect.

### The exact static solve is not compared with a Lean static solution

The Lean executable supplies chi0, eps, Neumann coefficients and finite partial
sums. The exact Gaussian-elimination W is computed on the Python side and tested
against eps W=v there. No Lean numerical static inverse is supplied; the tests
explicitly acknowledge this. The valid coefficient/partial-sum comparisons must
not be described as agreement of two independently obtained full static solutions.

A concrete fixture illustrates the distinction:

```
chi0 = [[-4,-2],[-2,-2]],  v = [[2,1],[1,3]]
W_exact = [[4/13,-3/13],[-3/13,23/39]]
partial_2 = [[404,457],[457,521]]
partial_3 = [[-6780,-7695],[-7695,-8735]].
```

The eigenvalues of v chi0 are -9 +/- sqrt(61), both of magnitude greater than one.
The formal coefficient identities remain valid, but these partial sums are not
converging to W_exact at unit coupling. Nothing in the source promises otherwise.

### The early-truncation mutant is nondiagnostic

`MutationDetection.test_an_early_truncation_is_detected` checks that partial_2 is
not W_exact. The same assertion is true for the intended, unmutated partial_3.
Replacing that mutant with the correct partial sum would still pass. Compare
against the intended validated partial_3 (or its exact finite residual) instead.
Separate tests already compare each emitted partial sum against the matching
reference order, so this does not invalidate the core result or show a corrupted
candidate escaped the complete gate. It is a test-characterization defect.

### “GPP bridge” is a scalar calibration identity, not a connected implementation

`gpp_static_limit` correctly shows that the chosen pole strength makes a scalar
rational function take the specified value at zero frequency. The pole location
is still input. No theorem maps it to the existing `GW.GPP.Data`/`sigmaChecked`
parameters or proves the frequency convolution. Keep this useful identity, but
call it a scalar static-matching check. Before any production matrix use, reconcile
matrix identity/off-diagonal conventions, complex elements, units, and pole rules.

## Where the project has drifted

The topics have not wandered randomly: both additions are relevant. The drift is
in **what completion is allowed to mean**. The original missing links keep moving
into an “input”, “specified”, or “out of scope” paragraph, while new checkpoint
labels turn green. A self-authored implementation brief is useful for organizing
work but cannot redefine completion of the owner's larger roadmap.

The reviewer also contributed to this: earlier reviews allowed progress with
clearly disclosed assumptions but did not consistently make the unresolved
interfaces control the next step. We should not respond by adding yet more review
bureaucracy. We should change the next scientific acceptance criterion.

Accurate status:

| Link | Present status |
|---|---|
| Selected classical ring data -> arbitrary-order coefficients -> formal screening | Implemented; reviewed with stated independent-build limits |
| Pairing-sum first-order algebra -> Hartree/Fock -> dressed ring zero | PR 10, useful conditional sub-result |
| Actual Gaussian/Gibbs moments -> those pairing sums and normalized expansion | Not proved here |
| General bare/bold and skeleton theorem (Part I Theorem 4.12) | Not completed |
| Specified finite electronic transitions -> static response -> formal screening | PR 11, useful prototype |
| Electronic model/sign/normalization conventions -> a pinned production path | Not yet established |
| Matched-input production numerical comparison on the new electronic route | Not done |
| Screened frequency dependence -> GW/GPP self-energy evaluator | Not connected |

This is not “C3 and C4 complete”. It is a completed selected-ring route plus two
initial interface probes. Do not estimate the remaining program by theorem count
or by the implementer's 12/25-minute timings.

## Recommended next checkpoint, not an automatically launched task

**Prioritize one matched-input BerkeleyGW static-screening comparison**, because it
most directly tests whether the accumulated models can serve the originally named
code. Do not add another isolated proof family before attempting this.

Choose one explicitly bounded interface, preferably production chi0 plus the bare
Coulomb matrix -> eps/inverse/W for one small, complete retained basis at fixed
nonzero q. It is acceptable to treat chi0 as input for this first comparison, but
then state that it validates the screening stage, not how chi0 was formed. Trace
the pinned implementation and document G/G' ordering, units, occupation/spin/
k-point weights, complex conjugation, Coulomb truncation and any symmetrization.
Do not discard imaginary parts to fit the present real-valued prototype.

Important: taking a block of an already inverted large matrix and comparing it
with the inverse of the corresponding uninverted block is generally invalid.
Use a complete small production cutoff or justify the appropriate reduction.

Success means an independently regenerated reference result and a production result
for the SAME defined problem, a predeclared numerical-error criterion, full source/
input provenance, and at least one physically motivated perturbation that the
comparison catches. Reproduce the current Lean gate in an independent worktree
as part of the baseline; the present reviewer has still not done that.

Absence of a fixture in Git is a starting condition, not proof that a comparison
cannot be done. First inspect existing authorized installations, prior runs and
available official examples. BerkeleyGW's manual identifies WFN/WFNq, epsilon.inp,
chimat/epsmat outputs and their meanings:
https://manual.berkeleygw.org/4.0/epsilon-overview/
https://berkeleygw.org/documentation/tutorial/tutorial-epsilon/

Suggested bounds for a later owner-authorized run: four cumulative active hours,
with a 45-minute access/data preflight. Return BLOCKED with the exact missing input,
license/access/tool or model-mapping obstacle rather than substitute synthetic
numbers and call the production milestone complete. Stop with CHECKPOINT_READY on
the stated matched-input result, ROUTE_REFUTED only for an actual counterexample to
a required assertion, or BUDGET_STOP on the spending limit. No automatic C5.

Keep the theoretical objective visible alongside this engineering test. Its next
honest interface is a finite-dimensional Gaussian-moment/source-generating-function
connection, or a bounded general pairing/skeleton decomposition theorem. Choosing
the production comparison first does not claim that those theoretical gaps vanish.

## Community and scope

Stay downstream. Do not vendor a parallel Gaussian/Feynman/inverse library because
an exact lemma was not found. Search pinned APIs and inspect relevant community
work before deciding what local special-purpose code is necessary. No upstream
issues, generated reviewer replies, bulk PRs, dependency migration, licensing or
visibility change is authorized by this review. Disclosing an assumption is good;
continually replacing the intended bridge with a new definition is not closure.
