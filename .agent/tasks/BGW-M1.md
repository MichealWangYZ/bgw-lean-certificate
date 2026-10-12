# BGW-M1 — one matched-input production screening comparison, then STOP

**Authorized now by the owner through the technical sign-off.** Execute only this
assignment when it reaches Claude; no additional activation question is needed.
A repository file is not a running worker. Reviewer/owner accepts the result.

Baseline: main `bbf6a6c44800f4c54f43b8757fac30ea267fdbe3`, containing repaired
C3.1/C4.1 at `36c33b95859a2220dfb25eb7d21f9f6ac9c834e8` and the review records.
Read `AGENTS.md`, `.agent/WAKEUP.md`, `.agent/STATE.md`, the updated roadmap,
`docs/LL-C3-C4-REVIEW.md`, and `../handoffs/C3-C4-R1-ACCEPTANCE.md` first.
The older GPP specification/state is historical to that track; do not erase it.

## 1. Question and claim boundary

Can one real BerkeleyGW static-screening calculation be checked against an
independently computed reference whose represented finite-matrix solution is
certified in Lean?

Close this existing interface rather than add another isolated model. Success is
one genuine matched-input result, not a generic matrix theorem plus synthetic
fixtures. The original goals — general many-body theory, a specified GW reference,
and testing BerkeleyGW — remain. This task validates one screening/inversion
stage, not the origin of chi0, material accuracy, the frequency convolution,
self-consistency, or the whole Fortran program.

The completed C3.1 Wick algebra remains conditional on its moment interpretation;
C4.1 remains a static prototype. Neither original C3/C4 roadmap row becomes
complete merely because BGW-M1 succeeds. Do not launch an undefined C5.

## 2. Access/data preflight — at most 45 active minutes

Use an isolated local branch/worktree. Preserve existing dirty/unrelated work.
Record the actual base, toolchain and bootstrap/gate commands. Freshly build the
project sources; do not reuse an old project executable as evidence. Disclosed
mathlib dependency caches are allowed. A baseline gate failure must be identified,
not silently waived. Routine pinned bootstrap in an isolated worktree is allowed;
no global installation, dependency/toolchain migration or infrastructure rewrite.

Look first for the owner's existing authorized BerkeleyGW source/build, prior
small runs, exported matrices and documented examples. Then inspect official
examples available under the owner's existing access. A fixture absent from Git
is not proof that no fixture can be obtained. Do not scan unrelated personal data.
No new paid compute, credentials, account connection, upstream contact or license
acceptance on behalf of the owner. Preserve third-party notices and distribution
restrictions; a source location/hash is not permission to redistribute a package.

Sources to read, not substitutes for inspecting the selected pinned code:
- https://manual.berkeleygw.org/4.0/epsilon-overview/
- https://manual.berkeleygw.org/4.0/epsilon-keywords/
- https://berkeleygw.org/documentation/tutorial/tutorial-epsilon/

The manual identifies WFN/WFNq, epsilon.inp, chimat/chi0mat and epsmat/eps0mat;
check the actual version's format and whether an output is epsilon or its inverse.

Choose one complete small retained basis, at static frequency and a fixed NONZERO
q, avoiding head/wing limits for this first test. Prefer a nontrivial off-diagonal
matrix of dimension at least two, small enough for a concrete Lean certificate.
An actual production run with a deliberately small full cutoff is acceptable if
labelled unconverged for material properties. A hand-written matrix sent only to an
extracted BLAS/LAPACK routine is not the production calculation required here.

Within preflight identify a reproducible acquisition/run path and a feasible full
matrix size. Existing authenticated local/remote outputs with adequate provenance
may be used; otherwise run the selected small official example on already-authorized
resources. If access, data, source provenance or a feasible environment is missing
at the cap, return BLOCKED with the exact missing item and attempted paths. Do not
replace it with synthetic data and mark the production requirement complete.

## 3. Freeze the interface before inspecting reference/production agreement

Write one short section of the eventual handoff naming the selected source revision,
source locations, run/inputs, q, frequency, full basis/cutoffs, and comparison target.
Do not create a new planning framework. There are two permitted input boundaries:

**Preferred:** production chi0 and bare Coulomb V, plus independently exported
pre-inversion E and post-inversion output. Check the selected epsilon-formation
convention separately, then the inversion/screening stage.

**Permitted narrower boundary:** the actual pre-inversion E and V from the production
run, with its post-inversion result. This checks the inversion/screening stage only;
formation of E is explicitly an input. State which boundary was used. Producing
E by inverting the candidate output would make the oracle circular and is forbidden.

For the chosen representation write the exact equation to check, e.g. E R = V or
E X = I. Do not infer the order from a filename. If only inverse dielectric X is
produced, validate it and derive screened R using the actual code's Coulomb
convention; distinguish production output from your derived quantity.

Trace G/G' ordering, real/complex storage, conjugation, units, spin/occupation/k-point
factors, Coulomb truncation and any symmetrization. With E as the declared input,
upstream weights are provenance, not newly verified physics. Keep complex entries;
a genuine real-flavor case is allowed, discarding imaginary parts is not.
Symmetrized and unsymmetrized matrices must be connected by explicit transformations
with their required invertibility/positivity assumptions, not by transpose guessing.

Do not take a block of a large inverse and compare it with the inverse of the
uninverted block. Use the complete retained production basis or a justified exact
reduction. Reject a scalar/diagonal-only fallback that avoids the chosen matrix test.

Record the numerical metric and pass rule BEFORE inspecting the candidate/reference
difference. Include an entrywise maximum error, a declared matrix norm, and a
normalized residual/backward error. Set thresholds using arithmetic/export precision,
dimension and measured INPUT conditioning, not the observed discrepancy. An ill-
conditioned or low-precision export may require higher precision or a BLOCKED result;
do not widen tolerances afterward. Distinguish numerical engineering tolerances
from a proved forward-error bound and from material-model error.

## 4. Independent reference plus a concrete Lean connection

Extract the small matrices at adequate precision, preserving full stored values
where possible. Record exact rational real/imaginary representations of binary
or decimal exports, the encoding convention and hashes. Rounded exported inputs
are not the unrounded physical system; state that interpretation.

Compute the reference from the declared input, without reading the production
answer as an expected value. Exact rational (or rational real/imaginary) elimination
is a useful option at small dimension. Arbitrary-precision solving is another
numerical route, but a numerical solve alone does not complete this task.

**Required Lean bridge:** use existing finite-matrix algebra to state the represented
screening equation and certify the actual reference for the selected production
input. Do not reimplement a general matrix library or formalize the entire solver.
An untrusted external solver may emit a certificate; the certificate is what Lean
checks. One sufficient pattern, over a suitable field, is:

    L * E = I,       E * R_ref = V.

Prove these equalities for the concrete encoded data using kernel-checked terms,
and use the general finite-matrix argument to conclude R_ref is the unique solution
of E R = V. For an inverse target, V=I. A corresponding two-sided inverse certificate
is also acceptable. If the reference is represented in another equivalent basis,
include that mapping in the statement rather than silently changing the problem.

A small verified residual-bound certificate instantiated on the same input is an
allowed alternative when exact rational solving is impractical. It must genuinely
bound the reference's discrepancy from the unique solution, with the necessary
invertibility/conditioning assumptions proved or concretely certified. A conditional
lemma with its numerical assumptions left unproved is not such a certificate.

A generic theorem, Python-only success, printed theorem names, or an executable
checker returning true with no checked instance is NOT the requested Lean result.
No sorry/admit/custom axioms/native_decide/unsafe proof shortcuts. The concrete
certificate module and general bridge must be included in the existing audit/build.
Use standard scalar/matrix types; no custom complex field or new proof framework.

This certifies a solution for explicitly represented finite inputs, not the IO
parser, the floating-point implementation, or the physical correctness of E. Check
extraction/encoding independently with hashes and a round-trip test. Compare the
production floating-point result separately against the certified reference with
the predeclared metric. A exact representation of a rounded E can differ from
forming E exactly from rounded chi0,V; do not conflate those two problems.

If only the production/Python comparison succeeds while this Lean connection is
blocked, preserve it as valuable partial evidence and return BLOCKED or BUDGET_STOP.
Do not redefine complete success as a Python-only comparison.

## 5. Mutations, evidence and reproducibility

Check at least one numerically nontrivial convention perturbation on the selected
input — e.g. a changed Coulomb prefactor, wrong basis permutation of ONE side, wrong
sign, or a conjugation/transpose mistake that is not an actual symmetry of this case.
Inject it into the checked path and show the stated comparison rejects it. The
unmodified control must pass the SAME criterion. Avoid a mutant that merely differs
from an unrelated exact solution, as in the repaired early-truncation test.

Also reject an ordinary wrong coefficient, missing/duplicate matrix labels and
mismatched shape. Reuse the existing small evidence validator where appropriate;
a new text schema, workflow platform, or collection of prose-enforcement tests is
not needed. A source mapping is not kernel-proved because the nearby algebra is.

Retain a minimal permitted data packet: source/run/input/output hashes, exact extraction
and generation commands, complete selected matrix/basis metadata, reference and
production results, concrete certificate, measured metrics, mutant outcomes and logs.
Large/restricted raw inputs may stay at a stable authorized location with reproducible
access instructions and hashes; report access limitations instead of inventing a
public download. Do not commit tool caches, credentials, local absolute symlinks or
large source/data bundles. Clearly distinguish committed from regenerable artifacts.

Run the existing full gate with all new theorem modules and scientific tests actually
included. Preserve old target statements and GPP scientific scope; use only unavoidable
existing manifest updates, with no expansion of what an old manifest claims to cover.

## 6. Budget and mandatory exits

Allowance: **4 cumulative active hours**, including builds, computation and tool waits.
Preflight cap 45 minutes, inside that allowance. Resumes do not reset the clock.
Reserve at most 15 additional minutes ONLY to preserve evidence/write the handoff.
Stop at the first applicable condition:

- **CHECKPOINT_READY:** actual production input/output with traced conventions;
  independent matched reference; concrete Lean-certified connection for that same
  represented input; predeclared numerical criteria met; meaningful mutant rejected
  and unmodified control accepted; reproducible evidence and full gate pass. Stop.
- **ROUTE_REFUTED:** an exact counterexample or sufficiently resolved evidence refutes
  a required source/algorithm correspondence. Distinguish a local implementation bug,
  input mismatch or floating noise from refutation of a physical approximation.
- **BLOCKED:** missing access/data/source semantics, an unresolved comparison mismatch,
  infeasible exact certificate, baseline/toolchain failure, need for unauthorized
  scope/resources, or a central obstruction with 60 active minutes without new evidence
  or two materially different unsuccessful approaches. Give a small reproducer and
  the minimum external decision needed; do not hide a mismatch by changing conventions.
- **BUDGET_STOP:** four hours expire or an unavoidable session interruption prevents
  reaching another status. Preserve partial work and actual open obligations.

Within scope, choose efficient extraction, exact solving and proof tactics. Beyond
scope: new material campaigns, frequency convolution, self-consistency, all of Wick/
skeleton theory, production-code fixes, full Fortran verification, analytic limits,
upstream contact, dependency migration, public/licensing changes, paid compute,
main merge, branch-stack cleanup or automatic next tasks.

## 7. One return packet

Write `.agent/handoffs/BGW-M1.md` with status, base/result commit or patch, active
time, input boundary selected, physical/source conventions, exact claim proved,
production/reference metrics, mutations, actual commands/exit codes, evidence paths,
and the main remaining gap. Give one recommended next decision, not a self-assigned
task. A valid blocked result is preferable to making the next checkbox green by
moving the required connection out of scope.

A local result commit is permitted. Push/PR creation for the worker result requires
separate owner permission; no merge, publication, contact or restart is authorized.
Report the terminal status and STOP for review. Do not ask repeatedly whether the
work is enough, self-accept, or continue to another milestone after finishing.
