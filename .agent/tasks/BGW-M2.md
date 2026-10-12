# BGW-M2 — independently exported chi to certified screening, then STOP

**AUTHORIZED: this task only.** The owner requested inspection of M1-R1 and a
longer-duration successor. Read `AGENTS.md`, `.agent/WAKEUP.md`, the updated
`docs/LIN_LINDSEY_ROADMAP.md`, and `../handoffs/BGW-M1-R1-ACCEPTANCE.md` first.
Then read M1's source, provenance, and returned R1 handoff. This current dispatch
supersedes older M1-only task pointers in historical state; do not replay a finished
task or wait for another activation confirmation.

Base: PR #14 repair `353f9803ec4e51c572dcaa4e3fc785e4a21f49fa` plus this plan.
Work in an isolated local branch/worktree. Preserve other writers and existing
runs. Standing permission covers private branch commits, pushes and review PRs;
not main merges, stack cleanup, licensing/visibility changes or upstream contact.

## 1. The one question and its endpoint

Can the production inverse be checked against a Lean-certified reference formed
from independently exported chi and V, while explicitly accounting for the
rounding between ideal formation and the stored dielectric matrix?

Keep the same BerkeleyGW 4.0 static, serial, real-flavor example, cutoff 1.5 Ry,
q=(0,0,1/2), full ordered nmtx=8 basis. No larger basis, second material or second
scientific question. Its deliberate lack of material convergence remains explicit.

The required deliverable is one connected finite-input result:

    independently exported chi_hat,V_hat
      -> exact E_star = I - V_hat*chi_hat
      -> certified inverse R_star and derived W_star
      -> quantified connection to stored E_hat and production inverse X_hat.

Also compare a separately built pristine executable with the instrumented one on
this input. This is empirical instrumentation-neutrality evidence for this run,
not a theorem that the patch is neutral on all inputs.

M1 already certifies inverse(E_hat). Do not substitute that old result, a Python-
only comparison, recover_chi(E_hat,V_hat), or another synthetic example for the
new deliverable. The origin of chi from wavefunctions, the general Wick/skeleton
problem, GPP frequency convolution, self-consistency and the rest of BerkeleyGW
remain outside this task. They remain goals, not completed or abandoned work.

## 2. Working allowance and internal waypoints

**12 cumulative active hours**, including computation, builds and tool waits,
across resumes. This is a ceiling, not a runtime target. Finish earlier when done.
Up to 20 additional minutes after a terminal condition may only save evidence and
write the handoff. No new paid resources, global installations or toolchain upgrade.
Use existing authorized CPU resources and existing reasonable concurrency; do not
interpret a longer allowance as authority to rent compute or spawn nested agents.

Internal waypoints are not separate review gates. When one passes, record its
commands/commit and continue to the next without asking the owner whether to proceed.

| Waypoint | Required evidence | Decision |
|---|---|---|
| A: baseline and access | Pinned input/source paths and hashes; working Lean baseline; reproducible pristine/instrumented build plan. Access preflight cap 60 active minutes. | Proceed if viable; otherwise BLOCKED. A running, making-progress build is not a missing-access failure. |
| B: actual input acquisition | Actual independent chi,V,E_hat,X_hat and ordered basis; pristine A/B output available; conventions and numerical rules frozen. Due by 3 cumulative active hours. | Proceed; missing data or unresolved mismatch at the cap means BLOCKED with partial evidence. |
| C: certificate feasibility | By 6 cumulative active hours, at least one NEW concrete actual-input formation-bound or E_star-inverse certificate compiles and is audited. A generic conditional lemma alone does not count. | Continue through the integrated result; otherwise BLOCKED, not another synthetic task. |
| D: integrated checkpoint | All acceptance items in sections 3–8, full gate, reproducible packet. | CHECKPOINT_READY and STOP, even with time left. |

At ANY point stop on an unresolved central obligation after 90 active minutes
without new evidence, or two materially different unsuccessful approaches that
leave that same obligation unadvanced, whichever happens first. Tactic variations,
renamed helpers and extra prose are not new evidence. Ordinary successful debugging
within fixed semantics is permitted. Do not silently redefine the task to avoid a cap.

## 3. Pristine/instrumented reproduction and acquisition

Read the selected pinned source and the official documentation yourself:
https://manual.berkeleygw.org/4.0/epsilon-overview/
https://manual.berkeleygw.org/4.0/epsilon-keywords/
https://berkeleygw.org/documentation/tutorial/tutorial-epsilon/
Documentation identifies the interface; the actual source fixes the convention.

Make separate pristine and instrumented source/build/run locations using safe,
fresh directories. Match input bytes, compiler/options/libraries, flavor, environment
and relevant thread settings. Preserve hashes and commands. Reuse disclosed mathlib
dependency caches, but freshly build project sources. M1's claims are not a substitute
for running the current baseline. No destructive deletion of existing run directories.
A small standalone run driver that resolves the repository root correctly is enough;
no scheduler, new provenance platform or new permanent reporting framework.

The instrumentation must independently export the actual chi entries consumed in
forming E, the actual row Coulomb factors, the pre-inversion E, post-inversion X,
and ordered G vectors at the same q. Inspect whether pol%chi has already been
modified, weighted or symmetrized at the selected point. Export the effective operand
if it differs from a nominal input, and describe that choice explicitly. Neither
chi nor E may be reconstructed by inverting/rearranging the answer being tested.

Use raw float64 bits plus round-trippable decimal representations, with finite-value
checks, explicit shape/index/run identities and exact rational decoding. Keep M1's
snapshot untouched. Join matrix/basis/chi files only after matching run ID, q, order,
dimension and hashes; duplicate, truncated, mixed-run or extra records must not be
silently overwritten. Reuse the repaired parser boundary instead of another ad hoc
name-keyed dictionary. No requirement for a universal file-format library.

**Pristine comparison:** compare all 64 entries of the retained inverse in the
ordinary production epsmat output, with the independently generated instrumented
output/dump. Equal whole output bytes suffice where metadata permits. Otherwise
use the source-documented numeric payload and compare all entries with fixed rules;
ignore only specifically identified nondeterministic header fields, not numeric
differences. Comparing only two printed diagonal entries is partial evidence, not
completion of this full-block check. Do not add instrumentation to the pristine
binary to make it readable. An existing official conversion utility is preferred;
a small inspected decoder for this format is acceptable if necessary.

Expected exact agreement is the default for identical deterministic builds/settings.
If nonidentical outputs arise, preserve them and diagnose before proceeding. A known,
source-supported effect may be covered by a rule frozen before the next run, with
all failed evidence retained. Do not tune a tolerance after seeing the discrepancy.
An unexplained instrumentation effect is BLOCKED, not production success.

## 4. Three matrices, not one silently interchangeable E

Use exact rational representations of the independently exported doubles:

    E_star := I - V_hat * chi_hat
    E_hat  := stored production pre-inversion matrix
    Delta  := E_hat - E_star.

V_hat is the full diagonal matrix made from the exported row factors. Use the
complete retained basis and the traced row convention. Preserve units, spin/occupation/
k-point provenance, Coulomb treatment and any transformations at the input boundary.
Do not discard imaginary parts; this task's genuine real-flavor restriction avoids
that, rather than approximating a complex problem by its real part.

Report every difference between E_hat and E_star, including exact zeros and
largest discrepancies. These matrices need not be equal. Proving equality by
redefining chi_hat as V_hat^-1(I-E_hat) would make the task circular.

Trace the source's operation sequence and compiler contraction/reassociation options.
A minimal one-multiply/one-subtract formation has a useful conservative budget with
u=2^-53 and gamma2=2u/(1-2u):

    B_ij = gamma2 * (abs(delta_ij) + abs(V_hat_ii * chi_hat_ij)).

Freeze this budget before inspecting formation errors. Establish that the selected
operands/path are finite and do not require an underflow/overflow exception. If the
traced path differs, propose and freeze a justified operand-based alternative before
comparing its new result; if doing so changes semantics or exceeds scope, stop.
Do not add an unexplained empirical multiplier or use observed Delta to choose B.

The task requires a **concrete Lean-checked inequality** for this data,
abs(Delta_ij) <= B_ij for all retained i,j, or a stronger precise instance-specific
certificate. This certifies the observed finite discrepancy against a stated budget;
it is NOT a universal formal proof of IEEE-754, the compiler or Fortran semantics.
A row-sum bound b_form=max_i sum_j B_ij can be certified similarly. State the exact
norm/row-sum convention; do not assume an arbitrary matrix norm instance means it.

## 5. Certified inversion and propagation of the formation difference

Compute R_star=E_star^-1 from E_star alone with an independent exact solver, using
an algorithm external to Lean as a certificate generator. Check actual concrete
inverse identities in Lean and derive uniqueness, reusing M1/standard matrix lemmas.
Do not formalize a new general solver. A genuinely certified residual-bound approach
is allowed if it proves invertibility/uniqueness and the required actual-input bounds;
a conditional theorem with its numeric hypotheses unchecked is not that alternative.

Let R_hat be the certified inverse of E_hat. Reuse M1 only if the newly exported
E_hat is proved/checked identical to its represented matrix. If it differs, preserve
the difference and certify the new instance; do not overwrite the original case.

Prove and instantiate the general algebraic identity

    R_hat - R_star = -R_hat * Delta * R_star.

This must follow from the inverse equations and the definition of Delta, not be
assumed. Keep multiplication order. It is the new connection from formation error
to the already certified inversion stage.

With W_star=R_star*V_hat and W_hat_ref=R_hat*V_hat, establish the corresponding
screening/uniqueness equations and

    W_hat_ref - W_star = -R_hat * Delta * R_star * V_hat.

Use existing standard matrix, finite-sum, absolute-value and norm APIs first. A small
concrete finite-row-sum certificate is acceptable if adapting a general norm interface
would obscure the statement. Do not build another matrix/norm/interval library.
Every claimed bound must either follow from checked lemmas or be concretely checked
on the represented matrices; a Python assertion alone is not a Lean certificate.

## 6. A composed error budget tied to the actual production inverse

X_hat denotes the exact rational decoding of the production floating-point inverse,
not an exact inverse. Separate three claims: formation error, inversion error for
stored E_hat, and total difference from the independently formed E_star problem.

Freeze the metrics and rules BEFORE examining X_hat-reference differences. Preserve
the existing M1 forward/error criteria, and keep the two residual normalizations
explicit: ||EX-I||_inf/(||E||_inf||X||_inf), versus the same denominator plus 1.
They are different diagnostics, not conflicting values.

For the row-sum infinity norm, a coherent total absolute budget is

    b_inv = 100*n*u*||E_hat||_inf*||R_hat||_inf^2
    b_shift = ||R_hat||_inf*b_form*||R_star||_inf
    b_total = b_inv + b_shift.

These formulas depend on inputs/certified references, not the observed output error.
Do not claim the engineering choice 100 proves universal LAPACK stability. Establish
for this represented case that the measured inverse error meets its budget and that
formation plus inversion fit the total budget. Prove/instantiate the inverse-shift
bound (or a tighter concrete finite-sum bound) rather than just quote it.

**Required finite endpoint:** certify in Lean a concrete inequality bounding the
actual encoded X_hat-R_star (row-sum or clearly related entrywise bound) using the
frozen total budget. Tie the literals/certificates to the same extracted X_hat,
E_hat, chi_hat and V_hat. This moves beyond simply printing a Python tolerance pass.
It remains a certificate for one represented output, not a proof of every run.

Report the corresponding derived screened quantities consistently. X_hat*V_hat
computed by the checker is a DERIVED exact transformation of exported data, not a
separately exported production W or a proof of its floating multiplication. Do not
add invented production arithmetic in the patch and call it an existing code path.
Actual W output is not required for this checkpoint; the production inverse and
certified derived screening are the deliberately fixed interface.

## 7. Adversarial tests and delivery

Use the same frozen decision rule for the unmodified control and mutations. At least:
wrong row/column Coulomb placement on the nonsymmetric case, wrong sign or prefactor,
a one-sided basis permutation, a mismatched chi/run identity, one ordinary wrong
formation or inverse entry, and a forged zero-formation-error claim. Compare each
mutant with the appropriate intended problem, not an unrelated exact solution.
A consistent permutation of ALL matrices/basis labels should remain valid after
explicit mapping; this is a useful positive control on the representation.

Retain parser regressions (duplicate run/q, nested start, dropped entry, mixed-file
metadata), exact bit/decimal checks and literal-to-certificate linkage. Check a
corrupted certificate is rejected, with the error recorded, outside the accepted
imported proof chain. Do not use `sorry`, custom axioms, `native_decide`, unsafe
proof shortcuts, false/empty hypotheses or hidden assumptions to obtain green builds.

One small rerunnable driver should use a supplied authorized source/input location,
validate hashes, create fresh temporary directories safely, reproduce extraction
and comparison, and rebuild/check the certificate. Do not embed /tmp paths as the
only durable access story. Restricted large inputs can remain outside Git; retain
hashes and accessible owner-approved archive locations. Do not upload source packages,
wavefunctions, credentials or caches merely to make a PR self-contained.

Run the full existing gate; every new module must actually be imported and included
in the exhaustive axiom audit. Preserve all older mathematical targets, fixtures,
allowed foundational axioms, and pinned dependencies. Only unavoidable existing
manifest updates are permitted. No prose-enforcement tests or new report hierarchy.
Read back what is committed versus generated. Local sources, code, source mapping,
input/output hashes, exact certificate-generation commands, metrics and mutation
results must be sufficient for a reviewer to identify precisely what was tested.

## 8. Terminal conditions and return

Stop at the FIRST applicable condition:

**CHECKPOINT_READY:** actual independently exported chi/V, mapped full-basis data,
pristine/instrumented full-block comparison, E_star/E_hat separation and formation
certificate, certified E_star inverse/uniqueness, instantiated inverse-shift relation,
concrete encoded-production total-error certificate, valid mutations/controls,
reproducible delivery and full gate all pass. Stop; do not begin M3 or expand the
physics because time remains.

**ROUTE_REFUTED:** an admissible checked counterexample refutes a required mathematical
or source-correspondence assertion. A tactic failure, a local bug, ordinary rounding,
or missing access is not refutation. Preserve the smallest decisive example and
specify exactly which assertion failed; do not equate it with failure of GW physics.

**BLOCKED:** failed access/data waypoint; unexplained pristine/instrumented mismatch;
required new semantics/resources/dependencies; infeasible actual-input certificate;
an unresolved comparison beyond the fixed criteria; missing 6-hour concrete-proof
waypoint; or the 90-minute/two-distinct-approach no-progress trigger. Preserve useful
partial work. Do not substitute an assumed bridge or synthetic data to claim success.

**BUDGET_STOP:** the 12-hour allowance expires, or an unavoidable context/session
interruption prevents continuation. Preserve a resumable result and consumed time.
A new session is not permission to reset the budget or restart automatically.

Write `.agent/handoffs/BGW-M2.md`: terminal status; actual base/result; time ledger;
waypoints reached; source/operand conventions; pristine-comparison coverage; exact
new theorem statements; E_star versus E_hat and all three error components; actual
commands/exit codes; committed/generated locations; remaining gaps; one recommended
next decision. No self-acceptance.

Commit, push and open/update ONE private result PR under the standing grant, then
report the terminal status and stop. No additional approval is needed for those
review-delivery writes. Do not merge main, clean up the PR stack, publish, change
licenses/visibility, contact upstream communities, schedule restarts or self-assign
the next stage. Community reuse remains mandatory; private longer work is not a
license to generate a competing general formalization library.
