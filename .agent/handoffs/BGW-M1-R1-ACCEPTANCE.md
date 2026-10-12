# BGW-M1-R1 acceptance and BGW-M2 dispatch

Date: 2026-09-16. Reviewer: ChatGPT, AI-assisted technical review.
Reviewed PR #14 head: `353f9803ec4e51c572dcaa4e3fc785e4a21f49fa`.

**ACCEPT_FOR_INTERNAL_PROGRESSION within the original narrower M1 scope.**
The represented pre-inversion E has a concrete inverse/screening certificate;
the committed production inverse agrees with that reference. R1 closes the
previously demonstrated run-boundary defects and supplies the missing small
provenance packet. No further repair-only round is requested.

The owner now requests a longer-duration successor. **BGW-M2 only is authorized**
under `../tasks/BGW-M2.md`, with a 12-active-hour ceiling and explicit earlier exits.
No additional activation confirmation is needed once Claude receives the task.
Posting this dispatch does not launch a process, merge a PR, or authorize M3.
The original general-theory and electronic self-energy goals remain unfinished.

## Freshly executed review, not just the worker's report

Reconstructed the relevant submitted files in an isolated review directory and
verified exact Git blob hashes before execution:

| File | Git blob |
|---|---|
| `bgw/m1_screening/extract.py` | `6074ec0c246ac2556422e898e4ae038bd4542165` |
| `bgw/m1_screening/reference.py` | `92f49da565f8d5dfdc5108c948e3cc090d524ff8` |
| `tests/test_bgw_m1.py` | `548a7eaad0066b547e93391ac33c8435e73702ef` |
| `GW/BGW/M1Screening.lean` | `58c13ea250265394e5be0d7f7707f85cf1d287e3` |
| `data/m1_eps_dump_q2.txt` (under `bgw/m1_screening/`) | `5b422d62f82665420a2850aeb3879ecf1f3b8c76` |
| `data/m1_gvec_q2.txt` (same directory) | `d51a609c1e9f3e0b003a6b8192b28a1a6d572e51` |

- All **34 original BGW-M1 tests pass on the committed dump**. Not synthetic
  candidate output and not a newly executed BerkeleyGW run.
- Independently recomputed the exact inverse with SymPy; it equals the reference.
  The entire current Lean file matches its blob after applying only the observed
  provenance-header edit to the previously reconstructed certificate. The formal
  definitions, numeric literals and proof bodies are unchanged.
- Nine direct malformed-input probes reject: repeated q; nested start; unexpected
  q in a single-slice load; in-block duplicate; mismatched end; out-of-block data;
  missing entry; empty dump; inconsistent dimension. A deliberately explicit,
  valid multi-q file still parses as two blocks. Single-slice rejection has not
  disabled the legitimate multi-q parser.
- Forward relative infinity-norm error remains `1.7112154669742808e-16` against
  `3.416065984394502e-13`; the original max-entry residual is
  `8.757690843317078e-17` against `8.881784197001252e-14`.

The residual discrepancy is resolved exactly, not left as an unexplained mismatch.
Let r=||EX-I||_inf and p=||E||_inf ||X||_inf. The worker reports
r/p = `7.008168410280357e-17`; the earlier reviewer used
r/(p+||I||_inf) = r/(p+1) = `5.562036787802374e-17`.
Both numbers reproduce. Keep each formula with its number; do not change a pass
criterion to make these reporting conventions agree.

Reproducer and observed results are in `audits/bgw_m1_r1_review/`. SymPy is an
optional reviewer dependency, not added to the project's runtime dependencies.
The historical script intentionally requires the reviewed source hashes.

## Source/provenance review and limits

Read the repaired extraction code, submitted tests, regeneration checker, new
relative-header instrumentation patch, provenance record, ordered basis and run
log excerpt. The packet now records WFN/WFNq, input, source/build/executable and
log hashes, q and full basis ordering. The committed excerpt records a completed
real-flavor static run with q-index 2 and nmtx 8. The six original data/definition
hash checks above support continuity of the reviewed finite problem.

**Not independently executed:** Lean/Lake and its axiom audit, the full repository
gate, BerkeleyGW compilation/run, patch application to the external pristine source,
verification of externally stored inputs/executables, or the pristine/instrumented
A/B experiment. Lean/Lake are absent in this review container and the fresh download
probe failed DNS resolution. The worker's 397 scientific + 14 workflow tests,
657 exhaustive audits and bit-identical fresh reproduction remain worker evidence.
No claim of independently repeated kernel or production execution is made here.

The remaining pristine-executable comparison is real, but it was not required to
prove the stored rational inverse. Include it in M2; do not create R2 solely for it.
Some reproduction shell lines still use placeholders and a working-directory-dependent
last command. M2's single runnable driver should resolve its own repository path,
use newly created directories, and verify the input hashes. This is a small carry
item, not grounds for another repair-only milestone.

Do not overstate the shell-count observation: nonconstant V alone does not force
E to be nonsymmetric. In this retained case E is directly checked to be nonsymmetric;
the ordered basis and Coulomb shells help explain the instance. Any more general
inference also needs the coupling/commutation information.

## Why the longer task is justified

M1 now reaches a genuine input-to-production-result boundary. M2 should extend it
one stage upstream to independently exported chi and V, explicitly separating
E_star=I-V_hat*chi_hat from stored E_hat, and bounding how that formation discrepancy
propagates through inversion. A pristine-versus-instrumented comparison on the same
input belongs inside that task. Merely repeating the existing matrix inverse on
more q points or larger matrices is not the next goal.

The longer allowance permits acquisition, source mapping, actual certificate work,
and integrated validation without returning at every routine substep. It is a cap,
not a minimum or a demand to manufacture extra work. Semantic changes and genuine
blockers still stop the task. Private commits, pushes and review PRs use the owner's
standing grant. No main merge, visibility/licensing change, upstream contact or new
paid resources are authorized.

Technical sign-off: **ChatGPT, 2026-09-16**, at the owner's request. This is an
AI-assisted scoped research decision, not human-maintainer approval, a DCO or
cryptographic signature, or certification of all of BerkeleyGW.
