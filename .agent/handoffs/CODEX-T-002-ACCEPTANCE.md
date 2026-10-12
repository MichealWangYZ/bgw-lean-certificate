# T-002 Acceptance

Status: accepted with the restricted scope below, including repair T-002-R1.
Supervisor: Codex. Final gate completed 2026-09-11 04:38:40 UTC.

## Scope Decision

The user directed Claude to pursue the next proposed milestone. There was no
pre-existing T-002 assignment; `.agent/tasks/T-002.md` records retrospective
acceptance criteria rather than pretending otherwise. The source mapping,
small genuine export, and scoped branch theorems fit that milestone. Codex
accepts the new source note in `docs/` and has integrated `docs/SOURCE_MAP.md`.
Future ownership remains task-specific, not blanket permission over `docs/`.

The BerkeleyGW 4.0 archive SHA-256 pin is sufficient to identify the inspected
source for this demo. It is not a VCS commit or authenticated signed release.
Codex checked the downloaded archive digest, matched all five cited source
files to archive bytes, and independently checked Spack's published digest.
Evidence: `artifacts/t002-source-provenance.json` and the linked source note.

## Review Corrections

- Exact-pole wording overstated the proof. The transcribed branch still has a
  zero denominator at `x=w`; S1 supplies a separate merged extension. Added an
  audited concrete theorem distinguishing their totalized Lean values.
- Occupation is not a common prefactor; only SX receives `occ`. Real flavor
  does not by itself imply real poles. Positive-real-mode and full-occupation
  restrictions are explicit. The provisional S1/S2 contract was not changed.
- Saved evidence contains 48 nonzero S1 comparisons and 48 zero placeholders,
  not 96 valid S1 inputs. Pre/post-sexcut capture stages are distinguished.
  Branch counts concern the occupied loop; the general dump lacks branch labels.
- The export checker previously passed empty input. Parsing, coverage, finite
  domain, coefficient, occupation, checksum, and mutation checks now reject
  missing or inappropriate evidence. Main verification includes both datasets.
- Transcript ulps are measured with `math.ulp`; maximum is 2.0839804, not the
  original <0.7 claim. Absolute error remains 5.784207551782198e-17.
- Upstream has 24 GPP assertions with two tolerances, not 13 uniformly checked
  assertions. The harness reads the upstream block and tests its parser.
- Claude fixed the supervisor's forced-single-thread reproduction setting.
  Inherited host threading restores exact saved text outputs without changing
  tolerances. Failed runs are retained and future failures get diagnostic reports.
- Codex added a final nonfinite benchmark-value guard and regression test.
  Threading dependence is observed; physical equivalence of differing
  off-diagonal outputs or a degenerate-subspace explanation is not proved.

The worker handoffs are retained unchanged as submitted. This acceptance and
the reviewed source notes supersede their incorrect or overly broad claims.

## Independent Verification

`bash scripts/verify.sh`: PASS on the final integrated code and source notes.
`artifacts/verification.json` records 43 input hashes and all step logs.

- 60 named theorem dependency prints; 126 exhaustive project theorem audits.
- Only `propext`, `Classical.choice`, and `Quot.sound` as proof dependencies.
- 9 compiler-generated unsafe runtime declarations reported separately; no
  theorem is accepted using them as a proof assumption.
- 17 Lean runtime cases and 25 Python tests pass.
- Both saved datasets pass, with 11 evidence-file checksums verified.
- General nonzero sample: max S1 residual about 6.25e-16, dimensionless.
- Near-pole sample: max S1 residual about 2.51e-19, dimensionless.

Codex recompiled and checked the standalone transcript. Claude did not edit
that Fortran source in R1; the retained transcript is the reviewed version.

Codex independently reran EPM, epsilon, and sigma for both source trees, then
repeated after the final finite-value guard. Reports:
`artifacts/t002-codex-reproduction/report.json` and
`artifacts/t002-codex-final/report.json`.
Each build satisfies all 24 upstream assertions; worst benchmark residual is
7.61e-7 against its 1e-6 tolerance. Pristine/instrumented sigma logs agree;
sigma log, branch counts, and both dumps match the saved text files bytewise.
The pristine Sigma source was recompiled in a disposable real-build snapshot;
this reuses compiled dependencies and is not a clean-toolchain reproduction.

## Trust Boundary and Next Action

Accepted: manually mapped exact-real identities for a restricted local kernel,
one documented source/run provenance chain, and host-specific numerical
regression evidence. The near-pole plot concerns an unprotected expression,
not a demonstrated BerkeleyGW defect.

Not accepted or claimed: whole-program BerkeleyGW verification, compiler
correctness, portable bitwise reproducibility, floating-point error bounds,
full unitful material self-energy certification, fractional-occupation
reachability, complex/GPU behavior, or physical accuracy.

No follow-on is active. A reasonable later bounded task would examine
fractional-occupation reachability, but it requires its own assignment.
No scheduler, commit, push, or publication was created by this acceptance.

## Delegation Record

User preference: Claude normally implements/debugs; Codex writes bounded jobs,
coordinates, reviews, independently validates, and accepts. Codex initially
took on more T-002 repair work than necessary and delegated the remainder.

T-002-R1 run: `20260911T042121Z-4fc60f38`, exit 0, no reported permission
denials, returned ready for review. It is now accepted after supervisor checks.
Worker lock is idle. Durable continuation is the task, handoffs, source, and
logs; a session ID or timer is not required.
