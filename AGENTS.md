# Project Instructions

## Collaboration and Evidence

- Explain assumptions, evidence, and tradeoffs. The user must be able to assess
  the mathematical and physical claim independently.
- Data takes precedence over notes, labels, and derived columns. Call out any
  disagreement.
- Read, in this order, before work: `.agent/STATE.md`, `docs/CODEMAP.md`,
  `docs/ENDPOINT.md` / `docs/BRIDGE.md` (the canonical specification and bridge), and
  the assigned task. `Specification.md` (v0.1) is the archived demo contract: read it
  for history only.
- State scientific claims at the scope of `README.md` and `docs/reviews/README.md`
  (REVIEW-28): conditional theory-to-specification identities, certified numerical
  evaluation of one pinned run. Do not say the project formally verified the core
  physics of BerkeleyGW.
- Keep formal proofs, executable tests, source correspondence, and physical
  accuracy as separate claims. Never imply numerical agreement proves a program.
- A specification (the archived demo's, or `docs/ENDPOINT.md` §4) is a
  provisional mathematical contract, not a user-approved physical model. Record
  proposed changes in the handoff instead of silently weakening theorem
  statements or changing occupancy conventions.

## Proof Integrity

- No `sorry`, `admit`, project-defined axioms, `native_decide`, or unsafe proof
  shortcuts. Use ordinary kernel-checked proof terms.
- Audit exported theorems with `#print axioms`. Only `propext`,
  `Classical.choice`, and `Quot.sound` are allowed foundational dependencies.
- Real and rational division in Lean is totalized; zero-denominator expressions
  must never be described as physically defined. Executable public evaluators
  reject nonpositive pole energies and zero surviving denominators.
- Use the pinned Lean/mathlib versions and narrow imports. Keep generated caches
  outside source control. Run `bash scripts/verify.sh` before acceptance.

## Ownership and Handoff

- Codex owns scope, integration, and acceptance; Claude implements one assigned
  bounded task. No nested agents or overlapping writers.
- Worker completion means ready for review, not accepted. The supervisor reruns
  checks and records the actual outcome.
- Durable state is task files, handoffs, run logs, and versioned source. A session
  ID is optional convenience and is never the only continuation mechanism.
- Read `.agent/WAKEUP.md` at every restart. A file is not a running scheduler.
- Do not install timers, recursively dispatch agents, or publish as part of a
  worker task. Do not edit unrelated files or delete existing user work.
- **Standing owner authorization (2026-09-16): committing and pushing worker
  branches no longer needs per-task permission.** The owner's stated reason is
  that this repository is private and nobody depends on it for work. That reason
  is what bounds the grant, so it does NOT extend to: merging into `main`,
  changing visibility or licensing, publishing, or any upstream/community
  contact. Those remain per-decision, and the outreach restrictions below are
  unaffected — they exist because of other communities' policies, not because
  of this repository's privacy.

## Architecture and workflow

- **Feature freeze (owner, 2026-10-01).** No new scientific work. Only the owner lifts
  it, by a recorded decision; see `.agent/STATE.md`. Scoped lift (owner, 2026-10-02):
  only the REVIEW-28 corrections F1–F4 (`.agent/tasks/R28-*.md`), extended (owner,
  2026-10-03) to the follow-up corrections of the post-fix review (`.agent/tasks/R28-R2.md`),
  and (owner, 2026-10-05) to PR #30 and its repo-wide completion R28-R3
  (`.agent/tasks/R28-R3.md`).
- **Canonical modules** per layer are listed in [`docs/CODEMAP.md`](docs/CODEMAP.md).
  Extend or reuse the canonical module. Do not reimplement a canonical layer (eps,
  eps⁻¹, Coulomb, GPP kernel, Σ, QP/roots, many-body theory, bridge). ARCHIVED modules
  are frozen, and nothing new may import them.
- **Registries are generated.** `python3 scripts/registry.py` writes the `GW.lean`
  imports, the `CheckAxioms` imports, the `scripts/gates.py` partition and the
  `PROVENANCE-R6` digests. Do not hand-edit them. `--check` runs in both gates.
- **Gates.** Run `bash scripts/verify.sh --gate fast` (< 10 min warm) before every
  commit. Run the full `bash scripts/verify.sh` (~1 h warm, ~5 h cold) before every
  merge; the supervisor reruns it.
- **One writer per file.** Task scopes must not overlap. Shared files (registries,
  `docs/BRIDGE.md` tables, `.agent/STATE.md`) are written by one designated integrator.
- **Test isolation.** No module-level mutable state may be shared across tests. Every
  test module must pass alone, in any order, and in parallel processes. This failed
  once: `cert.STATS`, BRIDGE-FIX.
- **Done includes** a factual `.agent/STATE.md` update that cites files.
- **Nested agents.** The rule above ("No nested agents or overlapping writers") was not
  kept this session. The supervisor ran BRIDGE-DISC, -Q0 and -COR in parallel, and all
  three wrote `GW.lean`, `GW/Audit.lean`, `scripts/gates.py`, `PROVENANCE-R6.txt` and
  `docs/BRIDGE.md` (merges `f4124da`, `3387327`). *Proposed, not decided:* a supervisor
  may run parallel workers only when their task files declare disjoint write scopes.
  Workers then never touch generated registries, and the integrator regenerates them
  after merging. Workers never spawn agents.
- **Recommendation (the owner has not decided).** A human reviews every change to a
  specification or transcription (`Specification.md`, `docs/ENDPOINT.md` §4,
  `SigmaSpec.lean`, `EpsSpec.lean`, the conventions in `bgw/endpoint/spec.py`) before
  anything relies on it.

## Community alignment

- Search the pinned dependency source before adding generic definitions or
  lemmas. Reuse existing APIs; a local wrapper needs a concrete interface reason.
  Do not upgrade or vendor libraries merely to claim compatibility.
- Keep model-specific experiments downstream and narrowly scoped. A successful
  example is not a universal diagram framework. Record semantic limitations and
  prove needed connections before extending a representation beyond its domain.
- Before a new general abstraction, inspect relevant community work and record
  the reuse decision briefly in the existing task handoff, not a new bureaucracy.
  External review availability is not a prerequisite for private exploration.
- No agent-initiated upstream issues, PRs, review requests, bulk patch batches,
  reviewer replies, or public outreach. Check the destination's current policy;
  do not generate messages for posting where LLM-written communication is banned.
- Any upstream proposal requires a human technical owner who understands the
  definitions and proofs, personally checks references, writes required human
  communication, discloses assistance, and verifies implemented review feedback.
  AI-to-AI review is not human sign-off. Maintainers' decline or lack of capacity
  is a reason to stay downstream, not to keep resubmitting split-up variants.
- Prefer small, useful, maintainable contributions over theorem counts, code
  volume or upstream-PR targets. Do not add tests policing these prose rules.
- The aim is a narrow downstream research asset that could later contribute
  selected results to existing libraries, not a competing general library that
  maintainers are asked to reconcile. Expert attention, review time and future
  maintenance are real costs.
- Novel local objects need missing semantics as their reason, not ease of code
  generation. Prefer explicit connections to established interfaces; do not
  imitate their names with subtly different meanings. A focused standalone
  project depending on mathlib is legitimate; do not vendor, upgrade or write a
  speculative adapter merely to claim alignment.
- Human duties before any community interaction (policies current when copied,
  2026-10-02 from `docs/LL-C1-REVIEW.md` §5; recheck them at the time): mathlib
  requires understanding and disclosure of AI-assisted contributions and
  prohibits LLM-written GitHub/Zulip comments; Physlib requires human
  responsibility for content, personal checking of bibliographic references,
  human reviewer communication, and independent checking of implemented feedback
  before re-review. A private agent-authored PR is not a template for upstream
  communication and does not satisfy these duties.
- Credit papers and reused library work, preserve source and licence notices
  (`THIRD_PARTY_NOTICES.md`), and do not present the agent workflow as a
  mathematical result or imply community endorsement.
- Policy sources: [mathlib contribution / AI-use policy](https://leanprover-community.github.io/contribute/index.html),
  [Physlib AI policy](https://github.com/leanprover-community/physlib/blob/master/AI-POLICY.md).
  The concrete LL-C1 findings stay in the archived `docs/LL-C1-REVIEW.md`.
