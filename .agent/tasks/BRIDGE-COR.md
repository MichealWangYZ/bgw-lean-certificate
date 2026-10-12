# BRIDGE-COR — a rigorous bound replacing the heuristic static remainder, then STOP

Base `bridge/theory-to-bgw` 848a277, branch `bridge-cor/work`. Written by the supervisor.

## Why

BRIDGE-MEASURE: the static remainder COR = ½(CH_exact − CH_partial) (Deslippe 2013,
empirical ½) moves O1 by ±117 meV (O1 = 15.4 meV). O1's value rests on a heuristic.
GW theory says the correct term is the DYNAMIC Coulomb-hole contribution of the omitted
(empty) bands n > N_b. Replace the heuristic by a proved enclosure.

## Targets

**C1 (theorem).** For an omitted empty band with `e_n − E ≥ D > 0` and a valid GPP mode
(`w̃ > 0`), bound the theory per-mode CH term (thK, empty branch, GW/Bridge) against the
static CH term of the same mode: prove an enclosure of the form
`dyn = θ · static` with `θ ∈ [θ_lo(D, w̃), θ_hi(D, w̃)]` (derive the exact
functions; e.g. from `w̃/(x − w̃)` with `x ≤ −D`), with sign conditions stated. Handle
invalid/dropped modes explicitly (their rule is BRIDGE's, not new). Sum over modes and
bands: when the weights have mixed signs a ratio bound fails — then bound
|dyn_tail − θ* static_tail| by Σ|weight|·max|kernel difference| instead. Derive
whatever form is actually true; do not force the ½.
**C2 (closure).** The static tail Σ_{n>N_b} (static CH) is EXACTLY computable from
completeness (`chpart_sum_eq_exact`): CH_exact − CH_partial. Combine: the theory Σ with
ALL bands ∈ SigT_partial + [enclosure], as a Lean theorem, under a hypothesis giving
D (lowest omitted band energy) and the w̃ range. Omitted bands' individual energies are
NOT available; the bound may only use D, w̃ bounds and computable static quantities.
If the bound needs |weight| sums over omitted bands that are not computable, say so and
find the computable majorant (e.g. via completeness of |M|² sums, Σ_n |M_n|² =
⟨ρ⟩-type identity) — that is the hard part.
**C3 (numbers).** Python, rigorous intervals (iv.py), Si-EPM: evaluate the enclosure for
Σ(X), Σ(L), Eqp1 and O1 (the Epsilon/Sigma run's band count and the highest computed band
give D; state where D comes from). Report O1 ∈ [lo, hi] with the heuristic replaced, and
where the ½ lands inside/outside. If the interval is uselessly wide, report its width
honestly and what would shrink it (more bands, sharper majorant).

## Rules

Same as `.agent/tasks/BRIDGE.md` section 3: no sorry/admit/axioms/native_decide/
ofReduceBool/implemented_by; axiom allowlist propext, Classical.choice, Quot.sound;
register new Lean modules in GW.lean and GW/Audit.lean; register new tests in
scripts/gates.py; re-sign bgw/weighted_audit/PROVENANCE-R6.txt digests that change;
independent Python oracle that never reads Lean output; do NOT build GWKernelData.
Two sibling agents work in parallel on other BRIDGE-* branches: keep docs/BRIDGE.md
edits to ONE new final section plus at most new table rows, so merges are textual.
Push to your own branch authorized; no merge, no PR. Never bare `git stash`, never
`pkill -f`. Targets may not be weakened; unreachable means BLOCKED with the exact
obstruction. Handoff in `.agent/handoffs/<TASK>.md`. Never self-accept.
