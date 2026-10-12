# BRIDGE-DISC — the GPP kernel discontinuity at (x, Ω²) = (0, 0), then STOP

Base `bridge/theory-to-bgw` 848a277, branch `bridge-disc/work`. Written by the supervisor.

## Why

BRIDGE-MEASURE finding 2: the theory empty-band GPP kernel at x = 0 is −I/2 for every
Ω² > 0 but 0 at Ω² = 0. On spec-A inputs ~5408 (X) / 1896 (L) modes at x ≈ 0 have
Ω² ~ 1e-15 only because binary64 `bdot` rounds the ideal fcc metric; with the exact
metric those Ω² are exactly 0. Switching them moves O1 by +28 meV. The answer then
depends on metric rounding — not credible unless settled.

## Targets

**D1 (Lean).** Prove the discontinuity precisely (limits along Ω² → 0⁺ at x = 0 and
x → 0 at Ω² = 0 differ; the value set of the kernel near (0,0)), and characterise it as
the physics of a zero-strength pole at zero energy (w̃ = √(Ω²/I) → 0 merges with the
pole at x = 0). State what the theory Σ is when a mode's pole strength vanishes
identically (the mode contributes nothing: W_c entry is 0 — prove from B2 `gppC`).
**D2 (Lean + exact).** Prove the Ω² of those modes is EXACTLY 0 for the ideal fcc metric:
identify the structural reason (e.g. (q+G)·B·(q+G') = 0 by symmetry/orthogonality, or
ρ(G−G') = 0) as a theorem over the exact metric, and show the exported `bdot` differs
from the ideal one only by rounding (bound). Then prove BerkeleyGW's drop rule
(|Ω²| < TOL_Small → skip) gives the exact-metric value, so O1 is unaffected: i.e.
SigmaSpec with rounded bdot = theory with ideal metric on these modes.
**D3.** Rigorous (iv.py) confirmation on Si-EPM: with the ideal metric (exact rational
fcc bdot) the O1 enclosure equals the spec-A one within its width, and the +28 meV
switch is 0. Add a departure-table row for this and the source-comment correction
(Ω² → 0 vanishing only for x ≠ 0).

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
