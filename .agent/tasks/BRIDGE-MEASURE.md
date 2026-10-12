# BRIDGE-MEASURE — how large are BRIDGE's named departures on Si-EPM, then STOP

Base: `bridge/theory-to-bgw` at `d9be4dd`. Branch `bridge-measure/work`, worktree
`.claude/worktrees/bridge-measure`. Written by the supervising session. Never self-accept.

## Question

`GW.Bridge.sigA_eq_theory` (GW/Bridge/Compare.lean) says SigmaSpec = theory Σ + COR
under hypotheses hC (Coulomb averages = bare v), hW (WingFree), hX (no TOL_Zero
replacement), hM (every mode ModeOK). On the actual Si-EPM O1 run, how much does
each violated hypothesis contribute to Σ(X), Σ(L), Eqp1 and O1?

## Targets (Python, rigorous where cheap, float with stated error otherwise)

1. Using the spec-A inputs `bgw/endpoint/cert.py` already loads (reuse its loaders
   and `iv.py`; do not modify them), count modes and total |weight| per class:
   kept-valid-generic, occupied near-pole, dropped (each threshold), invalid
   (wt2 < 0; and I = 0 cases), sexcut-clamped, empty near-pole zeroed,
   TOL_Zero-replaced wx, wing-affected entries.
2. For each class, the contribution to Σ(E) at the O1 states (X bands 5–6 avg,
   L band 5) and to Eqp1 and O1 when that class is switched from the BGW rule to
   the theory value (e.g. invalid modes: static-COHSEX limit vs what the theory
   GPP would need; Coulomb average vb vs bare v at the same q+G where finite;
   wing rule on/off; COR on/off, and COR's ½ vs 1 and 0). Use interval arithmetic
   (iv.py) where the class value is finite and cheap; label any float-only number.
3. A table in `docs/BRIDGE.md` ("Measured size of departures on Si-EPM"):
   class, count, Δ Σ(X), Δ Σ(L), Δ O1 (meV), method (rigorous / float).
   State clearly which departures are ill-defined to "switch off" (e.g. bare v at
   q+G = 0 diverges) and what comparison you made instead.

## Rules

Python + docs only; no Lean edits. Independent where it matters: do not trust
cert.py's branch labels blindly — recompute classes from the formulas in
`GW/Bridge/Compare.lean` definitions (ModeOK etc.) and cross-check the counts
against `bgw/endpoint/data/cert_o1.json` branch_stats. Write scope:
`bgw/bridge_measure/` (scripts, data json), `tests/test_bridge_measure.py`,
`scripts/gates.py` (register the test; re-sign PROVENANCE-R6 digest if it
changes), the docs section, `.agent/handoffs/BRIDGE-MEASURE.md`.
Do not append to docs/BRIDGE.md's existing departure table (another agent edits
it); add a separate section at the end. Push to `origin bridge-measure/work`
authorized; no merge. Long runs: keep under ~2 CPU-hours total.
