# BRIDGE-Q0 — the q → 0 screening derived and bounded, then STOP

Base `bridge/theory-to-bgw` 848a277, branch `bridge-q0/work`. Written by the supervisor.

## Why

BRIDGE-EPS derived eps for q ≠ 0; the q = 0 block's eps⁻¹ is an INPUT (`E0`). The
q = 0 treatment is where GW codes disagree (Rangel 2020: Coulomb divergence), and the
certificate shows O1 depends on the q0 direction by ~1 meV (cert_o1.json
O1_per_q0_op: 14.34 / 14.90 / 15.41 meV). Epsilon computes at a finite q0 = (0,0,0.001);
Sigma then applies the wing rule (zero wings except head at q = 0, head/wings scaled by
`oneoverq` mini-BZ averages; see SigmaSpec `epsS`, BRIDGE rows on wings).

## Targets

**Q1 (Lean).** The theory at q = 0 is the q → 0 limit: for the finite-k-grid RPA of
BRIDGE-EPS, prove the structure of χ0(q) as q → 0 (head ~ q², wings ~ q, body O(1),
with the k·p/commutator form of the coefficients stated as hypotheses if their
derivation needs the plane-wave momentum matrix element), hence eps⁻¹(q) → limits:
body → body of the inverse of the "head-projected" matrix, head/wings as the
direction-dependent limits. Prove what EpsSpec at finite q0 equals relative to that limit
(error O(|q0|) with an explicit constant from computable data if possible).
**Q2 (Lean).** Prove what SigmaSpec's q = 0 wing rule computes in terms of Q1's limit:
the head term × `oneoverq`-type mini-BZ average is the theory's mini-BZ integral of the
singular part; the zeroed wings are the angular average of odd-in-q wings (zero by
inversion symmetry of the average — prove it, stating the symmetry hypothesis); name
every remaining approximation (direction of q0 used for the body/head, isotropy
assumption for cubic Si).
**Q3 (numbers).** Rigorous where cheap: explain the 14.34 / 14.90 / 15.41 meV spread
(which symmetry ops give which, and why a cubic crystal gives a direction dependence at
all — finite q0, wings, or anisotropic head at finite k-grid), and give the theory's
O1 for the correct angular average, or an enclosure of it. Add departure rows.
Replace the `E0` input by the derived q = 0 block in a composed theorem if Q1–Q2
allow it (`sigA_eps_eq_theory` extended to q = 0), else state exactly what blocks it.

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
