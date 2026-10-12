# BRIDGE-EPS — the static RPA dielectric matrix derived from many-body theory, then STOP

Base: `bridge/theory-to-bgw` at `d9be4dd`. Branch `bridge-eps/work`, worktree
`.claude/worktrees/bridge-eps`. Written by the supervising session on the owner's
request. Targets may not be weakened; unreachable means `BLOCKED`. Never self-accept.

## Question

BRIDGE proved SigmaSpec = theory Σ with `eps^{-1}` as an INPUT. `Kernel/EpsSpec.lean`
(chi, v, eps) is still transcribed from the code. Is it what RPA theory says?

## Targets

**E1. chi0 from G0.** For a general finite fermion system (reuse
`GW/Endpoint/ManyBody/`, esp. `GWSecond.lean`'s `chi0t` and `ftDamped`), prove the
static (`omega = 0`, `eta -> 0+`) independent-particle polarisability is the
closed form `chi0_{(pair)} = sum over occupied v, empty c of 2-term
f/(e_v - e_c)` with the signs and factor derived (spin factor explicit).

**E2. Bloch specialisation.** With plane-wave orbitals on a finite k-grid, pair
densities `M_vc(k, G)`, show E1 gives EpsSpec's
`chi(G,G') = 4/(N_k Ω) Σ_k Σ_v Σ_c M M /(E_v(k+q) - E_c(k))`: derive the 4 (spin 2 ×
time-reversal/real-flavour 2, or whatever it truly is — if the derivation gives a
different factor that is a DISCREPANCY), the `1/(N_k Ω)` normalisation, and the
`k+q` vs `k` convention.

**E3. RPA dielectric matrix.** `eps = δ - v chi0` with `v(q+G) = 8π/|q+G|²` (Ry) is
the static limit of the RPA `W = (1 - v chi0)^{-1} v` (reuse `GW/LL/Electronic.lean`
`geoW`/`electronicW`), so `eps^{-1} v = W` exactly when `eps` is invertible (no
formal-series convergence claim needed). Prove the symmetrised vs unsymmetrised
form that EpsSpec/SigmaSpec use is consistent with BRIDGE's `W = eps^{-1} diag(v)`.

**E4. Comparison theorem** `epsSpec_eq_theory`: EpsSpec's eps equals the E2/E3
theory eps, every departure a named hypothesis (q = 0 head/wings treatment,
finite band sum, G-sphere, symmetry unfolding trust). Then compose with
`GW.Bridge.sigA_eq_theory` into one statement: SigA with eps^{-1} := inverse of
EpsSpec's eps equals the theory Σ built from theory chi0, plus COR, under the
union of named hypotheses. Add rows to `docs/BRIDGE.md`'s departure table.

## Rules

Same as `.agent/tasks/BRIDGE.md` section 3 (no sorry/axioms/native_decide/...;
axiom allowlist propext, Classical.choice, Quot.sound; register in GW.lean and
GW/Audit.lean; re-sign PROVENANCE-R6 digests; independent Python oracle;
do NOT build GWKernelData). Write scope: new files `GW/Bridge/Eps*.lean`,
`docs/BRIDGE.md` (append rows/section), `tests/test_bridge_eps.py`,
registration files, `.agent/handoffs/BRIDGE-EPS.md`. Push to
`origin bridge-eps/work` authorized; no merge. Exit CHECKPOINT_READY / PARTIAL / BLOCKED.
