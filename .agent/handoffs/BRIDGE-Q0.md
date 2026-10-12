# BRIDGE-Q0 handoff: the q → 0 screening derived and bounded

> **Correction (R28-R3, 2026-10-05).** "spread 4e-11" below is inward; the measured
> `eps_M_spread` is ≤ 5e-11. The `q0_error` bound is now evaluated with directed rounding
> (≤ 0.1812), and it is relative to the computed `Ẽ0`, which is the `q → 0` limit under
> `KPRay.OK`. The current values are in `docs/BRIDGE.md`.

Worker: Claude (implementer). Branch `bridge-q0/work`, worktree `.claude/worktrees/bridge-q0`.

Status: **CHECKPOINT_READY**, meaning ready for review. It is NOT accepted; Codex owns
acceptance. Q1, Q2 and Q3 are all delivered. The composed theorem without `E0` exists.
It is stated with the finite-`q0` block, not the limit block; see "Limits".

## Files

New:
* `GW/Bridge/EpsQ0.lean` (Q1, 26 theorems)
* `GW/Bridge/EpsQ0Sigma.lean` (Q2 plus the composition, 19 theorems)
* `bgw/bridge_q0/q0.py` and `bgw/bridge_q0/data/q0.json` (Q3)
* `tests/test_bridge_q0.py` (16 tests: toy oracle, committed data, fresh run)
* this handoff

Edited:
* `GW.lean`: 2 imports plus a docstring entry.
* `GW/Audit.lean`: 45 `#print axioms`, i.e. every theorem of both files.
* `scripts/gates.py`: `tests.test_bridge_q0` added to SCIENTIFIC.
* `bgw/weighted_audit/PROVENANCE-R6.txt`: GW.lean, Audit.lean and gates.py re-signed with
  `make_manifest.py`.
* `docs/BRIDGE.md`: table rows Q-1 to Q-7 after E-14, and one new final section.

No existing theorem statement and no existing `cert.py`/`iv.py`/`spec.py` was changed.

## Key theorems

* Q1:
  * `KPRay.head_tendsto`, `wing_tendsto`, `wing'_tendsto`, `body_tendsto`,
    `head_coef_nonpos`
  * `eps_conj`, `inv_scaled`
  * `q0_limit`, `chiSc_tendsto`
  * `schur_body`, `schur_head`
  * `chi0s_neg`, `parity_inv`
  * `inv_perturb`, `q0_error`
* Q2:
  * `thK_odd`
  * `sum_odd_zero`, `integral_odd_zero`, `wing_avg_zero`, `wing_sum_zero`
  * `head_avg`, `head_avg_spec`
  * `omT_wing`, `specMode_zeroI`
  * **`sigA_eq_theory_q0`**: no `q = 0` `WingFree`
  * **`sigA_eps_eq_theory_q0`**: EpsSpec on every block, no `E0`
  * `epsSpec_q0_scaled`, `vT_head`

## Explanation of the q0-direction spread

The 48 ops map `q0 ∥ b3` onto the 8 `<111>` directions, and O1 depends only on the axis:

* `±b3` (12 ops): 14.3435 meV
* `±b2` (12 ops, production op 48 = index 47 among them): 15.4058 meV
* `±b1` and `±(b1+b2+b3)` (24 ops): 14.9048 meV

The dominant cause is not q → 0 physics. RHO (EPM, from WFN_co) is
`2 Σ_{IBZ} w_k Σ_v |ψ|²` over Γ, L = b3/2 and X = (b2+b3)/2 without star averaging. It is
reproduced to 3.6e-15, and a fresh run confirms it. It enters Sigma through HL `Ω²`.
Its residual symmetry gives exactly the class pattern `{b3}`, `{b2}`, `{b1, s}`.

With the star-symmetrized RHO:
* X is op-independent.
* L has 2 classes: q̂ ∥ L gives 15.6498, the oblique axes give 15.7813.

That remaining 0.131 meV is genuine physics. It comes from the O(1) direction
dependence of the body limit of `eps⁻¹` (head-projected term; max 0.012). The head is
isotropic (ε_M = 15.3811 for every u, spread 4e-11), and the finite `q0` is negligible
(the exact k·p limit block changes O1 by ≤ 0.8 µeV).

The theory's angular average of the q = 0 cell (Wigner-Seitz `r³` weights, 400
directions, stable to 0.6 µeV against 200) is:

| RHO | angular average | spec B |
| --- | --- | --- |
| production | 14.8730 meV | 14.8897 |
| symmetrized | 15.7480 meV | 15.7484 |

This is a quadrature estimate, not an enclosure.

## Discrepancies and findings

1. **The RHO input is not cubic.** This is new and large: with the symmetrized RHO, the
   production O1 moves from 15.406 to 15.781 meV. It is a mean-field input defect, not a
   SigmaSpec formula departure (row Q-6). Either epm2bgw lacks star symmetrization or the
   test-suite input relies on it; this was not checked in the Fortran.
2. BRIDGE's `WingFree` at `q = 0` is false for the raw `eps0mat` (row wing 29). It turns
   out to be unnecessary, because the theory `SigT` never sees the q = 0 wings.
3. The `q0_error` bound is loose: 0.18, against an actual ≤ 5.4e-4.

## Commands and results

```
source scripts/env.sh
python3 bgw/endpoint/run_production.py $S/run --blas-threads 2          # 10 s
lake env lean GW/Bridge/EpsQ0.lean; lake env lean GW/Bridge/EpsQ0Sigma.lean   # exit 0, no warnings
lake build GW                                                            # Build completed successfully
lake env lean GW/Audit.lean                                              # rc 0, 4 min; all 45 new entries
                                                                         #   = [propext, Classical.choice, Quot.sound]
OMP_NUM_THREADS=1 python3 bgw/bridge_q0/q0.py $S/run --ndir 400 --workers 4   # 328 s -> data/q0.json
OMP_NUM_THREADS=1 python3 -m unittest tests.test_bridge_q0              # 16 OK (incl. fresh run)
python3 -m unittest tests.test_bridge tests.test_bridge_eps              # 26 OK
python3 scripts/make_manifest.py bgw/weighted_audit/PROVENANCE-R6.txt   # 3 refreshed
python3 -m unittest tests.test_provenance_committed tests.test_gate_partition tests.test_packet_references  # OK
grep sorry/admit/native_decide/implemented_by/ofReduceBool/axiom in EpsQ0*.lean  # nothing
```

NOT run:
* `scripts/verify.sh` and `CheckAxioms.lean`, because they build or import GWKernelData.
* `tests.test_bridge_measure`: unaffected, and slow.

## Failed attempts

* The first geometric explanation was wrong. It assumed the dependence comes only from
  the direction relative to the X/L little groups, which predicts 1 class at X and 2 at L.
  The data show 3 classes at both points. Testing covariance showed that the eps0
  block is covariant under the q0 little group while the Sigma side is not, and that led
  to RHO.
* Lean fixes:
  * `field_simp` needed a trailing `ring`.
  * `congr 1` on `diagonal` went too deep; `congrArg diagonal` was used instead.
  * The `if True` residue from `simp [scv]` was handled with explicit `hz`/`ho` lemmas.
* A slope check on individual squared matrix elements was noisy (0.8% on tiny values).
  It was replaced by aggregate `χ(q0)/t0²` against the limit coefficients.

## Limits

* The composed theorem uses the theory eps at the finite `q0`. The step to the limit
  block is proved entrywise only; the limit-block `SigT` is not related in Lean.
* No a priori `K` for the k·p remainder: `δ` is measured.
* Isotropy is measured, not proved.
* The next-order even wing terms are not bounded.
* The angular average is a quadrature estimate.

## Next action (Codex)

1. Review `KPRay.OK` (orthogonality and slope as hypotheses) and the `Wing`/`ZeroAt`
   statement of `sigA_eq_theory_q0`.
2. Decide whether the RHO symmetrization finding should become a separate input-correction
   task. It moves O1 by 0.38 meV, which is more than the q0 spread.
3. Merge note: `docs/BRIDGE.md` has new rows after E-14 plus a final section; siblings
   append too, so conflicts will be textual.
