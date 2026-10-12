# BRIDGE-COR handoff: a proved enclosure replacing the empirical ½ of COR

Worker: Claude (implementer). Branch `bridge-cor/work`, worktree
`.claude/worktrees/bridge-cor`, base `7ed810f` (task brief on `848a277`).

Status: **CHECKPOINT_READY**, meaning ready for review. It is NOT accepted; Codex owns
acceptance. All three targets are delivered, and the C3 enclosure is **uselessly wide**,
reported below.

## Files

New:
* `GW/Bridge/Cor.lean`: 59 theorems
* `bgw/bridge_cor/cor.py`
* `bgw/bridge_cor/data/cor.json`
* `tests/test_bridge_cor.py`: 13 tests, numpy oracle
* this handoff

Edited:
* `GW.lean`: import and docstring.
* `GW/Audit.lean`: 59 `#print axioms`.
* `scripts/gates.py`: `tests.test_bridge_cor` added to SCIENTIFIC.
* `bgw/weighted_audit/PROVENANCE-R6.txt`: re-signed GW.lean, GW/Audit.lean,
  scripts/gates.py.
* `docs/BRIDGE.md`: one new final section plus one table row, C-1, appended after E-14.

No existing theorem or file outside this scope was changed.

## Key theorems (GW/Bridge/Cor.lean)

* C1:
  * `thK_empty_ratio`: `thK = θ·(-I/2)`, `θ = w̃/(w̃ - x)`.
  * `thK_empty_enclosure`: `0 < θ ≤ w̃/(w̃ + D)` for `x ≤ -D`.
  * `theta_lower`: needs an upper bound `Y`; none is assumed.
  * `thK_empty_invalid`: `0`.
  * `thK_empty_abs`: `|thK| ≤ |I|/2`.
  * `thK_tail_mode`: centre/radius form.
  * `schM_tail_ratio`, `specK_tail_mode`: BerkeleyGW's rule on an omitted band, `D > ½`.
  * `psi_*`, `thK_diff_mode`, `specK_diff_mode`: the energy step.
* C2:
  * `pd_closure_amp`: `Σ_n M_n M_n' = Σ_v A_v A_v'` from completeness alone; no
    shift-closure needed.
  * `cloP_eq_rho`: with shift-closure this is BerkeleyGW's `ρ_aa`.
  * `tail_core`: Cauchy-Schwarz majorant.
  * `tailK_eq`: the omitted pair sums are computable.
  * **`sigT_all_bands`**, **`sigT_diff_all_bands`**, `sigT_tail_enclose` (generic).
  * **`sigA_all_bands`**, **`sigA_diff_all_bands`**.
  * Consistency with dyadic larger states: `sigTall_of_state`, `sigAall_of_state`,
    `completeK_of_complete`, `sigT_split`, `sigA_split`.

Hypotheses of the main statements:
* `CompleteK κ` at every q.
* `D_t` with `x ≤ -D_t` on every omitted band (`0 < D`, `½ < D` for the spec, `3/2 < D` for
  the spec's step).

## Finding: completeness as stated in BRIDGE is unsatisfiable on the data

`Bloch.Complete` is the hypothesis of `chpart_sum_eq_exact` and
`sigA_eq_theory_complete`. It asks the dyadic band rows to be exactly complete. It cannot
hold for the stored rows, for two reasons:

* For all 16 O1-scope `k - q` points, `I - R Rᵀ` has a negative pivot. `R` is the stored
  18 rows, and the check is an exact rational LDLᵀ in `cor.json` `completeness_check`.
  Binary64 eigenvector rows have `‖R‖₂² - 1 ≈ +2e-15`.
* Dyadic orthonormal completions do not exist in general.

Cor.lean therefore models the omitted bands as a REAL completion (`Compl`) with
`CompleteK κ`, and the scripts use a rigorous Gershgorin bound `κ ≥ ‖R‖₂²`
(`κ - 1 ≤ 3.3e-14`). The step "a real completion exists iff `κI - RᵀR ⪰ 0`" is standard
linear algebra and is NOT formalised. `sigA_eq_theory_complete`'s `hc` has the same issue.
It is not repaired here, because it is outside this task's scope.

## C3 numbers (Si-EPM, `cor.json`)

**Source of `D`.** `D_t = RYD·e_18(k - q_t) - E`. Band 18 is the highest computed band
(`number_bands 18`) at each `k - q` of WFN_inner, and sorted EPM eigenvalues put every
omitted band above it. The range is 19.8 to 26.7 eV (X) and 19.2 to 26.0 eV (L).

| | ½ heuristic (run) | rigorous, `D` only (`sigA_*_all_bands`) |
| --- | --- | --- |
| Σ(X), Σ(L) at Eo | -8.5247, -9.3498 eV | [-9.844, -6.754], [-10.672, -7.478] eV |
| Eqp1 X, L | 4.5315, 4.5161 eV | [3.35, 6.09], [3.33, 6.18] eV |
| **O1** | **15.41 meV** | **[-2814, +2747] meV**, width 5.6 eV |

* The ½ lies inside. Nothing narrower is implied: the oracle test
  `test_half_is_not_implied` builds a case where the ½ lies outside the enclosure.
* The uniform-θ family gives O1 = -101.3, -42.9, 15.4, 73.7, 132.1 meV at θ = 0, ¼, ½, ¾,
  1.
* Reading the Σ enclosures as a uniform θ gives [-0.99, 1.61] (X) and [-0.76, 1.39] (L)
  (float diagnostic, rounded outward).
* With the theory kernel on the omitted bands O1 ∈ [-2490, +2417] meV.

**What shrinks it** (diagnostic; it uses the omitted energies, so it is not part of the
bound). A second EPM run with `WFN_co.in:NumberOfBands=168` gives the enclosure with
`N_b` computed bands:

| `N_b` | 18 | 30 | 60 | 100 | 168 |
| --- | --- | --- | --- | --- | --- |
| O1 enclosure, meV | [-2814, 2747] | [-1327, 1287] | [-322, 301] | [-58.7, 48.5] | [-4.05, -3.51] |

> **R28 correction (2026-10-02):** this value is the spec's `SigAall`, which still contains the static residual `CORall` (+1.21 meV on O1; without it O1 ∈ [-5.25, -4.72] meV), and the enclosure is for an abstract `CompleteK` completion, not the physical omitted bands (R28-F3/F4, `docs/reviews/`).

At `N_b = 168` the value is the exact finite-basis all-band O1 (only ≤ 6 top basis bands
are still enclosed): **-3.8 ± 0.3 meV, not 15.4**. Σ(Eo) itself is close to the ½:
effective θ = 0.493 (X) and 0.491 (L). The static ½ misses the tail's energy dependence
(dΣ/dE changes by -8.6 and -10.4 meV/eV), and through the linearised Eqp1 that moves O1 by
-19 meV.

Validation of the added bands: a pinned BerkeleyGW Sigma run with `number_bands 164`
gives O1 = -3.76085 meV; the same Σ computed here gives -3.75499 meV. The difference is
5.9 µeV, the E1 level.

The Cauchy-Schwarz majorant is not the main limit. A float prototype (scratch, not
committed, not rigorous) with `w̃`-bins and a spectral split halves the Σ width at best,
3.1 → 1.7 eV. The floor is `θ ∈ (0, w̃/(w̃+D)]`, which comes from `D` alone. Levers that
would help: more bands; an upper bound on the omitted energies; energy moments
`Σ|M_n|²ε_n` from the Hamiltonian (Jensen-type bounds, since θ is convex in ε).

## Commands

```
S=<scratchpad>/cor
python3 bgw/endpoint/run_production.py $S/run --blas-threads 2
python3 bgw/endpoint/run_production.py $S/runall --blas-threads 2 --set WFN_co.in:NumberOfBands=168
python3 bgw/endpoint/run_production.py $S/run164 --blas-threads 2 \
    --set WFN_co.in:NumberOfBands=168 --set sig_GPP.inp:number_bands=164
OMP_NUM_THREADS=1 python3 bgw/bridge_cor/cor.py $S/run --all-bands $S/runall --bgw-run $S/run164
    # 105 s, writes bgw/bridge_cor/data/cor.json
lake env lean GW/Bridge/Cor.lean; lake build GW                # OK
lake env lean GW/Audit.lean                                    # rc 0; 159 GW.Bridge entries; all Cor
    # entries within [propext, Classical.choice, Quot.sound] (3 use a subset)
python3 scripts/make_manifest.py bgw/weighted_audit/PROVENANCE-R6.txt
python3 -m unittest tests.test_bridge_cor tests.test_bridge tests.test_bridge_eps \
    tests.test_bridge_measure tests.test_gate_partition tests.test_provenance_committed \
    tests.test_packet_references                               # 67 OK
```

The following were not run:
* `bash scripts/verify.sh`. It builds `GWKernelData` (verify.py line 84), which the brief
  forbids. I stopped it at its first step (`lake build` of the default targets) and ran
  the relevant pieces above instead.
* The full Python suite beyond those modules.

## Failed attempts and fixes

1. The first C2 used dyadic `Complete` on a larger `St`. It compiled, but the exact
   rational check showed it is vacuous on the data. It was replaced by `Compl` and
   `CompleteK κ`, and the dyadic version was kept only as the consistency lemmas.
2. The first `tail_core` was stated against `st`'s `xS`. It was replaced by an abstract
   version over real vectors.
3. `sigT_diff` via `Eq.trans_le (by rfl)` hit a heartbeat timeout. It was restructured
   with an explicit rewrite `hq`.
4. `n = 167` and `168` for the BerkeleyGW cross-check were rejected by Sigma. 168 fails
   because it needs one more band in WFN_inner; 167 fails because it splits a degenerate
   subspace. 164 is used.
5. The Eqp1 interval in the form `s0 + d/(1-d)·s0` over-widened by dependency
   (O1 [-4248, 4167]). The single-occurrence form `s0/(1-d)` (`eqp1_linear`) gives the
   numbers above.

## Next action (Codex)

1. Review the finding that `Complete` is unsatisfiable on dyadic data, and decide whether
   `sigA_eq_theory_complete` / `chpart_sum_eq_exact` should move to `CompleteK`.
2. Decide whether the finite-basis all-band O1 (-3.8 meV, a diagnostic that uses band
   energies) should be the reference for O1, instead of 15.4 meV.
3. Run `verify.sh` when building GWKernelData is acceptable.
