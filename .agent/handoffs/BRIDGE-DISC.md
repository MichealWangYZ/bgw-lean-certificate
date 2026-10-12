# BRIDGE-DISC handoff: the GPP kernel at (x, Ω²) = (0, 0), then STOP

Worker: Claude (implementer). Branch `bridge-disc/work`, worktree
`.claude/worktrees/bridge-disc`, base `7ea7dca` (task brief on `848a277`).

Status: **CHECKPOINT_READY** (D1, D2, D3 delivered), meaning ready for review. It is NOT
accepted; Codex owns acceptance.

## Result in one paragraph

The discontinuity is real, and it belongs to the theory kernel. At `x = 0` the HL term is
`∓I/2` for every valid `Ω²`, and at `Ω² = 0` it is `0`. It is not continuous at `(0, 0)`,
and near that point it takes every real value. Physically this is a zero-strength pole
merging with zero energy: the residue `R = I w̃/2` and the pole `w̃` both go to 0, and
`R/(0 - w̃) = -I/2`.

It does NOT reach O1. The task's hypothesis is confirmed: the structural reason is
**Cartesian orthogonality `q+G ⊥ q+G'`**, not `ρ(G-G') = 0`, since `ρ` is nonzero on every
such pair. In the ideal fcc metric the `Ω²` of those modes is exactly 0. The exported
`bdot` is that metric plus one ulp (`2⁻⁵⁴`) on each off-diagonal entry, so the spec's
`Ω²` on them is pure rounding, at most `2.1e-8 TOL_Small`. BerkeleyGW's drop rule then
gives exactly the ideal-metric theory value, `0`.

Rigorously, with the ideal metric everywhere, O1 ∈ [15.4057524, 15.4057536] meV. This
overlaps spec A's [15.4057524, 15.4057537], with a maximum difference of 1.29e-6 meV,
within the widths. The +28.37 meV switch class is empty, so the switch is 0. The +28 meV
was an artefact of evaluating the theory, not the spec, at a sub-ulp `Ω²`.

## Files

New:
* `GW/Bridge/Disc.lean` (44 theorems)
* `bgw/bridge_disc/disc.py`
* `bgw/bridge_disc/data/disc.json`
* `bgw/bridge_disc/data/coulomb_ideal.json`
* `tests/test_bridge_disc.py`
* this handoff

Edited:
* `GW.lean`: import and docstring entry.
* `GW/Audit.lean`: one new section with all 44 `#print axioms`.
* `scripts/gates.py`: `tests.test_bridge_disc` added to SCIENTIFIC.
* `bgw/weighted_audit/PROVENANCE-R6.txt`: digests of GW.lean, GW/Audit.lean and gates.py
  re-signed with `make_manifest.py`.
* `docs/BRIDGE.md`: departure-table rows 8a and 8b, plus ONE new final section.

`measure.py`, `cert.py`, `iv.py` and `certcoulomb.py` are imported and were not modified.
No existing theorem statement was changed.

## Key theorems (GW/Bridge/Disc.lean)

D1:
* `thK_emp_x0` / `thK_occ_x0`: `-I/2` and `I/2` at `x = 0`.
* `thK_zero_strength`: `thK occ I 0 x = 0`.
* `thK_x0_tendsto`: the limits along `Ω² → 0` on the valid side at `x = 0`.
* `thK_O0_tendsto`.
* `thK_tendsto_zero_of_ne`: for `x ≠ 0` the kernel does vanish, so the source comment is
  right only there.
* `thK_not_continuousAt` and `_occ`.
* `thK_cluster`: every `c ≠ 0` is taken arbitrarily near `(0,0)`, off the pole.
* Physics: `residue_eq`, `emp_as_pole`/`occ_as_pole`, `residue_tendsto_zero`,
  `wTilde_tendsto_zero`, `gppC_zero_strength`, `gppC_limit_off0`,
  `singlePole_zero_strength`, `blochSys_R_zero`.

D2:
* `dotM_ideal`: the ideal metric is `c` times the Cartesian dot.
* `omB_ideal_eq_zero_iff`: **the structural reason**. With `ρ, v ≠ 0`, off the head row,
  ideal `Ω² = 0` iff `Orth`.
* `dotM_ideal_int`, `ideal_gap`, `ideal_gap_vec`: the dot is 0 or at least `c/4`.
* `bExp_sub_ideal`, `bExp_close`: the exported `bdot` is the ideal metric plus one ulp off
  the diagonal; `cExp` is dyadic.
* `dotM_perturb`, `om2S_orth_bound`: the rounding bound.
* `drop_eq_ideal`, `disc_mode`: the drop rule gives the ideal-metric value, 0.
* `sigA_eq_theory_disc`: the Σ-level form. `SigA = SigTD + COR`, where the orthogonal pairs
  need only `abs(Ω²) < TS` instead of `ModeOK`.

## Commands and results

```
source scripts/env.sh
lake env lean GW/Bridge/Disc.lean                       # clean, no warnings
lake build GW.Bridge.Disc && lake build GW              # OK (GWKernelData NOT built)
lake env lean $S/Ax.lean                                # 44/44 [propext, Classical.choice, Quot.sound]
lake env lean GW/Audit.lean                             # 1207 entries, all within the allowlist, 3m50s
python3 bgw/endpoint/run_production.py $S/run --blas-threads 2          # fresh pinned run, 10 s
~/bgw-src/pyenv-e1/bin/python bgw/bridge_disc/disc.py $S/run --make-coulomb $S/coulomb_ideal.json --procs 6   # 37 s
OMP_NUM_THREADS=1 python3 bgw/bridge_disc/disc.py $S/run                 # census + D3, 35 s
python3 scripts/make_manifest.py bgw/weighted_audit/PROVENANCE-R6.txt    # 3 refreshed
python3 -m unittest tests.test_bridge_disc tests.test_bridge tests.test_bridge_measure \
    tests.test_gate_partition tests.test_provenance_committed tests.test_packet_references   # OK
```

`$S` is the session scratchpad subdirectory `disc/`. NOT run: `bash scripts/verify.sh`,
because it builds GWKernelData, which the task forbids.

Full Python gate (`python3 -m unittest <gates.modules('all')>`, 606 tests, 7.5 min): 1 failure
and 47 errors, none of them caused by this task.

* The 47 errors are `tests.test_ll_c2a/c2b/c3/c4`, which need `artifacts/ll-c*/..._values.json`.
  Those files are generated by the Lean executables in `verify.py` and were not built here.
* The 1 failure is `test_endpoint_e1.E14Certified.test_o1_enclosure_and_layer1_bound`. In the
  full run, `cert.main` reports undecided branches. It is pre-existing and depends on test
  order:
  * it passes alone, with the whole `test_endpoint_e1` module, and with every module that
    precedes it in the gate, with or without `test_bridge_disc`;
  * it fails identically in the full list WITHOUT `test_bridge_disc` (481 tests, the same single
    failure).

  So some module-level state in the full list leaks into `cert`. This was not investigated
  further, because it is out of scope.

Census (exact rationals, `disc.json` `census`):
* 52656 sphere pairs.
* 3112 Cartesian-orthogonal pairs off the head row: 568 at q = 0, 848 at each X-type q,
  0 at L-type q. `ρ ≠ 0` on all of them.
* The minimum nonzero `abs(ideal dot)/c` is exactly 1/4.
* `max om2S_orth_bound / TS` = 2.06e-8.
* The 20 spheres are identical under the ideal metric; the minimum margin is 0.030 Ry.

D3 tallies with the ideal metric:
* `drop_O` 0 / 0, down from 136512 / 68256.
* `drop_O_O0` 207360 / 103680, which is 70848 + 136512 and 35424 + 68256.
* `drop_I` loses its 5184 / 2592 rounding-zero modes to `drop_I_O0`.
* generic, near-pole, invalid, empty near-pole and zero-mode counts are identical.

## Failed attempts and fixes

* The first `--make-coulomb` wrapper replaced `multiprocessing.Pool` globally, and its own
  constructor then called the patched Pool, recursing. The fix keeps the original Pool and
  restores it afterwards.
* Test assertions were fixed three times:
  * the one-ulp direction: the ideal off-diagonal is one ulp *further* from 0;
  * the switch-row enclosure width is `[o1] - [o1]`, which is twice the width;
  * a too-tight vanishing rate for `x ≠ 0`: the value is O(√Ω²), not O(Ω²).
* Lean first pass:
  * `bd gl` is `ℕ → ℕ → ℝ`, so I added `bdF`;
  * `Orth` needed classical decidability for `OmD`;
  * I fixed the argument order of `PTD`/`SigTD`;
  * a `conv` rewrite of `O` also hit the `O` inside `wTilde`;
  * `thK_cluster` did not need `c ≠ 0` for its value claim, because totalization gives
    `c = 0` at `x = w̃`. The statement now also asserts `x ≠ w̃`, so it is about genuine
    values.

## Is O1 unaffected?

Yes, within the certified enclosure widths, about 1.3e-6 meV. Two caveats:
* The wavefunctions, energies and RHO are held fixed as spec A's inputs. The EPM step is
  upstream.
* The ideal scale `c = bdot₁₁/3` is a convention, not a derived result. Another `c` would
  only rescale the metric by O(1e-16).

## Side observation (not a target)

On the rounded metric, certcoulomb needed 26 flat-cone bounds; on the ideal metric it
needed 0. With the ideal metric, the `oneoverq` averages of symmetry-equivalent q become
identical. That is harmless, but it is another visible rounding effect.

## Next action (for Codex)

1. Review `Disc.lean`, especially `omB_ideal_eq_zero_iff`, `disc_mode` and
   `sigA_eq_theory_disc`. Also decide whether rows 8a and 8b replace BRIDGE-MEASURE note b's
   "ill-posed" wording.
2. Optionally discharge `hsmall` of `disc_mode` in Lean for the concrete run. That needs
   the GWKernelData sphere and RHO data, which this task could not build.
3. Run the full `bash scripts/verify.sh` when GWKernelData may be built.
