# BRIDGE-MEASURE handoff: measured size of `sigA_eq_theory`'s departures on Si-EPM

> **Correction (R28-R3, 2026-10-05).** Some "≤ ε" entries in the class table below round
> the measured interval half-widths inward. The outward values are: occupied near-pole
> ≤ 1.4e-6; TOL_Zero row ≤ 4e-8 (ΔΣ X) and ≤ 1.4e-6 (ΔO1); q = 0 wings ≤ 2.3e-6. The row
> "dropped, Ω² = 0 exactly" has no HL pole only when I ≠ 0; when I = 0 the HL pole has
> zero residue (`GPPModel`). The theory value is 0 either way. `measure.mev` is now
> outward (R28-R3), and `measure.json` is regenerated. The current values are in
> `docs/BRIDGE.md`.

Worker: Claude (implementer). Branch `bridge-measure/work`, worktree
`.claude/worktrees/bridge-measure`, base `4c84ed5` (task brief on top of `d9be4dd`).

Status: **CHECKPOINT_READY**, meaning ready for review. It is NOT accepted; Codex owns
acceptance. The work is Python and docs only. No Lean file was touched.

## Files (write scope respected)

New:
* `bgw/bridge_measure/measure.py`
* `bgw/bridge_measure/data/measure.json`
* `tests/test_bridge_measure.py`
* this handoff

Edited:
* `docs/BRIDGE.md`: one new final section, "Measured size of departures on Si-EPM
  (BRIDGE-MEASURE)". The existing departure table was not edited.
* `scripts/gates.py`: `tests.test_bridge_measure` added to SCIENTIFIC.
* `bgw/weighted_audit/PROVENANCE-R6.txt`: the gates.py digest was re-signed with
  `make_manifest.py`.

`bgw/endpoint/cert.py` and `iv.py` are imported and were not modified.

## Commands and results

```
nproc; free -g                                        # 16 cores, 23 GB; everything below runs single-threaded
python3 bgw/endpoint/run_production.py $S/run --blas-threads 2        # fresh pinned run, 10 s
python3 bgw/endpoint/cert.py $S/run --out $S/cert.json                # 56 s; branch_stats and O1 == committed cert_o1.json
OMP_NUM_THREADS=1 python3 bgw/bridge_measure/measure.py $S/run        # 197 s; writes data/measure.json
OMP_NUM_THREADS=1 python3 -m unittest tests.test_bridge_measure tests.test_bridge tests.test_gate_partition   # 33 OK, 28 s (includes a fresh-run test)
python3 scripts/make_manifest.py bgw/weighted_audit/PROVENANCE-R6.txt  # 1 refreshed (scripts/gates.py)
python3 -m unittest tests.test_provenance_committed tests.test_packet_references tests.test_gate_partition   # OK
```

`$S` is the session scratchpad. Total CPU used was about 25 minutes, including the
development runs. That is well under the 2 CPU-hour budget, and every run was
single-threaded.

NOT run: `bash scripts/verify.sh`, which builds Lean. Another agent was building Lean in
parallel, and this task has no Lean change.

## Result

The baseline unswitched pass gives O1 ∈ [15.4057524, 15.4057537] meV, inside
`cert_o1.json`.

**Count cross-check: no mismatch.** The float classifier over cert.py's exact scope gives:

* `invalid_modes` 163152
* `near_pole_modes` 91316
* `sexcut_clamped` 0
* exact `x = w̃`: 0

These equal `cert_o1.json` `branch_stats`. On the O1 scope, the interval and float
classifiers agree (invalid 1191456 / 595728, occupied near-pole 7380 / 4064).

In the table below, "count" is X / L modes over the O1 scope. ΔΣ is the change in the
multiplet-averaged Σ at Eo. ΔO1 goes through the linearised Eqp1. All values are in meV.

| Class | Count X / L | ΔΣ(X) | ΔΣ(L) | ΔO1 | Method |
| --- | --- | --- | --- | --- | --- |
| generic ModeOK | 2274772 / 1136564 | 0 | 0 | 0 (≤1.9e-6) | rigorous |
| occupied near-pole ModeOK | 7380 / 4064 | 0 | 0 | 0 (≤1.3e-6) | rigorous |
| I = Ω² = 0 | 9216 / 4608 | 0 | 0 | 0 | exact |
| dropped, Ω² = 0 exactly (both thresholds) | 77760 / 38880 | 0 | 0 | 0 | exact (Lean thK = 0; HL no pole) |
| dropped \|I\|<TS, x≠0 | 98496 / 49248 (all x) | ≈0 | -4e-7 | +1.1e-5 | rigorous + bound |
| dropped \|Ω²\|<TS, x≠0 | 136512 / 68256 (all x) | -8e-7 | -2e-7 | +1.6e-5 | rigorous |
| dropped \|Ω²\|<TS, x≈0 | 5408 / 1896 | +4.588 | +0.0446 | +28.37 | rigorous but ill-posed (sub-ulp Ω²) |
| invalid → skip (mode 0) | 1191456 / 595728 | -13.83 | +11.93 | -20.62 | rigorous (no theory value) |
| invalid → 2 Ry (mode 2) | same | +1.217 | +8.756 | -5.78 | rigorous |
| empty near-pole → theory | 320 / 608 | 0 | -1.764 | +12.74 | rigorous, ill-conditioned |
| sexcut clamp | 0 / 0 | 0 | 0 | 0 | exact |
| occupied x = w̃ (row 14) | 0 / 0 | 0 | 0 | 0 | rigorous |
| TOL_Zero (hX) | 12 / 4 triples | 0 | 0 | 0 (≤1.3e-6) | rigorous |
| q=0 wings (hW1) | 128 per (n1, band, E) | 0 | 0 | 0 (≤2.2e-6) | rigorous; exactly 0 |
| q≠0 wing factors (hW2) | 91728 / 45864 entries | +2.367 | +1.365 | +0.676 | rigorous |
| Coulomb vb → bare (hC), q+G=0 kept | all | +216.5 | +226.8 | -6.54 | rigorous |
| COR ½ → 0 | - | +596.5 | +743.8 | -116.68 | rigorous |
| COR ½ → 1 | - | -596.5 | -743.8 | +116.68 | rigorous |
| all well-posed switches, COR kept | - | +216.6 | +226.3 | -1.68 (O1 13.73) | rigorous |
| same, COR off | - | +804.7 | +959.1 | -116.9 (O1 -101.5) | rigorous |
| linearised Eqp1 → QP root (A1) | - | - | - | +53.58 | cited from qp_cert.json |

### Findings for the reviewer

1. **The static remainder COR is the dominant departure (-117 meV).** Without it O1
   changes sign to -101 meV. Invalid modes are 31% of all modes; replacing their static
   limit moves O1 by -20.6 meV (skip) or -5.8 meV (2 Ry). Bare-vs-averaged Coulomb moves
   it by -6.5 meV.
2. **New: the theory kernel is discontinuous at (x, Ω²) = (0, 0).** For every
   `Ω² > 0`, `emptyTerm(w̃²I, 0, w̃) = -I/2`; at `Ω² = 0` the value is 0. On spec A's
   inputs, 5408 / 1896 modes at `x ≈ 0` (n1 = a and its partners) have
   `0 < abs(Ω²) ~ 1e-15 < TOL_Small`.
   * Every such `Ω²` is exactly 0 in the ideal fcc metric. The nonzero value comes from
     the binary64 `bdot`; this was checked in exact rationals.
   * Switching them to the theory value moves O1 by +28.4 meV, a rigorous figure for the
     inputs taken as exact reals. With the ideal metric the same switch gives 0.
   * BerkeleyGW's drop rule is the ideal-metric value. Its source comment ("both terms
     vanish as Ω²→0") holds only for x ≠ 0.
3. **The empty near-pole switch (+12.7 meV) is ill-conditioned.** One L mode has
   abs(x − w̃) = 3.6e-4 eV. With bare Coulomb, the same switch contributes about 4.8 meV.
4. **Certified negligible:**
   * the ModeOK classes, which amounts to a numerical check of `mode_eq` on 3.4 M
     production modes;
   * hX;
   * the q = 0 wing rule, which is exactly null because `OmT` = 0 on those wings and the
     G = 0 closure holds with any band set;
   * all dropped classes away from x = 0.
5. **Classes that never occur at the linearised O1 energies:** the row 14 DISCREPANCY
   (x = w̃) and the `sexcut` clamp. At the A1 QP roots the clamp does occur (57936 per
   `qp_cert.json`), so it matters for A1 but not for this O1.

## Failed attempts and fixes

* **First classification (outward rounding on exact zeros).** Outward rounding of exact
  zeros (0·x gives [-5e-324, 5e-324]) meant no mode was found to have `I = Ω² = 0`.
  Structural zeros are now set exactly: zeroed eps entries, absent rho, and exactly
  vanishing dot products.
* **Interval dot product.** A rounded interval `(q+G')·B·(q+G)` enclosed 0 for about 1e-14
  values and left sign(Ω²) undecided on 136k modes. It was replaced by an exact rational
  dot on the binary64 `bdot`, returned as a one-ulp enclosure. That made sign(Ω²) exact,
  and it exposed finding 2.
* **Bounds for sign-undecided modes.** For dropped modes whose sign is undecided, the first
  version gave no value. It now uses monotone bounds on `abs(thK)` as a ± interval. The
  remaining unbounded modes carry `Σ|W||I|` of 3e-15 eV (float) and are excluded.
* **Test for the x = w̃ witness.** The first test expected a class for `x = w̃` exactly.
  The rigorous classifier correctly refuses to decide there (the `sqrt` interval straddles
  `x`), so the test now asserts that refusal, the theory value 1/4, and ModeOK one step
  away.
* **Test edits.** Two assertion fixes were needed (a static-limit arithmetic slip, and
  5e-324 vs 0).

## Limits

* The switched quantities are the specifications defined in `measure.py`; they are not
  physical error bars.
* The invalid rows have no theory value to switch to. They compare BerkeleyGW's options
  instead.
* The Coulomb switch keeps `vb` at q+G = 0, because the bare value diverges there. For
  scale only, setting that single entry to 0 moves O1 by +91 meV.
* Σ|W| and the conditioning diagnostics are float-only.
* The switches are not additive.

## Next action (for Codex)

1. Review the table and finding 2, and decide whether it belongs as a new row in the
   departure table. It is a theory-side discontinuity, not a spec bug.
2. Consider whether `sigA_eq_theory`'s COR (row 16) deserves a bound or a convergence
   task, since it dominates O1 on this basis.
3. Run the full `bash scripts/verify.sh` when the machine is free.
