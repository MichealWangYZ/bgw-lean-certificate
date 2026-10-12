# BRIDGE handoff: BerkeleyGW's GPP Sigma derived from G0W0, compared with SigmaSpec

Worker: Claude (implementer). Branch `bridge/theory-to-bgw`, worktree
`.claude/worktrees/bridge`, based on `main` 709220e. Status: **CHECKPOINT_READY**, meaning
B1 to B4 are delivered and ready for review. This is NOT accepted. Codex owns acceptance.

## Result in one paragraph

BerkeleyGW's per-state GPP Σ, as transcribed in `GW/Endpoint/Kernel/SigmaSpec.lean`,
equals the G0W0 + HL-GPP theory Σ derived here. The derivation starts from the damped
Fourier transform of `i G0 W_c` and the HL model, specialised to Bloch plane waves on
SigmaSpec's own data. The equality is `sigA_eq_theory`: `SigA = SigT + COR`, holding
under four named hypotheses (Coulomb averages `hC`, wing rule `hW`, `TOL_Zero` shift
`hX`, per-mode `ModeOK` `hM`) plus one explicit correction term `COR`, the half static
remainder. `COR` vanishes for complete bands (`sigA_eq_theory_complete`). Every excluded
mode case is characterised. The frequency integral's signs, the SX/CH split, the CH
factor ½, `w̃² = Ω²/I`, the HL `Ω²`, the occupied near-pole branch and the bare exchange
are **proved equal** to theory. **One DISCREPANCY**: on an occupied band at exactly
`x = w̃`, the spec gives `0` where theory gives the removable value `I/4` per unit weight
(`occ_pole_point`, `discrepancy_witness`). It is a single-point IEEE-NaN artefact, and it
was already known as LEAN-CERT finding 1. It is not a documented BerkeleyGW
approximation.

## Files (write scope respected)

New:
* `GW/Bridge/FreqIntegral.lean` (B1)
* `GW/Bridge/GPPModel.lean` (B2)
* `GW/Bridge/Bloch.lean` (B3)
* `GW/Bridge/Compare.lean` (B4)
* `docs/BRIDGE.md` (the departure table)
* `tests/test_bridge.py` (oracle)
* this handoff

Registration:
* `GW.lean`: 4 imports and a docstring entry, so `scripts/CheckAxioms.lean`, which
  imports `GW`, audits them.
* `GW/Audit.lean`: 59 `#print axioms`.
* `scripts/gates.py`: `tests.test_bridge` added to SCIENTIFIC. This was needed because
  `test_gate_partition` rejects unclassified modules. It is a registration file outside
  the literal list in the task; recorded here.
* `bgw/weighted_audit/PROVENANCE-R6.txt`: the three changed digests re-signed.

No existing theorem statement was edited.

## Key theorems

* B1: `GW.Bridge.sigt_limit`, `wct_limit`, `sigc_eq_terms`, `sigc_eq_sx_ch`, `g0_eq_G0t`
* B2: `gppC_static`, `gppC_tail`, `fsum_moment`, `single_pole_exists_iff`,
  `single_pole_unique`, `bgw_invalid_mode`, `static_pole_limit`, `sch_static_error`,
  `bgw_dropped`, `valid_neg_weight`
* B3: `bloch_sigc_eq`, `bloch_limit`, `bloch_wcFreq`, `screened_entry`, `pd_closure`,
  `pd_neg`, `omT_head`, `vBareK_key`
* B4: `mode_eq`, `sigA_eq_theory`, `cor_eq`, `chpart_sum_eq_exact`,
  `sigA_eq_theory_complete`, `occ_pole_point`, `discrepancy_witness`,
  `emp_near_zero`, `occ_generic_clamp`, `occ_near_clamp`, `wxS_close`,
  `wing_factors_point`, `om2S_eq`, `epsS_eq`, `eqp1_linear`

## Departure table

See `docs/BRIDGE.md` (22 rows). Summary:

* proved equal: rows 1-4, 4a, 10, 19
* named approximation:
  * 4b: `q = 0` Ω² wings
  * 5: Coulomb `vb`
  * 6, 7: eps⁻¹ wings
  * 8: drop thresholds
  * 9: invalid mode, which becomes the static-COHSEX limit
  * 11: empty near-pole CH = 0
  * 12, 13: `sexcut`
  * 15: `TOL_Zero`
  * 16, 16a: static remainder with factor ½ and the `Gch` restriction
  * 22: linearised Eqp1
* shared: 17 (bands), 18 (spheres), 20 (symmetry map, trust), 21 (real flavour, insulator)
* DISCREPANCY: 14 (`x = w̃`, occupied)

## Commands and results

```
source scripts/env.sh
lake build GW.Bridge.Compare                 # OK (builds FreqIntegral, GPPModel, Bloch)
lake env lean <scratch>/aud.lean             # the 59 GW/Audit.lean entries: all [propext, Classical.choice, Quot.sound]
lake env lean <scratch>/chk.lean             # collectAxioms over every GW.Bridge.* theorem: "BRIDGE AUDIT PASSED: 113 theorems"
lake build GW                                # "Build completed successfully." (6747 jobs)
lake env lean GW/Audit.lean                  # exit 0; 1114 audited entries (59 GW.Bridge), all within the allowlist
python3 -m unittest tests.test_bridge        # 16 tests OK (deterministic seed)
grep -nE "sorry|admit|native_decide|implemented_by|ofReduceBool|^axiom" GW/Bridge/*.lean   # nothing
```

NOT run:
* `scripts/CheckAxioms.lean`, because it imports the `GWKernelData` modules, which the
  task forbids building.
* `bash scripts/verify.sh`, because it builds `GWKernelData`.

The equivalent restricted check (`chk.lean` above) passed for all GW.Bridge theorems.
Codex should run the full gate on a machine with the cached kernel data.

## Failed attempts and fixes (for the reviewer)

* `closure` clashed with Mathlib's topological `closure`, so it was renamed `pd_closure`.
  Its first proof used `rw [sum_comm]`, which is ambiguous with sums on both sides; it
  was rewritten with `sum_comm.trans`.
* In the first `blochSys` the residue used `wgt … k.2 k.1`, which swapped `j`/`i`
  relative to the pole `w … k.1 k.2`. Lean caught it (the closed form did not match).
  Fixed to `k.1 k.2`.
* `rw [hO]` with `hO : O = w̃² I` also rewrote the `O` inside `wG I O`. Fixed with
  `generalize wG I O = w` then `subst`.
* Oracle: the first brute-force validity search could not tell "no solution" from
  "solution only as `w → 0`" for `(I ≠ 0, Ω² = 0)`. It was replaced by a sign-change
  test. A near-pole choice of `E` made the `η → 0` check flaky, so `E` is now chosen far
  from the poles.

## Honest limits

* The hypotheses of `sigA_eq_theory` are named; they are not verified on production data.
  * `hC` is false by design, because `vb` is a cell average.
  * `hX` fails for `n = a` at `q = 0`, `iw = 0`. The shift is < 2e-12 eV (`wxS_close`),
    but no Σ-level bound was formalised.
  * `hM` fails for dropped, invalid, clamped and empty-near-pole modes.
* The theorem characterises the spec as theory plus explicit departures. It does not
  bound the size of the departures on Si-EPM.
* `ShiftClosed` and `Complete` are stated as the exact combinatorial and orthonormality
  conditions. A sufficient condition for `ShiftClosed` (a nodup `k - q` sphere
  containing every `G_k - G`) was not formalised.
* Exchange: `Xq` is the same formula on the theory side. Its identification with
  first-order `ManyBody.sigX` is algebraic and not re-proved here.

## Next action (for Codex)

1. Review the departure table, especially whether row 14 should count as a DISCREPANCY
   or be downgraded to "IEEE artefact, measure zero".
2. Run the full `bash scripts/verify.sh` with the cached `GWKernelData`.
3. If wanted, a follow-up could measure on the production Si-EPM data how much weight
   falls into each `hM` exclusion: dropped, invalid, clamp, empty near-pole, `x = w̃`
   exactly. That turns the named departures into numbers.
