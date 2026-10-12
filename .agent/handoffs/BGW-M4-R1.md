# BGW-M4-R1 handoff: one GPP squared pole connected to the M2 certificate

**Status: CHECKPOINT_READY (ready for review, not accepted).**
Worker: Claude (Opus 5.5), session 2026-09-22. Branch `bgw-m4/gpp-preflight`
(PR #25), with `origin/bgw-m3/chi-transition-sum` (head 6bcdeee, including
PR #24) merged in first, because the M4 branch predated #24.

## Authorization

Brief: `.agent/handoffs/BGW-M4-PREFLIGHT.md` at 92e2a73. That document says
"documentation only". Separate execution authorization came from the user on
2026-09-22, who chose "Authorize the full work order" (steps 1–3) in session
`06be8555`, and it was repeated in this session ("take on the works of
PR 25"). The brief also says consolidation of M1–M3 comes before further
execution. That ordering was not followed, at the user's direction. Nothing
was merged.

## Result, in plain terms

- **Step 1, the input bridge: closed.** Sigma does not read M2's matrix
  directly. For each q it needs, it picks a stored block, relabels G vectors
  by a crystal symmetry plus an umklapp shift, multiplies by a ±1 phase, and
  first rescales the G = 0 "wings" (`fixwings`). Every one of those steps
  was traced in source and checked on data. For all 8448 surviving GPP
  records that read M2's block, the consumed number equals M2's certified
  `Xhat` entry, bit for bit, under that map. The feasibility run's mismatch
  came from comparing without the map.
- **Step 2, independent parameters: done** for the frozen target, source pair
  (1,2) (a wing). `Omega2` is rebuilt exactly from the primitive operands of
  `wpeff`, and `wtilde2` from that and the mapped M2 reference.
- **Step 3, error carried and checked in Lean: done.**
  `GW/BGW/M4GPP.lean` proves the four endpoint bounds. The screening bound
  uses M2's own `total_error_bound`, and the final bound is composed by a
  generic lemma. Five discriminating mutations each fail exactly where
  intended. Stopped before `sqrt(wtilde2)` and any self-energy term.

## Files

| File | Role |
| --- | --- |
| `bgw/m4_gpp/instrument_r1.py` | write-only export in `sigma_main.f90` (map, wing operands), `mtxel_cor.f90` (column, survived modes), `wpeff.f90` (primitive operands) |
| `bgw/m4_gpp/m4r1_instrument.patch` | its diff against the pristine tree (adds only) |
| `bgw/m4_gpp/data/m4r1_dump.dat.gz` | the export; all floats as IEEE bits |
| `bgw/m4_gpp/bridge.py` | map/operand/local checks, target rule, references, budgets |
| `bgw/m4_gpp/make_lean.py` | generates `GW/BGW/M4GPP.lean`; `--check` for drift |
| `bgw/m4_gpp/mutate.py`, `evidence/mutations.log` | Lean mutations |
| `bgw/m4_gpp/evidence/ab-neutrality.log` | run identity and pristine/instrumented A/B |
| `bgw/m4_gpp/PROVENANCE.md` | map, rule, budgets, values |
| `GW/BGW/M4GPP.lean` | 14 theorems, all `[propext, Classical.choice, Quot.sound]` |
| `tests/test_bgw_m4.py` | 17 tests, SCIENTIFIC gate |
| `GW.lean`, `GW/Audit.lean`, `scripts/gates.py` | registration |
| `bgw/m4_gpp/FINDINGS.md` | dated outcome note prepended; the old text is kept |

`bgw/m4_gpp/mtxel_cor_m4_dump.patch`, from the feasibility run, is left in
place. It is superseded by `instrument_r1.py`.

## Commands and results

```
curl <pinned URL> -> bgw40.tar.gz               sha256 1a85b03b…6a49  (matches pin)
micromamba env: gfortran 13.4.0, openblas 0.3.34, fftw 3.3.11   (~/bgw-src/mm)
make epsilon, make sigma (pristine), make sigma (instrumented)    rc 0
epsilon.real.x -> epsmat 61181 B; with date field = 19-Sep-2026 -> 4512f63a…  (M2/M3 pin)
sigma.real.x pristine / instrumented: exit 0; eqp0, eqp1, sigma_hp.log,
  ch_converge.dat, vxc.dat, x.dat IDENTICAL
python3 bgw/m4_gpp/bridge.py                      OK, 8448 records, 4 irq x 3 visits
python3 bgw/m4_gpp/make_lean.py --check           OK
lake env lean GW/BGW/M4GPP.lean                   0 errors (~8 s)
python3 bgw/m4_gpp/mutate.py                      control OK; 5/5 mutants fail exactly as expected
python3 -m unittest tests.test_bgw_m4             17 OK
bash scripts/verify.sh                            PASS (all): 513 scientific (2 skipped) + 14 workflow tests,
                                                  307 named audits, GW.BGW.M4GPP in the exhaustive audit
```

Endpoint values for the target: `|Ohat−OStar| = 7.1e-15 ≤ 1.1e-13`;
`|Ihat−IStar| = 1.5e-17 ≤ 2.4e-13`; `|Phat−Ohat/Ihat| = 7.2e-15 ≤ 9.8e-14`;
`|Phat−PStar| = 9.4e-14 ≤ 3.0e-9` (composed). `B_I ≪ |IStar|/2`, and
`PStar > 0`.

## Failed attempts and corrections, including my own

1. **The feasibility evidence could not be replayed.** `/tmp/bgw`, `/tmp/mm`,
   `/tmp/m3build`, `/tmp/m4run*` and the raw dump were all gone. Rebuilt from
   the pinned archive into `~/bgw-src`, outside `/tmp`.
2. **My first bridge run FAILED:** 1848 of 8448 records mismatched, all in
   M2 row/column 2. I had read only the `nm == 1` branch of the wing fix;
   `sigma_main.f90` also calls `fixwings` whenever `qlen**2 < avgcut`. Fix:
   export the wing operands, and include the normalization in T. It was not
   treated as a tolerance.
3. **My checker had a bug that the tests caught.** It kept one q visit per
   irq, but each irq recurs once per k-point, so two thirds of the map checks
   were skipped. Fixed so every visit is checked; the phase, index and
   symmetry corruption tests now fail as they should.
4. **Retracted suspicion.** I first thought the old `QVEC` records held the
   stored q rather than Sigma's rq. They held rq (`mtxel_cor` receives
   `rq(:,irq)` as `qk`). What the old export lacked was the column index and
   the wing operands.
5. Lean details: `+/-` inside a doc comment opens a nested comment. The
   `norm_num` simp set needed `abs_eq_max_neg` to evaluate `|literal|`, and
   `Matrix.cons_val_two` for index 2. Without that last lemma the
   wrong-source mutant failed for a tactic reason as well as the intended
   one; after the fix it fails only where intended.

6. **Corrected after independent audit:** PROVENANCE.md first said the
   date field could not explain M2's recorded `83358b72…`. Setting it to
   16-Sep reproduces that digest exactly; I had tried only 17-Sep.

## Judgment calls for the reviewer

1. **Wing operands as inputs.** T for the target includes
   `kappa = fact*oneoverq/(vcoul(1)*qlen)`. These are exported
   Coulomb/geometric values: `oneoverq` is a mini-BZ Monte Carlo average,
   and `qlen` is a rounded `sqrt`. I treated them like `vcoul` and `rho`, as
   explicit external inputs under the brief's "Primitive density, Coulomb,
   and geometric numerical operands are explicit external inputs". If Codex
   considers this a hidden promotion, the rule's target is a wing and the
   status becomes BLOCKED on reconstructing `oneoverq`. A non-wing target
   would be a different rule, and I did not change the rule.
2. **Target is a wing** because (1,2) is lexicographically first and
   eligible. It was not chosen for its residual.
3. **Rounding counts** 16/4/3 are an operation-trace model (PROVENANCE.md).
   They are fixed and pinned by a test, but a reviewer should recount them.
4. **`epsmat` identity** is established by masking the date field, not by
   the raw file digest the brief names. That digest is not reproducible by
   construction. The certificate itself binds values to M2's committed bits.
5. **Instrumentation scope** grew from `mtxel_cor` to `sigma_main` and
   `wpeff`. All three edits are write-only, and the A/B test shows six
   outputs byte-identical.
6. **Toolchain** was recreated with current conda-forge packages. Versions are
   recorded, not locked. Executable hashes differ from the historical builds.
7. A local `~/bgw-src` (archive, toolchain, trees, runs) was created outside
   the repo, as `/tmp` was before. The main checkout's `.lake/packages` and
   `.tools` are symlinked into the worktree; both are gitignored.

## Not claimed

Anything about other entries or q points; the correctness of `gmap`,
`fixwings` or `wpeff` in general; the provenance of `rho`, `vcoul`,
`oneoverq`, `qlen`, `wpsq`; the compiler; `sqrt(wtilde2)`; GPP accuracy;
self-energy or quasiparticle quantities.

## Next action

Codex review of this checkpoint, with judgment call 1 first. Then the brief's
own ordering: consolidate the M1–M4 stack. Not started.
