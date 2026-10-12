# G2 stage 3 handoff: spec A's O1 kernel-checked on the TRUE eps⁻¹

Status: ready for review. This is **not accepted**. Branch `lean/g2-stage3-sigma`,
forked from `bgw-e/endpoint` (be459c7). Nothing is merged.

**Outcome: full chain, both states, all 8 q-points.** The kernel checked

    GW.Endpoint.Kernel.S3.o1_enclosure :
      ∀ vb oq, VbHyp vbT eg.SV vb → VbHyp oqT eg.SV oq →
        O1 gl stX stL Etrue vb oq ∈ [8880811588953599 / 2^59, 8880812351936001 / 2^59]
    GW.Endpoint.Kernel.S3.o1_pos : … → 0 < O1 gl stX stL Etrue vb oq      (C1 for spec A)

The bounds are exactly the binary64 values of `cert_o1.json`
(`O1_lo = 0.015405752349084699`, `O1_hi = 0.015405753672648183` eV). They did not need
to be widened: the exact dyadic evaluation gives the tighter
`O1 ∈ [0.0154057525999968, 0.0154057534217509]` eV (width 8.2e-10 vs cert.py's 1.3e-9),
`Eqp1(X) ∈ [4.531541295252438, 4.531541295616094]`,
`Eqp1(L) ∈ [4.516135542194343, 4.516135542652441]` eV, each inside cert.py's interval.

`#print axioms` (`GW/Endpoint/Kernel/AuditSigma.lean`): `o1_enclosure`, `o1_pos`, `eqpX`,
`eqpL`, the per-(state,q) facts and the data theorems depend only on
`[propext, Classical.choice, Quot.sound]` (subsets). No `sorry`, axioms, `native_decide`,
`ofReduceBool` or `implemented_by`; all heavy checks are `decide +kernel`.

## What is proved (plain mathematics)

`SigmaSpec.lean` defines over ℝ, mirroring `cert.py` (`SigmaIV.eps_at/modes/kernel/prepare/
qpart/eqp1`, `total`):

- `epsS`: the eps⁻¹ entry Sigma uses at q, `±E(iq, idx i, idx j)` (relative phase signs),
  with the wing rule: q = 0 row/column z zeroed except the head; q ≠ 0 row z ×
  `oneoverq·|q|/(8π)`, column z × `oneoverq/(vbar(q+Gs₀)|q|)` (`|q| = √(q·B·q)`, real π).
- `IeS = δ − epsS`; `Om2S = wpsq/nelec · vbar(q+G)/(8π) · (q+G')·B·(q+G) · ρ(G−G')`,
  `wpsq = RYD²·16π·nelec/Ω`, ρ = the first matching entry of the RHO list (`find?`), 0 if
  absent; q = 0, G = 0 row: `wpsq/nelec · ρ(0)` at G' = 0, else 0.
- keep rule (`|I| ≥ TOL_Small ∧ |Ω²| ≥ TOL_Small ∧ |Ω²/I| ≥ TOL_Small`), `wtilde = √(Ω²/I)`
  or `1/TOL_Zero` for an invalid mode, `I_used` zeroed below TOL_Small.
- kernels: `schM` (generic `w I/(x−w)` iff `(x−w)² > 1/4 ∧ w² < (x−w)²·LIM1`, else 0),
  `ssxM = Cert.certSsx` (generic / near-pole / 0 with the sexcut = 4 clamps; proved equal
  to the source's rule in `CertSexcut.lean`); `wx = RYD(E_k − E_{k−q}) + iw` with the
  `|wx| < TOL_Zero → TOL_Zero` replacement.
- pair densities `pd` (= `mtxel_iv`), `vS = vbar/(N_q Ω)`, the quadratic form
  `quad F = Σ_i Σ_j M_i v_i M_j F(j,i)`; per (q, band): bare exchange `Xq`, exact static CH
  `CSq`, `ACq = −achs/2`, `Pq = CH/2 − [occ] SX`; `SigA = Σ_q (X + CS + Σ_n1 (AC + P))`.
- `eqp1 = Eqp0 + d/(1−d)(Eqp0 − Eo)`, `d = Σ(Eo+1) − Σ(Eo)` (dE = 1 eV), multiplet
  average, RYD conversion; `O1 = eqp1 stX − eqp1 stL`.

Constants: RYD = 13.60569253 (the decimal of `nrtype.f90`, exact rational), TOL_Small,
TOL_Zero as their binary64 values, LIM1 = 250000, 1/TOL_Zero = 10¹² (both exact in binary64).

`Etrue iq a b` = `(E{iq}.epsTrue)⁻¹ a b` (stage 2's true static RPA eps from the
wavefunction coefficients, inverted), 0 outside the block. `VbHyp vbT` says every Coulomb
average of `coulomb_cert.json` lies in its JSON box (the 1363 vbar keys `2(q+G)` and the 7
oneoverq keys `2q`, all the file's entries, as exact dyadics of the doubles).

The soundness chain (all in the default `GW` target, audited in `GW/Audit.lean`):
`schK_spec`, `ssxK_spec` (kernel values; every branch decided by exact endpoint
comparisons, divisions bracketed by floor / floor+1) → `nOK_sound` (hot path) ;
`tget_find` (Kronecker tables for RHO, Coulomb boxes, static-CH pair densities) ;
`ieBox_spec`, `om2_spec`, `entChk_sound` (per-entry `I_eps` box, Ω² box, drop decisions,
√ bracket by squaring) ; `mkEn_spec`, `vbOK_sound`, `wingOK_sound` (π by
`Real.pi_gt/lt_d20`, |q| by squaring), `exOK_sound`, `csOK_sound` → `stq_n`, `stq_x`,
`stq_cs` → `sig_bounds` → `eqp1_bounds` (`Eqp1 = Eo + Σ₀/(1 − d)`, monotone for Σ₀ < 0,
d < 1, both checked).

## What remains trusted

1. **Symmetry unfolding and the sphere/mapping data**: the coefficient lists at k and
   k − q (`real_coeffs`), the sphere orders, `Screening.mapping` (`idx`, signs, `z`, block
   `iq`) are captured from cert.py's own run (`capture_sigma`, wrappers on `mtxel_iv` and
   `SigmaIV.eps_at`) — Python-side, as in stage 2.
2. **Coulomb averages**: the boxes of `coulomb_cert.json` are hypotheses (`VbHyp`); their
   Arb derivation (certcoulomb.py) is outside Lean.
3. **Exporter**: `kernel_export.py --sigma` converts floats exactly (`as_integer_ratio`,
   asserted), asserts q-data identical across states, distinct G-vectors, `is0 ⇔ q = 0`.
   "These literals are cert.py's inputs" is a Python-side claim. Hints are never trusted.
4. **Modelling claim**: that `SigmaSpec` is BerkeleyGW's GPP Sigma (the correspondence is
   to cert.py/spec.py, whose production agreement is E1's evidence, not Lean's).
5. Stage-1/2 trust unchanged (symmetry unfolding for eps, the eps exporter).

## Design / measurements

- One theorem per (state, q, band, inner band) for the hot path (432), per entry column for
  the entry checks (645), modules of ≤ 12 columns / ≤ 5 inner bands, two serialized import
  chains (entries + L; X + exchange/static). 202 generated modules, 16 MB.
- **Kernel cache collision pitfall (again, sharper):** any two distinct literals with equal
  low 64 bits (not only trailing zeros: low limbs `…fff`/`…001` from `floor ± 1` of
  power-of-two-scaled values collide too) made the hot path superlinear (30 columns: 202 s
  instead of ~14 s). Fix: every hint rounded outward by a random odd amount < 2^62, pair
  densities divided by their common power of two (`xsOf`, exactness checked by `xsExact`),
  `TOL_Zero` comparisons as right shifts instead of products with 2^92.
- Tables by Kronecker digits (one shift + mod per lookup; slot distinctness by a bit set,
  `distinctB`, instead of `List.Nodup`, which took minutes).
- Builds (16 cores shared, nice, ≤ 2 heavy processes):
  - front data chain S3G…S3Pre (data elaboration, kOK of the pair densities): ~6 min;
  - heavy chains: **1 h 22 min wall, 8935 CPU-s, peak RSS 7.26 GB**;
  - S3Check 15 s, S3Tamper + AuditSigma 26 s;
  - `lake build GW` PASS; `lake build GWKernelData` PASS (incl. stages 1–2);
  - `lake build Main && lake env lean scripts/CheckAxioms.lean`: **AXIOM AUDIT PASSED:
    7430 theorems**, 202 S3 modules covered (1192 s, 3.2 GB).

## Negative controls (`Data/S3Tamper.lean`, in GWKernelData)

- `tamper_ent`: an entry's `I_eps` box moved above the true value → `entChk … = false`
  (`control_ent`: original record → `true`);
- `tamper_coef`: one k−q coefficient with one bit flipped → `kOK … = false`;
- `tamper_vb`: the Coulomb box of Gs₀ shifted by 2 ulp → `vbOK … = false`;
- `tamper_out`: a claimed hot-path enclosure collapsed to its upper end → `nOK … = false`.

## Commands

```
cd .claude/worktrees/lean-g2c && source scripts/env.sh
R=<scratch>/fix/run
python3 bgw/endpoint/kernel_export.py $R --sigma --sigma-pkl CAP.pkl --lean   # ~55 s; prints the
    # exact Python-mirror enclosure and whether it is inside cert_o1 (True)
nice lake build GW
nice lake build GWKernelData          # stage 1+2+3
lake env lean GW/Endpoint/Kernel/AuditSigma.lean
lake build Main && lake env lean scripts/CheckAxioms.lean
```

## Files

- New: `GW/Endpoint/Kernel/Sigma{Spec,Check,Kernel,Hot,Tab,Ent,Glue,Stq,Asm}.lean`,
  `GW/Endpoint/Kernel/AuditSigma.lean`, `GW/Endpoint/Kernel/Data/S3*.lean` (generated),
  this handoff.
- Edited (additively): `bgw/endpoint/kernel_export.py` (stage-3 section, `--sigma`),
  `GW.lean` (9 imports), `GW/Audit.lean` (section at end), `lakefile.toml` (3 roots added to
  `GWKernelData`, so `verify.py` builds them before the audit), `scripts/CheckAxioms.lean`
  (3 imports). `verify.sh` was not run end to end (time); its pieces above passed.

## Failed attempts

- `Int` arithmetic in the hot path: ~8× slower than ℕ and hit `maxRecDepth` on long folds.
- Accumulating per-row lists instead of per-column sums; structure-literal syntax
  `{ f := … }` over line breaks in generated files (parse error) → anonymous constructors.
- `decide (List.Nodup …)` for 1363 table keys: minutes → bit-set check.
- First hot-path benchmark: 7 ms per entry and superlinear (collisions above).

## Next action

Review `SigmaSpec` against cert.py (especially the wing rule, the q = 0 G = 0 Ω² row, the
index order `F(j,i)`), the capture wrappers, and the `VbHyp` statement form. Possible
follow-ups: Lean-side symmetry unfolding; merging the degenerate X bands to cut ~30% of
the hot path.
