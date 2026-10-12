# G2 unfolding handoff: stage-2/3 inputs computed in Lean from the IRREDUCIBLE WFN data

Status: ready for review. This is **not accepted**. Branch `lean/g2-unfold`, forked from
`bgw-e/endpoint` (6a609a2). Nothing is merged.

**Outcome (a): the composed theorems are kernel-checked.** Every coefficient list,
G-list, energy list, k-set, sphere, sphere order and eps index map that stages 2 and 3
consume is computed in Lean from the irreducible WFN / WFNq / WFN_inner data. The
kernel checks that these computed values equal the stage-2/3 inputs exactly
(`decide +kernel`). "Symmetry unfolding" is therefore no longer a trusted Python step.

    GW.Endpoint.Kernel.U.o1_enclosure_irr (vb oq) (hvb : VbHyp S3.vbT S3.eg.SV vb)
        (hoq : VbHyp S3.oqT S3.eg.SV oq) :
      O1 glI stXI stLI EIrr vb oq ∈ [8880811588953599 / 2^59, 8880812351936001 / 2^59]
    GW.Endpoint.Kernel.U.o1_pos_irr : … → 0 < O1 glI stXI stLI EIrr vb oq
    GW.Endpoint.Kernel.U.epsinv_irr_q{0,1,2} :
      IsUnit epsI{i} ∧ ∀ a b, epsI{i}⁻¹ a b ∈ [Q{i}.cert.outLo, outHi] / 2^SO

The inputs in these statements are definitions over the irreducible data:

- `glI = glOf wfni irr ecuts ecutb … S3.rhoT 4`;
- `stXI = stOf wfni [5,6] 18 … kX qh8`, `stLI = stOf wfni [5] …`;
- `epsI{i} = Matrix.of (epsR inp{i})`, with `inp{i} = epsIn wfn (wfnq | wfn) q{i} ecuts 4 18 …`;
- `EIrr` is `S3.Etrue` with `epsI{i}` in place of `E{i}.epsTrue`.

`wfn`, `wfnq` and `wfni` are the exact contents of the three files, as `Unf.Wfn`:

- the 48 integer `mtrx` and `t2 = tnp/π`, plus the raw `tnp`;
- `kpt` and `kw`;
- per irreducible k: the G-list, the coefficient rows and the energies;
- `bdot`, `celvol` and `gvec`.

All numbers are `Dy` values: exact dyadics of the binary64 numbers.

`#print axioms` (`GW/Endpoint/Kernel/AuditUnfold.lean`) gives `[propext, Classical.choice,
Quot.sound]` or a subset for all composed theorems, equalities, checks and tamper theorems.
No `sorry`, `native_decide`, `ofReduceBool`, `implemented_by` or axioms appear in any new
file (grep checked).

## What is defined (GW/Endpoint/Kernel/Unfold.lean, default `GW` target)

Everything is transcribed from spec.py / cert.py and read over exact integers
(k-points are at scale 2^-64):

- **`find kp`**: the FIRST `(ik, iop)` in file order such that `kp - M k_ik` is within
  `10^-9` of an integer vector `g`. This is `spec.Wfn.find`.
- **`rot`**: gives G-vectors `M G - g` and coefficients `flip(s(G)) c(G)`, with
  `s(G) = ((M G)·t2) mod 2`. Energies are unchanged. This is `cert.real_coeffs`.
  - `UnfoldPhase.flipG_phase` proves that `s(G)` is exactly `exp(-2πi (M G)·t)` for
    `t = t2/2`.
  - `rot_coef` states the coefficient rule: the result equals the textbook
    `c'(MG−g) = e^{-2πi M(k+G)·t} c(G)` times the dropped global phase `e^{2πi (Mk)·t}`.
  - `flipG_neg` proves that `±t` give identical signs. Hence the atom-mapping choice of
    the translation sign (`spec.atom_mapping_sign`) is immaterial here.
- **`kfull`**: the distinct `M k − floor(M k + 10^-9)`, first occurrence kept, in
  (k, op) order. This is `spec.EpsilonRun.kfull`.
- **`sphere`**: `gvec.filter (|q+G|²_B < ecut)`, exact. This is `spec.sphere_of` /
  `Run.sphere`.
- **`bgwSphere`**: `spec.bgw_order`, done exactly:
  1. stable sort by the exact norm;
  2. start a new group where a norm exceeds its predecessor by more than `10^-12`;
  3. sort by (group, GK), with `GK = g3 + E3 (g2 + E2 g1)` and `E` the extent of gvec.
- **`qdOf`**: `spec.Screening.mapping` / `cert.SigmaIV.eps_at`.
  - It takes the LAST `(iq, iop)` with `M q_iq − q` within `10^-6` of `g0`, where
    `q_iq = 0` for the q0 block.
  - `idx_i` is the position of `M⁻¹(Gs_i − g0)` in the block's G-list, with
    `M⁻¹ = det·adj`.
  - `neg_i` is the parity of `M(Gi_i − Gi_0)·t2`, i.e. the relative phase
    `phase/phase[0]`.
  - `z` is the position of `g0`.
- **`epsIn`** builds stage 2's `Input`: conduction bands 4..17 at k from WFN, valence
  bands 0..3 at k+q from WFNq (q0) or WFN, over `kfull wfn`, plus the sphere and the
  WFN header.
- **`stOf` / `kqOf` / `glOf`** build stage 3's `St` and `Gl`:
  - bands at k, and 18 bands at k − q, from WFN_inner;
  - `Gch` is the sphere at 0 with cutoff `max(ecuts, ecutb)`;
  - `qs = qh8.map qdOf`;
  - RHO is passed through (`S3.rhoT`).
- **`Dy.enc S`** writes a `Dy` in the data's literal form at scale `S`. `Dy.enc_val`
  proves this is exact when `e ≤ S`. Scales are only a representation; the real values
  are the file's numbers.

## Header and grid checks (`Data/UWR.lean`, kernel)

- **`kfull_eq`**: `kfull wfn` is the explicit 32-point list.
- **`wfn_closed`, `wfni_closed`**: the k-set is closed under all 48 operations, so it is
  the group closure of the irreducible points.
- **`wfn_kw`, `wfni_kw`** (the multiplicity weights):
  - every weight equals `|orbit(k)| / |kfull|`: 0.25 and 0.75 for WFN (orbits 8 and 24
    of 32); 0.125, 0.5 and 0.375 for WFN_inner (orbits of the 8-point grid);
  - the orbit sizes sum to `|kfull|`, so the orbits partition the set.
- **`wfn_sep`**: distinct kfull points differ by more than `2·10^-9`. So spec's dedup
  by `round(p, 9)` equals the exact dedup.
- **`t_ok`**: for all three files, the header `tnp` is `π·t2` within `10^-15`, with
  `|t2| ≤ 1`. `tOK1_sound` turns this into `|tnp − π t2| ≤ 10^-15 + 10^-20` via
  `Real.pi_gt_d20` / `Real.pi_lt_d20`.
- **`ops_same`**: WFNq and WFN_inner have the same operations as WFN.
- **`g_gap{t}`** (8 Sigma q-points; not needed for the statements): consecutive sphere
  norms differ by at most `10^-14` or by more than `10^-10`. So rounding cannot change
  BerkeleyGW's tie groups.

## Negative controls (`Data/UTamper.lean`, in GWKernelData)

- `control_rot`: the unfolding reproduces `E1` k-point 0, so `decide … = true`.
- `tamper_rot`: the stage-2 k-point with **one rotated coefficient's sign flipped**
  gives `false`.
- `tamper_phase`: the fractional translations set to 0 give `false` at k-point 1, whose
  op is non-symmorphic.
- `tamper_irr`: one irreducible WFN coefficient negated gives `false`.
- `tamper_kw`: swapped k-weights give `kwOK = false`.
- `tamper_neg`: one relative eps phase sign of Sigma's q-point 1 flipped gives `false`.

## What remains trusted

1. **The binary-file reader.** `bgwio.read_wfn` (WFN/WFNq/WFN_inner) and
   `kernel_export.py --unfold` turn the Fortran records into Lean literals, using
   `float.as_integer_ratio`, which is asserted exact. "`wfn` is the content of WFN" is a
   Python-side claim. The same holds for:
   - RHO (`S3.rhoT`, still from the stage-3 capture);
   - the eps headers: `q0`, `q1`, `q2`, `ecuts = 7.0` and `qgrid` (the 2×2×2 grid is
     hard-coded as `qh8`; the exporter asserts it);
   - sigma.inp: `kX`, `kL`, bands [5,6] and [5], `number_bands = 18`. `nv = 4` and
     `nocc = 4` are constants;
   - `ecutb = ecutwfc` of WFN_inner (`bare_coulomb_cutoff` is unset).
2. **Faithfulness of the transcription to spec.py/cert.py.** It covers the tolerances,
   the first/last-match rules, the `M` vs `M⁻ᵀ` convention and the dropped global phase.
   It is a reading of the Python code (cited in docstrings), cross-checked by an exact
   Python mirror (`unfold_mirror`) that asserts equality with `cert.real_coeffs`,
   `spec.sphere_of`, `Run.sphere`, `bgw_order` and `Screening.mapping` on the production
   run.
   - The float `np.round(k+q, 12)` is replaced by the exact `k+q`. The kernel equality
     with cert.py's captured data shows the same states were selected.
   - Whether spec.py's conventions are BerkeleyGW's is the E1 modelling claim, not Lean's.
3. **Stage 1–3 remaining items, unchanged:**
   - the Coulomb-average boxes (`VbHyp`, certcoulomb.py);
   - the modelling claim that `epsR` / `SigmaSpec` are BerkeleyGW's formulas;
   - that the WFN files are physically valid. The ops are used as given; whether they
     are symmetries of the atoms is not checked in Lean.

No longer trusted: the rotation of G, the per-G ±1 signs and the non-symmorphic phases,
the real-flavour phase removal (up to the dropped global phase, proved to be a unit
factor), the op choice, the 32-point k-set, the spheres and their order, and the eps
mapping (idx, neg, z, iq).

## Measurements (nice, one heavy process at a time, warm)

| module(s) | content | wall |
| --- | --- | --- |
| UWN/UWQ/UWI | irreducible data, 22k `Dy` + 3×1363 G (1.1 MB) | ~19 s each |
| UWR | kfull, closure, weights, sep, tOK | 17 s |
| UE{i}K0..K3 (×12) | 8 k-points each: unfold + equality | 32–36 s each (peak 3.5 GB) |
| UE{i} (×3) | assembly, sphere/B/Om/qn, composed theorem | 7–8 s |
| USG | 8 q-points: bgw-ordered spheres, Gb, mapping, gaps, Gch | 5 min 48 s |
| USX / USL | 8 × k−q states + head each | 29 / 30 s |
| US | composed O1 theorem | 4 s |
| UTamper | controls | ≈ 50 s |

The total is ≈ 17 CPU-min on top of stages 1–3. The peak RSS of any U module is ≤ 4.2 GB.
USG dominates, because the kernel does the sorting by Int arithmetic over 110-bit norms.
Speeding it up (ℕ offsets, precomputed keys) was not needed.

- `lake build GWKernelData`: PASS. The incremental run (U* only) took 17:05 wall.
  After the tamper fix it passed again (53 s).
- `lake build GW`: PASS. `lake env lean GW/Audit.lean`: the Unf section passes (listed
  axioms ⊆ the allowed three).
- `lake build Main && lake env lean scripts/CheckAxioms.lean`: **AXIOM AUDIT PASSED: 7874
  theorems** (stage 3 had 7430). It covers 27 new modules (Unfold, UnfoldPhase, the U* data,
  AuditUnfold). Wall time 20:18, peak 3.2 GB.

## Commands

```
cd .claude/worktrees/lean-unfold && source scripts/env.sh
R=<scratch>/fix/run
python3 bgw/endpoint/kernel_export.py $R --unfold --lean   # ~5 s: exact mirror asserted equal to
    # cert.real_coeffs/spec (all 3 eps q x 32 k, 8 Sigma q, both states), writes Data/U*.lean
nice lake build GWKernelData
lake env lean GW/Endpoint/Kernel/AuditUnfold.lean
nice lake build GW && lake env lean GW/Audit.lean
lake build Main && lake env lean scripts/CheckAxioms.lean
```

## Failed attempts / pitfalls

- **Exact norms for the Sigma sphere order.** Sorting by the exact `(|q+G|², GK)` gave
  the wrong order. The float `bdot` is symmetric, but the exact norms of
  symmetry-equivalent G differ at the 1e-16 relative level, so exact ties do not occur.
  The `TOL_Zero` grouping of `bgw_order` has to be transcribed literally (`gids`); the
  mirror caught this before any Lean build.
- **`gvec` (1363 entries) as one literal** hit `maxRecDepth`. It is now written as
  100-element chunks joined by `++`.
- **`tOK1` first used the wrong scale** (a 1e-5 tolerance). It was fixed to 1e-15 before
  `tOK1_sound` was written.
- **Two generator bugs:**
  - USG first lacked the S3Check import (unknown `S3.gl`);
  - the tamper `!b :: l` parsed as `!(b :: l)`.

  Both fixes are regenerated by the exporter.
- **Design choice: projections, not whole-structure equality.** The equalities are
  stated per projection or per list entry (`inp1.ks.getD t default = E1.inp.ks.getD t
  default`), not as one `decide` on the whole `Input`. This keeps each kernel check small
  (≈ 4 s per k-point) and avoids the literal cache-collision blow-up recorded in the
  stage-2 handoff. Assembly is by `list_eq_of_getD` / `Input.eq_of` / `St.eq_of` /
  `Gl.eq_of`.

## Files

- New:
  - `GW/Endpoint/Kernel/Unfold.lean`, `UnfoldPhase.lean` (both in `GW`) and `AuditUnfold.lean`;
  - generated `GW/Endpoint/Kernel/Data/U{WN,WQ,WI,WR,E0K0..E2K3,E0,E1,E2,SG,SX,SL,S,Tamper}.lean`;
  - this handoff.
- Edited (additively):
  - `bgw/endpoint/kernel_export.py` (`--unfold` section);
  - `GW.lean` (2 imports) and `GW/Audit.lean` (END section);
  - `lakefile.toml` (3 GWKernelData roots) and `scripts/CheckAxioms.lean` (3 imports).

## Next action

Review:

- the transcription of `find` / `rot` / `kfull` / `bgwSphere` / `qdOf` against
  spec.py/cert.py (the first vs last match, the 1e-9 / 1e-6 tolerances, `M` on
  reciprocal coordinates);
- the statement form of `o1_enclosure_irr`.

Possible follow-ups:

- export RHO and the eps/sigma.inp scalars through the same reader, which leaves only
  bgwio trusted;
- check atom mapping by the ops (needs `apos` as rationals);
- run `verify.sh` end to end.
