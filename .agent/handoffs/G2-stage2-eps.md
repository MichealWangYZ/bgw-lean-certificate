# G2 stage 2 handoff: the eps interval from the wavefunction coefficients

Status: ready for review. This is **not accepted**. Branch `lean/g2-stage2-eps`,
forked from `bgw-e/endpoint` (5173837). Nothing is merged.

**Outcome (a) for all three q-points.** `epsinv_true_q0`, `epsinv_true_q1` and
`epsinv_true_q2` are kernel-checked.

Stage 1 trusted Python's eps interval `Q{i}.cert.epsLo/epsHi`. Stage 2 defines the
static RPA eps in Lean as a real-number function of the (unfolded) wavefunction
coefficients, and the kernel checks that this true eps lies in stage 1's box. The
composition with `Q{i}.epsinv_enclosure_q{i}` gives the eps⁻¹ enclosure of the true
eps.

| theorem | q | n | kernel-data build (sequential CPU) |
| --- | --- | --- | --- |
| `GW.Endpoint.Kernel.E1.epsinv_true_q1` | (0,0,0.5) | 76 | 395 s (+ stage-1 Q1 chain 221 s) |
| `GW.Endpoint.Kernel.E0.epsinv_true_q0` | (0,0,0.001) | 65 | built in the full run below |
| `GW.Endpoint.Kernel.E2.epsinv_true_q2` | (0,0.5,0.5) | 92 | built in the full run below |

`#print axioms` (file `GW/Endpoint/Kernel/AuditEps.lean`): the composed theorems
depend on `[propext, Classical.choice, Quot.sound]`; every `decide +kernel` data
theorem (`kok*`, `glob`, `rows*`, `tamper_*`) depends on no axioms. No `sorry`,
`native_decide`, `ofReduceBool` or `implemented_by` anywhere.

## What is proved (plain mathematics)

Data (`Eps.Input`, all integers, i.e. exact dyadics of cert.py's floats): for each of
the N_k = 32 points k of the unfolded full grid, the valence G-vectors `Gv`,
coefficients `c_v(k+q, G')` (v = 1..4) and energies `E_v(k+q)`, and the conduction
G-vectors `Gc`, coefficients `c_c(k, G2)` (c = 5..18) and energies `E_c(k)` (Ry);
`bdot` = B, `celvol` = Ω, q, the sphere `Gs` (the eps rows/columns).

Definition (`EpsSpec.lean`, `Eps.epsR`):

    M_vc(k, G)  = Σ_{G' ∈ Gv, G2 ∈ Gc, G' - G2 = G} c_v(k+q, G') c_c(k, G2)
    chi(G, G')  = 4/(N_k Ω) Σ_k Σ_v Σ_c M_vc(k,G) M_vc(k,G') / (E_v(k+q) - E_c(k))
    v(G)        = 8π / |q + G|²_B,       |x|²_B = Σ_ab x_a B_ab x_b
    eps_ij      = δ_ij - v(Gs_i) chi(Gs_i, Gs_j)

This is exactly what `cert.epsinv_iv` / `cert.mtxel_iv` compute (real flavor; M
without conjugation; row scaling of v; valence at k+q, from WFNq for q0; `fact`
over the 32-point `kfull`), with π the real π.

`Eps.sound_rows` (`EpsSound.lean`): if `kOK` holds for every k-point, `chiGlobal`
holds and `chiRows … r0 L` holds, then for the rows r0 … r0+L-1 and every column j

    epsLo_ij / 2^SE  ≤  epsR i j  ≤  epsHi_ij / 2^SE.

Generated per q-point (`Data/E{i}Check.lean`):

- `eps_in_box`: every entry of `epsR inp` lies in stage 1's box `Q{i}.cert`;
- `epsTrue := Matrix.of (epsR inp)` on `Fin Q{i}.cert.n`, `epsTrue_mem`;
- `epsinv_true_q{i}`: `IsUnit epsTrue ∧ ∀ i j, epsTrue⁻¹ i j ∈ [outLo, outHi] / 2^SO`
  — the true eps (from the wavefunctions) is invertible and its inverse is in the
  enclosure that `SigmaIV` consumes.

## What is still trusted (not proved in Lean)

1. **Symmetry unfolding and the k-set.** The coefficient lists are cert.py's
   `real_coeffs` output: rotation of the irreducible coefficients by `spec.Wfn.find`,
   removal of the global phase, per-G signs ±1 (asserted in Python), and the 32-point
   `EpsilonRun.kfull`. Lean takes these lists as the input.
2. **The exporter.** `kernel_export.py --eps IQ` runs `cert.epsinv_iv` unchanged and
   wraps `cert.mtxel_iv` (records its arguments `Gv, cv[:nv], Gc, cc[nv:nbands], Gs`
   and reads `Ev[:nv]`, `Ec[nv:nbands]`, `k` from the calling frame) and
   `iv.inverse_cw` (reads `er.cr.bdot`, `celvol`, `kfull`, `q`, `Gs`, the eps box).
   Floats are converted with `float.as_integer_ratio`, asserted exact; it also asserts
   one `mtxel_iv` call per k-point, `Gout == Gs`, and distinct G-vectors (then
   cert.py's dict lookup equals the sum in `M`). "These literals are cert.py's
   inputs" is a Python-side claim.
3. **Modeling claim.** That `epsR` is BerkeleyGW's static RPA eps (the formula
   references above are spec.py's; the Lean definition only matches cert.py/spec.py).
4. Stage-1 remainder unchanged: the Sigma side (`SigmaIV`) still consumes the Python
   interval `inv`, not a Lean object.

Not trusted any more: all of `mtxel_iv`, chi, v(q+G), eps (iv.py's interval
arithmetic on them); the hints (pair densities `H`) are checked exactly.

## Design

- **Kronecker packing for mtxel** (`EpsCheck.kOK`). With `φ(g) = g₁ + L g₂ + L² g₃`
  (L = 2H+1, all wavefunction G-vectors in a box `[lo, lo+H]³`, all `Gs` in
  `[-H, H]³`, checked by the kernel), the correlation M_vc(G) is the coefficient of
  `2^(W s(G))` in the integer product `P_v · Q_c`, `P_v = Σ c_v(G') 2^(W e(G'))`,
  `Q_c = Σ c_c(G2) 2^(W f(G2))` (sign-split into two ℕ packs each). One GMP product
  of ~70 KB integers replaces #Gs × #G multiply-adds. Digits are read with a bias
  `Σ 2^(W-1) 2^(W s)` (`digit_int`), exact because `l1(c_v) l1(c_c) < 2^(W-1)` is
  checked; φ is injective on the differences that occur (`phi_zero`,
  `Cfg.slot_iff`: components of `Gv - Gc - G` are bounded by 2H < L). W = 232 bits (2·113 + log).
- **Packed chi rows** (`accRows`, `chiRows`). `X_ij = Σ_p D_p m_p(G_i) m_p(G_j)`:
  per pair p the row vector `V_p = Σ_j m_p(G_j) 2^(W2 j)` (sign-split, Horner) is
  added to row accumulator i with weight `D_p m_p(G_i)`; row i's entries are the
  base-2^W2 digits (W2 = 528 for q1). 1792 × 76 bignum axpys instead of 10M
  multiply-adds.
- **The inexact steps** are floor divisions whose inequalities the proof uses:
  `D = ⌊2^(SD+SEn)/(e_c - e_v)⌋` (SD = 64) brackets `2^SD/(E_c - E_v)` within 1
  (`dval_bounds`); the error `|Σ (ρ 2^SD - D) m m'| ≤ N_pairs Mmax²` (`Y_bound`);
  `u = v(G)·4/(N_k Ω) = 32π/(N_k Ω |q+G|²)` bracketed by `⌊32·πlo·2^…/(10²⁰ N_k Ω N)⌋`
  and `⌊…πhi…⌋ + 1` (`u_bounds`), with `Real.pi_gt_d20`/`Real.pi_lt_d20`
  (π ∈ (3.14159265358979323846, 3.14159265358979323847)). The final test per entry
  compares `lo ≤ δ + u y ≤ hi` at both ends of u and y in ℕ (`entryOK`, `combine`).
- **Hints**: `H t v c j = m_vc(k_t, G_j)` exactly (scale 2^-226). They are the
  interface between the per-k-point theorems and the chi theorems (the kernel cannot
  pass computed values between declarations); `kOK` checks them digit by digit.
- **Module layout** (`kernel_export.lean_eps`): `E{i}Cfg` (Gs, checker parameters),
  `E{i}K{m}` (data + hints + `kOK` theorem for 2 k-points each, two import chains),
  `E{i}Inp` (the `Input`, the hint table, `glob : chiGlobal`), `E{i}R{c}` (19 rows
  each, one chain), `E{i}Check`, `E{i}Tamper`. Build order is serialized for memory:
  stage 1 → q0 → q1 → q2 (`E0Cfg` imports `Q{0,1,2}Check`, `E{i}Cfg` imports
  `E{i-1}Check`).
- All hot-path arithmetic is ℕ (the kernel has GMP only for `Nat`); signed data are
  destructured once with `Int.rec` (`ipos`, `ineg`, `zeq`, `zleS`, `zgeS`).

## Measurements (q1, n = 76; one module at a time, `lake env lean`, wall / peak RSS)

| module | content | wall | RSS |
| --- | --- | --- | --- |
| `E1K0..K15` (×16) | 2 k-points each: elaboration ≈ 9 s, `kOK` ≈ 3 s per k-point | 15.6 s each (250 s) | 3.3 GB |
| `E1Inp` | Input + hint table, `chiGlobal` (1792 pairs × 76) | 27 s | 5.0 GB |
| `E1R0..R3` | 19 rows each | 26 / 28 / 30 / 32 s | 6.0–7.1 GB |
| `E1Check` | assembly | 2 s | 2.3 GB |
| `E1Tamper` | negative controls | 24 s | 5.6 GB |

Total q1 ≈ 395 CPU-s (6.6 min) of which ≈ 150 s is literal elaboration. For
comparison the direct evaluation would be ≈ 22.5M (mtxel) + 10M (chi)
multiply-adds, i.e. 50 CPU-min at stage 1's 1.1e4/s.

Single-operation measurements (kernel, `decide +kernel`):

- packing one band (165 coefficients) ≈ 60 ms; one product of two ~70 KB packs
  ≈ 1–2 ms; one digit ≈ 0.25 ms; `kOK` of one k-point (56 pairs, 4256 digits)
  ≈ 3.2 s.
- `Int` `+` on 230-bit literals ≈ 0.6 ms vs `Nat` ≈ 0.02–0.1 ms (hence the ℕ design).
- Data elaboration: 11 MB of source for q1 (hints ≈ 2/3); ≈ 9 s per 2-k-point
  module.

## Failed attempts / pitfalls (important for any further kernel work)

- **Kernel cache-key collisions for literals with ≥ 64 trailing zero bits.** In
  Lean 4.19 two Nat literals that agree in their low 64 bits give colliding cache
  keys; data at a common scale 2^S (every hint has ~100 trailing zeros) made each
  check superlinear in the number of values: 16 lists of 76 values took 3.1 s instead
  of 0.11 s (27x; same values without the zero low limb: 0.11 s). Fix: literals are
  written `zp m t` / `zn m t` = ±(m 2^t) with odd m (`Eps.zp`, `Eps.zn`). Stage 1's
  data (`Q*.lean`, common scale 2^S) has the same property; this is the likely cause
  of stage 1's "superlinear rows in one declaration" (7x) — rewriting its literals
  this way may speed stage 1 up substantially (not done: out of scope).
- `m <<< t` as literal syntax elaborates ~4x slower than the function application
  `zp m t` (46 s vs 11 s per module).
- `List.all`/`List.length` are fine; the earlier "slow `m.all`" was the collision
  above, not structural recursion.
- A single declaration for the whole chi check (all 76 rows) built but peaked at
  13.8 GB; split into 19-row blocks (6–7 GB each), one block chain at a time.
- A first `pairStats` fold with a (Bool × ℕ × ℕ) state was replaced by `pairsOK`
  (nested `all2`) and `sum3` (easier proofs, same speed).
- `if mode = 0 then … else …` inside a checked function slowed the kernel 3x in a
  test (avoid runtime switches in kernel-evaluated code).
- Build variance: the first run of a file is up to 2.5x slower (cold page cache);
  numbers above are warm.

## Full build (cold stage 1 + stage 2, this worktree)

- `nice lake build GW`: PASS, 3:51 wall, 6.7 GB peak.
- `nice lake build GWKernelData`: PASS, **23:03 wall, 2251 CPU-s, 9.9 GB peak**
  (the peak is a q2 row block, n = 92). This covers stage 1 (≈ 13 CPU-min) plus stage 2
  for q0, q1 and q2 (≈ 24 CPU-min), serialized.
- `lake env lean GW/Audit.lean`: the new Eps lemmas depend on `[propext, Classical.choice, Quot.sound]`.
- `lake env lean GW/Endpoint/Kernel/AuditEps.lean`: `epsinv_true_q{0,1,2}` and `eps_in_box`
  depend on `[propext, Classical.choice, Quot.sound]`; the data/tamper theorems depend on no axioms.
- `lake build Main && lake env lean scripts/CheckAxioms.lean`: `AXIOM AUDIT PASSED: 4093
  theorems`. It covers 73 `E*` data modules (3:57). `Main` must be built first:
  `verify.py` builds the default targets before the audit.
- Exact Python mirror (`--simulate`): no entry is outside the stage-1 box. The minimum
  margin, as a fraction of the box width, is 0.467 (q0), 0.466 (q1) and 0.450 (q2)
  at SD = 64.
- If memory is tight: the q2 row blocks need about 10 GB. Pass `--eps-rows 12`
  to the exporter to lower this.

## Negative controls (`Data/E{i}Tamper.lean`, in `GWKernelData`)

- `tamper_coef`: conduction coefficient 0 of band 0 at k-point 0 with one bit flipped
  (bit 85 of the 105-bit integer, i.e. a relative change ≈ 2^-20) → the kernel proves `kOK … = false`; `control_coef`: the same
  expression with the original coefficient → `true`.
- `tamper_box`: the box collapsed to its upper ends → `chiRows … 0 1 = false`.

## Commands

```
cd ../lean-g2b && source scripts/env.sh
R=<scratch>/fix/run
# capture (runs cert.epsinv_iv, ~5 s per q), exact data, hints, Lean modules; --simulate
# runs an exact Python mirror of chiOK first (0 entries outside, min margin 0.45-0.48)
python3 bgw/endpoint/kernel_export.py $R --eps 0 --eps-npz CAP0.pkl --simulate --lean
python3 bgw/endpoint/kernel_export.py $R --eps 1 --eps-npz CAP1.pkl --simulate --lean
python3 bgw/endpoint/kernel_export.py $R --eps 2 --eps-npz CAP2.pkl --simulate --lean
nice lake build GW                   # default target, now incl. EpsCheck/EpsSpec/EpsSound
lake env lean GW/Audit.lean          # new section at the end
nice lake build GWKernelData         # stage 1 + stage 2, serialized (see Full build)
lake env lean GW/Endpoint/Kernel/AuditEps.lean
lake env lean scripts/CheckAxioms.lean   # exhaustive audit, imports the E* roots
```

## Files

- New: `GW/Endpoint/Kernel/{EpsCheck,EpsSpec,EpsSound,AuditEps}.lean`,
  `GW/Endpoint/Kernel/Data/E{0,1,2}{Cfg,K*,Inp,R*,Check,Tamper}.lean` (generated),
  this handoff.
- Edited: `bgw/endpoint/kernel_export.py` (stage-2 section, `--eps`), `GW.lean`
  (3 imports), `GW/Audit.lean` (section at the end), `lakefile.toml` (roots of
  `GWKernelData`), `scripts/CheckAxioms.lean` (imports).

## Next action

- Review the spec definition `EpsSpec.epsR` against cert.py/spec.py and the capture.
- Possible reductions: hint size (≈ 2/3 of the 33 MB of data) — e.g. hints only at
  the digits actually needed, or per-k chi partial rows; stage-1 literal format
  (collision fix above).
- Stage 3 candidates: Lean-side unfolding (rotations of the irreducible coefficients;
  the per-G signs), and making `SigmaIV`'s input the Lean `inv`.
