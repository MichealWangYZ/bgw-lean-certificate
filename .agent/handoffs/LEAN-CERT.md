# LEAN-CERT handoff: Lean soundness lemmas for the E1.4 certificate

Status: ready for review, **not accepted**. Branch `lean/cert-lemmas`, forked
from `bgw-e/endpoint` at 7a4b7a5 (which already contains the near-pole
`w/sexcut` fix). Not merged anywhere.

Scope: new files `GW/Endpoint/CertInterval.lean`, `GW/Endpoint/CertInverse.lean`,
`GW/Endpoint/CertSexcut.lean`; three import lines in `GW.lean`; one appended
section of `#print axioms` lines (54 theorems) at the end of `GW/Audit.lean`.
Nothing else edited.

## What is proved (plain math)

All statements are over ℝ. "x ∈ [lo, hi]" is `x ∈ Set.Icc lo hi`.

### `GW/Endpoint/CertInterval.lean` (namespace `GW.Endpoint.Cert.IV`)

Rounding model `Rounding` = functions `down, up : ℝ → ℝ` with
`down r ≤ r ≤ up r`. An endpoint `_down(expr)` in iv.py is `down r` for the
exact real value `r` of `expr`. For x ∈ [lo, hi], y ∈ [lo', hi']:

- `neg_mem`: −x ∈ [−hi, −lo].
- `add_mem`: x + y ∈ [down(lo + lo'), up(hi + hi')].
- `sub_mem`: x − y ∈ [down(lo + −hi'), up(hi + −lo')] (iv.py sub is `self + (-o)`).
- `min4_le_mul`, `mul_le_max4`, `mul_mem`: x·y ∈ [down(min of lo·lo', lo·hi',
  hi·lo', hi·hi'), up(max of the same)].
- `sqr_mem`: x·x ∈ [if lo ≤ 0 ≤ hi then 0 else down(min(lo², hi²)), up(max(lo², hi²))].
- `recip_mem`: if ¬(lo ≤ 0 ∧ 0 ≤ hi): 1/x ∈ [down(1/hi), up(1/lo)].
- `div_mem`: x/y = x · recip(y) with the four-product rule on the recip endpoints.
- `sqrt_mem`: √x ∈ [max(down √lo, 0), up √hi].
- `abs_le_mag`: |x| ≤ max(|lo|, |hi|);
  `abs_mem`: |x| ∈ [if straddle then 0 else min(|lo|,|hi|), max(|lo|,|hi|)].
- `hull_mem`: x in either interval ⇒ x ∈ [min lo lo', max hi hi'].
- `select_mem`: for a real condition c and Booleans ct, cf with ct ⇒ c and
  cf ⇒ ¬c, `if c then xa else xb` lies in the np.where interval
  (a if ct, else b if cf, else hull).
- `certainly_{lt,le,gt,ge}_sound`: e.g. hi < lo' ⇒ x < y for all enclosed x, y.
- `ne_zero_of_not_contains_zero`.
- `sumDown`/`sumUp`, `sum_le_sumUp`, `sumDown_le_sum`, `sum_mem`: the
  sequential sum `s₀ = l 0, s_{j+1} = down(s_j + l(j+1))` (and the up version,
  = `_row_sum_up`) encloses ∑_{j≤N} x_j.
- `matmulUpAcc`, `sum_le_matmulUpAcc`: `out₀ = 0, out_{j+1} = up(out_j + up(t_j))`
  (`_matmul_up`) is ≥ ∑_{j<N} t_j.

### `GW/Endpoint/CertInverse.lean` (namespace `GW.Endpoint.Cert`)

Index type any `Fintype` with `DecidableEq` (includes `Fin n`).
`Dom A F` ⇔ |A i j| ≤ F i j ∀ i j; `RowLe Y c` ⇔ ∑_j Y i j ≤ c ∀ i;
`absM R` = entrywise |R|.

- `det_one_sub_ne_zero`: F ≥ |E|, all row sums of F ≤ β < 1 ⇒ det(1 − E) ≠ 0.
- **`neumann_cw`**: F ≥ |1 − R A|, row sums of F ≤ β < 1, P ≥ F·|R|, row sums
  of P ≤ ρ ⇒ A is a unit and ∀ m i j,
  |A⁻¹ i j − R i j| ≤ (∑_{k=0}^{m} F^k P) i j + β^(m+1) ρ / (1 − β).
- `neumann_cw_set`: same for every A0 in a set S with ∀ A0 ∈ S, F ≥ |1 − R A0|.
- `pow_le_of_chain`: b 0 ≥ β, b(k+1) ≥ b k · β, β ≥ 0 ⇒ b k ≥ β^(k+1)
  (the `bpow` loop).
- **`inverse_cw_sound`**: `neumann_cw` hypotheses plus T 0 ≥ P,
  T(k+1) ≥ F·T k (k < m), S ≥ ∑_{k≤m} T k, bpow ≥ β^(m+1), 0 < d ≤ 1 − β,
  tail ≥ bpow·ρ/d, B ≥ S + tail ⇒ A0 unit and R − B ≤ A0⁻¹ ≤ R + B entrywise.
  These hypotheses are exactly the quantities `inverse_cw` computes
  (iv.py:259-286), each discharged by the CertInterval lemmas.
- `balance s A i j := A i j · (s j / s i)` (= cert.py `eps * scale`,
  `scale = s[None,:]/s[:,None]`); `balance_eq`: = diag(s)⁻¹ A diag(s);
  `det_balance`: same determinant; **`balance_inv`**: (balance s A)⁻¹ =
  balance s A⁻¹; `balance_mem`: s > 0 preserves an entrywise enclosure;
  **`inv_mem_of_balanced`**: s > 0, balanced matrix invertible,
  (balance s A)⁻¹ i j ∈ [lo, hi] ⇒ A⁻¹ i j ∈ [lo·(s i/s j), hi·(s i/s j)].
  `s i / s j` is cert.py's `back = s[:,None]/s[None,:]`: the scaling side in
  cert.py:125-129 is correct.

### `GW/Endpoint/CertSexcut.lean` (namespace `GW.Endpoint.Cert`)

Real flavour, w > 0, s = sexcut > 0.

- `sexcut_generic_iff`: I ≠ 0, x² ≠ w²: s|I| < |w² I/(x² − w²)| ⇔ |x² − w²| < w²/s.
- `sexcut_near_iff`: I ≠ 0, x + w ≠ 0: s|I| < |−I w/(2(x + w))| ⇔ |2(x + w)| < w/s.
- `sexcut_nearSource_iff`: the same for the source expression
  −(w² I) delw / (4 w² (delw + 1/2)) (x ≠ w), via `GW.Endpoint.ssxNear_eq`.
- `srcSsx` (source branch structure + clamp, mtxel_cor.f90:1817-1848) and
  `certSsx` (cert.kernel's division-free branch/clamp tests and values).
  **`certSsx_eq_srcSsx`**: for all thresholds γ², limitone, TOL_Zero, all I,
  w > 0, s > 0, x ≠ w, x + w ≠ 0: certSsx = srcSsx. Covers every branch
  outcome and I = 0 (both 0).
- `certSsx_at_neg`: at x = −w cert.py's value is 0 (test certainly clamps).
- `certSsx_at_w`: at x = w (γ² ≥ 0) cert.py's value is −I/4.

`cert.py` now matches the pinned near-pole threshold: line 321
`lim_n = wt * I.exact(1.0 / SEXCUT)` = w/s, with `den_n = 2 (wx + wt)`.

## Findings about cert.py / iv.py

1. **x = w exactly (near-pole branch): cert value ≠ production value.** At
   wx = wtilde the Fortran (complex `wdiff`, `cden`, `delw`) computes
   `rden = 1/0 = Inf`, `delw = w·0·Inf = NaN`, `delwr = NaN`; both
   `wdiffr > limittwo` (0 > 0.25) and `delwr > TOL_Zero` (NaN) are false, so
   `ssx = 0`, `sch = 0` (mtxel_cor.f90:1819-1843). cert.py (lines 317, 329) takes
   `near_cond_t` because `wt² > 0 = wdiffr·TOL_ZERO`, and returns
   −I·w/(2·2w) = −I/4 (`certSsx_at_w`). Reproduced: `cert.SigmaIV.kernel(None,
   I.exact(2.0), m, True)` with w = 2, I = 0.3 gives −0.075; a numpy emulation
   of the Fortran statements gives 0.0 (emulation, not the compiled binary).
   The spec (exact reals) is undefined at this point; cert.py uses the
   continuous extension. Consequence: `certSsx_eq_srcSsx` must exclude x = w;
   it matters only if a production wx equals a wtilde exactly (a single point,
   but a jump of I/4 there). Decision for the owner: document as a spec
   choice, or make the cert hull with 0 when the wdiff interval contains 0.
2. **x = −w (hole-branch pole)**: Fortran gives NaN (generic branch for w > 1/4,
   near-pole branch otherwise, exact reals); cert.py gives 0. Not a
   disagreement with a finite source value; stated as `certSsx_at_neg`.
3. **Power-of-two balancing is not always exact (cert.py:126 and :129).**
   `I(eps.lo * scale, eps.hi * scale)` and `I(invb.lo * back, invb.hi * back)`
   are unrounded float products. Multiplying by 2^k is exact only if the
   result is not subnormal. Counterexample: lo = 3·2⁻¹⁰⁷⁴, scale = 0.5 gives
   `lo*scale` = 2·2⁻¹⁰⁷⁴ > 1.5·2⁻¹⁰⁷⁴ (lower endpoint rounded *up*; checked with
   `fractions.Fraction`). Symmetrically hi = −3·2⁻¹⁰⁷⁴ is rounded down. In
   practice entries that small do not occur (and exact zeros are fine), but
   the code does not check; wrapping these in `_down`/`_up` or asserting no
   subnormal results would close it. The Lean lemmas assume exact scaling.
4. `inverse_cw` never checks `down(1 − β) > 0`; the Lean theorem needs
   0 < d. Under IEEE it holds automatically for float β < 1 (1 − β ≥ 2⁻⁵³ is
   exact by Sterbenz for β ≥ 1/2, ≥ 1/2 otherwise), so no counterexample; a
   one-line assert would make it a checked fact.
5. Rounding directions of every iv.py op used by the certificate are outward
   (listed in CertInterval's docstring). `rad()` (iv.py:84-86) is not outward
   in the subnormal range (`0.5*hi` can round) but it is not used for
   soundness in cert.py.
6. The balancing scaling side is correct (point above under CertInverse).

## What remains unproved (named gaps)

- IEEE hypothesis: numpy float64 ops are correctly rounded binary64 with
  gradual underflow, so pred(fl r) ≤ r ≤ succ(fl r), and fl is monotone (used
  to read `_down(p.min())` as down(min of exact products)). iv.py asserts
  absence of flush-to-zero at import; the rest is trusted.
- Python-to-Lean correspondence: that iv.py/cert.py compute exactly the
  endpoint expressions and hypotheses stated here (including that the interval
  `E` in `inverse_cw` encloses 1 − R A0 via `matmul`, which is entrywise
  composition of `add_mem`/`mul_mem`/`sum_mem`, not formalized at matrix level).
- Fortran-to-Lean correspondence of `srcSsx` (hand transcription of
  mtxel_cor.f90:1817-1848, real flavour); the IEEE NaN behaviour of the
  Fortran at x = ±w is argued in prose, not in Lean.
- `modes()` (wtilde, keep, TOL_Small thresholds, invalid modes) and everything
  outside `kernel`'s ssx and `inverse_cw`: not covered.
- `certSsx` covers kept modes (`keep = True`); for `keep = False` cert.py
  returns 0 by construction.

## Commands and results

```
source scripts/env.sh
lake env lean GW/Endpoint/CertInterval.lean   # clean
lake env lean GW/Endpoint/CertInverse.lean    # clean, ~3 s
lake env lean GW/Endpoint/CertSexcut.lean     # clean, ~2 s
lake build GW                                 # Build completed successfully
lake env lean GW/Audit.lean                   # 54 new lines, all [propext, Classical.choice, Quot.sound]
BGW_TOOLCHAIN=$HOME/bgw-src/mm/envs/bgw bash scripts/verify.sh
```

verify.sh result: every Lean step passed (build, named-theorem print, "Audit
all project theorem dependencies", demo/evaluator/LL evaluations). The
scientific gate then FAILED on a 600 s timeout of the Python unittest batch
(tests.test_bgw_export ... tests.test_weighted_audit). This branch changes no
Python; the machine was shared with another long Python job at the time. Not
re-run in isolation; the reviewer should re-run it on a quiet machine.

`bash scripts/verify.sh --gate workflow`: 13/14 pass; FAILS
`tests/test_provenance_committed.py::test_current_manifests_match_the_files_as_they_stand`
because `bgw/weighted_audit/PROVENANCE-R6.txt` (lines 55-56) vouches for the
sha256 of `GW.lean` and `GW/Audit.lean`, which this task is required to edit.
The manifest is outside this task's write scope, so it was not touched. The
integrator must regenerate those two digest lines when merging (the parallel
QPUnique change to the same two files needs the same).

```
```

Setup: worktree `../lean-cert`, `.lake/packages` and `.tools` symlinked to the
main checkout (both gitignored).

## Failed attempts

- First CertInverse version lacked `import Mathlib.Data.Real.Basic`
  (NonsingularInverse does not bring ℝ): elaboration hung >10 min on failed
  instance searches instead of erroring quickly. Adding the import fixed it.
- `Mathlib.Analysis.SpecialFunctions.Pow.NNRpow` olean is not built in the
  shared package cache; removed the (unneeded) import.
- `split_ifs` over the nested source/cert `if`s split the clamp conditions
  too; replaced by explicit `by_cases` on the branch conditions.

## Next action

Reviewer: check the statement fidelity of `inverse_cw_sound` and `certSsx`
against iv.py:259-286 and cert.py:296-331; decide findings 1 and 3.

## Integration note (supervisor session, 2026-09-23)

Merged into bgw-e/endpoint. Findings 1, 3, 4 fixed in cert.py / iv.py
(commit 69e16ee); CertSexcut updated to the fixed kernel (`certSsx_at_w` now
states ssx = 0, the IEEE Fortran value; commit edf80c5). Certificates
re-generated: O1 enclosure [15.40575235, 15.40575367] meV, roots unchanged.
Provenance digests of GW.lean / GW/Audit.lean re-signed at integration.
