# A3 dimer part 2 handoff: Σ_c derived from i G0 W_c; U² coefficients and SOX

Status: **ready for review, not accepted.** Branch `lean/dimer-sigma`, forked
from `bgw-e/endpoint` at 7a4b7a5. Worktree `.claude/worktrees/lean-dimer2`.

## Summary

- **Task 3 is done with the analytic route (a).** Nothing is assumed any more
  between G0, W_c and `sigmaSinglePole`. The damped Fourier transform is a
  real Lebesgue integral over ℝ, and the η → 0⁺ limit is a real `Tendsto`.
  `sigmaC`, the function used by `sigmaC_orbital`, `qp_removal` and `qp_addition`,
  is now proved to be the η → 0⁺ limit of `∫_ℝ e^{iωτ-η|τ|} · i G0(τ) W_c(τ) dτ`.
  The G0 and W_c in that formula are the physical time-domain objects, and their
  own transforms are proved to be the HF resolvent `(ω - F)⁻¹` and the RPA `Wc`
  already in `HubbardDimer.lean`. Existing files are unchanged. No existing
  proof was touched.
- **Task 4 is done.** The orbital-basis two-electron integrals are proved by
  transforming the site-basis contact interaction. The second-order direct
  (ring) and exchange (SOX) self-energies are proved as finite sums. Their gap
  contributions are `+U²/(4t)` and `-U²/(8t)`. With explicit O(U³)/O(U⁴)
  remainders:
  gap_GW = HF + direct, gap_exact = HF + direct + SOX, and
  gap_GW - gap_exact = -SOX = +U²/(8t).

## Theorems (namespace `GW.Endpoint.HubbardDimer`)

### `GW/Endpoint/HubbardDimerSigma.lean` (Task 3)

Definitions:
- `ftDamped η f ω = ∫ τ : ℝ, exp(iωτ - η|τ|) f(τ)`
- `expSum`, `twoSided lp ln τ = if 0 < τ then Σ c e^{-iaτ} else Σ d e^{-ibτ}`
- `G0time orbs τ i j = -i Σ_k φ_k(i)φ_k(j)[θ(τ)(1-f_k) - θ(-τ)f_k] e^{-iε_k τ}`
  (τ = 0 takes the τ<0 branch; it is one point)
- `WcTime R Ω τ i j = -i R_ij e^{-iΩ|τ|}`
- `sigmaTime R Ω orbs τ i j = i · G0time · WcTime`
- `dimerOrbs t U = [(phiB, epsB, true), (phiA, epsA, false)]` (the list `sigmaC` uses)
- `g0HF`, `sigmaOrbitalFT`

Theorems:
- `integral_Ioi_osc` / `integral_Iic_osc` (η > 0): `∫_0^∞ e^{(i(ω-a)-η)τ} = i/(ω-a+iη)`,
  `∫_{-∞}^0 e^{(i(ω-b)+η)τ} = -i/(ω-b-iη)`. Both come from Mathlib's
  `integral_exp_mul_complex_Ioi/Iic`.
- `ftDamped_twoSided` (η > 0): `ftDamped η (twoSided lp ln) ω = Σ c_p i/(ω-a_p+iη) + Σ d_q (-i)/(ω-b_q-iη)`.
  This is exact, and integrability is proved.
- `ftDamped_twoSided_limit`: the η → 0⁺ limit is `Σ c_p i/(ω-a_p) + Σ d_q (-i)/(ω-b_q)`.
  It needs only `ω ≠ a` at poles whose coefficient is nonzero.
- `WcTime_eq`, `G0time_eq`, `sigmaTime_eq`: each time-domain object is a two-sided
  exponential sum. For Σ, particles go forward with e^{-i(ε+Ω)τ} and holes go
  backward with e^{-i(ε-Ω)τ}.
- **`sigmaSinglePole_eq_limit`** holds for any R, Ω and orbital list, and any real ω
  with `ω ≠ ε_k - Ω` (occupied k) and `ω ≠ ε_k + Ω` (empty k):
  `Tendsto (η ↦ ftDamped η (sigmaTime R Ω orbs · i j) ω) (𝓝[>] 0) (𝓝 (sigmaSinglePole R Ω orbs ω i j))`.
- **`sigmaC_eq_limit`** is the dimer instance with `resW`, `hRPA`, `dimerOrbs`. It
  holds for every real ω except `epsB - h` and `epsA + h`.
- **`sigBB_sigAA_eq_limit`** (via `sigmaOrbitalFT_limit`): the orbital matrix
  elements of the transform tend to `sigBB t U E` and `sigAA t U E`. These are
  exactly the functions in `qp_removal` and `qp_addition`.
- `WcTime_limit` (t > 0, U ≥ 0, ω ≠ ±h): the transform of `WcTime resW hRPA` tends to `Wc t U ω`.
  This is the proved RPA W_c.
- `G0time_limit`: the transform of G0time tends to `Σ_k φ_kφ_k^T/(ω-ε_k)`.
- `g0HF_resolvent` (ω ≠ epsB, epsA): `(ω·1 - fock t U) * g0HF t U ω = 1`.
- Small helpers: `list_sum_mul_left/right`, `list_sum_map_add`, `ofReal_list_sum`,
  `setIntegral_expList`, `I_mul_negI`, `negI_mul_I_div`, `I_mul_negI_div`.

### `GW/Endpoint/HubbardDimerSecondOrder.lean` (Task 4)

Definitions:
- `orb = ![phiB, phiA]`, `epsOrb = ![epsB, epsA]`
- `vSite U i j k l = U` if i=j=k=l, else 0
- `eri U p q r s = Σ_{ijkl} φ_p(i)φ_q(j)φ_r(k)φ_s(l) vSite`
- `sig2dir`, `sig2x`: the formula from the `second_order.py` docstring, split into its
  "2" part and its "-1" part, with occ = {B} and vir = {A}
- `gap2dir = Σ2dir_AA(epsA) - Σ2dir_BB(epsB)`, and `gap2x` likewise

Theorems:
- `eri_eq`: `<pq|rs> = U/2` if p+q+r+s is even (counting A = 1), else 0.
  This is derived from the site basis, not assumed.
- `sig2dir_B = -U²/(8t)`, `sig2dir_A = U²/(8t)`, `sig2x_B = U²/(16t)`, `sig2x_A = -U²/(16t)`.
- **`gap2dir_eq`**: `gap2dir = U²/(4t)`. **`gap2x_eq`**: `gap2x = -U²/(8t)`.
- `hf_U2_coeff`: `gapHF = 2t` exactly, so its U² coefficient is 0.
- `exact_expansion` (0 ≤ U ≤ 2t): `-U⁴/(512t³) ≤ gapExact - 2t - U²/(8t) ≤ 0`.
- **`exact_U2_coeff`** (ii):
  - `|gapExact - (gapHF + gap2dir + gap2x)| ≤ U⁴/(512t³)` on [0, 2t]
  - `(gapExact - gapHF)/U² → 1/(8t)` as U → 0⁺
- **`gw_U2_coeff`** (i):
  - `|gapGW - (gapHF + gap2dir)| ≤ U³/(4t²)` on [0, t]
  - `(gapGW - gapHF)/U² → 1/(4t)`
- **`gw_error_is_minus_sox`** (iii):
  - `|(gapGW - gapExact) + gap2x| ≤ 3U³/(16t²)` on [0, t]
  - `-gap2x = U²/(8t)`
  - `(gapGW - gapExact)/U² → 1/(8t)`
- `sigBB_second_order`, `sigAA_second_order`: `sigBB(epsB)/U² → -1/(8t)` and
  `(sigBB(epsB) - Σ2dir_BB(epsB))/U² → 0`, and the same for AA with +1/(8t).
  So GW's Σ_c at the HF energies equals the second-order direct self-energy at
  order U². It contains no exchange.
- Helpers: `tendsto_div_sq_of_bound`, `hRPA_continuous`, `hRPA_zero`.

Sign bookkeeping: the Σ2 values are evaluated at the HF energies, where
`E + e_a - e_r - e_s = 2epsB - 2epsA = -4t` and `E + e_r - 2e_a = +4t` exactly,
with no U dependence.

## Not proved, and limitations

- The transform is at T = 0, time-ordered, with a single-pole W_c. The
  convergence factor e^{-η|τ|} is applied to Σ(τ), the product. Putting separate
  infinitesimals on G0 and W instead gives the same limit off the poles, but that
  equivalence is not formalized. The limit is pointwise for real ω off the poles.
  It is not a distributional statement at the poles.
- Σ(τ) = i G0(τ) W_c(τ) is taken as the definition of the GW self-energy in time.
  This is the standard definition, not a derivation from Hedin's equations.
  The product is taken pointwise in the site indices (Σ_ij = i G_ij W_ij).
- The Task 4 "diagrammatic" identification is by the explicit second-order
  formulas (the `second_order.py` docstring), evaluated on this model. There is
  no general diagram framework. The Σ2 formula itself (with its 2 and -1
  spin factors) is taken as a definition from the textbook closed-shell
  expression. It is not derived from Wick's theorem here. *Superseded for
  this model (G3, 2026-09-25):* `HubbardDimerExactSigma.lean` derives the
  exact Σ from the Fock-space Lehmann G and proves Σ_exact = U/2 + sig2dir +
  sig2x for every U (off poles), so the formula with its spin factors is a
  theorem for the dimer; the general statement is G4.
- O(U³) remainders are explicit only on U ∈ [0, t] (GW) and [0, 2t] (exact).
  The limits are one-sided (U → 0⁺), like the existing `gw_error_leading`.
- These results are for the two-site model only.
- Doc notes in `GW/Endpoint/HubbardDimer.lean` (header, and the `sigmaSinglePole`
  docstring saying "NOT formalized") and in `.agent/handoffs/A3-dimer.md` are now
  out of date. They are outside my write scope, so I left them for the supervisor.
  Suggested wording: "derived in HubbardDimerSigma.lean (`sigmaC_eq_limit`)".

## Commands and results (worktree root)

```
ln -s <repo>/.tools .tools; source scripts/env.sh
python3 bgw/endpoint/a3_dimer/second_order_dimer.py   # ALL OK, 1.3 s
lake env lean GW/Endpoint/HubbardDimerSigma.lean        # clean
lake env lean GW/Endpoint/HubbardDimerSecondOrder.lean  # clean
lake build GW                                           # Build completed successfully (3m38s)
lake env lean GW/Audit.lean                             # 39 new lines, all [propext, Classical.choice, Quot.sound]
python3 -m unittest tests.test_endpoint_a3              # 7 tests OK
bash scripts/verify.sh                                  # FAIL: see below
```

`scripts/verify.sh` result (machine load average about 58, because other
sessions were running the same suite):
- All Lean stages passed. That includes the build, the named and exhaustive
  axiom audit, the demo, the oracle, the BGW exports, and the LL evaluators.
- The scientific-gate unittest step then hit verify.py's 600 s subprocess
  timeout.
- I re-ran the same scientific module list by hand without the timeout:
  `Ran 573 tests in 541 s, OK (skipped=2)`.
- The workflow gate, run by hand, has 1 failure:
  `tests.test_provenance_committed.test_current_manifests_match_the_files_as_they_stand`.
  `bgw/weighted_audit/PROVENANCE-R6.txt` pins sha256 digests of `GW.lean` and
  `GW/Audit.lean`. Both files necessarily change when new modules are added.
  Updating that manifest is outside my write scope. The supervisor must
  re-sign it after merge; that is also where the QPUnique change will land.

The numeric script `bgw/endpoint/a3_dimer/second_order_dimer.py` was run before
any proof:
1. It computes the damped FT of i G0 W_c and of W_c by quadrature at finite η
   (0.5 to 1) and compares with the closed form. Worst error is 1.9e-10.
2. It transforms the ERIs from the site tensor with einsum and checks them
   against the U/2-parity form (≤ 3e-16).
3. Direct gap = U²/(4t) and SOX gap = -U²/(8t) at three (t, U) points (≤ 3e-16).
4. The sympy U² coefficients are: exact 1/(8t), GW 1/(4t), HF 0 (and no U¹ term).
   They match direct and direct + SOX.

Hand mutations: each file was copied to the scratchpad with one change and
checked with `lake env lean`. Every mutation was rejected:
- W_c without |τ| (`e^{-iΩτ}`): 3 errors (`sigmaTime_eq`, both `*_limit`)
- G0 θ-branches swapped: 4 errors
- FT kernel `e^{-iωτ}`: 1 error (`ftDamped_twoSided`)
- Σ = G W without the `i`: 2 errors
- SOX sign flipped: 1 error (`sig2x_B`)
- direct factor 2 → 1: 1 error (`sig2dir_B`)
- vSite U → 2U: 1 error (`eri_eq`)

These were not added to `mutate_lean.py`.

## Failed attempts / notes

- `ring` does not close goals that contain `I`. `I_sq` has to be used
  explicitly: `linear_combination c * I_sq`, or `ring_nf; simp only [I_sq, I^3 = -I]`.
- `List.mem_cons_self` takes implicit arguments in this Mathlib.
- `field_simp` needed `t ≠ 0` in context. Without it, it left `U²·t·t⁻¹`.
- In this Mathlib, `tendsto_list_sum` exists as the additive form of
  `tendsto_list_prod`. There is no `Complex.ofReal_list_sum`, so a local
  induction lemma was added.
- The first form of the limit lemma required ω to avoid ALL four poles
  ε_k ± Ω. I weakened it to "poles with nonzero coefficient", so the dimer
  statement excludes only the two physical poles.

## Integration note

The coordinator is adding `GW/Endpoint/QPUnique.lean` on `bgw-e/endpoint`, with its
own `GW.lean` import and Audit section. My additions are two import lines after
`GW.Endpoint.HubbardDimer` and a separate commented section at the end of
`GW/Audit.lean`, so the merge should be trivial.

## Next action

Supervisor review. Optionally update the out-of-date "NOT formalized" notes
(see above), add `second_order_dimer.py` to a test/gate, and add the mutations
to `mutate_lean.py`.
