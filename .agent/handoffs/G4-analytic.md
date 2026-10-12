# G4-analytic handoff: the actual Σ(ω; λ) agrees with the formal coefficients to O(λ³)

Status: **ready_for_review**. Not accepted; Claude does not accept its own work.
Branch `lean/g4-analytic` (from `bgw-e/endpoint` @ `6a609a2`), pushed; no merge.
New Lean files: `GW/Endpoint/ManyBody/Jet.lean` (37 theorems), `GroundState.lean` (49),
`Analytic.lean` (18). Existing files touched only additively: `GW.lean` (one import),
`GW/Audit.lean` (new END section, 104 `#print axioms` lines).

Exit: **(a), the analytic theorem is proved.** The gap recorded in G4-general-gw.md is
closed for real λ: the formal coefficients are proved to be the coefficients of the
second-order expansion of the actual function λ ↦ Σ(ω; λ) built from the true ground state.

## 1. Statements (plain math)

Setting and hypotheses are those of G4-general-gw.md (`n` spin-orbitals, `H0 = Σ ε_p c_p†c_p`,
`V = ½ Σ v_pqrs c_p†c_q†c_s c_r`, `hv1`, `hv2`, `OffPoles ε O ω`), plus

* `IsGround ε O`: every other `|O|`-particle basis state has energy strictly above
  `E0 = Σ_{a∈O} ε_a` (Φ is the strict ground state of `H0` in its sector). This is
  stronger than `NonDeg` (which only excludes equality), and it is needed: "ground state"
  of `H(λ)` needs Φ to be the lowest state at λ = 0.

Real (not formal) objects, `Analytic.lean` / `GroundState.lean`:

* `Hl x = H0 + x V` (real matrix); `InSec O φ`: φ is supported on `|O|`-particle states.
* `IsGroundPair x μ φ`: φ ∈ sector, φ ≠ 0, `H(x) φ = μ φ`, and `μ ≤ μ'` for every sector
  eigenpair `(μ', φ')` with φ' ≠ 0 (μ is the lowest eigenvalue of H(x) in the sector).
* `greenR x E ψ` (literally the formula of `greenT`, with real matrix inverses):
  `G_pq = [⟨ψ|c_p (ω−(H−E))⁻¹ c_q†|ψ⟩ + ⟨ψ|c_q† (ω+(H−E))⁻¹ c_p|ψ⟩]·⟨ψ|ψ⟩⁻¹`;
  `green0R = diag (ω−ε_p)⁻¹`; `sigmaR x E ψ = green0R⁻¹ − (greenR x E ψ)⁻¹`.
  `greenR_smul`: G is independent of the normalization of ψ.
* `Σ1_pq = sig1 v O p q = Σ_{a∈O} ⟨pa‖qa⟩`, `Σ2 = sig2 = dir2 + sox2 + relax` — the same
  definitions used by `sigma1_eq_HF`, `sigma2_eq_direct_add_sox_add_relax` (imported).

| theorem | statement |
| --- | --- |
| `sigma_exact_expansion` | ∃ δ > 0, ∃ K, ∀ real x with \|x\| < δ: (i) `IsGroundPair x (ER x) (psiR x)`; (ii) every ground pair `(μ, φ)` has `μ = ER x` and `φ = α ψR(x)` with `α ≠ 0` (nondegenerate ground state); (iii) `det(ω−(H−E)) ≠ 0`, `det(ω+(H−E)) ≠ 0`, `det G ≠ 0` (ω off the poles, Σ a genuine inverse); (iv) for every ground pair and all p, q: `\|Σ(ω;x)_pq − (x Σ1_pq + x² Σ2_pq(ω))\| ≤ K\|x\|³` |
| `sigma_exact_minus_gw` | same δ, K: `\|Σ(ω;x) − Σ_GW^{≤2}(x) − x²(SOX + relax)\| ≤ K\|x\|³` |
| `sigma_exact_minus_gw_brillouin` | under Brillouin (`Σ1_ra = 0`, a∈O, r∉O): `\|Σ − Σ_GW^{≤2} − x² SOX\| ≤ K\|x\|³` |
| `groundPair_psiR`, `groundPair_unique` | existence / uniqueness-up-to-scale of the sector ground pair for \|x\| ≤ δ1 |
| `eig_exact` | `H(x) ψR(x) = ER(x) ψR(x)` exactly |
| `chi_bound1/2/3`, `E_bound` | explicit: `‖χ‖ ≤ a\|x\|`, `‖χ − xψ1‖ ≤ a²x²`, `‖χ − xψ1 − x²ψ2‖ ≤ b\|x\|³`, `\|E − (E0 + xE1 + x²E2)\| ≤ c\|x\|³` (sup norm) |
| `jetM_sigmaR` | entrywise, `Σ(ω;x) − trunc₂(sigmaT)(x) = O(x³)` (`Asymptotics.IsBigO` at `𝓝 0`) |

**GW side.** In this repository G0W0 is defined only through second order: the static part
`Σ_H + Σ_x` and the time-domain `Σ_GW⁽²⁾` whose η → 0⁺ transform is `dir2` (`gw2_limit`).
There is no full RPA function λ ↦ Σ_GW(ω; λ). So the GW "function" here is by definition
the polynomial `sigmaGW2 x = x(Σ_H + Σ_x) + x² dir2`, and the GW statement is the corollary
above (exact − GW = x²(SOX + relax) + O(x³) for the actual exact Σ). An analytic statement
about the full G0W0 function would first need `W(λ) = (1 − λvχ0)⁻¹λv` and `Σ = iG0W`
formalized as functions of λ (not done; outside this task).

What is NOT claimed: analyticity (only the O(λ³) bound; the proof never needs it), complex
λ, uniformity in ω, anything beyond second order.

## 2. Proof route and reuse decisions

1. **Jets (`Jet.lean`)** instead of Taylor's theorem / analyticity. `Jet f F` :≡
   `f(x) − (F₀ + F₁x + F₂x²) =O[𝓝 0] x³`. The jet-related pairs form a subring
   `jetRing ⊆ (ℝ → ℝ) × ℝ⟦X⟧`, so `Matrix.map_mul`, `RingHom.map_det`,
   `RingHom.map_adjugate` transport products, determinants and adjugates for free;
   inverses via `jet_inv` (scalar, constant term ≠ 0) and `JetM.inv`
   (`A⁻¹ = (det A)⁻¹ • adj A` on both sides; real side uses `Matrix.inv_def` +
   `Ring.inverse_eq_inv'`, so it holds for every x, no case split). Since the actual Σ is
   built from (ψ(λ), E(λ)) by exactly the ring operations and inverses of `sigmaT`, its jet
   equals the truncation of `sigmaT` — only coefficients 0, 1, 2 of `psiT`/`ET` matter.
   Mathlib's `HasFPowerSeriesAt` / `FormalMultilinearSeries` were not used: connecting them
   to `PowerSeries ℝ` matrix inverses has no API in the pinned Mathlib, and the jet ring
   needs none.
2. **Ground state (`GroundState.lean`)** without the spectral theorem or the IFT:
   intermediate normalization ψ = Φ + χ reduces `H(λ)ψ = Eψ` to the fixed point
   `χ = λ F(χ)`, `F(χ) = Rs(V(Φ+χ) − ⟨Φ|V(Φ+χ)⟩χ)`, `Rs` = sector-restricted
   `diag((E0−E_S)⁻¹)`. For `|λ|·4‖Rs‖‖V‖ ≤ ½` it is a ½-contraction of the closed unit
   ball: mathlib `ContractingWith.exists_fixedPoint'`. The expansion of χ and E follows
   algebraically from the fixed-point equation (`Fm_expand`, `Am_psi1`: the linear part
   applied to ψ1 is exactly `psi2` of `Perturb.lean`). Simplicity/lowest: a gap argument in
   the sup norm (`eq_smul_psiR`): any sector eigenvector with μ ≤ E(λ) satisfies
   `‖φ − φ_O ψ‖ ≤ ½‖φ − φ_O ψ‖`. Norms: mathlib's Pi sup norm plus the crude bound
   `‖Mx‖ ≤ (Σ|M_ij|)‖x‖` (`norm_mulVec_le`), avoiding the scoped matrix-norm instances.
   `Matrix.IsHermitian.eigenvalues` / Weyl perturbation bounds were not needed.

## 3. Commands and results

    cd <repo>/.claude/worktrees/lean-g4b && source scripts/env.sh
    nice lake build GW                    # Build completed successfully
    nice lake env lean GW/Audit.lean      # 2m44s; 412 ManyBody lines (308 old + 104 new),
                                          # all ⊆ {propext, Classical.choice, Quot.sound}
    grep -rn "sorry\|admit\|native_decide\|^axiom" GW/Endpoint/ManyBody/{Jet,GroundState,Analytic}.lean  # none
    bash scripts/verify.sh                # see §5

Mutation checks (each reverted):

| mutation | result |
| --- | --- |
| drop `relax` from `sig2` (Analytic.lean) | `tr2_sigmaT`, `sigma_exact_minus_gw` fail |
| hole resolvent `MmR` → `MpR` in `greenR` | `greenR_smul` rewrite fails, `jetM_greenR` fails (timeout on mismatch) |
| flip sign of `Rs` denominators (GroundState.lean) | `Rs_eq_Rr` fails |

## 4. Failed attempts / notes

* Only compile-level fixes (lemma names: `Metric.isClosed_closedBall`, `Set.MapsTo`,
  `Matrix.inv_def` ambiguity, `Finset.induction_on` case binder order; `IsBigO.bound` vs
  the new `Jet.bound` name clash). No mathematical dead ends.
* `simp` inside `Fm_expand` needed `mulVec_diagonal` in the second pass (after `funext`).

## 5. verify.sh

`nice bash scripts/verify.sh` (33 min wall; the machine was running other heavy kernel jobs):
build and audit steps passed; the **scientific gate hit the 600 s per-step timeout** of
`scripts/verify.py` (not a test failure). Rerun of exactly the same unittest list by hand:
`Ran 577 tests in 571.094s — OK (skipped=2)`, i.e. just under the limit under load.
Workflow gate run by hand (`python3 -m unittest tests.test_gate_partition
tests.test_packet_references tests.test_provenance_committed`): 14 tests, exactly one failure,
`test_provenance_committed.test_current_manifests_match_the_files_as_they_stand` — the
expected digest mismatch for `GW.lean` and `GW/Audit.lean` against
`bgw/weighted_audit/PROVENANCE-R6.txt` (both changed in scope; PROVENANCE-R6 and scripts/
are outside the write scope). Supervisor: rerun verify.sh on a quieter machine; consider
whether the 600 s scientific-gate timeout needs headroom (not changed: scripts/ is out of scope).

## 6. Next actions (supervisor)

* Review `IsGround` (strict ground state in the sector) as the added hypothesis.
* Optional: update docs/ENDPOINT.md A3(a) — the O(λ³) claim is now about the actual Σ.
* Optional: define the full G0W0 function of λ (RPA W) to make the GW side a genuine
  function statement rather than the second-order polynomial.
* Re-sign PROVENANCE-R6 if required (not touched).
