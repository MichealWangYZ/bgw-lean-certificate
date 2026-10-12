# A3(b) handoff: Hubbard dimer, exact vs G0W0@HF fundamental gap

Status: **ready for review, not accepted.** Branch `a3/hubbard-dimer`, forked
from `bgw-e/endpoint` at b1f0c16. Worktree `.claude/worktrees/a3-dimer`.

## The result in one paragraph

For the half-filled two-site Hubbard model (t > 0, U >= 0), the exact
fundamental gap is `sqrt(U^2+16t^2) - 2t`, and the one-shot G0W0@HF gap from
the full QP equation is `sqrt((2t+h)^2 + 4tU^2/h) - h` with `h = sqrt(4t^2+4tU)`.
For 0 <= U <= t, kernel-checked:

    U^2/(8t) - 3U^3/(16t^2)  <=  gap_GW - gap_exact  <=  U^2/(8t) - U^3/(16t^2)
    |gap_GW - gap_exact| <= (1/8) U^2 / t              (C = 1/8, p = 2)
    -U^2/(8t)  <=  gap_HF - gap_exact  <=  -U^2/(8t) + U^4/(512 t^3)   (U <= 2t)

**Leading order:** both errors start at U^2, with the SAME magnitude 1/(8t)
and opposite sign (`gw_error_leading`, `hf_error_leading` are the limits
err/U^2 -> +1/(8t), -1/(8t)). G0W0@HF overshoots: it gives twice the exact
second-order gap correction (U^2/(4t) instead of U^2/(8t)), the known effect
of the missing second-order exchange diagram. `no_cubic_bound` proves no bound
C U^3/t^2 holds, so p = 2 is sharp; the constant 1/8 is sharp by the limit.
G0W0@HF is strictly better than HF on (0, t] (`gw_beats_hf`), but only through
the U^3 term (at U = t: GW error +0.0212 t, HF error -0.1231 t).

## GW variant (named)

**G0W0@HF**, Romaniello-Guyot-Reining (JCP 131, 154111 (2009)) setup:
G0 = restricted HF (bonding orbital doubly occupied; eps = -/+t + U/2, which is
the U = 0 G0 with the Hartree+exchange shift U/2; self-consistency proved,
`hf_selfconsistent`); W = RPA from the spin-summed chi0 of that G0 with
v_ij = U delta_ij (proved to be the Hubbard interaction in normal-ordered form,
`two_dbl_eq_normal_ordered`); Sigma_c = i G0 W_c by residues; QP energies from
the full equation E = eps_HF + Sigma_c(E), root on the physical side of the
self-energy pole (unique there). A Hartree-only G0 (poles at -/+t + U) is a
different variant and is NOT covered.

## What this does NOT say

- It is a two-site model result. It is not a bound for silicon, Si-EPM or the
  BerkeleyGW run, and says nothing about GPP, plane-wave or convergence error.
- Only G0W0@HF as above; not scGW, not other starting points, not vertex GW.
- **Superseded 2026-09-23 (A3-dimer-2):** the residue evaluation is now derived
  in Lean (`HubbardDimerSigma.lean`, `sigmaSinglePole_eq_limit`); the text
  below is the original status. The residue evaluation of i∫G0 W_c was not
  formalized; `sigmaSinglePole` is the textbook T=0 pole formula, taken as a definition. It is checked
  numerically (imaginary-axis quadrature of -(1/2pi)∫G0(mu+i nu+i nu')W_c(i nu')
  with W_c from direct matrix inversion) to 2e-13 in `dimer.py`. Upstream (HF,
  chi0, RPA inversion, single-pole form of W) and downstream (orbital matrix
  elements, QP roots, gap, bounds) are kernel-checked.
- The ground-state property IS proved (no gap here): each sector energy comes
  with an eigenvector and a sum-of-squares variational lower bound over all
  vectors of that particle number (`IsSectorGround`), hence lowest eigenvalue
  and unique. H is built from Jordan-Wigner operators whose CAR are kernel
  checked, not transcribed.
- The bound regime is 0 <= U <= t (proof actually works up to U = 1.25 t,
  not stated). For U >> t both errors are O(U) and no statement is made.

## Files

- `GW/Endpoint/HubbardDimerFock.lean` - 16-dim Fock space, JW operators, CAR,
  number conservation, H, `H_mulVec`. (~2.5 min to elaborate: `decide +kernel`.)
- `GW/Endpoint/HubbardDimerExact.lean` - sectors, ground energies, `exact_gap`.
- `GW/Endpoint/HubbardDimer.lean` - HF, chi0, RPA W, Sigma, QP, bounds.
- `GW.lean` (+1 import), `GW/Audit.lean` (+61 `#print axioms`).
- `bgw/endpoint/a3_dimer/dimer.py` - sympy derivation + numerical ED/GW route;
  output `crosscheck.json`.
- `bgw/endpoint/a3_dimer/mutate_lean.py`, log `mutations.log`.
- `tests/test_endpoint_a3.py` (7 tests).

## Exact theorem statements (namespace GW.Endpoint.HubbardDimer)

```lean
def IsSectorGround (t U : ℝ) (N : ℕ) (E : ℝ) : Prop :=
  (∃ v : Fin 16 → ℝ, v ≠ 0 ∧ InSector N v ∧ H t U *ᵥ v = E • v) ∧
    ∀ v : Fin 16 → ℝ, InSector N v → E * (v ⬝ᵥ v) ≤ v ⬝ᵥ (H t U *ᵥ v)
theorem sector_grounds (ht : 0 < t) : IsSectorGround t U 1 (-t) ∧
    IsSectorGround t U 2 ((U - Real.sqrt (U ^ 2 + 16 * t ^ 2)) / 2) ∧ IsSectorGround t U 3 (U - t)
theorem exact_gap (ht : 0 < t) (h1 : IsSectorGround t U 1 E1)
    (h2 : IsSectorGround t U 2 E2) (h3 : IsSectorGround t U 3 E3) :
    E3 + E1 - 2 * E2 = gapExact t U        -- gapExact t U = √(U^2+16t^2) - 2t
theorem W_eq_inv (ht : 0 < t) (hU : 0 ≤ U) (h1 : ω ^ 2 ≠ 4 * t ^ 2)
    (h2 : ω ^ 2 ≠ hRPA t U ^ 2) : W t U ω = (1 - vC U * chi0 t U ω)⁻¹ * vC U
theorem sigmaC_orbital (t U ω : ℝ) :
    phiB ⬝ᵥ (sigmaC t U ω *ᵥ phiB) = sigBB t U ω ∧ phiA ⬝ᵥ (sigmaC t U ω *ᵥ phiA) = sigAA t U ω ∧
      phiA ⬝ᵥ (sigmaC t U ω *ᵥ phiB) = 0 ∧ phiB ⬝ᵥ (sigmaC t U ω *ᵥ phiA) = 0
    -- sigBB E = tU²/h / (E - epsA - h),  sigAA E = tU²/h / (E - epsB + h)
theorem qp_removal (ht : 0 < t) (hU : 0 ≤ U) (E : ℝ) (hE : E < epsA t U + hRPA t U) :
    E = epsB t U + sigBB t U E ↔ E = Erem t U
theorem qp_addition (ht : 0 < t) (hU : 0 ≤ U) (E : ℝ) (hE : epsB t U - hRPA t U < E) :
    E = epsA t U + sigAA t U E ↔ E = Eadd t U
theorem gw_gap_of_qp (ht : 0 < t) (hU : 0 ≤ U) : (existence of both roots) ∧
    ∀ Er Ea, Er < epsA + h → Er = epsB + sigBB Er → epsB - h < Ea → Ea = epsA + sigAA Ea →
      Ea - Er = gapGW t U               -- gapGW = √((2t+h)^2 + 4tU^2/h) - h
theorem gw_error_bounds (ht : 0 < t) (hU : 0 ≤ U) (hUt : U ≤ t) :
    U ^ 2 / (8 * t) - 3 * U ^ 3 / (16 * t ^ 2) ≤ gapGW t U - gapExact t U ∧
      gapGW t U - gapExact t U ≤ U ^ 2 / (8 * t) - U ^ 3 / (16 * t ^ 2)
theorem gw_error_abs (ht : 0 < t) (hU : 0 ≤ U) (hUt : U ≤ t) :
    |gapGW t U - gapExact t U| ≤ (1 / 8) * U ^ 2 / t
theorem hf_error_bounds (ht : 0 < t) (hU : 0 ≤ U) (hUt : U ≤ 2 * t) :
    -(U ^ 2 / (8 * t)) ≤ gapHF t U - gapExact t U ∧
      gapHF t U - gapExact t U ≤ -(U ^ 2 / (8 * t)) + U ^ 4 / (512 * t ^ 3)
theorem gw_beats_hf (ht : 0 < t) (hU : 0 < U) (hUt : U ≤ t) :
    |gapGW t U - gapExact t U| < |gapHF t U - gapExact t U|
theorem no_cubic_bound (ht : 0 < t) :
    ¬ ∃ C : ℝ, ∀ U : ℝ, 0 < U → U ≤ t → |gapGW t U - gapExact t U| ≤ C * U ^ 3 / t ^ 2
theorem gw_error_leading (ht : 0 < t) :
    Tendsto (fun U => (gapGW t U - gapExact t U) / U ^ 2) (𝓝[>] 0) (𝓝 (1 / (8 * t)))
theorem hf_error_leading (ht : 0 < t) :
    Tendsto (fun U => (gapHF t U - gapExact t U) / U ^ 2) (𝓝[>] 0) (𝓝 (-(1 / (8 * t))))
theorem gw_gap_error_main (ht : 0 < t) (hU : 0 ≤ U) (hUt : U ≤ t)
    (h1 : IsSectorGround t U 1 E1) (h2 : IsSectorGround t U 2 E2) (h3 : IsSectorGround t U 3 E3)
    (hr : Er < epsA t U + hRPA t U) (hr' : Er = epsB t U + sigBB t U Er)
    (ha : epsB t U - hRPA t U < Ea) (ha' : Ea = epsA t U + sigAA t U Ea) :
    |(Ea - Er) - (E3 + E1 - 2 * E2)| ≤ (1 / 8) * U ^ 2 / t
```

Proof route of the bound: with a = h/(2t) in [1, 3/2], U = t(a^2-1), both
squared-sqrt comparisons reduce to one-variable polynomials that factor as
(a-1)^3 (a+1)^2 p12(a)/2^18 and (a-1)^4 (a+1)^2 q7(a)/2^8 (found with sympy,
checked by `ring`); p12, q7 > 0 on [1, 3/2] by term bounds in w = a-1.

## Commands and results (worktree root, `source scripts/env.sh`)

```
python3 bgw/endpoint/a3_dimer/dimer.py          # ALL OK, 2.6 s
lake build                                      # Build completed successfully
lake env lean GW/Audit.lean                     # 61 HubbardDimer lines, all [propext, Classical.choice, Quot.sound]
lake env lean scripts/CheckAxioms.lean          # AXIOM AUDIT PASSED: 1002 theorems; 3 new modules listed
python3 bgw/endpoint/a3_dimer/mutate_lean.py --log bgw/endpoint/a3_dimer/mutations.log   # ALL OK, ~6 min
python3 -m unittest -v tests.test_endpoint_a3   # 7 tests OK
```

Numerical cross-check (8 points, t in {0.25,...,2}, U in {0,...,4}): worst
|ED - closed form| 2.7e-15; RPA pole 2.7e-13; residue 5.6e-13; frequency
quadrature vs pole formula 2.1e-13; QP removal root 1.3e-13; GW gap 2.6e-13.
Examples (t=1): U=0.1 exact 2.001249805, GW 2.002326210, HF 2; U=1 exact
2.123105626, GW 2.144290649. Symbolic: err_GW = u^2/8 - 3u^3/16 + 77u^4/512 - ...,
err_HF = -u^2/8 + u^4/512 (u = U/t).

Mutations (all rejected, full failing sets in the log; sha256 of the three
Lean files recorded): W-sign, pole-factor-2 (h^2 = 4t^2+8tU), residue-factor-2,
Sigma-pole-factor-2, no-spin-factor in chi0, no-exchange in Fock, linearised
QP (Erem := epsB + Sigma(epsB)), bound power 3, bound coefficient 1/16, HF
leading-coefficient sign, wrong N=2 root, excited N=3 state (eigenvector is
fine, variational clause fails), hopping sign, no Jordan-Wigner string. Plus
controls for the GW and Exact files. The Fock file has no separate control
run in the script (its unmutated build is the `lake build` above).

sha256: HubbardDimerFock 564fd3b8..., HubbardDimerExact 1b7f7928...,
HubbardDimer 8bb50d35... (full hashes in mutations.log).

## Failed attempts / notes

- `decide` (elaborator) on the quantified CAR relations timed out at 200k
  heartbeats; `decide +kernel` works (~1 min), axioms unchanged.
- `simp` over the 16x16 literal left `U*2 = 2*U ∨ v 15 = 0` for one row;
  closed by `Or.inl`.
- First sympy root check (`simplify(x - Erem) == 0`) failed on nested radicals;
  replaced by polynomial reduction modulo D^2 and h^2 relations.
- `chi0_eq` needs ω^2 ≠ 4t^2 (totalized division makes it false at the pole).

## Open item for the supervisor (outside my write scope)

`tests/test_gate_partition.py` will FAIL until `"tests.test_endpoint_a3",` is
added to `SCIENTIFIC` in `scripts/gates.py`. I did not edit gates.py because
it is outside the task's write scope, so I did not run the full
`scripts/verify.sh` (it would stop on that test). Everything else it runs for
Lean (build, Audit, CheckAxioms) was run by hand above.

## Next action

Supervisor review; add the gates.py line; optionally extend to the
Hartree-only G0 variant or to A3(c).
