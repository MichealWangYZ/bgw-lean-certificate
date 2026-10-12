# G4 handoff: A3(a) — structure of the GW error for a general finite fermion system

Status: **ready_for_review**. Not accepted. Claude does not accept its own work.
Branch `lean/g4-general-gw` (from `bgw-e/endpoint` @ `c1a834f`), pushed; no merge.
New Lean: `GW/Endpoint/ManyBody/*.lean` (18 files, ~3.1k lines, 308 theorems, all in
the new `GW/Audit.lean` section). Scripts: `bgw/endpoint/manybody/check_sigma2.py`,
`bgw/endpoint/manybody/dimer_check.py`.

## 0. The task statement is false as written — found numerically first, then proved

The task asked to prove `Σ2 = direct + SOX` for `H(λ) = H0 + λV` with a bare
one-body `H0`. **That is false in general.** Exact diagonalization
(`check_sigma2.py`, n = 4..6 random `ε`, random symmetric `v`) gives
`max|Σ2_exact - (dir + sox)| ≈ 13–30` against a scale of 14–33, but
`max|Σ2_exact - (dir + sox + relax)| ≈ 1e-7` (finite-difference noise), with

    relax_pq = Σ_{a∈O} Σ_{r∉O} (⟨pa||qr⟩ + ⟨pr||qa⟩) Σ1_ra / (ε_a - ε_r).

`relax` is the Hartree–Fock diagram with a first-order insertion on its internal
line (first-order change of the density matrix). It vanishes iff the occupied–empty
block of `Σ1` vanishes in the relevant combination; in particular under the
**Brillouin condition** `Σ1_ra = 0` (a ∈ O, r ∉ O), e.g. when `H0` is the Fock
operator of the reference or by a symmetry (dimer parity). With `--brillouin`
(parity-restricted `v`) the random check gives `3e-10` for `dir + sox`.
G0W0 built on the fixed `G0` does not contain `relax` either, so the correct general
statement (proved) is

    Σ_exact − Σ_GW = λ² (SOX + relax) + O(λ³),     = λ² SOX + O(λ³) under Brillouin.

I did **not** weaken the theorem to hide this; both the general form and the
Brillouin corollary are stated. Proposed change to docs/ENDPOINT.md A3(a) (not
edited — outside write scope): add "under the Brillouin condition" or "+ relax".

## 1. Theorems (plain math)

Setting. `n` spin-orbitals, Fock space = `Finset (Fin n)` with Jordan–Wigner
`c_p`, `c_p† = c_pᵀ`. `H0 = Σ ε_p c_p†c_p`. Index convention
`V = ½ Σ_{pqrs} v_pqrs c_p† c_q† c_s c_r` (`v_pqrs = ⟨pq|rs⟩`, electron 1 p→r, electron
2 q→s). Symmetry hypotheses: `hv1: v_pqrs = v_qpsr`, `hv2: v_pqrs = v_rspq` (V real
symmetric). No orbital reality `v_pqrs = v_rqps` assumed. `⟨pq||rs⟩ = v_pqrs − v_pqsr`.
`Φ` = basis vector of the occupied set `O`, `E0 = Σ_{a∈O} ε_a`.
`NonDeg`: no other basis state with `|O|` particles has energy `E0`.
`OffPoles ω`: `ω ≠ ±(E_S − E0)` for every basis state `S` (co-finite; implies ω ≠ 0,
ω ≠ ε_p). `GWOffPoles ω`: ω off `ε_r+ε_s−ε_a` and `ε_a+ε_b−ε_r` (incl. r = s, a = b).

Meaning of "O(λ³)": everything is a **formal power series** in λ (`PowerSeries ℝ`,
λ = X) at fixed real ω; statements are about coefficients `cf k` for k = 0, 1, 2.
**The analytic statement (that these are the Taylor coefficients of the true
function λ ↦ Σ(ω; λ)) is NOT proved.** The perturbed ground state is the
Rayleigh–Schrödinger `ψ = Φ + λψ1 + λ²ψ2`, `E = E0 + λE1 + λ²E2`; coefficients ≤ 2 of
G depend only on these.

Exact side (definitions `Exact.lean`, literal task definition):
`G_pq = [⟨ψ|c_p (ω−(H−E))⁻¹ c_q†|ψ⟩ + ⟨ψ|c_q† (ω+(H−E))⁻¹ c_p|ψ⟩] · ⟨ψ|ψ⟩⁻¹` with
matrix inverses in `Matrix _ _ ℝ⟦X⟧`; `G0 = diag (ω−ε_p)⁻¹`; `Σ = G0⁻¹ − G⁻¹`.

| theorem | statement |
| --- | --- |
| `ann_mul_cre_add`, `ann_mul_ann_add`, `cre_mul_cre_add` (S1) | CAR for every n |
| `H0_eq_diagonal`, `H0_mul_cre`, `H0_mul_ann` | H0 diagonal, `[H0,c†]=εc†`, `[H0,c]=−εc` |
| `resid_cf` (S2) | coefficients 0,1,2 of `(H−E)ψ` vanish (ψ solves the eigen-equation mod λ³) |
| `greenT_eq`, `feshbach`, `greenT_inv`, `sigmaT_eq` | exact Feshbach/Schur form `G⁻¹ = ω − ⟨ψ|ψ⟩⁻¹(Aᵀ𝓗A + Aᵀ𝓗N⁻¹Q𝓗A)` on Fock⊕Fock |
| `sigma_coeff0` | `Σ⁽⁰⁾ = 0` (so G(λ=0) = G0) |
| `sigma1_eq_HF` (S3) | `Σ⁽¹⁾_pq = Σ_{a∈O} ⟨pa‖qa⟩` |
| `sigma2_eq` (S4) | `Σ⁽²⁾ = ½Σ_{a,r,s}⟨pa‖rs⟩⟨rs‖qa⟩/(ω+ε_a−ε_r−ε_s) + ½Σ_{r,a,b}⟨pr‖ab⟩⟨ab‖qr⟩/(ω+ε_r−ε_a−ε_b) + relax` |
| `sig2_eq_dir_add_sox` | the two antisymmetrized sums = `dir2 + sox2` (non-antisymmetrized, uses hv1) |
| `sigma2_eq_direct_add_sox_add_relax`, `sigma2_eq_direct_add_sox` (Brillouin) | S4 exit |
| `gw1_eq_HF`, `gw_error_first_order` | `Σ_GW⁽¹⁾ = Σ_H + Σ_x = Σ⁽¹⁾_exact` |
| `gw2_limit` (S5) | `lim_{η→0⁺} FT_η[i G0 (v χ0 v)](ω) = dir2` (time domain, χ0 = −iG0G0) |
| `gw_error_second_order` | `Σ⁽²⁾_exact − FT_η[Σ⁽²⁾_GW] → SOX + relax` |
| `gw_error_second_order_brillouin` | `→ SOX` |
| `gw_error_coeff2` | `Σ⁽²⁾_exact − dir2 = SOX + relax` (coefficient identity) |

`dir2`, `sox2` as in `bgw/endpoint/second_order.py`'s spin-orbital form:
`dir2 = Σ v_pars v_rsqa/(ω+ε_a−ε_r−ε_s) + Σ v_prab v_abqr/(ω+ε_r−ε_a−ε_b)`,
`sox2 = −Σ v_pars v_rsaq/(…) − Σ v_prab v_abrq/(…)`.

GW definition (S5, `GWSecond.lean`): `G0_m(τ) = −i[θ(τ)(1−f_m) − θ(−τ)f_m]e^{−iε_mτ}`,
`χ0_{mm'}(τ) = −i G0_m(τ)G0_{m'}(−τ)`, `W⁽²⁾_{(pn),(nq)} = Σ v_{pm'nm} χ0_{mm'} v_{mnm'q}`,
`Σ⁽²⁾ = i Σ_n G0_n W⁽²⁾`; frequency via the dimer's damped transform `ftDamped`
(reused from `HubbardDimerSigma.lean`, `ftDamped_twoSided_limit`). What is DEFINED
rather than derived here: that `W⁽²⁾ = vχ0v` is the λ² term of RPA `W` (immediate
from `W = (1−λvχ0)⁻¹λv` with instantaneous `v`, not formalized), the orbital-pair
projection of `Σ = iGW`, and `Σ_GW⁽¹⁾ = Σ_H + Σ_x` (standard G0W0 static part; the
Hartree term is included explicitly because `H0` is bare). Higher GW orders are not
defined. A remark proved implicitly by the hypotheses: `dir2` has self-screening
poles at r = s / a = b that the exact Σ⁽²⁾ lacks (they cancel against SOX).

## 2. Proof architecture (reuse decisions)

* Fock space: explicit Jordan–Wigner on `Finset (Fin n)` (generalizing
  `HubbardDimerFock.lean`). Mathlib `ExteriorAlgebra`/`contractLeft` gives CAR
  abstractly but has no finset basis/transpose/matrix form in the pinned version; all
  later stages need concrete matrices.
* No Wick theorem: the key step is an **exact finite-dimensional Feshbach identity**
  (`Feshbach.lean`, generic over a comm ring): with `A` = columns `(c_p†ψ, c_pψ)` on
  Fock⊕Fock, CAR gives `AᵀA = ⟨ψ|ψ⟩·1`, and `G⁻¹ = ω − ⟨ψ|ψ⟩⁻¹(S + Jᵀ N⁻¹ J)`,
  `S = Aᵀ𝓗A`, `J = Q𝓗A`. Then `J = O(λ)` with `J⁽¹⁾ = ([V,c_q†]Φ, [c_q,V]Φ)` minus
  one-particle parts (the 2p1h/2h1p vectors), so the dynamic term is
  `J⁽¹⁾ᵀ (ω−𝓗0)⁻¹ J⁽¹⁾`, evaluated with 2p1h/2h1p Gram matrices derived from CAR
  (`Slater.lean`). The static term reduces by an operator identity to
  `ε δ⟨ψ|ψ⟩ + λ⟨ψ|{c_p,[V,c_q†]}|ψ⟩ + O(residual)`: HF at order 1, `relax` at order 2.
  Unlinked terms never appear. Formal series: mathlib `PowerSeries ℝ` and
  `Matrix.inv` over it (not the `invOfUnit`-over-matrices pattern of
  `GW/LL/Screening.lean`: the commutative scalar ring gives determinants and
  `inv_eq_left_inv` directly).
* GW time domain: reuse of `ftDamped`, `twoSided`, `ftDamped_twoSided_limit`.

## 3. Numerical cross-checks (run before proving)

    python3 bgw/endpoint/manybody/check_sigma2.py [--seed S --n N --nocc K] [--brillouin] [--gw]
    python3 bgw/endpoint/manybody/dimer_check.py [--t T --U U]

* seeds 1,5,9 (n=5,N=2), seed 4 (n=6,N=3): `Σ1−HF ≤ 2e-7`; `Σ2 − (dir+sox+relax) ≤ 1.2e-6`;
  `Σ2 − (dir+sox)` = O(10) (so relax is real). `--brillouin` (n=4): `3e-10`.
* `--gw` (imaginary-axis numerical convolution of G0 with vχ0v): `|Σ_GW⁽²⁾ − dir2| = 3e-3`
  (grid error) vs scale 4.8. (First attempt with `G0(ω+ω')` gave O(1) mismatch: for
  general orbitals `W_{pm,mq}(τ)` is not even; the convolution is `G0(ω−ω')`. Fixed.)
* Dimer (spin-orbital, bare bonding/antibonding basis): hv1, hv2 hold; Brillouin holds
  (parity), relax = 0; exact `Σ2 = dir2 + sox2` to 1e-9; gap combinations
  `dir-gap = U²/(4t)`, `sox-gap = −U²/(8t)` exactly — matching `gap2dir_eq`, `gap2x_eq`
  and `gw_error_is_minus_sox` of `HubbardDimerSecondOrder.lean` (which uses HF
  energies; difference O(U³)). A Lean instantiation of the general theorem for the
  dimer was not done (numerical agreement only; it would need the dimer's contact `v`
  in the orbital basis over `Fin 4`).

## 4. Mutation checks (each makes the named theorem fail)

| mutation | failing theorem |
| --- | --- |
| drop the `½` in `sig2p` (Dyn.lean) | `dyn_particle` (unsolved goals) |
| drop the hole term of `sox2` (DirectSOX.lean) | `sig2_eq_dir_add_sox` |
| flip `−occ` → `occ` in `G0t` for τ<0 (GWSecond.lean) | `sigGW2t_eq` |
| hole resolvent `MmT` → `MpT` in `greenT` (Exact.lean, rebuilt) | `greenT_eq` (Bridge.lean) |

## 5. Commands and results

    cd ../lean-g4 && source scripts/env.sh
    nice lake build GW                      # Build completed successfully (~4 min)
    nice lake env lean GW/Audit.lean         # 308 ManyBody lines; all ⊆ {propext, Classical.choice, Quot.sound}
    grep -rn "sorry\|admit\|native_decide\|^axiom" GW/Endpoint/ManyBody/   # none
    bash scripts/verify.sh                   # see §6

## 6. verify.sh

`bash scripts/verify.sh` (13m54s, nice): **scientific gate PASS**; **workflow gate FAIL**
with exactly one failure, `test_provenance_committed.test_current_manifests_match_the_files_as_they_stand`:
digest mismatches `GW.lean` and `GW/Audit.lean` against `bgw/weighted_audit/PROVENANCE-R6.txt`.
Expected: both files were changed in-scope (import line; new audit section) and the task
forbids editing PROVENANCE-R6 (the supervisor re-signs it). No other test failed.

## 7. Failed attempts / notes

* Direct Wick-style evaluation of the RS expansion of G was rejected up front (needs
  5-quasiparticle Gram matrices and unlinked-term cancellation); the Feshbach route
  avoids it entirely.
* `pkill -f` on a pattern matching the invoking shell killed the shell once (no
  effect on files).
* Early numeric GW check used the wrong convolution sign (see §3).

## 8. Next actions (for the supervisor)

* Decide the A3(a) wording (§0): "exact − GW = SOX + relax; = SOX under Brillouin".
* Optional: Lean instantiation for the dimer (`Fin 4`, contact v) to connect
  `gw_error_second_order_brillouin` with `gw_error_is_minus_sox` formally.
* Optional: formalize `W⁽²⁾ = vχ0v` as coefficient 2 of the RPA series (e.g. via
  `GW.LL.geoW`, which is typed on `Fin N` and would need the pair index reindexed).
* Re-sign `bgw/weighted_audit/PROVENANCE-R6.txt` if required (not touched).
