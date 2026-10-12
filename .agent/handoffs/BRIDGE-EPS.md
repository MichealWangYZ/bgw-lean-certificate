# BRIDGE-EPS handoff: the static RPA dielectric matrix derived from many-body theory

Worker: Claude (implementer). Branch `bridge-eps/work`, worktree
`.claude/worktrees/bridge-eps`, base `d9be4dd` (BRIDGE). Status: **CHECKPOINT_READY**.
E1 to E4 are delivered and ready for review. This is NOT accepted; Codex owns acceptance.

## Result in one paragraph

EpsSpec's `chi(G,G') = 4/(N_k Ω) Σ_k Σ_v Σ_c M_vc(k,G) M_vc(k,G')/(E_v(k+q) - E_c(k))`
and `eps = δ - v chi` with `v = 8π/|q+G|²` are what RPA theory gives, and **no
discrepancy was found**. Starting from the time-ordered `G0` (`= ManyBody.G0t`), the
`η → 0⁺` limit of the damped transform of `-i G0 G0` at `ω = 0` is the static `χ0`
(`chiF_limit`, `chiW_zero`). In that `χ0` every occupied/empty pair appears twice, once
per time ordering, each time with `1/(ε_v - ε_c)`. The spin sum gives exactly `2`
(`spin_chiS`). Time reversal makes the second ordering equal to the first (`TROK`), which
gives `4 = 2 × 2` (`bloch_chi`; `factor_two_wrong` refutes `2`). `1/(N_k Ω)` is the
`1/√V` per amplitude of the orthonormal plane waves on the BvK supercell. The `k + q`
convention is the momentum-conserving one. The RPA eps is `GW.LL.dielectric`, and
`eps⁻¹ v` is the unique RPA `W`. It equals the symmetrised form, the Neumann series plus
an exact remainder, and the `ω → 0` limit of the dynamic RPA `W`. `epsSpec_eq_theory`
states the eps matrix equality. `sigA_eps_eq_theory` composes it with BRIDGE's
`sigA_eq_theory`.

## Files (write scope respected)

New:
* `GW/Bridge/EpsChi0.lean` (E1)
* `GW/Bridge/EpsBloch.lean` (E2)
* `GW/Bridge/EpsRPA.lean` (E3)
* `GW/Bridge/EpsCompare.lean` (E4)
* `tests/test_bridge_eps.py` (oracle, 10 tests)
* this handoff

Registration:
* `GW.lean`: 4 imports plus a docstring entry.
* `GW/Audit.lean`: 49 `#print axioms`, i.e. every declared theorem of the four files.
* `scripts/gates.py`: `tests.test_bridge_eps` added to SCIENTIFIC.
* `bgw/weighted_audit/PROVENANCE-R6.txt`: re-signed the digests of `GW.lean`,
  `GW/Audit.lean` and `scripts/gates.py`.
* `docs/BRIDGE.md`: rows E-1 to E-14 inserted after row 22 of the departure table, and
  a new final section "BRIDGE-EPS". Both edits are localized. The sibling worker's own
  final section will conflict only textually at end-of-file.

No existing theorem statement was edited.

## Key theorems

* E1: `chiF_limit`, `chiW_zero`, `chi0F_eq_chi0t`, `gF_eq_G0t`, `chiS_diag_nonpos`,
  `chiW_continuousAt`, `excOff_zero`
* E2: `spin_chiS`, `bloch_chi`, `rem_zero`, `chi_eq_triples`, `epsSpec_chi_eq_theory`,
  `epsSpec_chi_eq_theory_bands`, `factor_two_wrong`
* E3: `rpa_solve`, `rpa_unique`, `rpa_dyson`, `partialScreened_eq_coeff_sum`,
  `rpa_neumann`, `chiMat_eq_chi0`, `theory_eps_eq_dielectric`, `wDyn_tendsto`, `sym_W`,
  `det_epsSym`, `WM_symm`, `WM_entry`
* E4: `epsSpec_eq_theory_rem`, **`epsSpec_eq_theory`**, `epsTheory_entry_limit`,
  `Espec_eq_Etheory`, `etheory_W`, **`sigA_eps_eq_theory`**,
  `sigA_eps_eq_theory_complete`

## Named hypotheses (the union, for the composed statement)

* BRIDGE: `hC` (Coulomb averages), `hW` (wings), `hX` (`TOL_Zero`) and `hM` (`ModeOK`).
  With `sigA_eps_eq_theory_complete` also `hc`, `hs`, `hch`, which make `COR = 0`.
* BRIDGE-EPS, per `q ≠ 0` block (`EpsBlock.OK`):
  * `qne`: `q + G_i ≠ 0`.
  * `vol`: `V = N_k Ω`.
  * `res`: `ResOK`, the unfolding trust. The Input's pairs are the Bloch pairs
    `(v,k+q),(c,k)` with EpsSpec's `M` and energies.
  * `tr`: `TROK`, time reversal.
  * `bands`: `Bands`, momentum conservation plus complete band sums.
* `q = 0` blocks `Z`: their `eps⁻¹` is the input `E0`. It is not derived.

## Departure rows added to `docs/BRIDGE.md`

* proved equal: E-1, E-2, E-4, E-5, E-6, E-10, E-11, E-12, E-13
* named hypothesis:
  * E-3: `TROK` (the factor 4 depends on it)
  * E-7: `Bands`, the finite band sum; `epsSpec_eq_theory_rem` gives the explicit
    remainder otherwise
  * E-14: the `q = 0` block
* shared: E-8 (G-sphere), E-9 (unfolding trust)
* DISCREPANCY: none

## Commands and results

```
source scripts/env.sh
cp -a ../bridge/.lake/build .lake/build          # reuse the BRIDGE worktree's build cache (same base)
lake env lean GW/Bridge/Eps{Chi0,Bloch,RPA,Compare}.lean   # each exit 0, no warnings
lake build GW                                     # "Build completed successfully." (6751 jobs)
lake env lean <scratch>/aud_eps.lean              # the 49 new Audit entries: all [propext, Classical.choice, Quot.sound]
lake env lean <scratch>/chk_eps.lean              # collectAxioms over every theorem constant of GW.Bridge.Eps*:
                                                  #   "BRIDGE-EPS AUDIT PASSED: 103 theorems" (incl. auto-generated)
lake env lean GW/Audit.lean                       # exit 0; 108 GW.Bridge entries (59 BRIDGE + 49 BRIDGE-EPS),
                                                  #   every entry within [propext, Classical.choice, Quot.sound]
python3 -m unittest tests.test_bridge_eps         # 10 tests OK (~12 s)
python3 -m unittest tests.test_provenance_committed tests.test_gate_partition   # 9 tests OK
grep -nE "sorry|admit|native_decide|implemented_by|ofReduceBool|^axiom" GW/Bridge/Eps*.lean   # nothing
```

NOT run:
* `scripts/CheckAxioms.lean`, because it imports `GWKernelData`.
* `bash scripts/verify.sh`, because it builds `GWKernelData`. The task forbids both.

## Oracle (independent, numpy only)

* E1: the numerical damped transform of `-i G0(τ) G0(-τ)` (Richardson in `η`) matches the
  closed form at `ω = 0` and at `ω ≠ 0`. A finite-difference static density response
  `d<g|n>/dλ` for `H0 + λ diag(g')` matches `chiS`. A single time ordering gives half and
  fails.
* E2 (the strong check): a 1D crystal in Ry, `H = -d²/dx² + 2V₁cos x + 2V₂cos 2x`, a
  4-cell BvK supercell, and the ecut-sphere basis `|k+G| ≤ Kc`. `⟨q+G|χ|q+G'⟩` is taken
  from the supercell's finite-difference density response (spin 2) to
  `λ(e^{i(q+G')x} + c.c.)`. It agrees with
  `4/(N_k Ω) Σ M M/(E_v(k+q) - E_c(k))`, computed with the real per-k coefficients, to
  `1.3e-11` (max abs; entries ~0.02-0.25). Factor 2 fails. The swapped convention (`v`
  at `k`, `c` at `k+q`) fails by 0.076.
* E3: Dyson, Neumann plus remainder, symmetrised `W`, symmetry of `W`, column scaling
  `W_ji = eps⁻¹_ji v_i`, and `W(ω) → W(0)`.
* E4: on a 5-cell crystal at `q = 2/5`, eps and eps⁻¹ from the supercell response equal
  those from the EpsSpec-style formula.

## Failed attempts and fixes (for the reviewer)

* `omit [DecidableEq ι]` failed because `FSys.f` needs decidable membership. All `omit`s
  were removed and the unused-section-variable linter was silenced per file.
* `by_contra h; apply hz` hit the `Decidable` instance goal. It was replaced by
  `Classical.byContradiction`.
* `nlinarith [...]` spread over two lines inside `by` did not parse, because the
  indentation ended the block. It was split into `have`s.
* The first `spin_chiS` proof expanded both Bool sums at once and got stuck. It was
  restructured with a per-orbital `inner` lemma.
* `rpa_dyson`: `rw [← this]` rewrote every `diagonal v`. It was replaced by
  `sub_eq_iff_eq_add.mp`.
* Oracle:
  * The `ω = 0` closed form produced NaN from the `m = m'` terms (`0/0`). Those terms
    are now skipped when `f_m = f_{m'}`.
  * The first "swapped convention" test demanded momentum conservation on the swapped
    pair, which makes `M ≡ 0`. It was replaced by the same index rule with `v` and `c`
    swapped, which is what a mis-transcribed code would compute.
  * The ecut-sphere basis `|k+G| ≤ Kc` (not `|G| ≤ Gmax`) is needed for the per-k
    bases to coincide exactly with the supercell basis at `k + q = 1`.

## Honest limits

* The pairing is taken as hypotheses (`ResOK`, `TROK`, `Bands`), and so is the
  normalisation `V = N_k Ω`: the plane-wave integrals are derived by hand in the
  `EpsBloch.lean` docstring and checked numerically. They are not formalised as
  integrals.
* Real orbitals and amplitudes (real flavour). The complex-flavour statement would need
  `conj` in `chiF`.
* No bound on the band-truncation remainder; `Bands` fails for any finite Input.
* The `q = 0` head and wings are not derived (`E0` is an input).

## Next action (for Codex)

1. Review `EpsBlock.OK`, especially whether `ResOK` and `TROK` state the right trust
   boundary.
2. Merge-order note: this branch and the sibling BRIDGE doc worker both append to
   `docs/BRIDGE.md`. Resolve the end-of-file conflict by keeping both sections.
3. Run the full `bash scripts/verify.sh` with the cached `GWKernelData`.
4. A possible follow-up: bound `remR + remA` numerically on the Si-EPM Input (the
   band-convergence of chi), and derive the `q → 0` head/wings.
