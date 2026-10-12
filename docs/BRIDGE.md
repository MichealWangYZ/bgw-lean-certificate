# BRIDGE: BerkeleyGW's GPP self-energy and G0W0 theory, conditional identities with the transcribed spec

Status: worker output, ready for review. Not accepted. Task: `.agent/tasks/BRIDGE.md`.

## Scope after REVIEW-28 (read this first)

An adversarial review of PR 28 at `d783e18` (`docs/reviews/REVIEW-28-adversarial.md`,
summary `docs/reviews/README.md`) found that this document described more than its
theorems state. The post-fix review of `b580e80` (`docs/reviews/R28-R2.md`) corrected
it further. The corrected scope, which governs every sentence below:

* **What the bridge is.** It is a set of **conditional theory-to-specification
  identities**: exact algebra about real-number definitions, under named hypotheses.
  It is not an end-to-end theorem about one physically identified finite fermion system
  instantiated on the certified run. The hypotheses `hC` (except trivially, by `vc := vb`), `hW`, `hX`, `ModeOK`, wing
  conditions, `Complete`, `CompleteK`, `Compat`, `MF.TR` and `DensOK` are not
  discharged on the certified Si-EPM run; several of them provably fail there (listed under "What is and is not claimed").
  A true implication with unfulfilled premises is not a run-specific conclusion.
* **F1, no common-system bridge; the R28-F1 restatement and its limits.** The composed
  theorems (`sigA_eps_eq_theory`, `sigA_eps_eq_theory_q0`) take the state `gl`, `st` and the screening blocks `bs`
  independently. `EpsBlock.OK` checks properties internal to each block; no field
  identifies a block's orbitals, energies, occupations, density, geometry or
  interaction with the ones the self-energy uses. The cross-system identification is
  therefore a trusted input. Corrected statement (R28-F1, `GW/Bridge/Common.lean`,
  kernel-checked): `GW.Bridge.Common.sigA_compat` says that for blocks, `gl` and `st`
  compatible with one `MF` (`Compat`), `SigA = SigT(S) + COR(S)`.
  * `MF` is a data record: grid, G-spheres, integer coefficient rows, energies, `nocc`,
    cell and the RHO list. It requires no orthonormality, no Hamiltonian and no
    eigen-equation, so `Compat` identifies the screening and Σ inputs as images of the
    same data, not as eigenstates of one `H`.
  * `Compat` means: the eps Inputs off `Z`, `gl` and `st` are `S`'s images under the
    index plans, and `k0` and every `k0 − q_t` are GRID points (fields `k0`, `minus`,
    added in R28-R2). Before R28-R2 the Σ state could sit at an off-grid index, and the
    REVIEW-28 adversarial case (same screening, arbitrary Σ energies) met the predicate;
    `offgrid_loophole` keeps that construction as a kernel-checked record. Now
    `compat_self` (given `k0`, `minus` on the grid) shows the predicate is satisfiable,
    and `compat_st_unique` / `compat_energy_shift` show that the adversarial case is
    compatible with no system, given one screening block off `Z` whose `plus` is onto the
    grid (implied by `EP.WF`), a nonempty multiplet, and the plans fixed.
  * `MF.blk_ok` proves `ResOK`, `Bands` and `vol` for the system's own blocks. `ResOK`
    and `Bands` hold by construction: the theory pair density (EpsSpec's `M`) builds
    momentum conservation in through the trusted index map `plus`. `TROK` follows only
    FROM the hypothesis `MF.TR`.
  * `MF.TR` is an exact ordered-list identity: no sphere permutation, no umklapp, no sign
    or multiplet rotation. At a grid point that `neg` fixes (a time-reversal-invariant
    point such as Γ, X, L when `neg` encodes `-k`) it forces every sphere vector to be 0
    (`MF.tr_fixed`); if its sphere at `k0` has a nonzero vector, no block whose `neg`
    fixes `k0` satisfies it (`compat_selfpaired_no_TR`). `Z` is a `Finset`, so `hP`/`hT` cover
    infinitely many blocks and some plan must satisfy `MF.TR` on the whole grid. With the
    plans' `neg` encoding `-k` on a grid that stores each k-point class once (trusted plan semantics, not a theorem, since `MF` has no k-coordinates), every block fixes X and L, whose spheres hold a nonzero
    vector, so none does: the hypotheses of `sigA_compat` are unsatisfiable
    (`hyps_unsat_of_selfpaired`; it needs no `hnp`). For arbitrary plans,
    `hyps_unsat_of_unpaired` gives the same from `hnp` (no grid index stores the negated
    sphere list of X or L), which `bgw/r28_f1/check.py` (`hnp`) checks numerically on the
    Si-EPM Σ grid. For X and L no grid point stores the negated sphere even as a set, so `hnp`
    holds there for any sphere ordering (`check.json` `hnp_holds_any_order_X`/`_L`); the ordered comparisons
    (the rotated order Σ reads, and the sorted order, where it holds trivially since a negated
    increasing list is decreasing) matter only at Γ, whose negated sphere is stored, as a set,
    at Γ itself. Storing X or L once does not by itself give `hnp`: a finite cutoff
    sphere does not determine k. Either way, for O1 the theorem cannot be applied at all. With every plan's
    `neg` encoding `-k` on a grid that stores each k-point class once (trusted plan semantics, not a theorem, since `MF` has no k-coordinates), `MF.TR` also
    excludes every Γ-centred grid, BerkeleyGW's standard ε setup, and recomputing ε on
    Σ's grid cannot satisfy it (all 8 Σ grid points are time-reversal-invariant; Python
    check). A generalised `TR` (sphere permutation, umklapp, orthogonal rotation within
    degenerate multiplets at self-paired points) is open, not done.
  * The `q = 0` blocks `Z` carry an INPUT `E0` on both sides (`Espec` and `Etheory`). The
    long-wavelength head and wings are not derived in the composed theorem;
    `Espec_q0_input` only says BerkeleyGW's `q0` block can be that input (BRIDGE-Q0 is the
    separate `q0` analysis).
  * `hC` (`vb = vc`) is trivially dischargeable by `vc := vb`. The physical case, `vc`
    the bare point values, fails on the run (`vb` are mini-BZ averages).
  * On the Si-EPM run `Compat` FAILS whenever a block that the Σ q-list reads is derived
    (outside `Z`) (Python check, `bgw/r28_f1/check.py`): Epsilon
    (WFN, shifted 32-point grid) and Sigma (WFN_inner, unshifted 8-point grid) share no
    k-point, although cell, G-list and cutoffs agree and one fitted local potential
    reproduces both energy sets to ≤ 2.4e-7 meV (measured / float). The density hypothesis
    `DensOK` fails too (RHO not star-averaged, the +0.38 meV of BRIDGE-Q0). So claim 2 is
    a conditional identity, not instantiated on this run (`docs/reviews/R28-F1.md`).
* **F2, the GPP results are formal properties and consequences of the specified HL
  ansatz, conditional on its oscillator-strength prescription.** `fsum_moment` is
  `-π (O/(2w)) w = -(π/2) O` once `O` is supplied. It is not a derivation of the
  physical f-sum rule from the fermion system: `OmT` uses the same helpers (`factW`,
  `rhoF`, `dotB`, `vec`) as the spec, and its identification with the system's
  response moment is not independently anchored. This finding has no R28 Lean task;
  the correction is this wording. A stronger claim would need an independently
  anchored identification of the prescription under stated Hamiltonian/basis
  assumptions.
* **F3, `CompleteK κ` is an abstract scaled-frame completion.** For `κ` above the
  largest eigenvalue of `RᵀR` (which the Gershgorin `κ` is) the defect `κI - RᵀR` has
  full rank `N`, so an exact completion needs at least `N` rows. The `N - m` omitted
  eigenvectors of the finite Hamiltonian cannot satisfy it. The BRIDGE-COR enclosures
  are conditional enclosures for such a completion, not a certificate about the true
  omitted bands. Corrected statement (R28-F3, kernel-checked):
  `GW.Bridge.sigA_all_bands_lowdin` (with `sigA_all_bands_true`,
  `sigT_all_bands_true` and the energy-step versions, `GW/Bridge/CorPerturb.lean`): if
  the stored rows' Gram defect η_t = ‖RRᵀ − 1‖_F² < 1, there EXIST exactly orthonormal
  rows `P` within δ_t = √η_t of the stored rows (the proof uses Löwdin's construction,
  `Lowdin.lowdin_nat`; the statement does not pin `P` to `(RRᵀ)^{-1/2}R`), `P` has exact
  completions by exactly L − N_b rows (κ = 1, the physical count;
  `Lowdin.exists_completion_nat`), and EVERY such completion satisfies the BRIDGE-COR
  enclosure widened by an explicit propagation term. The physical omitted EPM
  eigenvectors complete the EPM's OWN eigenvectors, not `P`. Covering them needs
  `sigA_all_bands_true` with `RowDist` (a distance bound) at the distance `d` between
  the EPM eigenvectors and the stored rows; that `d` is neither formalised nor
  evaluated (a Davis–Kahan residual/gap bound would give it, and at N_b = 30 and 100 the
  cut splits an exact degeneracy, so that route needs care there). On Si-EPM (Python
  intervals, iv.py; at N_b = 18): δ_t ≤ 5.34e-14; the propagation at d = δ_t (`P` against the stored
  rows, not the EPM eigenvectors' distance) adds ≈ 2.6e-4 meV (a float diagnostic, ≤ 2.7e-4; the enclosure itself is an iv.py interval); O1 ∈ [−2813.0693,
  +2746.4706] meV at N_b = 18 (`docs/reviews/R28-F3.md`). `CompleteK κ` itself remains
  an abstract scaled-frame completion.
* **F4, the static remainder is not removed.** `SigAall` is `SigA` plus the omitted
  bands' `ACq + Pq`. Its static term `CSq + Σ ACq` vanishes under extra sufficient
  conditions (`κ = 1`, shift closure, `Gch` coverage); with `κ ≠ 1` it is `(κ-1)I/4`
  per normalized channel, and even at `κ = 1` a finite sphere need not be
  shift-closed (review witness: remainder `-1/8`). Earlier "static remainder `0`" and "exact all-band value"
  wording is withdrawn. Corrected statement (R28-F4, `GW/Bridge/CorResidual.lean`,
  `docs/reviews/R28-F4.md`): `SigAall = Σ_q (Xq + Σ_n Pq) + tailD + CORall`
  (`sigAall_static_split`). Under `CompleteK κ` alone the residual splits exactly as
  `CORall = corScale κ + corShift + corGch` (`cor_all_decomp`): the closure scale
  vanishes at `κ = 1`, the shift-closure defect for a shift-closed sphere, and the `Gch`
  term under `Gch` coverage. `cor_all_eq_zero`: the three together are SUFFICIENT for
  `CORall = 0`, not necessary: the parts can cancel (`nn_corAll_zero`, R28-R2: `κ = 2`, no
  shift closure, no `Gch` coverage, `corShift = -1/8`, `corGch = +1/8`, `CORall = 0`). On Si-EPM the last two fail.
  Python intervals (iv.py): `CORall` = -2.22 (X) / -3.75 (L) meV per band, +1.21 meV on
  O1 (shift-closure defect +1.31, `Gch` coverage -0.10).
* **Instantiation.** The composed identities are not instantiated on this run, and for
  O1 they cannot be instantiated on any standard BerkeleyGW calculation as formalized:
  * `hX` fails structurally for Σ(Eo) (`iw = 0`): at `q = 0`, `x = 0` exactly for
    `n1 = a` and its degenerate partners, and every BerkeleyGW Σ q-list contains `q = 0`.
    The spec replaces `x` by `TOL_Zero` there; `wxS_close` bounds the shift by
    `2·TOL_Zero`, but no Lean theorem propagates that bound to Σ. The `iw = 1`
    evaluation Σ(Eo + dE) is covered where the other hypotheses hold.
  * With `k0` at X or L (and `neg` encoding `-k` on a grid that stores each k-point class once: trusted plan semantics, not a theorem, since `MF` has no k-coordinates), no block satisfies `MF.TR`
    (`compat_selfpaired_no_TR`), and since `Z` is finite the hypotheses of `sigA_compat`
    are then unsatisfiable (`hyps_unsat_of_selfpaired`; for arbitrary plans,
    `hyps_unsat_of_unpaired` from the numerically checked `hnp`; F1 above).
  * In `sigA_compat` the `q = 0` screening blocks are an input `E0` on both sides (the
    independent-block `sigA_eps_eq_theory_q0` uses EpsSpec's finite-`q0` block instead, but
    does not tie the blocks to the Σ system).

  What the identities give is the exact correspondence of formulas under named
  hypotheses, with every departure named and, where measured, sized.

## The question

`GW/Endpoint/Kernel/SigmaSpec.lean` was transcribed from BerkeleyGW 4.0's Fortran (via
`bgw/endpoint/cert.py`). A specification copied from the code will also copy the code's
bugs. So the question is: is each formula in it what G0W0 with the Hybertsen-Louie (HL)
generalized plasmon pole (GPP) gives, and where it is not, what exactly is the
difference? The theory side DERIVES the frequency/time structure (B1: the pole signs from
the damped Fourier transform of the time-ordered `G0`), the HL-GPP kernel algebra
(`mode_eq`, B2's pole existence criterion and, for `0 < Ω²/I`, uniqueness) and the
static χ0/RPA structure, including the factor 4 = spin × two time orderings (E1–E3). It SHARES with the
specification, by definition and not derived: the bare exchange `Sig.Xq`; the plane-wave
matrix elements, normalisation and contraction (`Sig.quad`, `xS`/`pd`,
`vS = v/(N_q Ω)`; only the per-mode kernel is the theory's); the epsilon Coulomb
`vT = EpsSpec.vC`; the common-system pair density (EpsSpec's `M`); the HL
oscillator-strength helpers (F2); and `G0` itself, the textbook T = 0 closed form `G0t`
taken as a definition (it is not derived from a Fock-space `H0` here; only the Hubbard
dimer has that link). Then one theorem states that the spec equals the theory, and every
difference appears in it as a named hypothesis or as an explicit correction term. That
theorem is conditional: its hypotheses are not asserted, and in part fail, on the run
(see "Scope after REVIEW-28").

## The chain (all kernel-checked, axioms within `propext, Classical.choice, Quot.sound`)

| Stage | File | Key theorem | Statement |
| --- | --- | --- | --- |
| B1 | `GW/Bridge/FreqIntegral.lean` | `sigt_limit` | Setting: a finite basis, `G0` time-ordered at T = 0 (`g0_eq_G0t`: it is `ManyBody.G0t`, the textbook closed form taken as a definition, not derived from a Fock-space `H0`), and a pole-sum `W_c(τ) = Σ_k -i R_k e^{-i w_k abs(τ)}`, whose transform is `Σ R 2w/(ω²-w²)` (`wct_limit`). For `E` off the poles (`OffPoles`), as `η → 0⁺`, the damped transform `ftDamped η (i G0 W_c)` tends to `Σ_n Σ_k R [f_n/(E-ε_n+w) + (1-f_n)/(E-ε_n-w)]`. The signs are derived, not assumed. |
| B1 | same | `sigc_eq_terms`, `sigc_eq_sx_ch` | For `w ≠ 0` and with `A = 2wR`, the closed form equals `occupiedTerm` / `emptyTerm` of `GW.GPP.PoleCancellation`. It also equals the HL split: screened exchange `-A/(x²-w²)` over occupied states plus Coulomb hole `A/(2w(x-w))` over all states (for occupied `x ≠ ±w`), via `rawOccupied_eq_occupiedTerm`. |
| B2 | `GW/Bridge/GPPModel.lean` | `gppC_static`, `gppC_tail`, `fsum_moment` | Formal properties of the specified HL ansatz, conditional on its oscillator-strength prescription `Ω²`: the model `eps⁻¹-δ = Ω²/(ω²-Ω²/I)` has static value `-I` when `I ≠ 0` and `Ω² ≠ 0` (`gppC_static`; Lean's totalized division gives `0`, not `-I`, at e.g. `I = 1`, `Ω² = 0`), and tail `ω²(eps⁻¹-δ) → Ω²` unconditionally (`gppC_tail`). `fsum_moment` is the algebraic substitution `-π (Ω²/(2w)) w = -(π/2)Ω²` for `w ≠ 0`; the spectral function and its first-moment integral are not formalized. This is not a derivation of the physical f-sum rule (REVIEW-28 F2). It equals `GW.LL.gppInvEps - 1` when `0 ≤ Ω²/I` (`gppC_eq_gppInvEps`). |
| B2 | same | `single_pole_exists_iff`, `single_pole_unique` | A single positive pole that matches both constraints exists iff `(I = 0 ∧ Ω² = 0) ∨ 0 < Ω²/I`. When `0 < Ω²/I`, the pole is unique: `w = √(Ω²/I)`, `R = Ω²/(2w)`. In the degenerate branch `I = Ω² = 0` the residue is forced to `0` and `w > 0` is arbitrary. |
| B2 | same | `bgw_invalid_mode`, `static_pole_limit`, `sch_static_limit`, `ssx_static_limit`, `sch_static_error` | For a mode with `wt2 < 0`, BerkeleyGW sets `wtilde = 10^12`. This is the `w → ∞` static-COHSEX limit of the statically matched pole. Both kernels go to `-I`, with exact CH error `abs(I) abs(x)/abs(w-x)`. The f-sum constraint is given up. |
| B3 | `GW/Bridge/Bloch.lean` | `bloch_sigc_eq`, `bloch_limit` | Build the B1 system on SigmaSpec's own data: orbitals `(q, n)`, poles `(G_j, G_i)`, residues `M_i v_i M_j Ω²/(2w̃)`. Its closed form is `Σ_q Σ_n PT`, which is BerkeleyGW's sum over `q, n, G, G'`. So, off the poles (`OffPoles`), `ftDamped(i G0 W_c)` tends to it. |
| B3 | same | `bloch_wcFreq`, `screened_entry` | In this basis the channel `W_c(ω)` is `Σ M_i v_i M_j (eps⁻¹_GPP(ω)-δ)_{ji}`, with `eps⁻¹_GPP(ω)` the GPP model. Separately, `screened_entry` is an identity about `GW.LL.dielectric`, not a property of the GPP `eps⁻¹(ω)`: `W_{ji} = eps⁻¹_{ji} v_i = (eps⁻¹ diag v)_{ji}` solves `eps W = diag v` when `det eps` is a unit (hypothesis `h`); without `h` it can fail (for a singular `eps` the totalized `eps⁻¹` is `0`). |
| B3 | same | `pd_closure`, `pd_neg` | If the bands are complete and the sphere is shift-closed, then `Σ_n M_n(G) M_n(G') = ρ_aa(G-G')`. |
| B4 | `GW/Bridge/Compare.lean` | `mode_eq` | On every `ModeOK` mode, the spec's `CH/2 - [occ] SX` (`schM`, `ssxM`) equals the theory kernel. |
| B4 | same | **`sigA_eq_theory`** | `Sig.SigA = SigT + COR` under the named hypotheses `hC`, `hW`, `hX`, `hM`. |
| B4 | same | `cor_eq`, `chpart_sum_eq_exact`, `sigA_eq_theory_complete` | `COR = ½(CH_exact - Σ_n CH_static)`, and this is `0` when the bands are complete (`Bloch.Complete`), the sphere is shift-closed and `Gch` covers the kept differences. Under those hypotheses the spec is the theory. `Complete` is unsatisfiable on the stored dyadic rows (BRIDGE-COR), so this corollary never applies to the run's data. |
| B4 | same | `occ_pole_point`, `discrepancy_witness` | The discrepancy. See below. |

`SigT` is the theory Σ in `GW/Bridge/Bloch.lean`: bare exchange plus the B1/B3 GPP
correlation. Its bare exchange is the spec's `Sig.Xq`, and its correlation `PT` is the
spec's `Sig.quad` with the theory per-mode kernel (rows 19, 19a). It uses the true
symmetry-mapped `eps⁻¹` without the wing rule (`epsT`), the HL `Ω²` (`OmT`), the exact
energy offset `x` (`xT`), and the exact pole `w̃ = √(Ω²/I)`. It applies no threshold, branch, clamp or remainder.

## Departure table

Status key: **proved equal** = a theorem shows the spec formula is the theory formula.
**named approximation** = a documented BerkeleyGW approximation, which appears as an
explicit hypothesis or correction term, with its effect characterised. **shared** = the
theory is defined with the same choice, so the choice is a convergence or basis
parameter, not a formula difference. **shared (definitional)** = the theory side uses the
spec's own Lean definition, so the equality holds by definition and is not an independent
check. **named hypothesis** = an assumed property, not proved; a numerical oracle may test
it. **DISCREPANCY** = the spec differs from theory in a way that BerkeleyGW does not
document.

| # | Formula | Theory | SigmaSpec | Status | Lean |
| --- | --- | --- | --- | --- | --- |
| 1 | Frequency integral of `i G0 W_c` | occupied `B/(E-ε+w)`, empty `B/(E-ε-w)` | per mode `CH/2 - [occ] SX` | proved equal | `sigt_limit`, `bloch_sigc_eq`, `mode_eq` |
| 2 | HL SX/CH split, CH factor `½` | `-A/(x²-w²)` occupied + `A/(2w(x-w))` all | `ssxM` generic `w²I/(x²-w²)`, `schM` `wI/(x-w)` times `½` | proved equal | `sigc_eq_sx_ch`, `mode_eq` |
| 3 | GPP pole `w̃² = Ω²/I` | static + HL-tail match (given the prescribed `Ω²`) | `wt2 = O/I`, `wtilde = √wt2` | proved equal | `single_pole_unique`, `keep_facts` |
| 4 | HL `Ω²_{GG'}` | `ω_p² ρ(G-G')/ρ(0) (q+G)·(q+G')/abs(q+G)²` | `Om2S` | proved equal (given row 5); both sides use the same helpers, so this is a formula identity, not an independent physical identification (F2) | `om2S_eq` |
| 4a | `Ω²` head at `q = 0` | `q → 0` limit | `wpsq` on `G = G' = 0` | proved equal (limit is direction-independent) | `omT_head` |
| 4b | `Ω²` wings at `q = 0` | no pointwise value (direction-dependent, O(1/abs(q))) | `0` | named approximation, set to `0` by convention (BerkeleyGW's; also the theory's `OmT`): on the `G = 0` row the leading odd O(1/abs(q)) part averages to 0, but the even O(1) part `ω_p² ρ(-G')/ρ(0)` does not and is dropped (Q-3); the `G' = 0` column wing tends to 0 | `OmT` definition |
| 5 | Coulomb `v(q+G)` | `8π/(Ω abs(q+G)²)` per q (`vBareK_key`); singular at `q+G = 0` | mini-BZ averages `vb/(N_q Ω)` | named approximation, hypothesis `hC`; for the certified run the exact mini-BZ averages `vb`, `oq` are kernel-checked (`Coul.vb_hyp`, `oq_hyp`), and production's Monte Carlo averages differ from them (E1) | `sigA_eq_theory` (`hC`) |
| 6 | `eps⁻¹` wings at `q = 0` | the q0 inverse: unscaled row wing O(1/abs(q)) and column wing O(abs(q)); the finite limits are `t · (row wing)` and `(column wing)/t` (`q0_limit`). The row wing diverges like 1/abs(q) only if its leading coefficient is nonzero | zeroed | named approximation, hypothesis `hW` part 1 | `epsS_eq` |
| 7 | `eps⁻¹` wings at `q ≠ 0` | unscaled | row × `oq abs(q)/(8π)`, column × `oq/(vb abs(q))` | named approximation, hypothesis `hW` part 2; the factors are exactly 1 for point values | `wing_factors_point` |
| 8 | Drop thresholds `abs(I)`, `abs(Ω²)`, `abs(wt2)` < `TOL_Small` | mode kept | contribution 0 | named approximation (part of `hM`). If `I ≠ 0 = Ω²` the static match is violated. Modes with `I = Ω² = 0` agree exactly. | `bgw_dropped`, `invalid_of_one_zero` |
| 8a | Dropped mode with `Ω² = 0` in the ideal fcc metric: `q+G ⊥ q+G'` (BRIDGE-DISC) | exactly `0` at every `x` (zero strength); with the rounded `bdot` the theory kernel would instead be `∓I/2` at `x = 0` (discontinuous at `(x, Ω²) = (0, 0)`) | `abs(Ω²) ≤ 2.1e-8 TS` (pure rounding) → dropped → `0` | proved equal to the ideal-metric theory; covered by `sigA_eq_theory_disc` (hypothesis replaces `ModeOK` there) | `drop_eq_ideal`, `disc_mode`, `omB_ideal_eq_zero_iff`, `bExp_sub_ideal`, `thK_not_continuousAt` |
| 8b | Source comment `Sigma/mtxel_cor.f90:743-745`: "If Omega2->0, both the SX and the CH terms vanish" | true only for `x ≠ 0`; at `x = 0` the CH term tends to `∓I/2` | the code drops the mode (value `0`) | comment corrected (the code is right, the stated reason is incomplete) | `thK_tendsto_zero_of_ne`, `thK_x0_tendsto` |
| 9 | Invalid mode `wt2 < 0` | no single pole exists | `wtilde = 1/TOL_Zero = 10^12` | named approximation (part of `hM`): the static-COHSEX limit, error `abs(I) abs(x)/abs(w-x)` | `bgw_invalid_mode`, `sch_static_error` |
| 10 | Near-pole branch, occupied | `w̃I/(2(x+w̃))` | CH = 0, SX = `-Iw̃/(2(x+w̃))` | proved equal (off `x = w̃`, unclamped) | `mode_eq` case 2 |
| 11 | Near-pole branch, empty (`abs(x-w̃) ≤ max(½, w̃/500)` eV) | `w̃I/(2(x-w̃))`, a true pole of Σ_c | 0 | named approximation (regularisation of a real pole) | `emp_near_zero` |
| 12 | `sexcut` clamp, generic branch, `x < 0` | `w̃I/(2(x+w̃))` (pole at `x = -w̃`) | SX zeroed, CH kept: `½ w̃I/(x-w̃)` | named approximation (`gpp_sexcutoff`, documented input). It removes the hole pole but keeps CH, which is the T-005 discontinuity. | `occ_generic_clamp` |
| 13 | `sexcut` clamp, near-pole branch | as 12 | 0 | named approximation | `occ_near_clamp` |
| 14 | **Occupied mode at exactly `x = w̃`** | removable singularity, value `I/4` per unit weight | **0** (IEEE: `delw = NaN`, both branch tests fail) | **DISCREPANCY** | `occ_pole_point`, `discrepancy_witness` |
| 15 | `wx` with `abs(x) < TOL_Zero` | `x` | `TOL_Zero` | named approximation, hypothesis `hX`; the shift is < 2e-12 eV | `wxS_eq`, `wxS_close` |
| 16 | Static remainder | none (all bands) | `CSq + Σ ACq` | named approximation, explicit correction `COR = ½(CH_exact - CH_partial)` (Deslippe et al. 2013, empirical ½); `COR = 0` for complete bands with a shift-closed `k - q` sphere and `Gch` covering the kept differences (completeness is unsatisfiable on the stored rows); with complete bands alone `COR = corShift + corGch` (`cor_decomp_complete`, R28-F4) | `cor_eq`, `chpart_sum_eq_exact`, `sigA_eq_theory_complete`, `cor_decomp_complete` |
| 16a | `CH_exact` restricted to `G_i - G_j ∈ Gch` and `abs(I) ≥ TOL_Small` | all `G - G'` | restricted | named approximation (hypothesis `hch` of the closure theorem) | `chpart_sum_eq_exact` |
| 17 | Finite band sum `n < number_bands` | all bands | `nbq` bands | shared (`SigT` sums the same bands); corrected by row 16 | `SigT` |
| 18 | G-sphere truncations (`Gs` for eps, `Gb` for exchange, wavefunction spheres) | infinite basis | finite | shared (convergence parameters) | `SigT`, `Xq` |
| 19 | Bare exchange | `-Σ_occ Σ_G abs(M)² v` | `Xq` | shared (definitional): `SigT` contains the spec's `Sig.Xq` literally, evaluated with `vc`; row 5 applies | `SigT`, `sigA_eq_theory` |
| 19a | Plane-wave projection: matrix elements, normalisation, `(j, i)` contraction | `M_n(G)` from the Bloch rows, `1/(N_q Ω)` | `Sig.quad`, `xS`/`pd`, `vS = v/(N_q Ω)` | shared (definitional): `PT` is `Sig.quad` with the theory per-mode kernel `thK`; only the kernel is derived (rows 1-3; the Ω² of row 4 is the supplied HL prescription built from the spec's helpers, F2) | `PT`, `SigT` |
| 19b | `G0` | time-ordered T = 0 Green's function of a finite fermion system | - (enters through B1) | shared (definitional): the textbook closed form `G0t`, taken as a definition, not derived from a Fock-space `H0` (only the Hubbard dimer has that link); the B1/E1 "system" is energies, occupations and pair amplitudes | `G0t`, `g0_eq_G0t`, `gF_eq_G0t` |
| 20 | Symmetry map `idx`, `neg` of `eps⁻¹` | `eps⁻¹(Sq)` from `eps⁻¹(q)` | mapped block entries | shared; for the certified data the maps are computed in Lean from the irreducible headers by the transcribed unfolding (`U.`, `Unf.epsIn`); that `eps⁻¹(Sq)` physically equals the rotated `eps⁻¹(q)` is not formalised | `epsT` |
| 21 | Real flavour (`tan φ = 0`), T = 0 insulator occupation `n < nocc` | same | same | shared | - |
| 22 | Linearised `Eqp1`, forward difference `dE = 1 eV` | root of `E = ε + Σ(E)` | `Eo + Σ(Eo)/(1 - dΣ/dE)` | named approximation, not part of Σ | `eqp1_linear` |
| E-1 | Static `chi0` from `G0` (BRIDGE-EPS) | `lim_{η→0⁺} ftDamped(-i G0 G0)` at `ω = 0`: each occupied/empty pair twice, `1/(ε_v - ε_c)` | `chi` summand `M M/(E_v - E_c)` | proved equal | `chiF_limit`, `chiW_zero`, `epsTheory_entry_limit` |
| E-2 | Spin factor `2` | spin-diagonal density, spin-independent `ε`, occupation | factor in `4` | proved equal (closed shell, no SOC: shared) | `spin_chiS` |
| E-3 | Time-ordering factor `2` | particle-first pair `(c,k'),(v,k'-q)` + hole-first pair `(v,k+q),(c,k)` | factor in `4`; only the second pair is in the data | named hypothesis `TROK` (time reversal, grid closed under `k ↦ -k`); `4 = 2 × 2` proved, `2` refuted | `bloch_chi`, `factor_two_wrong` |
| E-4 | `1/(N_k Ω)` | orthonormal plane waves on the BvK supercell `V`, `1/√V` per amplitude | `4/(N_k Ω)` | shared: the theory is defined with `1/√V` per amplitude (`spinSys`; the plane-wave orthonormality behind it is by hand, not formalised); `V = N_k Ω` is `EpsBlock.OK.vol` (by definition in `MF.sp`); the `4 = 2 × 2` is proved (E-2, E-3) | `spinSys`, `chi_eq_triples`, `epsSpec_chi_eq_theory` |
| E-5 | `k + q` convention | momentum conservation: `⟨c,k\|e^{-i(q+G)r}\|v,k'⟩ ≠ 0` iff `k' = k + q` | valence at `k + q`, conduction at `k` | named hypothesis `ResOK` (+ numerical oracle: the swapped convention fails); Lean has no k-coordinates; in the common system `ResOK` holds by construction through the trusted index map `plus` (`MF.blk_ok`) | `ResOK`, oracle |
| E-6 | Sign of the denominator | `1/(ε_v - ε_c) < 0`, `chi` diagonal `≤ 0` | `eden = 1/(e_val - e_cond)` | proved equal | `chiW_zero`, `chiS_diag_nonpos` |
| E-7 | Finite conduction-band sum | all empty states | the Input's `cc` bands | named approximation, hypothesis `Bands`; explicit remainder `remR + remA` otherwise; in `sigA_compat` shared (the system is the finite band set, `MF.blk_bands`) | `epsSpec_eq_theory_rem`, `rem_zero` |
| E-8 | Eps G-sphere | infinite plane-wave basis | `Gs × Gs` block, inverse of the truncated matrix | shared (convergence parameter; the theory eps is the same block) | `epsM`, `blk` |
| E-9 | Symmetry unfolding of the states | full-grid Bloch states | `ks` built by `real_coeffs` | shared, recorded trust (`ResOK`) | `ResOK` |
| E-10 | Bare Coulomb in Epsilon | `8π/\|q+G\|²` (Ry, `e² = 2`), no average | `vC` | shared (definitional): `vT` is EpsSpec's `vC`; `q + G = 0` excluded (`EpsBlock.OK.qne`) | `vT` |
| E-11 | Row-scaled vs symmetrised eps; `W` | `W = v^{1/2} eps~⁻¹ v^{1/2}` | `eps_ij = δ - v_i chi_ij`, `W_ji = eps⁻¹_ji v_i` | proved equal (`v > 0`, `det eps ≠ 0`); `W` symmetric for symmetric `chi` | `sym_W`, `det_epsSym`, `WM_symm`, `WM_entry`, `etheory_W` |
| E-12 | `eps⁻¹ v` vs the RPA series | `W = (1 - v chi0)⁻¹ v` (`GW.LL.electronicW`) | matrix inverse | proved equal (`det eps ≠ 0`): unique solution of `eps W = v`, Dyson, Neumann terms + exact remainder, no convergence claim | `rpa_unique`, `rpa_dyson`, `rpa_neumann`, `theory_eps_eq_dielectric` |
| E-13 | Static limit | `W(ω) → W(0)` as `ω → 0` | static eps (then GPP, rows 3-9) | proved (gapped, `det eps ≠ 0`) | `wDyn_tendsto`, `chiW_continuousAt` |
| E-14 | `q = 0` block (head, wings) | `q → 0` limit | not EpsSpec (BerkeleyGW: small `q0`) | named approximation: input `E0` on the blocks `Z` | `Espec`, `Etheory`, `sigA_eps_eq_theory` |
| Q-1 | `χ0` at small `q` (BRIDGE-Q0) | head `~ q²`, wings `~ q`, body `O(1)` (orthogonality + k·p slope) | EpsSpec at `q0 = 0.001 b3` | proved (k·p slope `p_x` a hypothesis, `KPRay.OK`); measured: `χ_00/t0²` = -0.71438 vs limit -0.71444 | `head_tendsto`, `wing_tendsto`, `body_tendsto` |
| Q-2 | `q = 0` block of `eps⁻¹` | `q → 0` limit along `u`: head `1/ε_M`, body = inverse of the head-projected matrix, `t·`row wing, col wing`/t` | EpsSpec's inverse at `q0` | proved limit (under `KPRay.OK`, Q-1); finite-`q0` error bounded, relative to the computed `Ẽ0`, by `β²δ/(1-βδ)` ≤ 0.1812 (actual ≤ 5.4e-4); O1 moves ≤ 0.8 µeV | `q0_limit`, `schur_body`, `schur_head`, `q0_error` |
| Q-3 | `q = 0` wings | leading term odd in `q`, cell average 0; next order even `O(1)` (weight `1/N_q`) | zeroed | proved: leading term averages to 0 (inversion-symmetric cell); theory's `SigT` does not depend on them at all (`OmT = 0` there); next order dropped: named approximation | `thK_odd`, `wing_avg_zero`, `sigA_eq_theory_q0` |
| Q-4 | `q = 0` head | `⟨v g⟩` over the cell | `vb(0) · g(q0)` | named approximation: isotropy (`ε_M(u)` measured constant to 5e-11); error `≤ K(⟨8π/q⟩ + vb |q0|)` | `head_avg`, `head_avg_spec` |
| Q-5 | `q = 0` body direction | cell average over `u` of the direction-dependent body limit | one direction `S q0` (production: op 48, `±b2`) | named approximation: single direction; O(1) body dependence (0.012); O1 per axis 15.650 / 15.781 (sym. RHO), angular average 15.748 | `q0_limit` (limit depends on `u`) |
| Q-6 | RHO (`Ω²` via `ρ(G-G')`) | cubic ground-state density | unsymmetrized sum over the 3 IBZ k-points of WFN_co | **input departure** (mean field, not Sigma): star asymmetry 0.55; with the symmetrized RHO, O1 (op 48) 15.406 → 15.781 meV | measured only |
| Q-7 | `E0` input of BRIDGE-EPS | derived | - | removed: EpsSpec on every block, `q0` block included | `sigA_eps_eq_theory_q0` |
| C-1 | Omitted-band CH tail (BRIDGE-COR; replaces row 16's `½`) | dynamic tail `Σ_{n ≥ N_b}`: per mode `θ·(-I/2)`, `θ = w̃/(w̃ + ε_n - E) ∈ (0, w̃/(w̃ + D)]` | `½ ×` static tail (`COR`) | named approximation; conditionally ENCLOSED for an abstract `CompleteK κ` completion (not the true omitted eigenvectors, F3), whose target `SigAall` keeps its static term (F4): `\|tail - Σ v T c\| ≤ Σ \|v\| √T √T r`, `T` from `CompleteK`; the enclosure is 5.6 eV wide in O1 at `N_b = 18` (section BRIDGE-COR); the all-band Σ keeps a static residual `CORall = corScale + corShift + corGch` (`cor_all_decomp`, docs/reviews/R28-F4.md) | `thK_empty_enclosure`, `tailK_eq`, `sigA_all_bands`, `sigT_all_bands`, `cor_all_decomp` |

A valid mode with `I < 0` and `Ω² < 0` gives a positive pole with negative spectral
weight (`valid_neg_weight`). The model accepts such a mode. BerkeleyGW does not reject it
for the sign of `R`: if kept (`keepM`) it gets `w̃ = √wt2` (`wtM`, `keep_facts`); below
`TOL_Small` it is dropped like any other entry. This is a property of HL GPP, not a
departure from it.

## The discrepancy (row 14)

At exactly `x = E - ε_n = w̃` on an occupied band, theory gives the continuous value
`Ω²/(4w̃²) = I/4` per unit weight. This is the removable singularity of `occupiedTerm`,
and its occupied pole is at `x = -w̃`. The spec returns `0` (`occ_pole_point`, for every
kept valid mode; minimal instance `discrepancy_witness`: `I = Ω² = 1`, `x = 1`, spec `0`,
theory `1/4`). SigmaSpec encodes the IEEE behaviour of the Fortran, argued in
`GW/Endpoint/CertSexcut.lean`. The Python oracle re-implements the Fortran branch logic
in binary64 and reproduces the `0`. One ulp away, the source already gives `I/4`
(`tests/test_bridge.py::test_x_equals_wtilde_discrepancy`). So the discrepancy is a
single-point discontinuity. It is not documented as an approximation, and it has
measure zero. It was already known to the project as LEAN-CERT finding 1. This pass
identifies it as the only place where the transcribed formula departs from theory
without a documented BerkeleyGW reason. Its weight in a production run (whether any
`x = w̃` coincidence occurs exactly) is not measured here.

## What is and is not claimed

* Claimed, kernel-checked: the four modules above. That means 113 theorems, all within
  the allowlist. 59 of them are named in `GW/Audit.lean`.
* The main theorem is exact algebra about real-number definitions. Its hypotheses are
  NOT asserted to hold in the Si-EPM production run. In particular:
  * `hC` with `vc` the bare point values fails by construction, because `vb` is an
    average. (`vc := vb` discharges it trivially, but then `SigT` uses the averages.)
  * `hX` fails structurally at `iw = 0`, not only on this run: at `q = 0`, `x = 0`
    exactly for `n1 = a` and its degenerate partners, and every BerkeleyGW Σ q-list
    contains `q = 0`. So Σ(Eo) of no standard calculation is covered (`wxS_close` bounds
    the `TOL_Zero` shift, but no Lean theorem propagates it to Σ).
  * `hM` fails for dropped, invalid and clamped modes.

  The theorem says what the spec is in terms of theory plus these named departures. It
  does not say that the departures are small. Their per-mode effect is given by rows 8
  to 15. Their production-run weight per `ModeOK` class is measured in BRIDGE-MEASURE
  (Python), not bounded.
* The composed screening theorems (BRIDGE-EPS, BRIDGE-Q0) take the screening blocks
  `bs` and the self-energy state `gl`, `st` independently, with no common-system
  compatibility field (REVIEW-28 F1). That the blocks describe the same mean-field
  system as the self-energy is trusted, not proved. R28-F1's `sigA_compat` adds that
  identification under `Compat`, but for O1 its hypotheses are unsatisfiable when the
  plans' `neg` encodes `-k` on a grid that stores each k-point class once (trusted plan semantics, not a theorem, since `MF` has no k-coordinates; `hyps_unsat_of_selfpaired`), or given the numerically checked
  `hnp` (`hyps_unsat_of_unpaired`) (scope section, F1).
* Not claimed: that `SigmaSpec` is what the Fortran computes (that is the E1 layer),
  that production's Monte Carlo `vb`/`oq` equal the exact averages (they do not exactly; E1;
  the exact averages are kernel-checked in `Coul.vb_hyp`/`oq_hyp`), that the symmetry map
  is physically correct, or the accuracy of GW or of the GPP (layer 3).
* Independent numerical oracle: `tests/test_bridge.py`, 16 tests, numpy only. It never
  reads Lean output or the project's BerkeleyGW transcriptions.

## BRIDGE-EPS: the static RPA dielectric matrix, derived and compared with EpsSpec

Status: worker output, ready for review. Not accepted. Task: `.agent/tasks/BRIDGE-EPS.md`.

BRIDGE took `eps⁻¹` as an input. `GW/Endpoint/Kernel/EpsSpec.lean` (chi, v, eps) was
also transcribed from the code. BRIDGE-EPS derives the static RPA eps from the
time-ordered `G0` (the closed form `G0t`, a definition; the "finite fermion system" is
energies, occupations and pair amplitudes) and compares. **Result: no
discrepancy.** EpsSpec's `chi = 4/(N_k Ω) Σ_k Σ_v Σ_c M M/(E_v(k+q) - E_c(k))` is the
theory static `χ0`: the `4` is spin (`2`) times the two time orderings (`2`, equal by
time reversal, the named hypothesis `TROK`), the `1/(N_k Ω)` is the supercell
normalisation of the plane waves, and the `k + q` convention is the momentum-conserving
one (the named hypothesis `ResOK`, tested by the oracle). The bare Coulomb `vT` is
EpsSpec's `vC` by definition. Rows E-1 to E-14 above.

| Stage | File | Key theorem | Statement |
| --- | --- | --- | --- |
| E1 | `GW/Bridge/EpsChi0.lean` | `chiF_limit`, `chiW_zero` | `ftDamped η ⟨g\|-i G0(τ) G0(-τ)\|g'⟩ ω → Σ P P ((1-f)f' - f(1-f'))/(ω - Δε)`; at `ω = 0` this is `Σ_{v∈O} Σ_{c∉O} [P_cv P_cv + P_vc P_vc]/(ε_v - ε_c)` (`chiF`/`chi0F` are `ManyBody.chi0t`: `chi0F_eq_chi0t`) |
| E2 | `GW/Bridge/EpsBloch.lean` | `spin_chiS`, `bloch_chi`, `epsSpec_chi_eq_theory(_bands)` | for `V > 0`: spin sum `= 2/V`; with `ResOK`, `TROK`: `chiS = 4/V Σ_T M M/(E_v - E_c) + 2/V (remR + remA)`; EpsSpec's `chi` is `chiS` (minus the remainder) |
| E3 | `GW/Bridge/EpsRPA.lean` | `rpa_unique`, `rpa_neumann`, `theory_eps_eq_dielectric`, `wDyn_tendsto`, `sym_W` | theory eps is `GW.LL.dielectric`; when `det eps ≠ 0`, `eps⁻¹ v` is the unique RPA `W` and (gapped) the static limit of the dynamic RPA `W`; it equals the symmetrised form (`v > 0`, `det eps ≠ 0`) |
| E4 | `GW/Bridge/EpsCompare.lean` | **`epsSpec_eq_theory`**, `epsSpec_eq_theory_rem`, **`sigA_eps_eq_theory`**, `sigA_eps_eq_theory_complete` | EpsSpec's eps matrix `=` theory `1 - v χ0`; composed: `SigA (eps⁻¹ := inverse of EpsSpec's eps) = SigT (eps⁻¹ := inverse of theory eps) + COR` (Mathlib's totalized inverse on both sides; a genuine inverse when `det eps ≠ 0`, which is not established for these blocks) under BRIDGE's `hC`, `hW`, `hX`, `hM` plus `EpsBlock.OK` per `q ≠ 0` block |

What is not claimed: that the screening blocks `bs` and the self-energy state are the
same physical system (the theorem takes them independently; REVIEW-28 F1); that `ResOK` holds for the Si-EPM Input (the unfolding is recorded
trust, as in EpsSpec); that the band sum is converged (for the physical all-band system `Bands` fails for any
finite Input, and its size is the explicit remainder, not bounded here; in the R28-F1
common system it holds by construction because the system is the finite band set, so
there the truncation is shared, not removed); anything about `q = 0`
(input `E0`); that production's Monte Carlo `vb`/`oq` of Sigma equal the exact averages (BRIDGE row 5). The
numerical oracle `tests/test_bridge_eps.py` (numpy, never reads Lean output) checks E2
from first principles: the finite-difference density response of an `N_k`-cell 1D
supercell to a static cosine agrees with the Bloch formula to `1e-11`, and the factor `2`
and the swapped `k`/`k+q` convention both fail.


## Measured size of departures on Si-EPM (BRIDGE-MEASURE)

Status: worker output, ready for review, not accepted. Task `.agent/tasks/BRIDGE-MEASURE.md`.
Script `bgw/bridge_measure/measure.py`, data `bgw/bridge_measure/data/measure.json`,
tests `tests/test_bridge_measure.py`. Python only; no Lean statement changed.

**What was done.** The spec-A inputs of `bgw/endpoint/cert.py` were loaded with its own
loaders (its `epsinv_iv`, `real_coeffs`, `mtxel_iv`, `prepare`, the symmetry map and
`CertCoulomb`; cert.py and iv.py are not modified). A new per-mode classifier was written
from the Compare.lean / SigmaSpec.lean definitions (`keepM`, `wt2`, `wtM`, `Generic`,
`ClampG`, `ClampN`, `ModeOK`). It does not use cert.py's kernel, and `Ω²` is recomputed
from `Bloch.OmT`. Each class was then switched from the BerkeleyGW rule to the theory value
`thK` where one exists. Σ, Eqp1 and O1 were re-evaluated in iv.py interval arithmetic,
with every branch condition asserted decided and every denominator certainly nonzero.
The unswitched pass gives O1 ∈ [15.4057523, 15.4057537] meV (outward-rounded; Python
interval, iv.py), inside the E1 certificate
(`cert_o1.json`).

**Count cross-check (no mismatch).** A second, plain-float classifier covers cert.py's
exact accumulation scope: X, L and the 48 q = 0 ops, plus Γ v/c. It reproduces
`cert_o1.json` `branch_stats` exactly:

* `invalid_modes` = 163152
* `near_pole_modes` = 91316
* `sexcut_clamped` = 0
* no exact `x = w̃`

On the O1 scope, the interval and float classifiers agree:

* invalid: 1191456 (X), 595728 (L)
* occupied near-pole: 7380 (X), 4064 (L)

**Scope and units.** The O1 scope is X (bands 5 and 6) and L (band 5), each at E = Eo and
E = Eo + 1 eV, over all 8 q, all 18 n1 and every (G, G'). Counts are modes summed over that
scope, given as X / L. Σ|W| is the sum of |M_r v_c M_c| in eV over the same scope. ΔΣ is the
change in the multiplet-averaged Σ(Eo), in meV. ΔO1 goes through the linearised Eqp1, so it
also includes ΔΣ(Eo + 1 eV).

**Precision.** "rigorous" means an interval enclosure. The enclosure half-width of ΔO1 is
at most 2.3e-6 meV. A 0 marked "≤ ε" is an enclosure that contains 0 with half-width at
most ε; an unmarked 0 in a rigorous row is such an enclosure with half-width below 1e-7
meV, and "exact" marks an exact 0. A row with count 0 / 0 has an exact 0 (the class is
empty; its re-run enclosure, where computed, has half-width at most 1.32e-6 meV), and in the two
dropped `Ω² = 0` rows ("Lean `thK` = 0 = spec") the 0 is exact (theory and spec are both 0 per mode). The
only float-only numbers are the Σ|W| column and the conditioning diagnostics named in the
text.

| Class (hypothesis) | Count X / L | Σ\|W\| eV X / L | ΔΣ(X) meV | ΔΣ(L) meV | ΔO1 meV | Method |
| --- | --- | --- | --- | --- | --- | --- |
| generic, valid, unclamped (ModeOK 1) | 2274772 / 1136564 | 1308 / 711 | 0 | 0 | 0 (≤ 1.9e-6) | rigorous; `mode_eq` measured |
| occupied near-pole (ModeOK 2) | 7380 / 4064 | 3.9 / 2.9 | 0 | 0 | 0 (≤ 1.4e-6) | rigorous; `mode_eq` measured |
| `I = Ω² = 0` (ModeOK 3: q = 0 zeroed wings) | 9216 / 4608 | 76 / 87 | 0 | 0 | 0 | exact (both 0) |
| dropped, `|I| < TS`, `Ω² = 0` | 6912 / 3456 | 12 / 4.9 | 0 | 0 | 0 | Lean `thK` = 0 = spec; HL has no pole if `I ≠ 0` and the zero-residue pole if `I = 0` (the classifier certifies only that the `I` enclosure is not `[0, 0]`); theory value 0 either way |
| dropped, `|I| ≥ TS`, `Ω² = 0` | 70848 / 35424 | 59 / 30 | 0 | 0 | 0 | as above |
| dropped, `|I| < TS`, `Ω² ≠ 0`, `x ≠ 0` (hM) | 98496 / 49248 (all x) | 60 / 47 | ≈ 0 | -4e-7 | +1.1e-5 | rigorous enclosure plus rigorous bound; see note a |
| dropped, `0 < |Ω²| < TS`, `x ≠ 0` (hM) | 136512 / 68256 (all x) | 96 / 50 | -8e-7 | -2e-7 | +1.6e-5 | rigorous; 69120 / 34560 have `Ω²/I < 0` (no pole) |
| **dropped, `0 < |Ω²| < TS`, `x ≈ 0`** (hM) | 5408 / 1896 | - | **+4.588** | **+0.0446** | **+28.37** | rigorous on spec-A inputs, but ill-posed: note b |
| dropped, `|wt2| < TS` | 0 / 0 | 0 | 0 | 0 | 0 | - |
| **invalid, `wt2 < 0`** (hM): BGW static limit → skip (`invalid_gpp_mode 0`) | 1191456 / 595728 | 508 / 277 | -13.83 | +11.93 | **-20.62** | rigorous; no theory value exists (note c) |
| invalid → `w̃ = 2 Ry` (`invalid_gpp_mode 2`) | same | same | +1.217 | +8.756 | -5.78 | rigorous |
| **empty near-pole zeroed** (hM) → `w̃I/(2(x-w̃))` | 320 / 608 | 0.064 / 0.097 | 0 (-0.050 at Eo+1) | **-1.764** (+0.083 at Eo+1) | **+12.74** | rigorous; ill-conditioned (note d) |
| `sexcut` clamp, generic / near (hM) | 0 / 0 | 0 | 0 | 0 | 0 | exact at Eo, Eo+1 (note e) |
| occupied `x = w̃` exactly (row 14 DISCREPANCY) | 0 / 0 | 0 | 0 | 0 | 0 | exact (class empty); the count is rigorous: the classifier refuses to decide a possible `x = w̃`, and the pass completed |
| `TOL_Zero` `wx` replacement (hX) → exact `x` | 12 / 4 (a, n1, E) triples; 84612 / 29617 modes | - | 0 (≤ 4e-8) | 0 (≤ 4e-8) | 0 (≤ 1.4e-6) | rigorous |
| q = 0 wings zeroed (hW 1) → raw `eps0mat` wings | 128 per (n1, band, E) | - | 0 (≤ 5e-8) | 0 (≤ 8e-8) | 0 (≤ 2.3e-6) | rigorous; exactly 0 in the reals (note f) |
| q ≠ 0 wing factors (hW 2) → 1 | 91728 / 45864 wing entries (all q) | 409 / 270 | +2.367 | +1.365 | +0.676 | rigorous |
| Coulomb averages `vb` (hC) → bare `8π/abs(q+G)²` at q+G ≠ 0 | every entry | - | +216.5 | +226.8 | **-6.54** | rigorous; q+G = 0 kept at `vb` (note g) |
| static remainder COR, ½ → 0 | - | - | +596.5 | +743.8 | **-116.68** (O1 = -101.3) | rigorous |
| COR, ½ → 1 | - | - | -596.5 | -743.8 | +116.68 (O1 = +132.1) | rigorous |
| all well-posed switches together (hC, hW, hX, dropped x ≠ 0, empty near-pole), COR kept | - | - | +216.6 | +226.3 | -1.68 (O1 = 13.73) | rigorous |
| the same without the empty near-pole switch | - | - | +216.6 | +226.9 | -6.51 (O1 = 8.89) | rigorous |
| the same as the row two above, with COR off (closest to `SigT` on this basis) | - | - | +804.7 | +959.1 | -116.9 (O1 = -101.5) | rigorous |
| linearised Eqp1 → QP root (row 22, not Σ) | - | - | - | - | +53.58 (O1 = 68.99) | rigorous, from BGW-A A1 `qp_cert.json`, not recomputed |

**Reading the table.**

* The decisive departures are **COR** (-117 meV; O1 changes sign without it), **invalid
  modes** (31% of all modes; -20.6 or -5.8 meV depending on the substitute), and the
  **Coulomb average** (-6.5 meV).
* The following are ill-posed switches, not small corrections (notes b and d): the
  sub-ulp `Ω²` at `x ≈ 0` (+28 meV) and the empty near-pole regularisation (+12.7 meV).
* The following are certified negligible (≤ 2e-5 meV):
  * the hypotheses the theorem proves equal: ModeOK 1 and 2, measured here as `mode_eq`;
  * hX, `TOL_Zero`;
  * the q = 0 wing rule;
  * every dropped class away from `x = 0`.
* The row 14 DISCREPANCY and the `sexcut` clamp do not occur at the O1 evaluation energies.
* The switches are not additive. Every mode's value and branch depend on `v` and `eps⁻¹`, so
  the empty near-pole switch contributes +12.7 meV alone but about +4.8 meV on top of bare
  Coulomb.
* The linearised Eqp1 amplifies energy-dependent changes:
  ΔEqp1 ≈ ZΔs0 + Z² s0 (Δs1 − Δs0), with s0 ≈ -8.5 / -9.3 eV and Z ≈ 0.80. So a ΔΣ present
  only at Eo is multiplied by Z − Z² s0 ≈ 6.3 (X) / 6.8 (L) in ΔEqp1. This is why the rows with ΔΣ only at Eo
  (notes b and d) move O1 so much.

**Notes.**

* **a. Dropped modes with `|I| < TS`.** Where sign(I) is certain the theory value is enclosed
  exactly. 2160 / 1080 modes have `Ω²/I < 0` and no theory value. 88192 / 44520 have `I`
  enclosing 0: these are symmetry zeros of eps⁻¹ carried as noise of about 1e-14. For those,
  the monotone bound `|thK| ≤ abs(Ω²)/(2 w_min (w_min - abs(x)))` holds whenever `thK` exists,
  and it enters as a ± interval. 3328 / 1680 are unbounded (no usable bound) and are
  excluded. Their `Σ|W||I|` is 3e-15 eV (float).
* **b. `x ≈ 0` with `0 < |Ω²| < TS` (a real finding).**
  * **Where these modes are.** `x` is within `TOL_Zero` of 0 for n1 = a at q = 0, for the
    degenerate X partner, and for the symmetry-equivalent `k - q`.
  * **Why the theory value jumps.** For every `Ω² > 0`,
    `emptyTerm(w̃²I, 0, w̃) = -I/2`, however small `Ω²` is. At `Ω² = 0` the value is `0`
    (Lean totalisation), and HL has no pole there. So the theory kernel is discontinuous at
    `(x, Ω²) = (0, 0)`. BerkeleyGW's comment that both terms vanish as `Ω² → 0` holds only
    for `x ≠ 0`.
  * **Where the nonzero `Ω²` comes from.** All 136512 / 68256 of these modes have
    `Ω² = 0` exactly in the ideal fcc metric `B ∝ [[3,-1,-1],[-1,3,-1],[-1,-1,3]]`. The
    nonzero `(q+G')·B·(q+G) ~ 1e-17` comes from the binary64 `bdot`, because -1/3 is not
    representable. This was checked in exact rationals (`dot_exact`); the test is
    `test_drop_O_is_metric_rounding`.
  * **What the numbers mean.** The +28.37 meV is exact for spec A's inputs read as exact
    reals. With the ideal metric the same switch gives 0. The switch is therefore ill-posed,
    and BerkeleyGW's drop is the ideal-metric value. The x ≈ 0 subset of the `|I| < TS`
    class moves O1 by -1.3e-5 meV only.
* **c. Invalid modes.** `single_pole_exists_iff` fails for `wt2 < 0`, so the theory has no
  HL pole to switch to. The table therefore compares BerkeleyGW's default (static COHSEX,
  `w̃ = 10^12`) with its other documented options (`Sigma/mtxel_cor.f90:780-791`):
  * option 0 skips the mode;
  * option 2 fixes `w̃ = 2 Ry` and applies the ordinary branch rules;
  * option 1 (imaginary `w̃`) is complex-flavour only.
* **d. Empty near-pole.** `abs(x - w̃) ≤ ½` eV sits next to a true pole of theory Σ_c. At L one
  mode has `abs(x - w̃) = 3.6e-4` eV, and its largest single-mode contribution is 0.19 meV
  (float diagnostic). The switch value is finite and enclosed, but it depends strongly on
  where the poles fall. With bare Coulomb, `w̃` moves and the same switch gives about
  +4.8 meV.
* **e. sexcut clamp.** The clamp count is 0 at E = Eo and Eo + 1 eV, which is where the
  linearised O1 is evaluated. At the full-QP root energies of BGW-A A1 the clamp is active:
  `qp_cert.json` counts 57936 clamped modes. Its weight there is not measured here.
* **f. q = 0 wing rule.** At q = 0 the raw `eps0mat` wings are not small: the row wing reaches
  29 and the column wing 3e-5. The switch is still exactly null in the reals, for two
  reasons:
  * `OmT` is 0 on every q = 0 wing, which makes the GPP term 0;
  * in the static remainder, `M_n(G = 0) = δ_na` at q = 0, so `Σ_n M_n(0) M_n(G) = ρ_aa(G)`
    holds with any band set, and CH_exact and Σ CH_static cancel entry by entry.
* **g. Coulomb at q + G = 0.** The bare value diverges, so it cannot be switched off, and the
  average was kept there. For scale only (not a departure), setting that single entry to 0
  moves Σ(X) and Σ(L) by +2431 meV each and O1 by +91.3 meV. This is what the regularisation
  carries.

**Not claimed.** These numbers describe the named departures of one theorem on one
unconverged Si-EPM run (18 bands, 2×2×2 grid, 7 Ry). They are not an estimate of the GW or
GPP error, and not a convergence statement. The rigorous rows are enclosures for the
switched specification as defined here. They are not a physical error bar.


## BRIDGE-Q0: the `q → 0` screening, the `q = 0` wing rule, and the q0-direction spread

Status: worker output, ready for review. Not accepted. Task: `.agent/tasks/BRIDGE-Q0.md`.
Files: `GW/Bridge/EpsQ0.lean` (Q1), `GW/Bridge/EpsQ0Sigma.lean` (Q2),
`bgw/bridge_q0/q0.py` + `data/q0.json` (Q3), oracle `tests/test_bridge_q0.py`.
Rows Q-1 to Q-7 above.

**Q1 (Lean).** On a ray `q = t u` of the finite transition set (`KPRay`): orthogonality
`M_x(0, G=0) = 0` and a k·p slope `d/dt M_x = p_x` (hypothesis; the commutator form
`p = ⟨c|2(k+G)·u|v⟩/(E_v-E_c)` is used numerically, not derived) give head `~ q²`, wings
`~ q`, body `O(1)`. Conjugating by `diag(t at G=0, 1)` turns `eps(q)` into a scaled
RPA matrix `Ẽ(t) → Ẽ0(u)`; hence (`q0_limit`) head → `Ẽ0⁻¹_zz = 1/ε_M(u)` (`schur_head`),
body → inverse of the head-projected matrix (`schur_body`), `t·`row wing and col wing`/t`
converge (the unscaled row wing is then O(`1/q`), and diverges like `1/q` unless
`Ẽ0⁻¹_zj = 0`; on the Si data it does, row wing 29 at `t0 = 0.001`, measured). `parity_inv`: `u ↦ -u` flips the
wings, keeps head and body. `q0_error`: in the `ℓ∞` operator norm, EpsSpec at `q0` is
within `β²δ/(1-βδ)` of the computed `Ẽ0` entrywise (scaled wings included); `Ẽ0` is the
`q → 0` limit under `KPRay.OK`, and the two theorems are not composed in Lean.
Measured (intervals, upper bounds rounded up): `δ ≤ 0.05494`, `β ≤ 1.7275`, bound
`≤ 0.1812`; actual differences head ≤ 5.2e-6, body ≤ 5.4e-4, scaled wings ≤ 1.4e-4. The
bound is valid but loose.

**Q2 (Lean).** `thK_odd`: the GPP kernel is odd in `(I, Ω²)`; with odd leading wings and an
even weight the wing integrand is odd and averages to 0 over any inversion-symmetric
measure (`wing_avg_zero`) or inversion-closed direction set (`wing_sum_zero`).
`head_avg(_spec)`: with a direction-independent head limit (isotropy) and Lipschitz
constant `K`, `|⟨v g⟩ - vb g(q0)| ≤ K(⟨8π/|q|⟩ + vb|q0|)`. `sigA_eq_theory_q0`: the theory
`SigT` does not see the `q = 0` wings (its `OmT` is 0 there), so BRIDGE's `q = 0`
`WingFree` hypothesis (false for the raw `eps0mat`: row wing 29) is dropped.
**`sigA_eps_eq_theory_q0`: SigmaSpec with EpsSpec's inverse on every block, the `q0`
block included, equals `SigT` (theory RPA eps on every block) `+ COR`; the `E0` input is
gone.** What still separates it from a `q → 0` theory is named, not bounded through the
GPP: the single direction (Q-5), finite `|q0|` (entrywise bound only; measured effect on
O1 ≤ 0.8 µeV), the next-order even wing terms (Q-3).

**Q3: the 14.34 / 14.90 / 15.41 meV spread.** The 48 ops send `q0 ∥ b3` to the 8 `<111>`
directions, 6 ops each. O1 depends only on the axis: `±b3` (0-based op indices 0,2,4,7,12,13,16,19,29,30,36,37)
14.3435; `±b2` (9,11,22,23,28,31,38,39,41,43,45,47)
15.4058 (production's op 48 is index 47); `±b1` and `±(b1+b2+b3)` (the other 24) 14.9048. Two causes:

1. **Not physics: the RHO input is not cubic.** EPM writes RHO as
   `2 Σ_{k∈IBZ} w_k Σ_v |ψ_vk|²` over WFN_co's three IBZ points Γ, L = b3/2, X = (b2+b3)/2
   (weights 1/8, 4/8, 3/8) without star averaging (reproduced to 3.6e-15). So ρ(G) has
   only the symmetry that fixes both the b3 axis and the x axis: e.g. ρ = 1.7045 on
   `±b3`, 1.9009 on the other six first-shell vectors, and up to 0.55 differences further
   out. That is exactly the observed class pattern `{b3}`, `{b2}`, `{b1, b1+b2+b3}`.
   ρ enters Sigma only through HL `Ω² ∝ ρ(G-G')`. With the star-symmetrized ρ, Eqp1(X) is
   op-independent. L keeps two classes: q̂ along the L axis (b3), 15.6498, and the other
   three axes, 15.7813.
2. **Physics, what remains (0.131 meV).** The head is isotropic: `ε_M(u) = 15.3811` for
   every u, to 5e-11, since the 32-point Epsilon k-set is O_h-closed. So the head does not
   cause it, and neither do the finite `q0` (the exact k·p limit block moves O1 by ≤ 0.8
   µeV) or the wings (zeroed, and not seen by the theory). The cause is the body limit:
   it depends on q̂ at O(1) (max 0.012 over directions), through the head-projected rank-1
   term. Σ at L is not a cubic invariant, so q̂ along L differs from oblique q̂.
   A cubic crystal is isotropic only for the angular average, not per direction.

**The theory's O1 for the angular average** of the q = 0 cell: the k·p limit block at
direction u, weighted by the q = 0 Wigner-Seitz cell's `r(u)³`. This is a quadrature
estimate, not an enclosure. Each evaluation is an interval, and N = 200 and 400 Fibonacci
directions agree to 0.6 µeV.

| O1 (meV) | production RHO | symmetrized RHO |
| --- | --- | --- |
| spec A (q0 block, op 48) | 15.4058 | 15.7813 |
| k·p limit block, op 48 | 15.4050 | 15.7806 |
| 48-op mean of O1, q0 block (float mean of the per-op endpoints; not spec B) | 14.8897 | 15.7484 |
| angular average of the limit | **14.8730** | **15.7480** |
| per-direction range | 14.34 to 15.45 | 15.42 to 16.33 |

With a cubic ρ the 48-op average is already the angular average to 0.4 µeV. With the
production ρ it is 17 µeV off. Neither average is certified: the quadrature error is not
bounded, and the per-direction range shows that f(û) varies more between the axes than
along them.

**Not claimed.** No rigorous a priori `K` for the k·p remainder (δ is measured at `q0`).
No bound of the next-order even wing terms. No propagation of the entrywise `q0_error`
through the nonlinear GPP. `ResOK`/`TROK` for the `q0` block are the same recorded trust
as for other blocks. Isotropy is measured, not proved. RHO is a mean-field input defect
that the theory does not fix.


## The GPP kernel at (x, Ω²) = (0, 0) and the ideal fcc metric (BRIDGE-DISC)

Status: worker output, ready for review, not accepted. Task `.agent/tasks/BRIDGE-DISC.md`.
Lean `GW/Bridge/Disc.lean` (44 theorems, axioms within the allowlist), script
`bgw/bridge_disc/disc.py`, data `bgw/bridge_disc/data/{disc,coulomb_ideal}.json`, tests
`tests/test_bridge_disc.py`. Departure-table rows 8a and 8b.

**Question.** BRIDGE-MEASURE finding 2: at `x = 0` the theory kernel is `-I/2` for every
`Ω² > 0` but `0` at `Ω² = 0`. On spec A's inputs, 5408 (X) / 1896 (L) dropped modes at
`x ≈ 0` have `0 < abs(Ω²) ~ 1e-15`. Switching them to the theory value moves O1 by
+28.37 meV. Is O1 then an artefact of how `bdot` was rounded?

**Answer: no. O1 is unaffected.** The +28 meV is an artefact of evaluating the THEORY with
the rounded metric. The spec's drop rule already gives the ideal-metric value.

**D1, the discontinuity (Lean).** Write a valid mode by its pole, `Ω² = w̃² I`. Then
`thK = I w̃ / (2(x ∓ w̃))` (`thK_emp_eq`, `thK_occ_eq`), and:

* at `x = 0` it is `∓I/2` for every valid `Ω²`, however small (`thK_emp_x0`, `thK_occ_x0`),
  so the limit along `Ω² → 0` is `∓I/2` (`thK_x0_tendsto`);
* at `Ω² = 0` it is `0` for every `x` (`thK_zero_strength`), so the limit along `x → 0` is `0`;
* for `x ≠ 0` it tends to `0` as `Ω² → 0` (`thK_tendsto_zero_of_ne`);
* it is not continuous at `(0, 0)` (`thK_not_continuousAt`, `thK_not_continuousAt_occ`);
* in every neighbourhood of `(0, 0)` it takes every real value (`thK_cluster`, off the pole
  `x ≠ w̃`; the value `0` by `Ω² = 0`).

The physics is a zero-strength pole at zero energy. The mode's `W_c` pole has residue
`R = Ω²/(2w̃) = I w̃/2` (`residue_eq`), and its empty-band Σ term is `R/(x - w̃)`
(`emp_as_pole`). As `Ω² → 0`, the residue and the pole energy both go to 0 at the same rate
(`residue_tendsto_zero`, `wTilde_tendsto_zero`). At `x = 0` the ratio `-R/w̃ = -I/2`
survives. In frequency, `eps⁻¹ - δ = gppC` keeps its static value `-I` at `ω = 0` for every `I ≠ 0` and
`Ω² ≠ 0` (`gppC_static`), but it tends to 0 at every `ω ≠ 0` (`gppC_limit_off0`). So the
limit concentrates `-I` on `ω = 0`; it is not the zero function.

When the strength vanishes identically (`Ω² = 0`), the `W_c` entry is 0 at every frequency
(`gppC_zero_strength`). The B1/B3 residue is 0 (`blochSys_R_zero`,
`singlePole_zero_strength`), so the mode contributes nothing to the theory Σ at any energy.
With `I ≠ 0` such a mode has no single-pole HL form (`invalid_of_one_zero`). The value 0 is
the one that agrees with a vanishing `W_c`.

**D2, why `Ω² = 0` exactly (Lean + exact).**

* In crystal coordinates the ideal fcc reciprocal metric is
  `c[[3,-1,-1],[-1,3,-1],[-1,-1,3]]`. This is the Gram matrix of `(-1,1,1)`, `(1,-1,1)`,
  `(1,1,-1)`, so `(q+G')·B·(q+G) = c · cart(q+G')·cart(q+G)` (`dotM_ideal`).
* Off the `q = 0` head row, with `ρ(G-G') ≠ 0` and `v ≠ 0`, the ideal `Ω²_{GG'}` is 0
  exactly when `q+G ⊥ q+G'` in Cartesian space (`omB_ideal_eq_zero_iff`).
* The structural reason is **Cartesian orthogonality**. It is not a symmetry zero of `ρ` or
  of eps⁻¹: on every orthogonal pair of the run `ρ(G-G') ≠ 0` (`orth_rho_zero = 0`).
* The orthogonal pairs off the head row are:
  * 568 at `q = 0`;
  * 848 at each of the three X-type `q` (crystal `(0,½,½)` and permutations);
  * none at the L-type `q`.
  In total 3112 of the 52656 sphere pairs.
* `2(q+G)` is an integer vector, so the ideal dot is `c k/4` with `k ∈ ℤ`
  (`dotM_ideal_int`). It is therefore 0 or at least `c/4` in size (`ideal_gap`). The census
  finds the minimum nonzero value to be exactly `c/4`.
* The exported binary64 `bdot` is `c(4δ - 1)` with `c = bdot₁₁/3 = 6754344342867980·2⁻⁵⁴`.
  That `c` is itself binary64. The only difference is ONE ulp, `2⁻⁵⁴`, on each off-diagonal
  entry (`bExp_sub_ideal`, checked against the WFN header).
* A metric within `δ` entrywise moves the dot by at most `δ Σ|u_a||w_b|` (`dotM_perturb`).
  On an orthogonal pair the spec's `Om2S` is therefore pure rounding, bounded by
  `om2S_orth_bound`. On every orthogonal pair of the run that bound is at most
  `2.1e-8 TOL_Small` (exact rational evaluation, `disc.json` `census`).
* So the spec drops every such mode, and a dropped mode's value 0 is exactly the
  ideal-metric theory value, at every `x` including `x = 0` (`drop_eq_ideal`, `disc_mode`).
  At the level of Σ, `sigA_eq_theory_disc` restates `sigA_eq_theory` with `SigTD`, which is
  `SigT` with the ideal-metric `Ω² = 0` on the orthogonal pairs. Under it, those modes need
  only `abs(Ω²) < TOL_Small` instead of `ModeOK`.
* All 20 G-spheres that Sigma and Epsilon build from `bdot` are the same sets under the
  ideal metric. The smallest exact margin `abs(abs(q+G)² - ecut)` is 0.030 Ry.

**D3, rigorous (iv.py) on Si-EPM.** Spec A was re-evaluated with the ideal metric
everywhere it uses `bdot`:

* Epsilon's chi → eps → eps⁻¹ enclosure;
* the spheres;
* `Ω²`;
* `abs(q)` in the wing factors;
* the mini-BZ Coulomb averages, re-certified with Arb on the ideal cell
  (`coulomb_ideal.json`: max relative change 3.8e-16, and 0 flat-cone bounds instead of 26,
  because with the rounded metric some cones of the cell are nearly, but not exactly, flat).

Wavefunctions, energies and RHO are inputs and were held fixed. The pass used
bgw/bridge_measure/measure.py's classifier (imported, not modified).

| Quantity | Spec A (rounded `bdot`) | Ideal metric |
| --- | --- | --- |
| O1 enclosure (meV, outward-rounded) | [15.4057523, 15.4057537] | [15.4057523, 15.4057537] |
| `dropped, 0 < abs(Ω²) < TS` modes, X / L | 136512 / 68256 (5408 / 1896 at `x ≈ 0`) | 0 / 0 (all now exact `Ω² = 0`) |
| `dropped, Ω² = 0 exactly`, X / L | 70848 / 35424 | 207360 / 103680 |
| ModeOK, invalid, empty near-pole counts | as BRIDGE-MEASURE | identical |
| the "+28 meV" switch (`drop_O_x0` → theory), ΔO1 | +28.37 meV | 0 (class empty; enclosure ±1.3e-6) |

The two O1 enclosures overlap, and their largest possible difference, 1.29e-6 meV, is
below the spec-A width (≈ 1.31e-6 meV) and slightly above the ideal width (≈ 1.27e-6 meV). The +28 meV came from evaluating the theory
kernel, which is discontinuous at `(0, 0)`, at a sub-ulp `Ω²`. It is not a departure of the
spec. BerkeleyGW's source comment (`mtxel_cor.f90:743-745`, "if Omega2 -> 0, both the SX
and the CH terms vanish") is right only for `x ≠ 0` (row 8b). Its drop rule nevertheless
gives the right value here, because these `Ω²` are exactly zero in the ideal metric.

**Not claimed.**

* That every `0 < abs(Ω²) < TS` mode in other materials is a rounding zero. The argument
  uses this run's metric, spheres and data, and the bound of `om2S_orth_bound`.
* Anything about modes with a genuinely small but nonzero ideal `Ω²` at `x = 0`. There are
  none here, but there the discontinuity would be real and the drop rule would be a
  departure.
* That the ideal metric is "the" crystal. `c = bdot₁₁/3` keeps the diagonal; a different
  `c` rescales `v` and `abs(q)` by O(1e-16).
* That the wavefunctions would be unchanged under the ideal metric. The EPM step is
  upstream of spec A.

## BRIDGE-COR: a conditional enclosure for an abstract completion, in place of the empirical `½`

**Scope (REVIEW-28 F3, F4).** Every statement in this section is about a completion `cp`
satisfying `CompleteK κ`. With the Gershgorin `κ` (above `λ_max(RᵀR)`) no set of
`N - m` physical omitted eigenvectors satisfies it, so the enclosures are conditional
enclosures for an abstract scaled-frame completion, not a tolerance certificate for
the omitted bands of the finite Hamiltonian. Their target `SigAall` adds the omitted
bands' `ACq + Pq` and keeps the static residual `CORall = corScale + corShift +
corGch` (`cor_all_decomp`, R28-F4, `docs/reviews/R28-F4.md`). Where earlier text said
"ALL bands (static remainder `0`)" or "exact finite-basis all-band value", read
"`SigAall` for the completion, static residual included". Corrected F3 statement:
**R28-F3 correction** (full statement in the F3 item of "Scope after REVIEW-28"):
`GW.Bridge.sigA_all_bands_lowdin` covers EVERY exact (κ = 1, L − N_b rows) completion of
SOME exactly orthonormal rows `P` within √η_t of the stored rows, with an explicit
propagation term. It does not cover the EPM's own omitted eigenvectors: those need
`sigA_all_bands_true` with the distance bound `RowDist` at the EPM eigenvectors'
distance `d`, which is neither formalised nor evaluated. On Si-EPM (Python intervals,
iv.py) the propagation at d = δ_t adds ≈ 2.6e-4 meV at N_b = 18 (float diagnostic, ≤ 2.7e-4), and O1 ∈ [−2813.0693, +2746.4706] meV
at N_b = 18 (`docs/reviews/R28-F3.md`).

Status: worker output, ready for review, not accepted. Task `.agent/tasks/BRIDGE-COR.md`.
Lean `GW/Bridge/Cor.lean` (59 theorems, all within the allowlist); script
`bgw/bridge_cor/cor.py` (iv.py intervals), data `bgw/bridge_cor/data/cor.json`, oracle
`tests/test_bridge_cor.py`.

**The question.** `COR = ½(CH_exact - CH_partial)` (row 16) stands in for the omitted
bands `n ≥ N_b` of the Coulomb-hole sum, with an empirical factor `½`; it moves O1 by
±117 meV (BRIDGE-MEASURE). GW says the omitted bands contribute their DYNAMIC CH term.

**C1, one mode (proved).** On an empty band with `y = ε_n - E ≥ D > 0`, a valid GPP mode
(`Ω²/I > 0`, `w̃ = √(Ω²/I)`) gives exactly `thK = θ · (-I/2)` (the static CH term times `θ`)
with `θ = w̃/(w̃ + y)`, `0 < θ ≤ θ_hi = w̃/(w̃ + D)` (`thK_empty_ratio`,
`thK_empty_enclosure`). There is no `θ_lo > 0` from `D` alone: `θ → 0` as `y → ∞`; an
upper bound `Y` on the omitted energies would give `θ ≥ w̃/(w̃ + Y)` (`theta_lower`), and
none is assumed. Invalid modes have theory value `0` (`thK_empty_invalid`), every mode
`|thK| ≤ |I|/2` (`thK_empty_abs`). BerkeleyGW's own rule on an omitted band (kept modes,
valid or invalid with `w = 1/TOL_Zero`) is in the generic branch for `D > ½` and has the
same form with `w = wtM`; dropped modes give `0` (`schM_tail_ratio`, `specK_tail_mode`).
The energy step `Σ(E + 1 eV) - Σ(E)` has kernel `ψ = θ(w, y-1) - θ(w, y) ∈ (0, ψ(w, D)]`
for `w > 0`, `y ≥ D > 1` (`psi_pos`, `psi_anti`, `thK_diff_mode`; BerkeleyGW's rule,
`specK_diff_mode`, needs `D > 3/2`).

**C2, all bands (proved).** The weights `M_i v_i M_j` of a mode have mixed signs over
bands, so no ratio bound survives the sum. `tail_core`: with per-mode centre `c` and radius
`r` (`c = θ_hi/2 · (-I/2)`, `r = θ_hi/2 · |I|/2`),
`|tail - Σ_{ij} v_i T_ij c_ji| ≤ Σ_{ij} |v_i| √T_ii √T_jj r_ji` (Cauchy-Schwarz over the
omitted bands). The omitted-band pair sums `T_ij = Σ_{n ≥ N_b} M_n(G_i) M_n(G_j)` need no
omitted-band data: `T = κ Σ_v A_v(G_i) A_v(G_j) - Σ_{n < N_b} M_n(G_i) M_n(G_j)` with
`A_v(G) = c_a(Gq_v + G)` (`tailK_eq`), from completeness alone. Shift-closure of the
`k - q` sphere is not needed; with it the first term is BerkeleyGW's `ρ_aa(G_i - G_j)`
(`cloP_eq_rho`). The main statements are:

* `sigA_all_bands`: the spec's Σ with ALL bands of a `CompleteK κ` completion
  (`SigAall`, which keeps the static remainder `CORall = corScale + corShift + corGch`,
  nonzero in general: `sigAall_static_split`, `cor_all_decomp`) lies in the run's Σ
  (with its `COR`) plus `Σ v T cS ± Σ |v| √T √T rS`;
* `sigA_diff_all_bands`: the same for the energy step;
* `sigT_all_bands`, `sigT_diff_all_bands`: the theory Σ (`SigT`), with the generic form
  `sigT_tail_enclose`.

The hypotheses are only `D` (every omitted band has `x ≤ -D_t`) and `CompleteK κ`.
Neither is discharged for the true omitted bands (F3).

**Completeness had to be generalised (finding).** `Bloch.Complete` on SigmaSpec's dyadic
rows, the hypothesis of `chpart_sum_eq_exact` and `sigA_eq_theory_complete`, cannot hold
for the stored data. An exact completion of computed rows `R` needs `I - R Rᵀ ⪰ 0`. For
every O1-scope `k - q` point the stored binary64 rows have `‖R‖₂² - 1 ≈ +2e-15`, so
`I - R Rᵀ` has a negative pivot (exact rational LDLᵀ, `cor.json` `completeness_check`).
In addition, a dyadic completion of dyadic rows does not exist in general. Cor.lean
therefore takes the omitted bands as a REAL completion `cp` with `CompleteK κ`: computed
plus omitted rows resolve `κ I`. `κ` is a rigorous Gershgorin bound on `‖R‖₂²`, with
`κ - 1 ≤ 3.3e-14` (18 rows) and `≤ 9.7e-14` (168 rows). Because `κ` exceeds
`λ_max(RᵀR)`, `κI - RᵀR` is positive definite of rank `N`, so an exact completion
needs at least `N` rows. A physical completion has `N - m`. However small `κ - 1` is,
`CompleteK κ` is therefore not satisfied by the true omitted eigenvectors (REVIEW-28 F3,
two-dimensional witness in `docs/reviews/counterexamples.py`). `completeK_of_complete`,
`sigTall_of_state` and `sigAall_of_state` prove that for a larger dyadic state these are
the old notions.

**C3, Si-EPM numbers.**

*Where `D` comes from.* `D_t = RYD·e_18(k - q_t) - E`, where band 18 is the highest band
the run computed (`number_bands = 18`) at each `k - q` of WFN_inner. The EPM eigenvalues
are sorted, so every omitted band lies above it. `D` is 19.8 to 26.7 eV (X) and 19.2 to
26.0 eV (L) at `E = Eo`, and 1 eV less at `Eo + 1 eV`.

*Conditional O1 for the completion, heuristic replaced.* This is `sigA_all_bands` and
`sigA_diff_all_bands`, evaluated at 18 bands, with every other BerkeleyGW rule kept.

| quantity | ½-heuristic (run) | enclosure for a `CompleteK` completion, `D` only |
| --- | --- | --- |
| Σ(X) at Eo | -8.52474 eV | [-9.844, -6.754] eV |
| Σ(L) at Eo | -9.34982 eV | [-10.672, -7.478] eV |
| dΣ/dE, X / L | -0.2481 / -0.2510 | [-0.280, -0.229] / [-0.286, -0.232] |
| Eqp1, X / L | 4.5315 / 4.5161 eV | [3.35, 6.09] / [3.33, 6.18] eV |
| **O1** | **15.41 meV** | **[-2814, +2747] meV** (width 5.6 eV) |

The enclosure is uselessly wide. Per band the tail radius is ≈ 1.54 eV (X) and ≈ 1.60 eV
(L). The centre is +0.23 / +0.27 eV relative to the run's Σ. The finite-basis static tail
is -1.188 / -1.480 eV, against `2·COR` = -1.193 / -1.488 eV from BerkeleyGW's `ρ_aa`
closure. The -4.4 / -7.5 meV difference is `2·CORall`, the static residual that the
all-band Σ keeps: shift-closure defect `2·corShift` = -4.57 / -7.89 meV plus `Gch`
coverage `2·corGch` = +0.13 / +0.39 meV, with the scale term below 1e-9 meV
(docs/reviews/R28-F4.md). The ½ lies inside, as it
must, since nothing narrower is implied. Reading the enclosure as a uniform `θ` in
`COR(θ)` gives θ ∈ [-0.99, 1.61] (X) and [-0.76, 1.39] (L) (float diagnostic, rounded
outward). The uniform-θ family itself
gives O1 = -101.3, -42.9, 15.4, 73.7, 132.1 meV at θ = 0, ¼, ½, ¾, 1. With the theory
kernel on the omitted bands (invalid modes 0, dropped modes their HL value) O1 ∈
[-2490, +2417] meV.

*Why it is wide.* Three reasons:

* From `D` alone `θ` can be anything in `(0, θ_hi]`, with `θ_hi = w̃/(w̃ + D)` and
  `D ≈ 20` to 27 eV. Under BerkeleyGW's invalid-mode rule `θ_hi ≈ 1`.
* Cauchy-Schwarz over mixed-sign weights inflates the radius to about 1.3 times the whole
  static tail.
* The X and L enclosures are independent. The linearised `Eqp1 = Eo + Σ/(1 - dΣ/dE)`
  passes Σ's width on with a factor of about 0.8.

*What shrinks it: more bands.* This diagnostic uses the omitted bands' energies, so it is
NOT part of the bound. A second pinned EPM run with `NumberOfBands 168` in WFN_co.in
(the whole 11 Ry basis at the 168-vector spheres) supplies bands 19..168. The enclosure
is then re-evaluated with `N_b` computed bands:

| `N_b` | 18 | 30 | 60 | 100 | 168 |
| --- | --- | --- | --- | --- | --- |
| O1 enclosure, meV | [-2814, 2747] | [-1327, 1287] | [-322, 301] | [-58.7, 48.5] | **[-4.05, -3.51]** |

Python intervals (iv.py), for a `CompleteK κ` completion of the top rows. At `N_b = 30`
and `100` the cut splits an exactly degenerate pair at the O1 `k - q` spheres (gap
≈ 2e-15 Ry, float), so the truncated band set there depends on the solver's choice
within the multiplet; `N_b = 18`, `60` and `168` have gaps ≥ 0.0037 Ry.

At `N_b = 168` only the ≤ 6 top basis bands of the 174-vector spheres (ε ≈ 150 eV) are
still enclosed. The result, **O1 ≈ -3.8 ± 0.3 meV**, is a band-converged diagnostic in
the same basis: the spec's Σ over all bands of the finite basis (Python interval,
BerkeleyGW cross-checked at 164 bands, not kernel-certified; for R28-F3's κ = 1
completions of `P` it is [-4.044, -3.512] meV). It is not an exact all-band value with
the remainder removed. The top rows enter through `CompleteK κ` (F3), and the value
still contains the static residual `CORall` (BerkeleyGW's `CSq` plus the `ACq` of every
band), which is not zero: on O1 it contributes +1.21 meV, of which the shift-closure
defect is +1.31 and the `Gch` coverage -0.10. With the residual removed the all-band O1
is [-5.25, -4.71] meV (Python interval, iv.py; `residual.json`
`lowdin.residual_removed`, from R28-F3's κ = 1 enclosure at 168 bands;
docs/reviews/R28-F4.md), outside [-4.05, -3.51], so the difference exceeds the stated
±0.3. That the residual's shift + `Gch` part carries over unchanged to that completion is
argued (it reads no `k - q` band), not proved. Neither number is kernel-certified. Compare
≈ 15.40575 meV, the specification's kernel-checked value for this run as configured (18 bands,
½ remainder; a code claim; unaffected). The following are measured, not proved:

* Σ(Eo) itself is close to the heuristic. ΔΣ = +8 meV (X) and +13 meV (L), which is an
  effective θ of 0.493 / 0.491.
* The static ½ has no energy dependence, and the omitted bands do. dΣ/dE changes by -8.6
  (X) and -10.4 (L) meV/eV. Through the linearised Eqp1 this moves Eqp1 by +53 / +72 meV
  and O1 by -19 meV.
* With the theory kernel on bands 19..168 the all-band O1 is [-9.62, -9.23] meV. The same +1.21 meV static residual is included.

*Cross-check against the Fortran.* A pinned BerkeleyGW Sigma run with `number_bands 164`
(its own COR included; 164 is the largest count that splits no degenerate multiplet)
gives O1 = -3.76085 meV. The same Σ here gives -3.75499 meV (interval width 1e-6 meV), which agrees at
the 5.9 µeV level; E1 found 5.2 µeV at 18 bands. This validates the added bands, not a
vanishing remainder: both sides include their own `COR` (R28-F4).

A sharper majorant is a second lever, but it is not the main one. A float prototype
(scratch, not committed, not rigorous) splits the kernel into `w̃`-bins. For each bin it
uses the spectral decomposition of the bin's static matrix instead of entrywise
Cauchy-Schwarz. At its best (4 bins) the width of Σ(X) is 1.7 eV, against 3.1 eV here.
With one bin it is nearly sign-definite, which leaves about `θ_hi · |static tail| ≈ 0.8`
eV; that remainder is set by `D` alone. Only information on the omitted energies can
beat it: an upper bound, or first moments `Σ_n |M_n|² ε_n` from the Hamiltonian.

**Not claimed.** The following are not claimed:

* The finite-basis "all bands" of the 11 Ry EPM basis are not the infinite-basis limit.
  The rigorous table above is an enclosure of `SigAall` for an abstract completion
  (`CompleteK κ`), not a physical error bar, and not a certificate for the true omitted
  eigenvectors (F3).
* That the all-band Σ has no static remainder. `κ = 1`, shift-closure and `Gch`
  coverage together are sufficient for `CORall = 0` (`cor_all_eq_zero`), not necessary.
  On Si-EPM the last two fail, and `CORall` = -2.22 (X) / -3.75 (L) meV per band (Python
  intervals, iv.py; docs/reviews/R28-F4.md).
* The all-band numbers are diagnostics that use the omitted energies.
* The consistency between the 18-band and the 168-band WFN_inner is measured, not proved.
  The first 18 bands agree up to degenerate rotations, and the run's O1 is reproduced
  bit-for-bit in intervals from the 168-band file.



## BRIDGE-FIX: E14 test-order failure, and where the non-cubic RHO comes from

Status: worker output, ready for review, not accepted. Handoff `.agent/handoffs/BRIDGE-FIX.md`.

**E14 under `pytest tests`.** `cert.STATS` is a module-level counter dict that
`SigmaIV.kernel` increments. `cert.main` reported it without resetting it, so its
`branch_stats` included counts from any earlier in-process evaluation. A1's
`qp_cert.certify_root` rejects wide brackets because they have undecided branches,
and that leaves `undecided_sexcut = 6` behind. Pytest runs `test_endpoint_a`
before `test_endpoint_e1` (alphabetical order), so E14 saw a nonzero undecided
count that was not its own. The fix: `cert.main` and `qp_cert.main` clear the
counters on entry and report a copy. E14 now seeds a stale `undecided_*` counter
before it calls `cert.main`, so the gate checks this every time, whatever ran first.
`scripts/verify.py` runs `unittest` over `gates.SCIENTIFIC` in list order. There
`test_endpoint_e1` precedes `test_endpoint_a`, and the bridge modules before it
leave `cert.STATS` empty (measured), so the gate did not hit the failure.

**Why RHO is not cubic: the testsuite input meets a converter limitation. It is
not documented and it is not intended.**
`epm2bgw` computes RHO in `CalculateDensity`
(`MeanField/EPM/pwHamMod.f90:501-550`) as a plain weighted sum
`Σ_k w_k Σ_{n≤nocc} |ψ_nk(r)|²` over exactly the k-points it was given (`:523-533`).
There is no loop over symmetry operations and no star sum. The 48 operations from
`get_symmetries` (`epm2bgw.f90:431`) are only written into the headers
(`epm2bgw.f90:612-616`). The result is multiplied by `2/nspin` (`:593`) and written
out. `KPointsList` takes the listed points and normalises the weights
(`kPointsMod.f90:178-215`). It never unfolds them. The testsuite's
`Si-EPM/WFN_co.in:39-45` (byte-identical to `bgw/export/WFN_co.in`) lists the three
IBZ points Γ, (0,0,½), (0,½,½) with star weights 1, 4, 3. Those weights are correct
for IBZ use in Epsilon and Sigma, but not for a density that is never star-summed.
That input is the cause. In BerkeleyGW 4.0, `CalculateDensity` is only correct when
the k-list is symmetry-closed, and neither `MeanField/EPM/README` nor the code says
so. `Si.test` checks only WFN_co eigenvalues (lines 34-36), never RHO. Replayed from
`WFN_inner` with weights 1/8, 4/8, 3/8, RHO is reproduced to 7.1e-15
(ρ(±b3) = 1.704458, other first-shell vectors 1.900884).
Sigma does not repair it. `read_rho` (`Common/read_rho_vxc.f90:124-215`) reads the
data (`:173`), checks only that ρ(0) is real and positive (`:186-200`), and only
warns if the inversion reality `c(G) = c(-G)*` fails (`:203-210`, `:218-240`). Then `wpeff`
(`Sigma/wpeff.f90:158-161`) uses `ρ(G-G')` directly in the frame of the rotated
full-BZ q. So the asymmetry reaches `Ω²` as measured in BRIDGE-Q0 (row Q-6).
