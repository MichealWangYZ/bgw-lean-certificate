# Details: claims, evidence and caveats

This is the complete statement of what the project establishes, with every hypothesis and
caveat. The short overview is the [README](../README.md).

## Formalized G0W0/GPP components and certified numerical evaluation of a BerkeleyGW Si-EPM benchmark

> We formalized selected mathematical components of the real-valued
> G0W0/Hybertsen–Louie GPP workflow in Lean and developed kernel-checkable numerical
> certificates for a fixed BerkeleyGW 4.0 Si-EPM specification. The project contains
> conditional theory-to-specification identities and documents the assumptions,
> implementation conventions, and exceptional cases at their boundaries. For the pinned
> calculation, the recorded production O1 differs from the certified specification
> enclosure by at most 5.21 micro-eV. Binary decoding/export, source-to-specification
> correspondence, production execution, and the remaining physical identifications are
> not all end-to-end formally verified.

The title and the quoted paragraph are the wording that the adversarial review of PR 28
proposed ([`docs/reviews/REVIEW-28-adversarial.md`](reviews/REVIEW-28-adversarial.md),
summarised in [`docs/reviews/README.md`](reviews/README.md)). None of the first three
steps it names (decoding/export, source-to-specification correspondence, production
execution) is formally verified; see "Trusted, not proved" below. This project does
**not** claim to have formally verified the core physics of BerkeleyGW.

Status (2026-10-12): **accepted within the documented scope** by the bounded R28-R3
closeout review ([`docs/reviews/R28-R3-INDEPENDENT.md`](reviews/R28-R3-INDEPENDENT.md); seal record
[`.agent/handoffs/BGW-SEAL-2026-10-12.md`](../.agent/handoffs/BGW-SEAL-2026-10-12.md)). That review is an
AI-assisted technical review (Codex), separate from the Claude authoring session; it is not a
human-maintainer signature and not an independent replay of the toolchain. Scientific work is
frozen; the disclosed open questions below are parked, not pending fixes.

## Where to read

| Document | Content |
| --- | --- |
| [`.agent/STATE.md`](../.agent/STATE.md) | current state, claims with their kind of evidence, open decisions |
| [`docs/CODEMAP.md`](CODEMAP.md) | canonical and archived modules per layer, gates, dependency rules |
| [`docs/ENDPOINT.md`](ENDPOINT.md) | the pinned calculation, observable O1, specification (§4), the three error layers |
| [`docs/BRIDGE.md`](BRIDGE.md) | conditional theory-to-specification identities and the departure table |
| [`docs/reviews/`](reviews/README.md) | REVIEW-28, its counterexample script, and the post-fix review R28-R2 |
| [`docs/review/index.html`](review/index.html) | generated reviewer's guide to the chain of item 1 below: each Lean definition next to the BerkeleyGW source it transcribes |

## What is established, and with what evidence

Evidence labels: **kernel-checked** (a Lean theorem, standard axioms only); **Python
interval** (outward-rounded binary64 interval arithmetic, `iv.py`, not re-checked in Lean);
**measured** (plain floating point or a production run); **trusted** (an input or
correspondence assumed, not checked mechanically).

**1. Certified numerical evaluation of the specified finite calculation (kernel-checked).**
`GW.Endpoint.Kernel.Headline.o1_enclosure_irr_unconditional` (target `GWKernelData`) has no
hypothesis. It proves that O1_specA = Eqp1(X, bands 5–6 average) − Eqp1(L, band 5), the
real number defined by the Lean specification, lies in
[8880811588953599/2^59, 8880812351936001/2^59] eV, i.e. in [15.405752349, 15.405753673] meV
(decimals rounded outward; width 1.32 neV). Its inputs are:
* the spheres, coefficient rows, energies and ε index maps, unfolded in Lean from the
  irreducible WFN/WFNq/WFN_inner literals;
* the exact mini-BZ Coulomb averages `vbTrue`/`oqTrue`;
* the exact ε⁻¹ of the specified ε blocks.

`Headline.o1_pos_irr_unconditional` proves Eqp1(X) > Eqp1(L). It compares X and L only.
That the conduction minimum among all sampled k-points (Γ included) is at L is a Python
interval result (`cert_o1.json`, `CBM_certainly_at_L`). The older names stay valid:
`Coul.o1_enclosure_unconditional` (the same interval, on the S3 literals rather than the
irreducible data), `U.o1_enclosure_irr` (irreducible data, but keeps the Coulomb-box
hypotheses `VbHyp`) and `S3.o1_enclosure`.

Scope: one input, BerkeleyGW 4.0's `testsuite/Si-EPM` with 18 bands and a 7 Ry screened
cutoff, and one code path: real flavour; GPP with the default invalid-mode convention;
`fdf = 2`, dE = 1 eV; no truncation; `avgcut = 1e12`; Vxc = 0; 8 q-points.

Production: the recorded production O1 = 15.400547 meV (`sigma_hp.log`, measured) agrees
with the spec-A enclosure to 5.21 µeV. This distance is checked in exact rational
arithmetic against the kernel-checked endpoints, allowing 1 neV of print rounding
(`tests/test_endpoint_e1.py::test_o1_enclosure_and_layer1_bound`). Individual Eqp1 differ from spec A by ≈ 0.14–0.18 meV (CH by
≈ 0.14–0.30 meV), because production uses Monte Carlo Coulomb averages and spec A the exact ones;
these differences largely cancel in O1. With production's own Monte Carlo averages,
`cert.py` (Python interval) encloses the printed Eqp1 of the four O1/O2 states and O1
(`test_production_conventions_enclose_production`).

The theorem is about the specification evaluated on fixed data, not about the Fortran
executable. Trusted, not proved:
* the decoding and export of the run files into Lean literals (`kernel_export.py`,
  `bgwio.py`). The density list RHO and the run parameters (cutoffs, q-list, scales) are
  export literals. No committed digest links the literals to the run files; a
  field-by-field decode comparison was done in review, but it is not automated;
* the correspondence between the BerkeleyGW Fortran and the specification. The post-fix
  review (by the authors' supervising agent, not an independent reviewer) compared them line by line with pristine BerkeleyGW 4.0 on every active code
  path and found no discrepancy (`docs/review/index.html` sets them side by side). That
  is source reading plus numerical agreement on one run, not a proof;
* the production execution.

**2. The two O1 numbers, and what each is.**
* **≈ 15.40575 meV** (kernel-checked, item 1) is the specification's value for this run as configured
  (18 bands, the empirical `½` static remainder). It is a code claim about the specified
  18-band calculation, not the physical band ordering.
* **≈ −3.8 meV** is a band-converged diagnostic in the same basis: the spec's linearised
  O1 with the Σ band sum over all 168 computed bands of the 11 Ry EPM basis (ε from the
  18-band run), static residual included. The ≤ 6 remaining rows of the 174-vector
  spheres are enclosed over every exact completion of the Löwdin rows, not the EPM's own
  omitted eigenvectors (see F3 below). It is the Python interval [−4.05, −3.51] meV
  (R28-F3). BerkeleyGW's own 164-band run gives −3.76085 meV (measured). It is not
  kernel-certified.
* Without the static residual the all-band value is [−5.25, −4.71] meV (Python interval,
  `bgw/r28_f4/data/residual.json` `all_band_O1_meV.lowdin.residual_removed`
  [−5.2499, −4.7189], outward; computed with R28-F3's own dΣ/dE). That the residual's shift and `Gch` parts carry over
  unchanged to the Löwdin completion is argued (they read no k − q band), not proved. The
  164-band BerkeleyGW run contains BerkeleyGW's own static remainder, so it does not
  cross-check this value.

So C1 (O1 > 0) holds for the specified 18-band calculation and is not robust to the band
count. At 18 bands it is not robust to the static-remainder convention either: BerkeleyGW's
own unremaindered Eqp1′ columns give O1 = −101 meV (`docs/ENDPOINT.md` E1/E2). Which number is the project's reference is an open owner decision.

**3. Conditional theory-to-specification identities (kernel-checked algebra; the Si
numbers in this item carry their own labels).** `GW/Bridge/*` proves the transcribed
specification equal to a theory-side self-energy and static RPA dielectric matrix, plus
named correction terms, under named hypotheses.
* **Derived in Lean:** the frequency/time structure (B1: pole signs from the damped
  Fourier transform of the time-ordered `G0`); the HL-GPP kernel algebra (`mode_eq`, B2's
  pole existence criterion and, for `0 < Ω²/I`, uniqueness); the static χ0/RPA
  structure, including the factor 4 = spin × two time orderings (E1–E3).
* **Shared with the specification by definition, not derived:** the bare exchange
  `Sig.Xq`; the plane-wave matrix elements, normalisation and contraction (`Sig.quad`,
  `xS`/`pd`, `vS` = v/(N_q Ω); only the per-mode kernel is the theory's); the ε Coulomb
  `vT = EpsSpec.vC`; the common-system pair density, which is EpsSpec's `M` with momentum
  conservation built in through the index map `plus`; the HL oscillator-strength helpers
  (`factW`, `rhoF`, `dotB`, `vec`). `G0` itself is the textbook T = 0 closed form `G0t`,
  taken as a definition. The bridge does not derive it from a Fock-space H0; only the
  Hubbard dimer has that link.
* **What the identities give.** They are conditional identities. They are not instantiated
  on the certified run. For O1 they cannot be instantiated on any standard BerkeleyGW
  calculation as formalized: `hX` fails at q = 0, iw = 0; in the common-system
  `sigA_compat`, `MF.TR` cannot hold at X and L (with `neg` encoding −k on a grid that stores each k-point class once: trusted plan semantics, not a theorem, since `MF` has no k-coordinates) and the q = 0
  block is an input `E0` (the independent-block `sigA_eps_eq_theory_q0` uses EpsSpec's finite-q0 block instead,
  but does not tie the blocks to the Σ system). All three under F1. What they give is the exact
  correspondence of formulas under named hypotheses, with every departure named and,
  where measured, sized (`docs/BRIDGE.md`, "Scope after REVIEW-28").

The review findings bound what may be said:
* **F1 (one system).** The composed bridge takes the screening blocks and the self-energy
  state independently. `GW.Bridge.Common.sigA_compat` restates it for blocks, `Gl` and
  `St` that are images of one `MF` under the plans (`Compat`). `MF` is a data record
  (grid, spheres, integer coefficient rows, energies, `nocc`, cell, RHO list). It requires
  no orthonormality and no Hamiltonian or eigen-equation. Since R28-R2, `Compat` requires
  `k0` and every `k0 − q_t` to be grid points (fields `k0`, `minus`). Before that, the Σ
  state could sit at an off-grid index, and REVIEW-28's adversarial case (same screening,
  arbitrary Σ energies) met the predicate; `offgrid_loophole` keeps that construction as
  the record. `Compat` is satisfiable (`compat_self`), and, given one non-input block whose
  `plus` map is onto the grid, the adversarial case is compatible with no system
  (`compat_st_unique`, `compat_energy_shift`). `MF.blk_ok` proves
  `ResOK`, `TROK`, `Bands` and `vol` for the system's own blocks. `ResOK` and `Bands` hold
  by construction of the pair density; `TROK` holds only given `MF.TR`. Limits:
  * `MF.TR` is an exact ordered-list identity: no sphere permutation, no umklapp, no sign
    or multiplet rotation. At a grid point that `neg` fixes (a time-reversal-invariant
    point such as Γ, X or L) it forces every sphere vector to be 0 (`MF.tr_fixed`), so a
    block whose `neg` fixes `k0` with a nonzero sphere vector cannot satisfy it
    (`compat_selfpaired_no_TR`). Because `Z` is finite, `hT` must hold for some block off
    `Z`. With the plans' `neg` encoding `-k` on a grid that stores each k-point class once (a trusted plan premise covering every plan index outside `Z`; not a theorem, since `MF` has no k-coordinates), every block fixes X and L, whose spheres
    hold a nonzero vector, so the hypotheses of `sigA_compat` are unsatisfiable for O1
    (`hyps_unsat_of_selfpaired`). For arbitrary plans, `hyps_unsat_of_unpaired` gives the
    same from `hnp` (no grid index stores the negated sphere list of X or L), which
    `bgw/r28_f1/check.py` (`hnp`) checks numerically on the Si-EPM Σ grid (no grid point stores
    the negated sphere of X or L even as a set, so `hnp` holds there for any sphere ordering). Storing X or L
    once does not by itself give `hnp`: a finite cutoff sphere does not determine k. Either way,
    for O1 the theorem cannot be applied at all. With every plan's `neg` encoding −k on a grid
    that stores each k-point class once (trusted plan semantics, as above), `MF.TR` also excludes every Γ-centred
    grid, BerkeleyGW's standard ε setup, and recomputing ε on Σ's grid cannot satisfy it as stated, since all 8 Σ grid
    points are time-reversal-invariant. (At Γ the `hnp` data check holds only for the two
    sphere orderings it compares: on the Si-EPM grid Γ's negated sphere is stored, as a set,
    at Γ itself.) Generalising `TR` (sphere permutation, umklapp,
    rotation within degenerate multiplets) is open.
  * The q = 0 screening blocks `Z` carry an input `E0` on both sides. The long-wavelength
    head and wings are not derived in the composed theorem; `Espec_q0_input` says only
    that BerkeleyGW's q0 block can be that input. BRIDGE-Q0 is the separate q0 analysis.
  * `hC` (vb = vc) is trivially dischargeable by vc := vb. The physical case, vc = the bare
    Coulomb point values, fails on the run (vb are mini-BZ averages). Nothing in `Compat`
    ties the Σ plan's q and G maps to the screening blocks' (`coulomb_same` states that
    link but is not a premise), so the theorem does not identify the Σ and ε interactions.
  * `hX` fails structurally for Σ(Eo): at q = 0 and iw = 0, x = 0 exactly for n1 = a and
    its degenerate partners, and every BerkeleyGW Σ q-list contains q = 0. The spec
    replaces x by `TOL_Zero` there; `wxS_close` bounds |Δx| < 2·`TOL_Zero`, but no Lean
    theorem propagates that bound to Σ. So the identity does not cover Σ(Eo) for any
    standard run. It does cover the iw = 1 (Eo + dE) evaluation where the other
    hypotheses hold.
  * On the Si-EPM run `Compat` fails whenever a block that the Σ q-list reads is derived
    (outside `Z`). Epsilon (WFN, shifted 32-point grid) and Σ
    (WFN_inner, unshifted 8-point grid) share no k-point. Cell, G-list and cutoffs agree,
    and a local potential fitted to WFN_inner reproduces the other files' energies to
    ≤ 2.4e-7 meV (measured, Python). `DensOK` fails too (RHO is not star-averaged; the
    +0.38 meV of BRIDGE-Q0). See `docs/reviews/R28-F1.md`.
* **F2.** The GPP results are formal properties and consequences of the specified HL
  ansatz, conditional on its oscillator-strength prescription. They do not derive the
  physical f-sum rule from the fermion system.
* **F3.** `CompleteK κ` remains an abstract scaled-frame completion. It is not a tolerance
  certificate for the true omitted finite-basis eigenvectors. Corrected statement,
  `GW.Bridge.sigA_all_bands_lowdin` (`GW/Bridge/CorPerturb.lean`): if the stored rows'
  Gram defect η_t is < 1, then
  * there EXIST exactly orthonormal rows P within √η_t of the stored rows. The proof uses
    Löwdin's construction (`Lowdin.lowdin_nat`); the statement does not pin P to
    (RRᵀ)^{-1/2}R;
  * P has exact completions by exactly L − N_b rows, the physical count
    (`Lowdin.exists_completion_nat`);
  * every such completion whose omitted bands lie at least D_t above the state
    (D_t > 3/2 eV) satisfies the BRIDGE-COR enclosure, widened by an explicit
    propagation term.

  The physical omitted EPM eigenvectors complete the EPM's own eigenvectors, not P.
  Covering them needs `sigA_all_bands_true` with `RowDist` at the distance d between the
  EPM eigenvectors and the stored rows. That d is neither formalised nor evaluated (a
  Davis–Kahan residual/gap bound would give it; at N_b = 30 and 100 the cut splits an
  exact degeneracy at some k − q). Si numbers (Python interval, `bgw/r28_f3/f3.py`): at
  N_b = 18, δ_t ≤ 5.34e-14, the propagation at d = δ_t (P against the stored rows) adds
  ≈ 2.6e-4 meV and O1 ∈ [−2813.0693, +2746.4706] meV; at N_b = 168, δ_t ≤ 2.17e-13, the
  propagation adds ≈ 2.5e-3 meV and O1 ∈ [−4.05, −3.51] meV. The propagation figures are
  plain-float diagnostics; δ_t and the O1 enclosures are iv.py outward bounds (`docs/reviews/R28-F3.md`).
* **F4.** `SigAall` keeps a static remainder term. It is not "all bands with static
  remainder zero". R28-F4 (`GW/Bridge/CorResidual.lean`, `docs/reviews/R28-F4.md`) splits
  it exactly, for a `CompleteK κ` completion, as
  `CORall = Σ_t (corScale κ + corShift + corGch)` (`cor_all_decomp`; the
  three parts, the closure scale, the shift-closure defect and the `Gch` coverage, are
  defined independently). κ = 1, shift closure and `Gch` coverage are sufficient for
  `CORall = 0` (`cor_all_eq_zero`), not necessary. On Si-EPM (Python interval) it is
  −2.22 meV (X) and −3.75 meV (L) per band, which is +1.21 meV on O1 with 168 bands
  (+1.22 meV with 18).

**4. Approximation layer (mixed evidence).** The full-QP O1 is kernel-checked with no
Coulomb-box hypothesis: `Headline.roots_exist_irr_unconditional` proves that the full QP equation has
a unique root in each of two brackets, and `Headline.o1_fullQP_irr_unconditional` that for
those roots EX − EL ∈ [68.9856742, 68.9856744] meV. That the brackets hold the principal
roots (largest Z), and the cover of the enumeration window, are Python results.
(`R.o1_fullQP_irr` itself keeps the `VbHyp` hypotheses.) The following are measured or
estimated only: FF-RPA, evGW0/evGW and the SOX estimate. The `GW.Endpoint.ManyBody`
results about the GW error structure of finite fermion models are kernel-checked model
theorems; they are not bounds for silicon (`docs/ENDPOINT.md` §A).

**Not claimed:**
* that the BerkeleyGW Fortran is correct on any input;
* that its floating-point execution stays within 5.21 µeV for other runs;
* that the 18-band calculation is converged;
* that GW or the GPP describe silicon;
* that the EPM describes real silicon.

## Proof integrity

The project uses no `sorry`, `admit`, project axioms, `native_decide`, `ofReduceBool` or
`implemented_by`. `scripts/CheckAxioms.lean` enumerates every theorem in the imported
project modules and rejects any dependency beyond `propext`, `Classical.choice` and
`Quot.sound`. Lean's division is totalised, and so is Mathlib's matrix inverse (`A⁻¹ = 0`
for a singular `A`), so a zero-denominator expression or the inverse of a matrix not shown
nonsingular is never read as physically defined. A proof audit is not a compiler-correctness claim. The
trusted computing base is:
* the Lean 4.19.0 kernel, including its GMP-accelerated `Nat` arithmetic, which the large
  `decide +kernel` certificates use heavily;
* the Mathlib oleans fetched by `lake exe cache get`, not rebuilt locally;
* the elan installer, fetched by `scripts/bootstrap.sh` from the elan repository's
  `master` branch.

No lean4checker or other external-checker replay has been run. Full gate from a clean
build: PASS at cd97681 (2026-10-03). Every project module was first built from scratch at 18e3700 in a fresh worktree (4 h 52 min, 0 errors, no module replayed; Mathlib oleans from cache). At cd97681 the gate rebuilt the changed modules (including RO1, RIrr and Headline) and replayed the rest from that clean build. The exhaustive axiom audit covered 34552 theorems, standard axioms only, including the four Headline theorems; 689 scientific and 14 workflow tests passed, with 2 environment skips (pinned BerkeleyGW compiler absent; no supervisor fresh run). That gate covered PR #29 as of cd97681. PR #30 (f9cf59a; Codex's independent-re-review fixes) and R28-R3 (Python interval code, regenerated JSON, tests, Lean docstrings and one new theorem) came later; their gates are recorded in `docs/reviews/R28-R3.md`. Latest full gate of the merged R28-R3 code (author/supervisor-reported, not independently reproduced): PASS at 47a46c9 (2026-10-08; PR #31 head, whose tree is that of main at 94393de), recorded in [the PR #31 gate comment](https://github.com/MichealWangYZ/physics_lean_bgw/pull/31#issuecomment-6074498928). After the 2026-10-07 `SigmaSpec`/`EpsSpec` docstring edit it rebuilt all 1376 certificate-data modules from source. The exhaustive axiom audit covered 34553 theorems, standard axioms only; 694 scientific and 15 workflow tests passed (including `test_python_compiles`), with 2 environment skips (pinned BerkeleyGW compiler absent; no supervisor fresh run). Historical R28-R3 checkpoints: 214b656 full PASS (2026-10-05; 14 workflow tests; the commit after it fixed `make_review.py` and added `test_python_compiles.py`, checked by the fast and workflow gates); e3ae6b4 full PASS (rebuilt 1339 certificate-data modules after the kernel-file comment edits); 7435f99 full PASS; PR #30 at f9cf59a full PASS. The R28-R3-CLOSEOUT patch (2026-10-09: `cor.py` radius reporting, its tests, and docs) changed executable code after 47a46c9 and is not covered by that gate; its own validation is recorded in `.agent/handoffs/R28-R3-CLOSEOUT.md`. Its gate, author-run at e8ef424 (2026-10-09): fast and full PASS; 34553 theorems, standard axioms only; 699 scientific and 15 workflow tests; 2 environment skips. The public snapshot was gated again on its own tree (full PASS; 699 scientific and 16 workflow tests).

## Build and verify

```bash
bash scripts/bootstrap.sh          # user-space Lean 4.19.0 + mathlib v4.19.0 caches
bash scripts/verify.sh --gate fast # routine gate, < 10 min warm
bash scripts/verify.sh             # full gate, ~1 h warm / ~5 h cold; before any merge
lake build GWKernelData            # the kernel-checked numerical certificates (slow, several GB)
```

The pinned BerkeleyGW 4.0 archive (sha256 `1a85b03b…`) and its builds live outside git;
see `bgw/m4_gpp/PROVENANCE.md` and `bgw/README.md`. The workflow (supervisor, bounded
worker tasks, handoffs, gates, generated registries) is described in
[`AGENTS.md`](../AGENTS.md). The original scalar pole-cancellation demo
([`Specification.md`](../Specification.md), `lake exe gpp_demo`) is the archived founding
contract of the project. It is kept and is not extended.

## Credits

**Jinyuan Wu** ([@jywu20](https://github.com/jywu20)) proposed the idea for this
project: formalising a scalar algebraic identity from a production many-body
physics kernel and checking it against the shipped Fortran. The framing of the
question is his.

The formalisation, audits and analysis code in this repository were written by
Claude (Anthropic) under the direction of the repository owner, with a
supervising agent (also Claude, so not independent of the authors) reviewing and
integrating the work. `AGENTS.md` describes that workflow and `.agent/handoffs/`
retains the record, including the corrections that review caught. The external reviews
so far are REVIEW-28, by Codex (`docs/reviews/`), and Codex's independent re-review of
PR #29, whose four MINOR findings PR #30 fixed (`docs/reviews/R28-R2.md`, "Note after
PR #30"), and Codex's independent R28-R3 review, whose four MINOR findings the R28-R3 closeout fixed
and which accepted the result within its documented scope (`docs/reviews/R28-R3-INDEPENDENT.md`).

## Licensing and copyright

This project's own work is BSD 3-Clause; see [`LICENSE`](../LICENSE).
BerkeleyGW-derived material stays under BerkeleyGW's own licence, scoped in
[`THIRD_PARTY_NOTICES.md`](../THIRD_PARTY_NOTICES.md).

Copyright is held jointly by Yizhou Wang and Jinyuan Wu. Note that much of the
expression here was generated by Claude under the holders' direction; `LICENSE`
states what that means for the rights asserted, so a recipient is not misled
about how the work was produced.
