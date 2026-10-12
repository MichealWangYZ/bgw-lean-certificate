# Scientific endpoint: one production BerkeleyGW observable, three error layers

**Reviewer's guide:** open `docs/review/index.html` (regenerate with
`python3 bgw/endpoint/make_review.py`): the chain node by node, each Lean
definition next to the BerkeleyGW source it transcribes, with a checklist.

Status: plan and gates written 2026-09-22 at the owner's direction. Nothing
here is accepted. This document supersedes the per-record roadmap for the BGW
track; `docs/LIN_LINDSEY_ROADMAP.md` (LL theory) is parked, not extended.

**Scope after REVIEW-28 (2026-10-02; updated R28-R2, 2026-10-03).**
`docs/reviews/REVIEW-28-adversarial.md` found the layer-1 result supported within its trust
boundaries (the kernel-checked enclosure is about the specification on fixed exported data;
export, source-to-spec correspondence and production execution are trusted). Scope: one
input (BerkeleyGW 4.0 testsuite Si-EPM, 18 bands) and one code path (real flavour; GPP with
the default invalid-mode convention; fdf = 2, dE = 1 eV; no truncation; avgcut = 1e12;
Vxc = 0; 8 q-points). How to quote O1:
* **≈ 15.40575 meV** (kernel-checked, `Headline.o1_enclosure_irr_unconditional`, no
  hypothesis: O1_specA ∈ [15.4057523, 15.4057537] meV) is the specification's value for
  this run as configured (18 bands, `½` static remainder). It is a code claim about the
  specified 18-band calculation, not the physical band ordering.
* **≈ −3.8 meV** is the spec's linearised O1 with the Σ band sum over all 168 computed bands of the 11 Ry EPM basis (ε from the 18-band run; the ≤ 6 remaining rows enclosed over every exact completion of the Löwdin rows, not the EPM's own omitted eigenvectors, whose distance is not evaluated),
  static residual included (`docs/BRIDGE.md` BRIDGE-COR): Python interval (iv.py)
  [−4.05, −3.51] meV over every exact completion of the Löwdin rows (R28-F3); BerkeleyGW's
  164-band run gives −3.76085 meV. Not kernel-certified. Without the static residual
  (+1.21 meV on O1, Python interval) it is [−5.25, −4.71] meV (Python interval, not
  BerkeleyGW-checked; that the residual carries over unchanged to the completion is argued,
  not proved; `docs/reviews/R28-F4.md`).

The link from this specification to G0W0 theory is a set of conditional
theory-to-specification identities (`docs/BRIDGE.md`, "Scope after REVIEW-28"), not an
end-to-end physical derivation.

## 1. What we want to be able to say

> For the pinned BerkeleyGW 4.0 Si-EPM GPP calculation, the production value of
> observable O differs from the mathematical specification evaluated on the
> same production inputs by at most δ_impl (certified). Under the numerical
> controls we could vary, O moves by δ_conv (empirical). The physical
> conclusion "sign(O) = s" does / does not survive both.

Three layers are kept apart and never added into one number:

| Layer | Question | Kind of evidence |
| --- | --- | --- |
| 1 implementation | Does the program evaluate the specified finite calculation? | certified enclosure of the spec on production inputs; independent reproducer; mutation detectability |
| 2 convergence | Is that finite calculation stable as controls are enlarged? | empirical multi-dimensional sweeps; labelled empirical |
| 3 model | Is GPP/GW itself right? | **not claimed** |

A small δ_impl says nothing about layer 2. Layer 2 says nothing about layer 3.

## 2. The production calculation and the observable (E0)

Calculation: BerkeleyGW 4.0 testsuite `Si-EPM`, real flavour, serial, exactly
the shipped `WFN*.in`, `epsilon.inp` (epsilon_cutoff 7.0 Ry), `sig_GPP.inp`,
run by the pristine binaries of the pinned archive (sha256 1a85b03b…).
Mean field is an empirical pseudopotential with `Vxc = 0`, so `E_QP = E_EPM +
Σ`: the "physics" is internal to this model, not real silicon.

Observable O1 (the conclusion carrier): the QP conduction-band ordering

    Δ_XL = Eqp1(X, lowest conduction multiplet) − Eqp1(L, lowest conduction multiplet)

with k-points X = (0, ½, ½) and L = (0, 0, ½) in reciprocal-lattice
coordinates, and each energy taken as the average over its degenerate multiplet
(basis-invariant). Conclusion C1: **Δ_XL > 0, i.e. the QP conduction energy
at L lies below that at X.** C1 compares X and L only; that the conduction
minimum over all sampled k-points (Γ included) is at L is a Python interval
result (`cert_o1.json` `CBM_certainly_at_L`), not a Lean theorem.

Why this one: it is decided by a difference of two large self-energies, so it
is exactly the kind of quantity that looks stable while its parts are not.
In mean field X is below L by 0.628 eV. The archived run gives Δ_XL = +15.4 meV
at 7.0 Ry, but the 1.5 Ry run used by M1–M5 gives Δ_XL = −75.4 meV. **The sign
already flips with one control.** That is a layer-2 warning noted here, not yet
a result.

Secondary O2: indirect QP gap `min_k Eqp1(c) − Eqp1(Γ, v)`; constituents
(X, SX−X, CH, static remainder, Z) of all four states, reported so that
cancellation is visible.

## 3. Gates and exit conditions

Every gate is a command that exits 0 on pass, is wired into
`bash scripts/verify.sh`, and binds its evidence by sha256. "Exit" means stop
this milestone and report; all exits other than SUCCESS are legitimate results.

### E0 — pin the calculation and the observable

PASS when all hold:
1. `bgw/endpoint/run_production.py` rebuilds a fresh run from the testsuite
   inputs with the pristine binaries and records input/binary hashes.
2. The fresh run reproduces the archived `bgw/export/sigma_hp.log` diagonal
   table to its printed precision (1e-9 eV) for every state entering O1/O2.
3. `bgw/endpoint/observable.py` extracts O1, O2 and constituents; the
   multiplets are identified from mean-field energies (tolerance recorded) and
   the production values are equal across each multiplet.
4. `bgw/endpoint/ledger.json` lists every spec↔production correspondence item
   with status `proved | certified | measured | gap | unexamined`.

Exits: fresh run does not reproduce (→ environment finding, stop); O1 is not
basis-invariant (→ redefine with a recorded reason, or stop).

### E1 — certified layer-1 bound on O1

Target: `|O1_prod − O1_spec| ≤ δ_impl`, where `O1_spec` is the specification
(section 4) evaluated on the production *inputs* WFN, WFNq, WFN_inner, RHO — so
the epsilon stage is inside the chain, not trusted.

Sub-gates, each a checkpoint commit:

| Step | Pass condition |
| --- | --- |
| E1.1 readers + bare exchange | independent float64 reproducer matches production `X` for all 24 diagonal states to ≤ 1e-6 eV |
| E1.2 GPP correlation | SX−X, CH (with and without static remainder), Eqp0, Eqp1, Z match to ≤ 1e-6 eV |
| E1.3 epsilon stage | chi, ε, ε⁻¹ recomputed from WFN/WFNq match `eps0mat`/`epsmat` entrywise; the Σ reproducer then runs on the recomputed ε⁻¹ |
| E1.4 certification | the float reproducer is replaced by rigorous enclosure arithmetic; enclosure of O1, O2 and constituents; the printed Eqp1 of the four O1/O2 states and O1 inside the enclosure computed with production's own Monte Carlo Coulomb averages (with the exact averages, spec A, production O1 agrees to 5.21 µeV while individual Eqp1 differ by ≈ 0.14–0.18 meV; see E1 result). *Amended 2026-09-22:* the plan said the interval rules' soundness would be proved in Lean. It was not: those rules are textbook and a Lean proof would cover their mathematics, not the numpy code that implements them, which is where the risk is; that code is instead tested against exact rationals (`IntervalArithmetic`). Lean proves the one non-textbook rewrite the evaluator makes (`GW/Endpoint/NearPole.lean`, mutation-checked). *Amended 2026-09-23 (LEAN-CERT):* the mathematics is now proved as well -- enclosure of every iv.py operation under an explicit rounding hypothesis (`CertInterval.lean`), the componentwise Neumann enclosure and balancing of `inverse_cw` (`CertInverse.lean`, `inverse_cw_sound`), and the equivalence of cert.kernel's division-free sexcut tests with the source's (`CertSexcut.lean`, `certSsx_eq_srcSsx`). That the numpy code computes these formulas remains the tested, unproved correspondence. *Amended 2026-09-25 (G2 stage 1):* for eps^-1 that correspondence is closed -- the Lean kernel re-checks cert.py's certificate in exact integer arithmetic (`decide +kernel`, no native code) and proves every real matrix in cert.py's eps interval invertible with inverse inside the claimed enclosure, at all three q (`epsinv_enclosure_q{0,1,2}`, target `GWKernelData`, ~13 CPU-min). *Amended 2026-09-25 (G2 stage 2):* the eps interval itself is now kernel-checked from the unfolded wavefunction coefficients (`eps_in_box`, `epsinv_true_q{0,1,2}`: the TRUE static RPA eps of the Lean formula `Eps.epsR` -- pair densities, 4/(N_k Omega) chi with exact energy denominators, 8 pi/|q+G|^2 with real pi -- is invertible with inverse in cert.py's enclosure). *Amended 2026-09-26 (G2 stage 3):* the E1 enclosure of O1 is kernel-checked (O1 only; O2 is a Python interval): `S3.o1_enclosure` -- for every Coulomb average inside its coulomb_cert.json box, O1_specA computed with the TRUE eps^-1 (stage 2) lies in cert_o1.json's binary64 interval [8880811588953599, 8880812351936001]/2^59 eV = [15.405752349, 15.405753673] meV (decimals rounded outward; width 1.32 neV; the exact evaluation inside the proof is tighter, 0.82 neV) -- and `S3.o1_pos` (Eqp1(X) > Eqp1(L) for spec A). At that date the unfolding and the Coulomb boxes were still inputs; the next two amendments discharge them. *Amended 2026-09-27 (G2 unfold):* the symmetry unfolding is kernel-checked too: `U.o1_enclosure_irr` starts from the IRREDUCIBLE coefficients of WFN/WFNq/WFN_inner and the crystal's symmetry operations (k-set closure, weights, spheres, BerkeleyGW's sphere order and eps index map all checked); it keeps the Coulomb-box hypotheses `VbHyp`. *Amended 2026-09-28 (G2-coulomb):* the Coulomb averages are proved in Lean, so the stage-3 theorem holds without hypothesis on the stage-3 literals (`Coul.o1_enclosure_unconditional`, `Coul.o1_pos_unconditional`): every one of the 1363 vbar and 7 oneoverq boxes of coulomb_cert.json contains the true mini-BZ average (`Coul.vb_hyp`, `Coul.oq_hyp`; Lebesgue integral over the exact cell, cone decomposition, kernel-checked cubature with proved remainders). The cell is the 26-half-space cell of certcoulomb.py; it equals the Wigner-Seitz cell up to measure zero because it contains it and has the same volume (`volume_cell`: 1/8 of the crystal cell). Not in Lean: that BerkeleyGW's Monte Carlo averages estimate this quantity (that is spec A vs production, E1). *Amended 2026-10-03 (R28-R2):* the headline theorems compose the unfolding and Coulomb results: `Headline.o1_enclosure_irr_unconditional` (O1_specA from the irreducible data and the exact averages lies in the interval above) and `Headline.o1_pos_irr_unconditional` (Eqp1(X) > Eqp1(L); it compares X and L only), both with no hypothesis, target `GWKernelData`. Full gate from a clean build: PASS at cd97681 (2026-10-03). Every project module was first built from scratch at 18e3700 in a fresh worktree (4 h 52 min, 0 errors, no module replayed; Mathlib oleans from cache). At cd97681 the gate rebuilt the changed modules (including RO1, RIrr and Headline) and replayed the rest from that clean build. The exhaustive axiom audit covered 34552 theorems, standard axioms only, including the four Headline theorems; 689 scientific and 14 workflow tests passed, with 2 environment skips (pinned BerkeleyGW compiler absent; no supervisor fresh run). That gate covered PR #29 as of cd97681. PR #30 (f9cf59a; Codex's independent-re-review fixes) and R28-R3 (Python interval code, regenerated JSON, tests, Lean docstrings and one new theorem) came later; their gates are recorded in `docs/reviews/R28-R3.md`. Latest full gate of the merged R28-R3 code (author/supervisor-reported, not independently reproduced): PASS at 47a46c9 (2026-10-08; PR #31 head, whose tree is that of main at 94393de), recorded in [the PR #31 gate comment](https://github.com/MichealWangYZ/physics_lean_bgw/pull/31#issuecomment-6074498928). After the 2026-10-07 `SigmaSpec`/`EpsSpec` docstring edit it rebuilt all 1376 certificate-data modules from source. The exhaustive axiom audit covered 34553 theorems, standard axioms only; 694 scientific and 15 workflow tests passed (including `test_python_compiles`), with 2 environment skips (pinned BerkeleyGW compiler absent; no supervisor fresh run). Historical R28-R3 checkpoints: 214b656 full PASS (2026-10-05; 14 workflow tests; the commit after it fixed `make_review.py` and added `test_python_compiles.py`, checked by the fast and workflow gates); e3ae6b4 full PASS (rebuilt 1339 certificate-data modules after the kernel-file comment edits); 7435f99 full PASS; PR #30 at f9cf59a full PASS. The R28-R3-CLOSEOUT patch (2026-10-09: `cor.py` radius reporting, its tests, and docs) changed executable code after 47a46c9 and is not covered by that gate; its own validation is recorded in `.agent/handoffs/R28-R3-CLOSEOUT.md`. *Amended 2026-10-07 (owner sign-off, docstrings only):* the `SigmaSpec.lean` header now names `schM`/`ssxM` and states that `Cert.certSsx` equals the source's branch/clamp rule under `certSsx_eq_srcSsx`'s hypotheses `0 < w`, `0 < s`, `x ≠ w`, `x + w ≠ 0`, and the stale "recorded trust" notes on the unfolding, sphere orders, eps mapping and Coulomb averages in `SigmaSpec.lean` and `EpsSpec.lean` now point to the `U.`, `Coul.` and `Headline.` theorems. (Until then this cell recorded the qualification here and said the spec files were deliberately not edited; that is historical.) Still trusted (current): the decoding and export of the run files into Lean literals (`kernel_export.py`, bgwio), including the float-to-dyadic transcription; the density list RHO and the run parameters (cutoffs, q-list, scales) are export literals, and no committed digest links the literals to the run files (a field-by-field bgwio decode comparison was done in review, not automated); RYD = 13.60569253 and the binary64 thresholds as constants; the modelling claim that these Lean formulas are BerkeleyGW's (source reading plus numerical agreement on one run: with production's Monte Carlo averages cert.py encloses the printed Eqp1 of the four O1/O2 states and O1; with the exact averages production O1 agrees with the spec-A enclosure to 5.21 µeV); the production execution. |
| E1.5 silent-error hunt | each item in section 5 is examined and ledgered; each injected fault class moves O1 by more than δ_impl (detectable) or is recorded as undetectable |

E1 SUCCESS exit: O1 and O2 enclosed; production values inside (as met: with
production's Monte Carlo Coulomb averages, see E1.4); δ_impl ≤ 1 meV
(i.e. far below |O1| = 15 meV — otherwise report "layer 1 not decisive");
no ledger item `unexamined`; every `gap` quantified or explicitly reasoned;
`bash scripts/verify.sh` passes; handoff written.

E1 other exits:
- FINDING — a production value lies outside the enclosure: attribute it to a
  spec misreading (fix the spec, cite the source line) or to the program
  (minimal reproducer, source line). Either way this ends E1 with a result.
- ILL-DEFINED — O1 depends on an arbitrary choice (e.g. a degenerate
  multiplet cut by `number_bands`): quantify the range; report.
- STALL — the same blocker three times, or a component that cannot be pinned
  from source after reading it: mark `gap`, continue the others; if it is on
  O1's critical path, stop and report.

Out of scope for E1: layers 2 and 3; the EPM diagonalisation (its output is an
input); compiler correctness; MPI (runs are serial).

### E1 result (exit: SUCCESS, 2026-09-22; ready for review, not accepted)

> For the pinned Si-EPM GPP run, O1_prod = +15.400547 meV (sigma_hp.log) and
> the specification evaluated exactly on the same mean-field files gives
> O1_specA in [15.4057523, 15.4057537] meV (rigorous enclosure, width
> 1.32 neV, no undecided branch; kernel-checked since 2026-09-26, now as
> `Headline.o1_enclosure_irr_unconditional`, see E1.4; the 2026-09-23
> soundness fixes -- outward-rounded rebalancing, ssx = 0 at wdiff = 0,
> near-pole sexcut threshold w/sexcut -- did not move O1 beyond the last
> quoted digit). **Production O1 agrees with the spec-A enclosure to 5.21
> micro-eV** (exact arithmetic, allowing 1 neV of print rounding), almost all
> of it the Monte Carlo quadrature of the Coulomb averages. This holds for O1
> only: the individual Eqp1 differ from spec A by ≈ 0.14–0.18 meV (CH by
> ≈ 0.14–0.30 meV) and the differences largely cancel in O1; with production's own
> Monte Carlo averages cert.py encloses the printed Eqp1 of the four O1/O2
> states and O1.
> Over every q -> 0 direction BerkeleyGW could have picked, O1 lies in
> [14.34, 15.41] meV; spec B (direction-averaged) gives 14.8897 meV (both
> Python, cert.py).
> C1 (O1 > 0) therefore holds for the specified finite 18-band calculation,
> with a layer-1 margin of more than three orders of magnitude (it is not
> robust to the band count, see the scope note at the top). O2 (indirect
> gap) is enclosed in [4.35243970, 4.35243972] eV and the CBM over all
> sampled k-points is at L (Python interval, cert.py; not kernel-checked);
> |O2_prod - O2_specA| <= 33.4 micro-eV.

Evidence: E1.1-E1.3 reproduce the production table to print precision (<=
5e-10 eV) from WFN-level inputs (tests/test_endpoint_e1.py); E1.4
`bgw/endpoint/cert.py` + `data/cert_o1.json`, Coulomb enclosures
`certcoulomb.py` + `data/coulomb_cert.json`; E1.5 `data/mutations_e1.log`
(15/15 counterfactual conventions detected) and `sphere_margins.py`.

Trust base of the certified numbers: IEEE-754 round-to-nearest for numpy's
elementwise + - * / sqrt (iv.py; validated against exact rationals, not
proved); Arb/python-flint 0.9.0 ball arithmetic and acb.integral; the
transcription of the production conventions in spec.py (checked by the
print-precision agreement and the mutation study, not proved). For the O1
enclosure the kernel-checked theorems of E1.4 remove the first two items;
O2, the constituents and the q -> 0 direction range still rest on them.

Findings along the way (each is now in spec.py with its source line):
1. Sigma's q -> 0 treatment uses ONE direction of the anisotropic eps0mat,
   chosen as the last matching symmetry op; the choice moves O1 by up to
   1.06 meV and splits exactly degenerate states (Gamma valence SX-X spread
   36 meV before BerkeleyGW's multiplet averaging hides it).
2. The Monte Carlo Coulomb averages differ from the integrals they estimate
   by up to 1.7e-3 relative and break star symmetry; on O1 this is 5 micro-eV.
3. Epsilon's k-sum runs over the 32-point symmetry closure of the shifted
   2x2x2 grid.
4. Sensitivity of O1 to documented GPP conventions (from the mutation study;
   these are NOT implementation errors): invalid-mode skipping -5.2 meV
   (sign flip), no static remainder -101 meV (sign flip), remainder factor 1
   +132 meV, keeping unoccupied near-pole CH +34.8 meV, dE = 0.5 eV +18.6 meV.
   The sign of O1 is decided by conventions whose correctness is a layer-2
   (band convergence: the remainder) or layer-3 (GPP) question.

### E2 — convergence structure of O1 (empirical)

Controls: number_bands (Sigma and Epsilon together; with and without the
static remainder), screened cutoff (epsilon_cutoff), k/q grid, wavefunction
cutoff, and the q0 direction. Every run through
`bgw/endpoint/run_production.py --set`, hashes recorded.

PASS (the empirical characterisation is complete) when all hold:
1. one-dimensional sweeps of each control about the production point;
2. a joint number_bands x epsilon_cutoff grid (the Qiu-type coupled pair),
   and a k/q-grid sweep at the largest affordable (bands, cutoff);
3. constituents (X, SX-X, CH, remainder, Z for both states) tabulated for
   every run, so that cancellation is visible;
4. an empirical convergence estimate for O1 with the method stated
   (extrapolation form, residuals, and what it assumes), labelled empirical;
5. the E1 reproducer agrees with production at two non-production points
   (layer 1 does not silently degrade across the sweep).

Exits: FINDING if O1 changes sign within the reachable controls (C1 not
robust: report where); BUDGET if a single run exceeds 2 h or the sweep 10 h
wall on this machine (report the reachable region and stop); STALL as in E1.

### E2 interim result (2026-09-23; 125 points, 2 still running; EMPIRICAL)

Data: `bgw/endpoint/data/e2_results.jsonl` (one JSON per point: controls,
band count actually used, O1 with and without the static remainder, all
constituents, file hashes, host). Tables: `python3 bgw/endpoint/e2_analyze.py`.

1. **Coupled nb x ecuts (Qiu-type false convergence).** At the production
   ecuts = 7 Ry, raising the band count alone drives O1 from +15.4 meV to
   -3.8 (N=2), -12.3 (N=4), -2.5 (N=6), +0.4 (N=8) meV. Raising ecuts at
   fixed nb = 18 looks converged (19.5 meV by 14 Ry). The production value
   is positive at these settings because two truncation errors cancel.
2. **Sign.** Every point with ecuts >= 14 Ry has O1 > 0 (smallest +7.8 meV,
   N=4, 98 bands); all negative values are at ecuts = 7 with >= 98 bands.
3. **Magnitude is not converged.** Over the ecuts-converged region O1 spans
   ~8 to ~39 meV: band count (N=2, ecutwfc 25: 30.9 -> 38.6 meV from 104 to
   452 bands; 1/nb, nb^-2/3, nb^-1/2 extrapolations give 41.5 / 43.6 / 45.7
   meV, residuals <= 0.14 meV -- the limit depends on the assumed form),
   mean-field basis (ecutwfc 11 -> 15 moves the EPM X-L gap itself by
   +9.4 meV; converged by 15), and k/q grid (non-monotonic: at 150 bands,
   ecuts 25: N=2 19.7, N=4 10.1, N=6 19.7 meV; at the best basis N=4 gives
   28.3 vs 37.5 meV for N=2).
4. **The static remainder carries the sign at production settings**
   (O1' = -101 meV without it) and becomes small only when the basis is
   nearly complete (O1 - O1' = 1.5 meV at ecutwfc 25, 452 bands): it
   compensates plane-wave basis incompleteness, not only band truncation.
5. **Cancellation.** O1 is a residual of X-L differences of ~+0.71 eV
   (exchange), ~-0.43 eV (SX-X) and ~+0.50..0.60 eV (CH): 2-6 % of each.
6. Layer 1 holds across the sweep: the E1 reproducer matches production at
   N2_nb54_ec14_eb14 to 4.9e-10 eV (`e2_layer1.py`).

Still open for the E2 PASS: the two running points (N8 150 bands ecuts 25;
N6 300 bands ecutwfc 20 ecuts 25), a second layer-1 check at an N>2 point,
and the E2 write-up. Many dense-grid band counts fail the multiplet-safe
window rule; they are recorded in `*.errors.jsonl`, never relaxed.

### Scope change (owner, 2026-09-23)

Layer 2 (band count, cutoffs, k-grid) is **out of scope** from here on: the
E2 data above stay as recorded, but no convergence claim will be made and
the E2 PASS conditions are withdrawn. Layer 3 -- how far the GW/GPP
approximations are from the quantity they approximate -- **is in scope**,
and replaces E3 below.

### A — the approximation layer (bounds on the GW approximations)

The production number is the end of a chain of approximations; each link is
bounded separately and never folded into another:

| Link | Approximation | Reference quantity | Evidence |
| --- | --- | --- | --- |
| A1 | linearised QP equation (Eqp1) | root of E = Emf + Sigma_GPP(E) | certified (`qp_cert.py`) |
| A2 | Hybertsen-Louie plasmon pole | full-frequency RPA W(omega) (contour deformation) | production FF run; numerical accuracy of the FF reference measured by refinement |
| A3 | GW (vertex = 1) | exact many-body self-energy | no theorem bounds this for a real solid. (a) Lean, done 2026-09-25 (G4): structure of the error for any finite fermion model H0 + lambda V with real two-body integrals, H0 diagonal in the reference orbitals and a nondegenerate Slater-determinant reference (hypotheses in A3(a) below) (first order exact; at second order GW misses SOX and, unless the Brillouin condition holds, the relaxation term relax); (b) certified exact-vs-GW gap on an exactly solvable model; (c) size of the leading neglected term for Si-EPM, labelled an estimate |

Every A-result states which spec it refers to (spec A of E1) and keeps the
E1 layer-1 bound separate.

**A1 result (certified, 2026-09-23).** For spec A the full GPP QP equation
has roots X in [4.1943900697, 4.1943900699] eV and L in [4.1254043954,
4.1254043956] eV (decimals rounded outward): each is a certified sign change of f(E) = Emf + Sigma(E) - E
on a bracket over which every GPP branch is decided (so f is continuous
there). O1_fullQP = **68.985674 meV** versus the linearised ≈ 15.40575 meV:
the linearisation moves O1 by **-53.58 meV** and each QP energy by -0.34 /
-0.39 eV. Cause: with Vxc = 0 (EPM) the QP energy lies ~7 eV from Emf, far
outside the reach of one Newton step. Sexcut clamps are active within 1 meV
of the X root.

**A1 root enumeration (certified, 2026-09-23; `qp_unique.py`,
data/qp_unique.json, Lean `qp_roots_enumerated`).** In the window
[-10^4, 10^4] eV each state's full GPP QP equation has EXACTLY TWO roots,
each in a certified isolating bracket (branches fixed, f' enclosed away from
0, opposite end signs), and no zero elsewhere (interval exclusion, plus a
certified branch split at the one jump of f across 0 per state):

| state | root (eV) | Z = 1/(1 - dSigma/dE) |
| --- | --- | --- |
| X | 4.1943900698 | 0.858 |
| X | 29.9246473945 | 0.042 |
| L | 4.1254043955 | 0.855 |
| L | 30.4614676479 | 0.036 |

The earlier "one sign change in [Emf-12, Emf+2]" was a window artefact. The
principal (largest-Z) roots give O1 = 68.986 meV; pairing the two
low-weight solutions would give -537 meV. C1 therefore holds for the
standard choice of the principal QP solution, a choice now explicit.
*Kernel-checked 2026-09-28 (G2 roots; composed without hypothesis
2026-10-03, R28-R2):* on the true eps^-1, from the irreducible WFN data and
the exact Coulomb averages, with no hypothesis,
`Headline.roots_exist_irr_unconditional` gives exactly one zero of the full
QP equation in each of the two brackets and
`Headline.o1_fullQP_irr_unconditional` gives, for those zeros, O1_fullQP in
[68.9856742, 68.9856744] meV > 0 (both conventions at wx = wtilde).
`R.rootX0` / `R.rootL0` (stage-3 literals, for every Coulomb average in its
certified box) add the derivative enclosure (hence Z) and an isolating
sub-bracket; `R.o1_fullQP_irr` itself keeps the box hypotheses `VbHyp`. That
these brackets hold the PRINCIPAL (largest-Z) roots, the cover of the rest of
the window (so "exactly two roots") and the low-weight brackets remain the
Python certificate above: kernel-checking ~1350 boxes per state was
measured at ~3000 CPU-hours.

The certificate is independent of how the Fortran behaves where it divides
by zero (wx = w, wx = -w for a mode): E1 never evaluates there
(`wdiff_zero_possible` = `source_undefined_possible` = 0), no root bracket
contains such a point, and elsewhere the kernel encloses both IEEE-NaN and
continuous conventions. Beyond the window nothing is claimed (the invalid-mode convention
wtilde = 1e12 eV puts artificial structure near 1e12 eV).

**A1 production cross-check.** Production's own GPP Sigma(E) on a 1 meV
grid over Eo +- 8 eV (`finite_difference_form -3`; `a1_production_check.py`,
data/a1_production_check.json) has exactly one sign change per state in the
window: X 4.19457, L 4.12559 eV, O1 = 68.971 meV. The 0.18 meV per-state
difference from spec A is the Monte Carlo Coulomb average (the float
reproducer with the replicated Monte Carlo gives 4.19456 / 4.1256); on O1 it
is 15 micro-eV. In this mode the printed Eqp1 (4.4736 eV for X) is not a
root of the QP equation (the source says so: write_result.f90:129), and
spectrum.dat's i4 frequency index overflows to '****' beyond 9999 points.

**A1 qualification (float, 2026-09-23).** The unique root above exists
because production's sexcut clamp removes the hole-branch SX poles
(E = e_occ - w). With sexcut disabled the same GPP QP equation has, within
+-0.6 eV, 11 sign changes for X (1 a genuine root, at 4.011 eV) and 5 for L
(root at 3.857 eV): O1 would be ~+154 meV and the solution not unique. The
certified A1 number is therefore a property of the regularised GPP
equation, not of GPP-GW as such.

**A2 (measured, 2026-09-23).** Full-frequency RPA GW by contour deformation
(production binaries; eps: real-axis step 0.1 eV to 40 eV, 30 imaginary
frequencies; sigma: Sigma(E) on Eo +- 12 eV, step 0.1, full QP equation by
interpolation). O1 = +58.3 meV (broadening 0.05 eV), +67.2 (0.1 eV),
+58.1 (15 imaginary frequencies); at broadening 0.02 eV the X state has two
QP solutions. The imaginary-axis quadrature is converged at ~0.2 meV; the
broadening is not a numerical nuisance but a regularisation of the same
pole structure that sexcut removes in GPP.

**A2 at a well-defined energy.** Because the QP roots sit in Sigma's pole
structure, the clean plasmon-pole comparison is the correlation self-energy
at E = Eo: Sigma_c(X) - Sigma_c(L) = +113.4 meV (GPP) vs +145.0 meV
(full-frequency RPA, CD), stable to 0.25 meV over broadening 0.02-0.1 eV,
real-grid step 0.05-0.1 eV and 15-30 imaginary frequencies. **The
plasmon-pole model error on this O1 contribution is -31.6 meV.** BerkeleyGW's
CD residue term interpolates W linearly on the real grid and its imaginary
integral uses piecewise-constant quadrature (cd_int_method 0). An
independent reproduction (`spec_cd.py`, `a2_repro.py`; float) matches the
production CD diagonal table of all 14 multiplets to within half a print
unit (<= 5e-7 eV); evaluated without interpolation and with a converged
imaginary-axis quadrature (`a2_exact.py`) the same formula differs from
production by +0.009 meV on Sigma_c(X) - Sigma_c(L) (the 30-point
quadrature is ~0.55 meV off per state but cancels), and its eta -> 0 limit
is regular (145.0022 - 3.31 eta^2 meV). **Plasmon-pole model error at E = Eo:
-31.588 meV** on Sigma_c(X) - Sigma_c(L) (per state -96.3 X, -64.7 L meV),
unaffected by the CD numerics (0.009 meV) or eta (0.03 meV).

**A3(b) exactly solvable model (Lean, kernel-checked; branch a3/hubbard-dimer,
merged).** For the half-filled Hubbard dimer with 0 <= U <= t
(`GW/Endpoint/HubbardDimer*.lean`, `gw_gap_error_main`): for any sector
ground energies and any physical-side QP solutions,
|gap_G0W0@HF - gap_exact| <= U^2/(8t); the U^2 is sharp (`no_cubic_bound`);
both the GW and HF errors start at +-U^2/(8t) -- G0W0 doubles the exact
second-order gap correction, i.e. it misses the second-order exchange --
and GW beats HF only through U^3. *Added 2026-09-23 (A3-dimer-2):* the
single-pole Sigma_c is now derived in Lean from the time-domain
i G0(tau) W_c(tau) (damped Fourier transform, eta -> 0+, real omega off the
poles; `sigmaSinglePole_eq_limit`), and the U^2 structure is exact
(`HubbardDimerSecondOrder.lean`): gap_HF = 2t, the second-order direct
(ring) term gives +U^2/(4t), the second-order exchange (SOX) -U^2/(8t);
gap_GW = HF + direct + O(U^3), gap_exact = HF + direct + SOX + O(U^4), so
gap_GW - gap_exact = -SOX + O(U^3) = U^2/(8t) + O(U^3)
(`gw_error_is_minus_sox`). *Added 2026-09-25 (G3):* the closed-shell
second-order formula is no longer taken on trust for the dimer:
`HubbardDimerExactSigma.lean` builds the exact G by Lehmann over all N+-1
eigenstates of the Fock-space H and proves Sigma_exact = U/2 + direct + SOX
exactly, for every U (with HF orbital energies in the denominators; checked
independently by exact diagonalisation: pole at +-3t + U/2, weight U^2/4).
A model result, not a bound for silicon.

**A3(a) general finite fermion system (Lean, 2026-09-25; branch
lean/g4-general-gw, merged; `GW/Endpoint/ManyBody/`, 308 theorems).** For
any H = H0 + lambda V on the Fock space of n spin-orbitals (H0 one-body
diagonal, V a general two-body interaction with real integrals v_pqrs = v_qpsr = v_rspq,
nondegenerate Slater-determinant ground state of H0), at real omega off the
unperturbed excitations, as formal power series in lambda:
Sigma_exact = lambda HF + lambda^2 (direct + SOX + relax) + O(lambda^3)
(`sigma1_eq_HF`, `sigma2_eq_direct_add_sox_add_relax`) and, at omega also
off the GW poles (`GWOffPoles`: omega + eps_a - eps_r - eps_s != 0 and
omega + eps_r - eps_a - eps_b != 0 for occupied a, b and empty r, s; this also
excludes points such as r = s that are not Fock-space excitations),
Sigma_G0W0 = lambda HF + lambda^2 direct + O(lambda^3) (`gw1_eq_HF`,
`gw2_limit`), so Sigma_exact - Sigma_GW = lambda^2 (SOX + relax) + O(lambda^3)
(`gw_error_second_order`); relax_pq = sum_{a occ, r emp} (<pa||qr> + <pr||qa>)
Sigma1_ra / (eps_a - eps_r) is the HF diagram with a first-order insertion
and vanishes under the Brillouin condition Sigma1_ra = 0 (then the error is
lambda^2 SOX, `gw_error_second_order_brillouin`). The plan's statement
(SOX only) was false for a non-HF H0 -- found by the worker, confirmed
by exact diagonalisation (`python3 bgw/endpoint/manybody/check_sigma2.py --n 4`,
default seed: max mismatch ≈ 13.5 without relax, ≈ 6e-7 with it). Relevance here: the EPM starting point is not HF, so relax is
in principle present for Si-EPM; the A3(c) estimate covers SOX only. *Added
2026-09-27 (G4-analytic):* the formal coefficients ARE the expansion of the
actual function: for |lambda| < delta the true ground state of H(lambda) in
the sector is simple and lowest, omega stays off the poles, and
|Sigma(omega; lambda) - (lambda Sigma1 + lambda^2 Sigma2)| <= K |lambda|^3
(`sigma_exact_expansion`; hypothesis `IsGround`: the Slater determinant is
the strict ground state of H0 in its sector; eigenvector by a contraction
fixed point, no spectral theorem). The GW side is still the second-order
polynomial `sigmaGW2` = lambda (Sigma_H + Sigma_x) + lambda^2 dir2 (a full G0W0
function of lambda would need RPA W(lambda) as a function); it is G0W0 through
second order only where `GWOffPoles` holds, which `sigma_exact_minus_gw` does not
assume (elsewhere `dir2` has totalized 1/0 denominators). On the GW side G0 (the textbook T = 0 closed form `G0t`, not derived from the
Fock-space H0), W^(2) = v chi0 v, the orbital-pair projection of i G W and
Sigma_GW^(1) = Hartree + bare exchange are definitions.

**Why A1 and A2 are large here.** With Vxc = 0 (EPM), Sigma ~ -9 eV and the
conduction QP solutions (4.1-4.5 eV) lie below the mean-field valence top
(~10 eV), i.e. deep inside the pole/satellite structure of Sigma built from
G0. One-shot G0W0 assumes the QP energy is close to the G0 pole; here it is
~7 eV away. The dominant layer-3 question for this calculation is the
starting point / self-consistency, which the next step (eigenvalue
self-consistent GW) tests. Across every well-defined treatment so far, at
the production settings, O1 stays positive (15.4 to ~154 meV); the sign is
not robust to the band count (≈ −3.8 meV with all bands of the basis, scope
note at the top).

**A3 starting point: evGW0 (production binaries, 2026-09-23).** Iterating
the QP energies in G (`eqp_corrections`, W from EPM fixed; `evgw0.py`)
converges O1 to **+137.87 meV** (stable to 1e-6 eV after ~10 iterations;
data/evgw0.json), with QP energies X 2.742 eV, L 2.604 eV and O2 = 4.709 eV.

| treatment | O1 (meV) |
| --- | --- |
| G0W0-GPP, linearised (production) | +15.4 |
| G0W0-GPP, full QP equation, sexcut (certified, A1) | +69.0 |
| G0W0-GPP, full QP equation, no sexcut | ~+154, not unique |
| G0W0 full-frequency RPA (CD, broadening 0.05-0.1 eV) | +58 to +67 |
| evGW0-GPP | +137.9 |
| evGW-GPP (G and W; `evgw.py`) | +134.20 +- 0.03 |

evGW: O1 and O2 (5.042 eV) settle to 0.05 meV / 5 micro-eV, while a few
high-band energies keep oscillating (max |dE| 0.2-1.1 eV per iteration): not
fully converged, recorded as such. WFNq receives the QP shift of the WFN
point it is displaced from by q0 (O(q0) neglected).

**A3(c) leading vertex term (estimate).** Second-order self-energy with
bare v (`second_order.py`; its integrals reproduce the production X to
1e-10 eV). On the evGW0 QP spectrum, evaluated at each state's own QP
energy, the second-order exchange (SOX, the leading term GW omits) moves O1
by **+1.98 meV** (the second-order direct term, contained in GW, by -3.30
meV); at E = Emf on the EPM spectrum: -0.39 vs +15.3 meV. At the one-shot
Eqp1 energies the second-order terms are dominated by near-zero energy
denominators and are not meaningful. This is an estimate, not a bound: no
theorem controls vertex corrections in a solid.

C1 (O1 > 0) holds in every well-defined treatment at the production settings
(not robust to the band count, scope note at the top); the magnitude of O1 is
not determined to better than an order of magnitude by the GW hierarchy
itself, while the leading vertex correction is estimated at ~2 meV.

## 4. Specification (as reproduced; every convention is cited in `bgw/endpoint/spec.py`)

The object is BerkeleyGW's finite GPP calculation, in exact real arithmetic,
on the mean-field files WFN, WFNq, WFN_inner, RHO (Rydberg units, eV at the
end with RYD = 13.60569253):

- **Screening.** chi0(q) = 4/(N_k Omega) sum_k sum_{v<=4<c<=18} M M* /(E_v - E_c)
  over the 48-op closure of the shifted grid (32 k-points, not the nominal 8),
  eps = 1 - v chi with v = 8 pi/|q+G|^2, eps^-1 its inverse; at q0 = (0,0,0.001).
- **Symmetry.** Wavefunctions and eps^-1 are carried to the full q-grid by the
  space-group formula; for each q, Sigma uses the LAST (iq, op) that matches
  (irrbz has no exit), which for q = 0 is op 48 of 48.
- **Coulomb.** v(q+G) is the mini-BZ (Wigner-Seitz cell of the q-lattice)
  average of 8 pi/|q+G+p|^2 for EVERY (q, G) (avgcut = 1e12 Ry). Spec A uses
  the exact average; production estimates it by Monte Carlo (MT19937, seed
  5000, first nn2 points).
- **Wings.** q = 0: wings zeroed, head kept. q != 0: row/column of the
  IRREDUCIBLE G = 0 (target G = g0) scaled by oneoverq |q|/(8 pi) and by
  oneoverq/(vcoul(1) |q|), vcoul(1) the sortrx-first element.
- **GPP.** Omega^2 = omega_p^2 vbar(q+G)/(8 pi) (q+G).(q+G') rho(G-G')/rho(0);
  I = delta - eps^-1; modes with |I| < 1e-6, |Omega^2| < 1e-6 or
  |wtilde^2| < 1e-6 dropped; wtilde^2 < 0 ("invalid") -> static limit
  wtilde = 1e12 eV. Generic branch where |wx - wtilde| > gamma = 0.5 eV and
  |wtilde/(wx - wtilde)|^2 < 2.5e5; otherwise occupied bands use the combined
  SX+CH limit -I wtilde/(2(wx + wtilde)) and unoccupied bands drop CH;
  SX set to 0 when |SX| > 4|I| and wx < 0.
- **Self-energy.** X, SX(E), CH(E) summed over 8 q, 18 bands, the spheres
  |q+G|^2 < 11 Ry (bare) and < 7 Ry (screened); static remainder
  achcor = (1/2)(exact static CH - sum_n1 partial static CH); diagonal
  elements averaged over degenerate multiplets.
- **QP.** Eqp1 = Eqp0 + dS/(1-dS) (Eqp0 - Eo), dS the forward difference with
  dE = 1 eV, Vxc = 0 (EPM).

Spec B differs from A only in the q = 0 cell: the average of the Sigma
contributions over the 48 rotations of eps0mat (the angular average of the
direction-dependent q -> 0 limit, exact for a cubic crystal).

## 5. Silent-error checklist (E1.5)

rounding and floating-point propagation over the full sums; branches (GPP
branch selection, TOL_Zero, sexcut, fixwings); indexing (gmap, umklapp,
k+q folding); units (Ry/eV, cell volume, Coulomb prefactor); symmetry
unfolding (rotations and non-symmorphic phases in diamond); degenerate
multiplets cut by `number_bands`; near-pole modes; sqrt of the squared pole;
q→0 Coulomb averaging and its randomness; the head/wings of ε⁻¹.

## 6. Trust base (stated, not hidden)

The current trust list for Claim 1 is the one in E1.4 and README.md ("Trusted, not
proved"): the export of the run files into Lean literals, the Fortran-to-specification
correspondence, and the production execution. The O1 enclosure itself is kernel-checked.
The items below concern the Python-only results:

Lean kernel for proved rules; IEEE-754 round-to-nearest binary64 for the
Python enclosure arithmetic (the `Rounding` hypothesis of `CertInterval.lean`); the Python reproducer's
code (mitigated by mutation tests and a second independent check where
feasible); the production input files as produced and their export into
Lean literals (RHO and the run parameters are export literals; no committed
digest links the literals to the run files).

## 7. What changes in the existing architecture

M1–M5 per-record Lean certificates stay as unit evidence of kernel pieces;
no further per-record certificates are written — they do not scale to the full
sums. LL theory (PR #26) is parked.
