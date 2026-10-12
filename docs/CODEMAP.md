# Code map: canonical and archived modules

Written by WRAPUP (2026-10-01) under the feature freeze (`.agent/STATE.md`). Status: worker
output, ready for review, not accepted. Updated 2026-10-02 by R28-WORDS: the four open
questions below received labels in `.agent/tasks/R28-WORDS.md` (the REVIEW-28 brief), and
those labels are applied here. Updated 2026-10-03 by R28-R2: `GW.Endpoint.Kernel.Headline`
and the new `GW.Bridge.Common` theorems (`.agent/tasks/R28-R2.md`).

**How "canonical" was decided.** It was decided from the import graph and from the modules
the final theorems use, not by guessing. The final theorems are those of `docs/ENDPOINT.md`
(the headline compositions without Coulomb-box hypothesis `Headline.o1_enclosure_irr_unconditional`,
`o1_pos_irr_unconditional`, `roots_exist_irr_unconditional`, `o1_fullQP_irr_unconditional`;
the theorems they compose, `S3.o1_enclosure`, `o1_pos`, `Coul.o1_enclosure_unconditional`,
`U.o1_enclosure_irr`, `R.o1_fullQP_irr`; the A3 many-body results) and of `docs/BRIDGE.md`
(the conditional identities `sigA_eq_theory`, `sigA_eps_eq_theory`, `sigA_eq_theory_q0`,
`sigA_eps_eq_theory_q0`, `sigA_eq_theory_disc`, `sigA_all_bands`, and the R28 additions
`sigA_compat`, `sigA_all_bands_lowdin`, `cor_all_decomp`).
* A module is CANONICAL if it is in the import closure of the `GWKernelData` roots
  (`lakefile.toml`), of `GW/Bridge/*`, or of an A3 result named in `docs/ENDPOINT.md`.
* A module is ARCHIVED if no canonical module imports it and a later lineage replaced
  what it did.
* A module of an older lineage that a canonical module imports is load-bearing, carries
  no ARCHIVED banner, and is CANONICAL (labelled 2026-10-02; WRAPUP had called these
  RETAINED and left the label open).

`python3 scripts/registry.py` regenerates the registries from the source tree; see
`AGENTS.md`.

## Layers

`Data.*` means `GW/Endpoint/Kernel/Data/*`. These modules are GENERATED and built only by
the non-default target `GWKernelData`. `GW.Endpoint.Kernel.Headline` is hand-written, a
`GWKernelData` root, and built only by that target too.

| Layer | Canonical Lean | Canonical Python | Archived (superseded by) |
| --- | --- | --- | --- |
| Input / export | `GW.Endpoint.Kernel.Unfold`, `UnfoldPhase`; `Data.U*` (symmetry unfolding from the irreducible WFN data) | `bgw/endpoint/run_production.py` (inputs: `bgw/export/*.in`, `*.inp`), `bgwio.py`, `observable.py`; Lean emitters `kernel_export.py`, `coulomb_export.py` | `bgw/oracle.py`, `bgw/reproduce.py`, `bgw/verify_export.py`, `bgw/kernel_transcript.f90`, the `bgw/export/*.dat` dumps (T-001…T-002 transcript checks; replaced by `spec.py` + `cert.py` on the full production run) |
| eps (static RPA) | `GW.Endpoint.Kernel.EpsSpec`, `EpsCheck`, `EpsSound`; `Data.E*` | `bgw/endpoint/spec.py` (`Screening`), `cert.py` (`epsinv_iv`) | `GW.BGW.M3Transfer`, `GW.BGW.M3Chi`, `bgw/m3_chi/` (BGW-M3: two chi entries; replaced by `EpsSpec` + `Data.E*`) |
| eps⁻¹ | `GW.Endpoint.Kernel.Check`, `Sound`, `GW.Endpoint.CertInverse`; `Data.Q*` | `iv.py` (`inverse_cw`), called by `cert.py` (`epsinv_iv`) | `GW.BGW.M1Screening`, `GW.BGW.M2Screening`, `bgw/m1_screening/`, `bgw/m2_screening/` (BGW-M1/M2: one 8×8 block; replaced by `Data.Q*Check`, `Data.E*Check`) |
| Coulomb | `GW.Endpoint.Coulomb.*`; `Data.Coul*` | `bgw/endpoint/coulomb.py`, `certcoulomb.py` | none |
| GPP kernel | `GW.Endpoint.Kernel.SigmaSpec` (modes, branches, thresholds), `GW.Endpoint.NearPole`, `GW.Endpoint.CertSexcut` | `spec.py` (`gpp_modes`, `gpp_kernel`), `cert.py` (`SigmaIV.kernel`) | `GW.GPP.BerkeleyGWMap`, `GW.GPP.PoleDomain`, `GW.BGW.M4GPP`, `bgw/m4_gpp/`, `bgw/occupation_audit/`, `bgw/weighted_audit/`, `bgw/branch_boundary/` (T-002…T-005 branch audits, BGW-M4 single pole; replaced by `SigmaSpec` + BRIDGE rows 8-15) |
| Σ | `SigmaSpec`, `SigmaCheck`, `SigmaKernel`, `SigmaHot`, `SigmaTab`, `SigmaEnt`, `SigmaGlue`, `SigmaStq`, `SigmaAsm`; `Data.S3*`; `GW.Endpoint.CertInterval` (the iv.py operations) | `cert.py`, `iv.py`, `spec.py` | `GW.GPP.FiniteSelfEnergy`, `GW.Examples`, `Main` (`gpp_demo`), `scripts/reference.py`, `scripts/plot_demo.py` (the Specification.md v0.1 synthetic demo); `GW.BGW.M5Sigma`, `bgw/m5_sigma/` (BGW-M5: one mode; replaced by `Data.S3*`) |
| QP / O1 | `SigmaSpec` (linearised `Eqp1`, O1); `Data.S3Check` (`o1_enclosure`, `o1_pos`), `Data.CoulTab` (`Coul.vb_hyp`, `oq_hyp`, `o1_enclosure_unconditional`), `Data.US` (`o1_enclosure_irr`, `o1_pos_irr`, which keep `VbHyp`); `GW.Endpoint.Kernel.Headline` (`o1_enclosure_irr_unconditional`, `o1_pos_irr_unconditional`: the irreducible-data theorems with the Coulomb boxes discharged, no hypothesis; no new mathematics). `o1_pos*` compares X and L only; the minimum over all sampled k-points is Python (`cert_o1.json`) | `cert.py` (O1), `observable.py` | none |
| Roots (full QP equation) | `GW.Endpoint.Kernel.RootSpec`, `RootCheck`, `RootKernel`, `RootHot`, `RootStq`, `RootAsm`, `GW.Endpoint.QPUnique`; `Data.R*` (`R.roots_exist_irr`, `R.o1_fullQP_irr`, which keep `VbHyp`); `Headline.roots_exist_irr_unconditional`, `o1_fullQP_irr_unconditional` (no Coulomb-box hypothesis; `o1_fullQP_irr_unconditional` is stated for the bracketed zeros, which `roots_exist_irr_unconditional` shows exist and are unique). That the brackets hold the principal roots is Python (`qp_unique.py`) | `qp_cert.py`, `qp_unique.py`, `qp_full.py`, `a1_production_check.py` | none |
| Many-body theory | `GW.Endpoint.ManyBody.*` (G4: finite fermion models, GW error structure), `GW.Endpoint.HubbardDimer*` (A3(b)) | `bgw/endpoint/manybody/`, `a3_dimer/`, `second_order.py`, `evgw0.py`, `evgw.py`, `spec_cd.py`, `a2_*.py` (A2/A3, measured only) | `GW.LL.RingHalfEdge`, `GW.LL.Wick`, `LLMain`, `LLC2AMain`, `LLC2BMain`, `LLC3Main`, `LLC4Main`, `ll/*.py` (LL-C1…C4, the Lin-Lindsey classical Gibbs track, parked per `docs/ENDPOINT.md` §7; electronic many-body theory continues in `GW.Endpoint.ManyBody`) |
| Bridge (theory → spec; conditional identities, scope per `docs/BRIDGE.md` "Scope after REVIEW-28") | `GW.Bridge.*` (12 modules at d783e18; R28 additions: `GW.Bridge.Common` (R28-F1: `MF`, a data record that requires no orthonormality and no Hamiltonian; `Compat`, which since R28-R2 requires `k0` and every `k0 − q_t` on the grid; `sigA_compat`, `compat_self`, `compat_st_unique`, `compat_energy_shift`, `MF.blk_ok`, `Espec_q0_input`; R28-R2: `offgrid_loophole` (the case the grid fields close), `MF.tr_fixed`, `compat_selfpaired_no_TR` (`MF.TR` cannot hold for a block whose `neg` fixes a grid point with a nonzero sphere vector), `hyps_unsat_of_unpaired` (for X/L the hypotheses of `sigA_compat` are unsatisfiable given `hnp`: no grid index stores the negated sphere list of X or L, checked numerically on the Si-EPM Σ grid by `bgw/r28_f1/check.py`, for any sphere ordering; storing X/L once does not give `hnp`); R28-R3: `hyps_unsat_of_selfpaired` (the same without `hnp` when every plan's `neg` fixes X/L, whose spheres hold a nonzero vector; that every plan's `neg` fixes X/L follows from `neg` encoding `-k` on a grid that stores each k-point class once only as trusted plan semantics, not as a theorem, since `MF` has no k-coordinates)), `GW.Bridge.CorResidual` (R28-F4), `GW.Bridge.CorPerturb`, `GW.Bridge.Lowdin` in `CorPerturbLowdin` (R28-F3)) | `bgw/bridge_measure/`, `bgw/bridge_q0/`, `bgw/bridge_disc/`, `bgw/bridge_cor/`, `bgw/r28_f1/`, `bgw/r28_f3/`, `bgw/r28_f4/` | none |

**CANONICAL older-lineage modules (imported by canonical `GW.Bridge`; labelled CANONICAL
2026-10-02, formerly "RETAINED").** They are canonical for the layer they serve; reuse
them instead of reimplementing it:
* `GW.GPP.PoleCancellation`: `occupiedTerm`/`emptyTerm`, used by `Bridge.FreqIntegral`.
* `GW.LL.Diagram`, `Ring`, `StructuralRing`, `Screening`, `Electronic`:
  `dielectric`/`electronicW`/`gppInvEps`, used by `Bridge.GPPModel` and `Bridge.EpsRPA`.

## Documents

| Canonical | Archived (superseded by) |
| --- | --- |
| `README.md` (scope summary), `.agent/STATE.md`, `docs/ENDPOINT.md`, `docs/BRIDGE.md`, `docs/CODEMAP.md`, `docs/reviews/` (REVIEW-28, the post-fix review R28-R2, and the index `docs/reviews/README.md`), `docs/review/index.html` (the reviewer's guide to the certified-evaluation chain, generated by `bgw/endpoint/make_review.py`; regenerate it after a full gate, since it reads `artifacts/axioms.log`); the generator's footer links this file | `docs/ROADMAP.md` (GPP-kernel stages; replaced by `docs/LIN_LINDSEY_ROADMAP.md`, then `docs/ENDPOINT.md`); `docs/LIN_LINDSEY_ROADMAP.md` (parked; `docs/ENDPOINT.md`); `docs/DEMO_RESULTS.md`, `docs/BERKELEYGW_4.0_GPP.md`, `docs/SOURCE_MAP.md` (demo and T-002…T-005 records; `docs/ENDPOINT.md` §4); `docs/LL-*-REVIEW.md` (LL review records; the live community-alignment rules and policy sources of `docs/LL-C1-REVIEW.md` §5 are copied into `AGENTS.md`, 2026-10-02) |

`Specification.md` (v0.1) is the contract of the archived demo. It is kept unchanged as
the project's founding specification (its bytes are digest-pinned in
`bgw/weighted_audit/PROVENANCE-R6.txt`). The canonical specification is `docs/ENDPOINT.md` §4,
transcribed in `SigmaSpec.lean` and `EpsSpec.lean`. The reading order in `AGENTS.md` and
`CLAUDE.md` is now `.agent/STATE.md` → this file → `docs/ENDPOINT.md` / `docs/BRIDGE.md`,
with `Specification.md` listed last as the archived demo contract.

**Withdrawn layer (E2), ARCHIVED 2026-10-02.** `bgw/endpoint/sweep.py`, `e2_analyze.py`
and `e2_layer1.py`, with `bgw/endpoint/data/e2_results.jsonl`. E2 was withdrawn from scope
on 2026-09-23 (`docs/ENDPOINT.md`). The three scripts carry the banner; the data is kept.
They are not in `gates.ARCHIVED_PATHS` yet: that file is generated, so the integrator adds
them.

## ARCHIVED banners

Each archived file has a one-line `ARCHIVED (2026-10-01)` banner. The banner is merged
into the first line of the file's top docstring or title, so no line number moves:
historical handoffs and audits cite `file:line`. This changed comments only, not
statements.

The following files are archived but have **no banner**, because recorded evidence pins
their bytes (sha256) and a banner would falsify that record:
* `GW/BGW/M2Screening.lean` (`bgw/m2_screening/evidence/full-proof-replay.log`)
* `GW/BGW/M3Chi.lean` (`bgw/m3_chi/evidence/mutations.log`)
* `GW/BGW/M4GPP.lean` (`bgw/m4_gpp/evidence/mutations.log`; also GENERATED, and
  `tests/test_bgw_m4.py` compares it with `make_lean.render`)
* `GW/BGW/M5Sigma.lean` (`bgw/m5_sigma/evidence/mutations.log`; generated, `tests/test_bgw_m5.py`)
* `bgw/m2_screening/{extract,reference,run_m2}.py` (`full-proof-replay.log`)
* `bgw/m3_chi/mutate_certificate.py`
* `bgw/m4_gpp/{instrument_r1,mutate}.py`, `bgw/m5_sigma/{instrument_m5,mutate}.py`
  (mutation and A/B-neutrality logs)
* `ll/ring_reference.py` (`audits/ll_c1_review/evidence.json`)
* `bgw/branch_boundary/README.md`, `bgw/branch_boundary/branch_boundary.f90`
  (`.agent/handoffs/T-005-R1.md`); `bgw/kernel_transcript.f90` (Fortran, no docstring;
  covered by `bgw/README.md`)

Their directory-level `PROVENANCE.md`/`README.md` carry the banner instead.

## Allowed dependency direction

```
Coulomb.*  ─┐
Kernel.Check → EpsCheck → EpsSpec → SigmaSpec → Sigma{Check,Kernel,Hot,Tab,Ent,Glue,Stq,Asm} → Root* → Data.* (generated) → Kernel.Headline
NearPole → CertSexcut ┘           └→ Unfold → UnfoldPhase
ManyBody.* ← HubbardDimer*
Bridge.* → {Endpoint.Kernel.SigmaSpec, EpsSpec, ManyBody.GWSecond, GPP.PoleCancellation, LL.{Diagram,Ring,StructuralRing,Screening,Electronic}}
```

* Canonical modules may import canonical modules (including the older-lineage ones
  above). They must not import an ARCHIVED module.
* `GW.Endpoint.*` must not import `GW.Bridge.*`, because the bridge is downstream of the
  spec it compares with.
* Only exporters write `Data.*`: `kernel_export.py` writes eps, Σ, unfolding and roots,
  and `coulomb_export.py` writes `Coul*`. Do not edit `Data.*` by hand.
* ARCHIVED modules are frozen. They may keep importing whatever they import now, but
  nothing new may depend on them.
* Python follows the same direction. `bgw/bridge_*` import `bgw/endpoint`. The reverse
  direction does not occur.
* **Exception (recorded, not fixed).** `bgw/endpoint/mutate_lean.py` (E1.4, canonical)
  loads the archived `bgw/m4_gpp/mutate.py` as a utility. `run_production.py` and
  `sweep.py` read the input decks in `bgw/export/`. Those decks are shared input data,
  not archived code.

## Former open questions (labelled 2026-10-02 in `.agent/tasks/R28-WORDS.md`; applied)

1. **RETAINED modules.** `GW.GPP.PoleCancellation` and the five `GW.LL` modules imported
   by `GW.Bridge` are CANONICAL (section above).
2. **E2 scripts.** `bgw/endpoint/sweep.py`, `e2_analyze.py`, `e2_layer1.py` are ARCHIVED
   as a withdrawn layer, with a banner (section above). Their data is kept.
3. **`docs/LL-C1-REVIEW.md`.** The live rules it supplied (community alignment, human
   ownership before upstream contribution, policy sources) are copied into `AGENTS.md`.
   The review itself stays ARCHIVED.
4. **`Specification.md`.** The reading order in `AGENTS.md`/`CLAUDE.md` is STATE →
   CODEMAP → ENDPOINT/BRIDGE; `Specification.md` is kept and labelled the archived demo
   contract.

## Tests: fast gate and redundancy candidates

`bash scripts/verify.sh --gate fast` (WRAPUP item 5; the map is `FAST` in `scripts/gates.py`)
runs these steps:
* the registry check;
* `lake build GW`;
* the memoized audit of the default library (`scripts/CheckAxiomsFast.lean`; no
  `GWKernelData`);
* the workflow tests;
* the canonical scientific tests whose covered paths changed, as parallel processes.

The change is the uncommitted diff, or the last commit if the tree is clean
(`--base REF` overrides this). The selection works like this:
* A changed path that no test covers and that is neither prose/Lean (`NO_PYTHON_TEST`)
  nor archived makes the selection unsure. Then every `FAST` module runs.
* Tests of archived lineages (`ARCHIVED_TESTS`) run only in the full gate.
* An archived path that changed is reported.

**Measured wall time** (warm `.lake/build`, 16 cores, 2026-10-01; `artifacts/verification-fast.json`):
* 66 s with no scientific change: the registry check took 1.5 s, `lake build GW` 2.3 s,
  and the audit 61.5 s over 3571 theorems; the 3 workflow modules then ran.
* 439 s with `--all-tests`, the worst case when the selection is unsure. Of that,
  `test_endpoint_e1` took 360 s and `test_endpoint_a` 196 s, both in parallel.

The fast gate is not a substitute for the full gate before a merge. In particular it
does not check:
* `GWKernelData` and its audit;
* the Lean executables;
* the exact oracle;
* the BerkeleyGW export checks;
* the archived tests.

**Redundancy candidates (same claim checked twice).** These are for the owner. No test
was deleted or changed. Each pair uses independent implementations (a separate oracle in
each module), so "redundant" means the claim is the same, not that the code is.

| Claim | Checked in | Note |
| --- | --- | --- |
| Theory kernel at `x = 0` is `∓I/2` for every small `Ω²` | `test_bridge_measure.Unit.test_x0_discontinuity`; `test_bridge_disc.test_x0_is_minus_half_I_for_every_small_Omega2` | the disc test covers more values and both occupations |
| Occupied `x = w̃` discrepancy: theory `I/4`, spec `0` | `test_bridge.test_x_equals_wtilde_discrepancy`; `test_bridge_measure.test_discrepancy_witness` | measure additionally checks its classifier refuses `x = w̃` |
| Invalid mode (`wt2 < 0`) → static-COHSEX limit | `test_bridge.test_invalid_mode_static_limit`; `test_bridge_measure.test_invalid_mode_is_static`; `test_bridge_cor.test_bgw_rule_invalid_mode_is_static_limit` | cor's version is on omitted bands (θ ≈ 1) |
| Empty near-pole mode dropped | `test_bridge.test_empty_near_pole_dropped`; `test_bridge_measure.test_empty_near_pole_zeroed` | |
| `mode_eq` (spec = theory on `ModeOK` modes) | `test_bridge.test_generic_branch_equal` + `test_occupied_near_pole_equal`; `test_bridge_measure.test_mode_eq_on_random_modeok` | |
| `cert_o1.json` has `wdiff_zero_possible = 0` | `test_endpoint_a.test_committed_certificates_are_convention_free`; `test_bridge_measure.test_counts_match_certificate` | the same JSON field |
| Fresh pinned BerkeleyGW run (computation, not claim) | `test_endpoint_e0` (2 runs), `test_endpoint_e1` (shared with `test_endpoint_a`), `test_bridge_measure`, `test_bridge_q0`, `test_bridge_disc` | about 10 s each. One shared run would save about 1 min |
