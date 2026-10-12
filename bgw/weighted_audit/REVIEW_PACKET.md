# External review packet — ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md.

**Live status lives elsewhere.** This document does not carry its own status,
because a hard-coded "draft" becomes false the moment Codex signs. The
authoritative record is
[`.agent/handoffs/CODEX-T-003-T-004-ACCEPTANCE.md`](../../.agent/handoffs/CODEX-T-003-T-004-ACCEPTANCE.md);
read its status block before quoting anything here. At the time of writing that
record is unsigned, and `.agent/STATE.md` carries the current milestone state.

Nothing here has been uploaded or sent anywhere.

Two release gates, deliberately not conflated:

* **Private external review** requires Codex's validation of the current repair
  pass.
* **Public publication** additionally requires choosing a license for this
  project's original code. **BSD 3-Clause is now chosen**; see `LICENSE` and
  `THIRD_PARTY_NOTICES.md`. The
  BerkeleyGW-derived material stays under BerkeleyGW's terms either way.

The project formalises **one scalar algebraic identity** from the
generalized-plasmon-pole self-energy kernel of BerkeleyGW 4.0 in Lean 4, and
then tests how that identity relates to the shipped Fortran. This packet asks a
reviewer to attack the physical interpretation, not to admire the proofs.

---

## 1. Claim / evidence table

Each row is a separate claim with its own evidence and its own strength. **No
row implies another.** "Kernel-checked" means the Lean kernel checked a proof
term; "measured" means a program was run; "read" means a human read Fortran.

| # | Claim | Strength | Evidence |
| --- | --- | --- | --- |
| C1 | The scalar identity `-A/(x^2-w^2) + A/(2w(x-w)) = A/(2w(x+w))` holds for real `A,x,w` with `w != 0`, `x != +-w`, and the merged form is the continuous extension at `x = w` | **kernel-checked** | `GW/GPP/PoleCancellation.lean`; audited in `GW/Audit.lean` |
| C2 | An exact rational evaluator agrees with the real model, and its checked entry point rejects nonpositive poles and vanishing denominators | **kernel-checked** | `GW/GPP/FiniteSelfEnergy.lean` |
| C3 | **At full occupation (`occ = 1`)**, under the mapping `A = Omega2 = w^2*ieps`, `x = wxt`, `w = wtilde`, the generic branch of `sigma_gpp_cpu` **is** C1's left side and the near-pole branch **is** its right side. At `occ != 1` the two differ by exactly C9's `branch_mismatch`, so the identification is occupation-conditional and C9, not C3, is the general statement | **read** (transcription) + **kernel-checked** (the resulting identities) | `docs/BERKELEYGW_4.0_GPP.md` sections 2-3; `GW/GPP/BerkeleyGWMap.lean` |
| C4 | A standalone transcript of the kernel's statements agrees with the exact merged form to `5.784e-17` absolute, `2.0839804` ulps | **measured** | `bgw/oracle.py`. An earlier claim of "<0.7 ulp" was wrong; see section 7 |
| C5 | A benchmark-validated BerkeleyGW 4.0 Si-EPM run reproduces all 24 shipped GPP assertions, and 96 exported records agree with C1's forms (48 nonzero comparisons, 48 zero placeholders) | **measured** | `bgw/export/`, `bgw/verify_export.py`, `docs/BERKELEYGW_4.0_GPP.md` section 7 |
| C6 | MP1 smearing cannot reach the GPP path at all in this revision; `occ_broadening` is rejected unless `freq_dep==2 .and. freq_dep_method==2` | **read** + **measured** (observed `die()`, exit 134) | `Sigma/inread.f90:528-532`; `bgw/occupation_audit/fixtures/smear_rejected.out` |
| C7 | Fermi-level half occupation (`occ = 0.5`) **does** reach the near-pole branch: 3702 evaluations in one real run | **measured** | `bgw/occupation_audit/REPORT.md` section 3 |
| C8 | That witness configuration is **physically inconsistent** and BerkeleyGW says so (`RHO` charge 8.0 vs occupations 7.0) | **measured** | `bgw/occupation_audit/fixtures/fermi_run_notices.txt` |
| C9 | At `occ != 1` the two branch formulas differ exactly by `(1-occ)*(Omega2/(2w(x+w)) + Omega2/((x-w)(x+w)))` | **kernel-checked** | `GW.GPP.BGW4.branch_mismatch` |
| C10 | As a **chosen pre-outer-factor L1 diagnostic**, that difference aggregates to **1.056%** of the affected GPP accumulators, and reaches **49.6%** in one per-call accumulator group | **measured**, partially weighted, **not a physical error estimate** | section 4 below; `artifacts/t004/weighted_mismatch.json` |
| C11 | Whether the developers intend `occ = 0.5` to be excluded here, or regard the error as negligible, is **unknown** | **not determined** | nothing read says |
| C12 | `MeanField/EPM/epm2bgw.f90:456` is the ONLY assignment to `ifmax` and broadcasts a single scalar to every k-point and spin, so `ncrit > 0` is unreachable through the EPM route **for any material** | **read** (single-site source claim), **not yet independently validated** | `.agent/handoffs/T-006-CAPABILITY-SCOUT.md` section 5 |
| C13 | Band-index symmetry `Sigma_nm = Sigma_mn` is **not testable** on this dataset: the transposes `(8,1)` and `(1,2)` were never computed by the probe run. The ket band `m` IS recoverable from the export by fingerprinting, so the blocker is a missing run, not a missing field | **measured**, **not yet independently validated** | `bgw/weighted_audit/symmetry_audit.py` |
| C14 | The 49.6% figure is a plateau: it is the reported maximum for every relative small-reference cutoff in `(1.919051e-4, 1.457943e-1]`, same argmax group throughout | **measured**, **not yet independently validated** | `bgw/weighted_audit/cutoff_sweep.py` |

### Claims explicitly NOT made

BerkeleyGW is not verified. The GPP model's physical accuracy is not assessed.
No floating-point error bound is proved. Nothing here is a final self-energy, a
physical energy error, an observable, an eV result, or a defect report. The complex flavor, GPU paths, full-frequency
and COHSEX kernels, `wpeff`, the static remainder and the quasiparticle root
solve are all outside every claim above.

---

## 2. Source references

Pinned revision: BerkeleyGW 4.0 source archive, SHA-256
`1a85b03b83b339056f65124bfa96832ca61152236d9bb1cb372e3040fc686a49`, the same
digest published in the Spack recipe. Not a VCS commit: the official GitLab
repository is not publicly readable and no public mirror was found.

| Location | What is there |
| --- | --- |
| `Sigma/mtxel_cor.f90:1685-1931` | `sigma_gpp_cpu`, the transcribed kernel (CPU, real flavor only) |
| `:1810-1812` | `wtilde2 = wtilde**2`, `Omega2 = wtilde2 * I_eps_array` -- the recompute that makes the large-pole limit `-ieps`, not 0 |
| `:1828-1843` | the three-way branch: generic, near-pole, dropped |
| `:1847-1848` | the `sexcut` clamp |
| `:1854-1855`, `:1908`, `:1915` | accumulation; note `occ` multiplies SX only |
| `:1530-1532` | `asxt(iw) += asxtemp(iw)`: where a call's accumulator is finalised |
| `:1397-1411` | `flag_occ`, `occ = 0.5` at the Fermi level, and the smearing override |
| `:779-797` | the five `invalid_gpp_mode` policies; default `-1` takes `case default` |
| `Sigma/inread.f90:82`, `:455-456` | the only two assignments to `invalid_gpp_mode` |
| `Sigma/inread.f90:528-532` | the guard that excludes smearing from GPP |
| `Sigma/input.f90:806` | `kp%el = kp%el*ryd`: energies inside the kernel are **eV** |
| `Sigma/shiftenergy.f90:113` | `fact = ryd/ndeg`, applied far outside the kernel |
| `Common/input_utils.f90:120-313` | `find_efermi`; `:237-238` is the `rfermi` branch |

---

## 3. Reproducible commands

No BerkeleyGW build or run is needed for anything in this section.

```bash
source scripts/env.sh
bash scripts/verify.sh                                   # full gate
python3 bgw/verify_export.py --all                       # T-002 saved exports
python3 bgw/occupation_audit/check_occupation.py         # T-003 48-record witness
python3 bgw/weighted_audit/weighted_mismatch.py          # T-004 all 3702 events
python3 -m unittest discover -s tests -v                 # every test
```

Regenerating the physical data needs a BerkeleyGW tree; the exact recipe,
digests, compiler and threading are in `bgw/weighted_audit/PROVENANCE.txt`
and `docs/BERKELEYGW_4.0_GPP.md` section 7.

---

## 4. Numerical results by output group

### 4.1 What is and is not weighted

The weight applied is the inner-loop factor only:

```text
K = aqsntemp(ig,n1) * MYCONJG(aqsmtemp(igp,n1)) * vcoul(igp)
```

Real flavor, so `MYCONJG` is the identity and no conjugation is applied. A
record with a nonzero imaginary pole component is rejected, not approximated.

**Missing from every number below, and the missing set differs by output
type** (correction, review finding 2):

| Output | Missing outer factors |
| --- | --- |
| both | `neq(irq)` (diagonal `sigma_main.f90:1586-1587`, offdiagonal `:1860-1861`); the q-sum; `ax`; `achcor` |
| diagonal `icalc=1` | `ryd` **and** `1/ndeg`, both in `fact = ryd/dble(ndeg(ii))` at `shiftenergy.f90:113`. The degenerate subspaces are built at `:69` by a loop over `sig%ndiag` only. |
| offdiagonal `icalc=2` | `ryd` only, applied with `neq` at `sigma_main.f90:1860-1861`. Offdiagonal elements receive **no** `1/ndeg` average. |

**Units** (correction, review finding 2): `ssx` and `sch` are dimensionless,
but the weight carries `vcoul(igp)`, which BerkeleyGW holds in Rydberg. So
these sums, and `asxtemp`/`achtemp` themselves, are **intermediate Rydberg**
values -- *not* dimensionless, and *not* eV. An earlier version of this packet
said "dimensionless"; that was wrong.

They remain **not a final self-energy, not a physical energy error, not an
observable, and not an eV result** -- the outer factors above have not been
applied. They are, however, energies in intermediate Rydberg units; earlier
revisions said "not an energy", which contradicted that.

`aqsn`, `aqsm`, `vcoul` and `qk` are **captured inputs**: no relation internal
to a record constrains them, so they are not independently validated.

### 4.2 Grouping

One `mtxel_cor` call accumulates into `asxtemp(iw)`/`achtemp(iw)`, so the
group is `(call_id, iw)`. `(in, il, ispin, icalc, iw, qk)` is **not** a valid
key: the offdiagonal band index `m` is implicit in the `aqsm` array rather than
passed, and even diagonal calls repeat that tuple (128 duplicates among 384
diagonal accumulator rows). The instrumentation therefore emits an explicit
per-call counter, and `(call_id, iw)` is verified unique. The outer identity
`(icalc, in, il, iband, ispin, qk)` is carried alongside and cross-checked for
consistency within a call. Different `iw` are never summed together, because
that would add different energy evaluations of the self-energy.

### 4.3 Totals

All 3702 qualifying events, none skipped, 0 singular, 53 groups, 456
accumulator rows, 0 groups without a matched accumulator.

The count is **not** hard-coded. The analyser reads the run's own tally
(`fixtures/fermi_branch_occ_counts.dat`), validates it with the T-003 checker's
tally logic unmodified, and requires the export to equal its near-pole
`occ != 1` count exactly. A tally altered from `76461 3702` to `76462 3701` --
preserving the row sum, so it survives the cross-run invariant -- is rejected.
The control tally must still show zero `occ != 1` events in every row.

**What that proves, precisely.** The checker establishes **cardinality and
record-id sequentiality against a validated tally**. It does not by itself
establish that these records *are* the counted events rather than a same-sized
different set. That conclusion additionally rests on two documentary links,
recorded in the JSON under `completeness_evidence`:

1. **same derived predicate** -- counting and emission happen at two sites in
   the same inner loop of `sigma_gpp_cpu`, both gated on
   `t4_b == 2 .and. t4_o == 2`, so a counted event and an emitted record are
   the same event. Readable in `bgw/weighted_audit/t004_instrument.patch`;
2. **same-run provenance** -- the saved tally file and the saved record file
   were written by the **same instrumented execution of the same binary**, per
   `bgw/weighted_audit/PROVENANCE*.txt`.

Cardinality plus sequential ids plus (1) and (2) give completeness. A reviewer
who does not accept (1) or (2) should read the claim as cardinality only.

**Correction, review finding 1, refined by T-004-R3 item 3.** An earlier
version quoted `0.673%`, formed by summing *signed* mismatches across all 53
per-call accumulator groups before dividing. Quoting that as "the" effect size
was wrong. But the replacement is **not** "the physically correct" number
either, and an intermediate revision of this packet overstated it as such.

The honest statement: taking magnitudes per `(call_id, iw)` produces a **chosen
dataset L1 norm** that avoids cancellation *within this diagnostic*. That is a
property of the choice. It is **not** evidence that inter-call or inter-q
cancellation is physically meaningless -- BerkeleyGW deliberately sums related
q-point and call contributions, with their outer factors, on the way to a
self-energy, and such cancellation is part of how the physical result is
formed. **Neither the L1 norm nor the signed cross-group ratio is a physical
error estimate.** The gap between them measures how much this dataset cancels
internally, not which one is right.

| Quantity | Value |
| --- | --- |
| per-call-group magnitudes, `sum_g abs(signed_g)` | `0.03155665844126213` |
| sum of `abs(asxtemp+achtemp)` over the affected calls | `2.98873078872563` |
| **per-call-group magnitude / affected accumulators** (`per_call_group_l1_over_accumulators`) | **`0.010559`, i.e. 1.056%** -- a chosen pre-outer-factor L1 diagnostic, not a physical error |
| sum of absolute weighted mismatches, per record | `0.0442668976572322` |
| within-group cancellation (`sum_g abs(signed_g)` / per-record absolute) | `0.713` |
| largest single term | `0.01887507` (record 1970) |
| that term as a fraction of the largest per-call group's signed mismatch | `131%` |
| signed counterpart (`cross_group_signed_over_accumulators`) | `0.006731` -- also not a physical error |

Neither field is designated primary in the JSON; `per_call_group_l1_note` and
`cross_group_warning` say so. The signed row is retained because it was
previously reported. The gap between the two is 36% of the L1 magnitude: that is the internal cancellation
of this dataset, reported rather than adjudicated.

### 4.4 By group

| View | Value |
| --- | --- |
| groups | 53 |
| largest per-call accumulator-group ratio, excluding small references | **`0.496`** (call 107, `iw=2`, diagonal, band 8, 134 events, accumulator `-0.02903`) |
| groups above 10% of their accumulator (small references excluded) | 7 of 53 |
| largest group ratio of any kind | `9.356` (call 11, `iw=2`, **offdiagonal**, accumulator `-3.7e-06`) |
| groups flagged small-reference | 6 |

**The `9.356` figure is a small-reference artefact and is not evidence of a
large effect.** Its reference accumulator is `3.7e-06`, four orders of
magnitude below the largest accumulator in the dataset (`0.19915`). The
analyser flags any group whose reference is below `1e-3` of that maximum and
reports the maximum ratio both with and without those groups. After that
stated exclusion, `0.496` is the largest per-call accumulator-group ratio in
this dataset -- a description of the dataset, not a claim that it is the
physically meaningful figure.

### 4.5 Where the diagnostic is concentrated

`ig` and `igp` are indices into BerkeleyGW's sorted G-vector list. An earlier
version called record 1970 "the `G = G' = 0` mode"; the export does **not**
contain G-vectors, so that identification is not established here and has been
removed.

Record 1970 dominates: `ig = 1`, `igp = 1`, `n1 = 1`, `wtilde = 21.41492` eV,
`wxt = 21.42123` eV, so `|wxt - wtilde| = 6.30e-03` eV -- deep inside the
near-pole window. The mismatch carries a factor `1/((x-w)(x+w))`, so it grows
as the pole is approached while the recorded contribution stays finite. The
result is therefore **dominated by pole proximity in a handful of `(ig,igp,n1)`
terms**, not spread evenly.

### 4.5a The grouped subtotal agrees in two arithmetic implementations

The instrumentation accumulates `sum(K*L)` over exactly these records in the
Fortran's own arithmetic; the analyser compares it per group and fails above
`1e-11` relative. Observed maximum: `8.601382692417945e-15` over 53 groups,
totals agreeing to `1.385e-16`. Only quantities the code already computes are
summed; the alternative branch expression is never evaluated in Fortran.

**What this does not establish.** It validates the grouped *subtotal* in two
implementations. It does **not** independently validate any individual captured
weight or local value, and it does not bound their individual reconstruction
errors: errors in individual terms can cancel within a subtotal. The individual
weights remain captured inputs, not independently validated quantities, exactly
as `weights_captured_not_validated` records.

### 4.6 The comparator is not a counterfactual run

`branch_mismatch` compares two algebraic expressions at identical inputs. A
program that actually took the generic branch would additionally re-apply the
`sexcut` clamp to the generic `ssx`. On these records that would have made no
difference (`generic_clamp_would_differ = 0`), but the comparator ignores it by
construction and is not a simulation of BerkeleyGW with the branch removed. No
BerkeleyGW source was modified to substitute the alternative expression.

### 4.7 The probe itself is not physical

Every number in this section comes from the T-003 witness: a Si-EPM run with
`fermi_level_absolute` set to inner band 1's energy. That places the Fermi
level below the valence maximum; BerkeleyGW reports `RHO` total charge
`8.00000` against occupations giving `7.00000`, and warns that the GPP plasma
frequency does not track a manual Fermi level. The run completes and is not
rejected, which is the point -- **no guard prevents the combination** -- but it
is not a physically self-consistent calculation, and these numbers must not be
read as an error in a real material.

---

## 4.9 T-006 material: NOT independently validated

**Read this before quoting anything in C12, C13 or C14.** Everything in
sections 1-4.8 was produced under a two-party process: Claude implemented and
Codex independently validated, re-ran and signed. The T-006 results (C12, C13,
C14, and the Lean `PoleDomain` module) have had **no second pair of eyes**.
They were produced by Claude and by subagents Claude directed, and verified
only by Claude re-running them. The owner chose to send them to external review
in place of that second pass, which is why this section exists rather than a
supervisor signature.

Concretely, that means:

* C12 is a **single-site source reading**. It is easy to check -- `grep -n
  ifmax MeanField/EPM/epm2bgw.f90` shows one assignment at line 456 -- and a
  reviewer should check it rather than take it, because it is load-bearing: it
  is the reason the project's stated blocker was wrong, and the reason a real
  witness needs a DFT campaign.
* C13's `m`-recovery by fingerprinting matched the `sigma.inp` offdiag block
  exactly, which is a strong consistency signal but is not a proof that the
  fingerprinting is sound.
* C14 is a robustness property of a **reporting choice**. Every caveat in
  section 4 applies to it unchanged. It says nothing about whether the ratio is
  physically meaningful; it says only that the number is not an artifact of the
  particular cutoff chosen.
* The `GW/GPP/PoleDomain.lean` theorems ARE kernel-checked and covered by the
  exhaustive axiom audit, so their correctness does not depend on review. What
  is unreviewed is the design judgement: that a two-level bundle was necessary
  and that the single bundled type the recommendation asked for is impossible.

Also unverified, and worth a reviewer's suspicion: `docs/` records gfortran 13,
the machine now has 16.2.0, and `bgw/reproduce.py` was not rerun. The archived
byte-exact Si-EPM reproduction is therefore **unchecked** under the current
compiler, not known-good.

## 5. Unresolved questions for the reviewer

Please challenge these directly rather than confirming them.

1. **Is the mapping right?** `A = Omega2 = wtilde^2*ieps`, `x = wxt`,
   `w = wtilde`, with `K` stripped. Does the occupied generic branch really
   correspond to C1's left side, given that `occ` multiplies SX but not CH?
2. **Is the grouping physically meaningful?** `(call_id, iw)` scopes one
   accumulator element. Is a per-call partial sum a meaningful object at all,
   or does only the full q- and band-summed `Sigma` mean anything, making
   section 4 a category error?
3. **Are the units and the stripped factors defensible?** These are
   intermediate Rydberg values with the outer factors stripped, and the
   stripped set differs between diagonal and offdiagonal outputs (4.1). Is a
   pre-outer-factor L1 diagnostic informative at all, or does omitting `neq`,
   `ryd` and (for diagonals) `1/ndeg` make the 1.056% figure uninterpretable?
4. **Is the occupation treatment right?** `occ = 0.5` at the Fermi level within
   `sig%tol = 1.3606e-5` eV, MP1 smearing excluded from GPP. Is the
   half-occupation branch of `mtxel_cor.f90:1399-1403` intended to be reachable
   in the near-pole branch at all?
5. **Is the branch predicate complete as we state it?** We claim near-pole
   `<=> |wxt - w| <= max(gamma, |w|/500)` and `delwr > TOL_Zero`. Is anything
   missing (setup skips, the `Omega2 < TOL_Small` cycle, the five
   `invalid_gpp_mode` policies)?
6. **Are we mistaking the comparator for physical truth?** `branch_mismatch` is
   a difference between two formulas. Does a nonzero value mean anything about
   BerkeleyGW's accuracy, or only that the near-pole branch is an approximation
   whose error is already understood and accepted by its authors?
7. **The large-sentinel limit, and what it should be compared against.** The
   limit is `(occ-1/2)*ieps`, finite and frequency-independent. We previously
   compared it to `sigma_cohsex` and got the opposite sign; that comparison was
   **withdrawn** (review finding 4) because `sigma_cohsex` accumulates its CH
   channel only when `sig%exact_ch == 0`, and every run here uses
   `exact_static_ch 1`. So: what *is* the right reference for that limit, and
   is a mode pushed to `1e12` eV meant to contribute a finite amount at all?
8. **What evidence would justify a next milestone?** An earlier version of
   this question assumed a self-consistent metallic witness "needs the complex
   flavor and HDF5". **That premise was wrong**, and the correction changes the
   question. Both were built and validated against upstream benchmarks in a few
   hours (C12's report); complex flavor is one preprocessor symbol and HDF5
   needed no download. The actual obstruction is C12: `epm2bgw` broadcasts a
   single `ifmax` to every k-point, so the EPM route cannot produce a partially
   occupied conduction band at all, for any material. A real witness therefore
   needs **a new mean-field calculation** (a DFT code and a pseudopotential),
   not a flavor or a library.

   So the question to answer is: given that the cheap route is closed by
   construction rather than by a missing asset, is a genuine metallic witness
   worth a DFT campaign -- or is the honest conclusion that the half-occupation
   case is a source-level curiosity with no physical consequence? A middle
   option exists and we are not sure it is worth it: the EPM `"El"`
   free-electron case gives a symmetry-protected band touching with `RHO` and
   `vxc.dat`, which is better than the current manually-shifted witness and
   worse than real graphene-at-K, but jellium is not a material and its Fermi
   level is a user choice.

---

## 6. Files a reviewer needs

Small and self-contained; no `/tmp` paths are required to read or re-check any
of it.

**Read this first: live status**
`.agent/handoffs/CODEX-T-003-T-004-ACCEPTANCE.md` -- the authoritative status
record, unsigned at the time of writing.
`.agent/STATE.md` -- current milestone state.

**Contract and proofs**
`Specification.md`; `GW/GPP/PoleCancellation.lean`;
`GW/GPP/FiniteSelfEnergy.lean`; `GW/GPP/BerkeleyGWMap.lean`; `GW/Audit.lean`.

**Source correspondence**
`docs/BERKELEYGW_4.0_GPP.md`; `docs/SOURCE_MAP.md`.

**This milestone**
`bgw/occupation_audit/REPORT.md`; `bgw/occupation_audit/check_occupation.py`;
`bgw/weighted_audit/weighted_mismatch.py`; this file;
`artifacts/t004/weighted_mismatch.json`.

**Provenance, current revisions**
`bgw/weighted_audit/PROVENANCE-R6.txt` is the **single current cross-audit
manifest**: it vouches for every file changed in the latest pass, whether it
belongs to the weighted audit or the occupation audit. Every other manifest is
historical and **deliberately stale**, including the superseded weighted
`PROVENANCE-R4.txt`, `PROVENANCE-R5.txt` and `bgw/occupation_audit/PROVENANCE-R4.txt`, which is the
prior *occupation* revision rather than a current one. Repaired digests are recorded as new
revisions instead of by rewriting history.
`tests/test_provenance_committed.py` enforces that every vouched
repo-relative file is committed, that the single current manifest matches, that
the historical ones really are stale, and that owner-controlled files are
tracked by git but not vouched for.

**Licensing**
`THIRD_PARTY_NOTICES.md` -- BerkeleyGW's license and copyright in full, plus an
inventory of every file here that is redistributed, diffed, quoted or derived
from it. This project's own code is BSD 3-Clause; see `LICENSE`, which
states the boundary between the two bodies of work.

**Supervisor review records**
`.agent/handoffs/CODEX-ACCEPTANCE.md` (T-001);
`.agent/handoffs/CODEX-T-002-ACCEPTANCE.md` (T-002 and R1);
`.agent/handoffs/CODEX-T-003-REVIEW.md`;
`.agent/handoffs/CODEX-T-003-R1-REVIEW.md`.

**Worker handoffs, retained as submitted including their superseded claims**
`T-001.md`, `T-002.md`, `T-002-R1.md`, `T-003.md`, `T-003-R1.md`,
`T-003-R2.md`, `T-004.md`, `T-004-R1.md`, `T-004-R2.md`, `T-004-R3.md`,
`T-004-R4.md`, `T-004-R5.md`, `T-006.md`, `T-006-CAPABILITY-SCOUT.md`.

A reviewer should read the acceptance and review records before the worker
handoffs: the handoffs contain claims that later review corrected, and they are
deliberately not rewritten.

**Data, if the reviewer wants to recompute**
`bgw/weighted_audit/fixtures/` (3702 records, 456 accumulator rows, both
tallies); `bgw/occupation_audit/fixtures/`; `bgw/export/`.

## 7. Known errors already found and corrected

Listed because the correction history is itself evidence about how much to
trust the rest. **Attribution is mixed**, and an earlier version of this
section wrongly claimed every correction was supervisor-found.

| # | Error | Corrected in | Found by |
| --- | --- | --- | --- |
| 1 | "<0.7 ulp" transcript agreement; actually 2.0839804 ulps | T-002 | supervisor |
| 2 | "96 records agree with S1"; actually 48 comparisons + 48 zero placeholders | T-002 | supervisor |
| 3 | Exact-pole wording overstated what was proved | T-002 | supervisor |
| 4 | "13 GPP assertions"; upstream has 24 under two tolerances | T-002 | supervisor |
| 5 | Checker accepted corrupted fields and a negative event count | T-003-R1 | supervisor |
| 6 | Invalid-mode default claimed to be `wtilde = 0`; it is the `1e12` sentinel | T-003-R1 | supervisor |
| 7 | Large-sentinel `ssx` claimed to tend to 0; it tends to `-ieps` | T-003-R2 | supervisor |
| 8 | `abs(wxt-w) <= 0.5` claimed necessary for near-pole; the `delwr` route also selects it | T-003-R2 | supervisor |
| 9 | Sentinel limit identified with the COHSEX value; the identification is false | T-003-R2 | **self**, reported in `T-003-R2.md` before the work began |
| 10 | Headline quoted the signed cross-group ratio (`0.673%`) as *the* effect size | T-004-R1 | supervisor |
| 11 | Weighted sums called dimensionless; they are intermediate Rydberg | T-004-R1 | supervisor |
| 12 | `1/ndeg` listed as universally missing; it applies to diagonal outputs only | T-004-R1 | supervisor |
| 13 | `signed_over_local` overwritten by the reconstruction residual before emission | T-004-R1 | supervisor |
| 14 | Accumulator identity exported but never checked against its records | T-004-R1 | supervisor |
| 15 | Provenance-vouched files absent from the commits | T-004-R1 | supervisor found 4; **self** found 5 more while repairing |
| 16 | The withdrawn COHSEX comparison still had a passing test asserting it | T-004-R2 | supervisor |
| 17 | Export count hard-coded rather than tied to the run's own tally | T-004-R2 | supervisor |
| 18 | `T-004-R1.md` falsely stated the COHSEX test had been removed | T-004-R2 | **self**, found while doing 16 |
| 19 | Module contract still said dimensionless / universally-missing `1/ndeg` after the JSON was fixed | T-004-R3 | supervisor |
| 20 | Broken clamp sentence; finite sentinel presented as equal to its limit | T-004-R3 | supervisor |
| 21 | 1.056% L1 overstated as preferable to physical cancellation | T-004-R3 | supervisor |
| 22 | Tally check overstated as proving whole-population completeness | T-004-R3 | supervisor |
| 23 | Correction count and blanket supervisor-found attribution both wrong | T-004-R3 | supervisor |
| 24 | Packet kept "not an energy" and a `(DRAFT)` title after the units were corrected to intermediate Rydberg | T-004-R4 | supervisor |
| 25 | Rejected "cancellation has no physical meaning" / "defensible aggregate" wording survived in a code comment and in `reference_warning` | T-004-R4 | supervisor |
| 26 | `completeness_evidence` asserted a tally-based check even under `--no-tally` | T-004-R4 | supervisor |
| 27 | Packet called occupation R4 current while the provenance test had demoted it | T-004-R4 | supervisor |
| 28 | Emitted `what` still pointed readers at the deleted fields `aggregate_note` and `cross_output_warning`; the saved JSON carried the same error | T-004-R5 | supervisor |
| 29 | Completeness source comment still said counting and emission happen "in one place", said "one execution of one binary", and named the removed `COMPLETENESS_EVIDENCE` | T-004-R5 | supervisor |
| 30 | Grouped `sum(K*L)` subtotal check overstated as validating each individual weight and local value | T-004-R5 | supervisor |
| 31 | Evidence index omitted the `T-004-R4.md` handoff; "previously published"/"published statements" claimed a publication that never happened | T-004-R5 | supervisor |
| 32 | Correction row 10 called the grouped contributions unrelated, the semantics rejected in T-004-R3 | T-004-R5 | supervisor |
| 33 | `test_acceptance_record_is_still_unsigned` would have failed the gate the moment Codex legitimately signed | T-004-R5 | supervisor |
| 34 | T-003 recorded that no real-flavor non-HDF5 band-touching asset existed; `testsuite/Graphene` ships `RHO`/`WFN_co`/`WFN_fi`/`vxc.dat`. It is still insufficient (its k-grids miss the Dirac point) but the stated reason was wrong | T-006 | **self** |
| 35 | The blocked items were recorded as needing the complex flavor and HDF5. Both were built in hours; the real obstruction is `epm2bgw.f90:456` | T-006 | **self** |

**This table is not a quality claim.** A long correction list is not evidence
of rigour; it is evidence that many written statements here were wrong on
first writing, and that independent review is doing most of the detection. Two
entries were self-reported plus two more in T-006, one was split, and the other thirty were found
by supervisor review. Note also that rows 24-27 are *residues of the repair
that produced rows 19-23*, and rows 28-33 are residues of the repair that
produced 24-27: a correction pass is itself a place where new wrong statements
enter, and this has now happened twice in a row. The right inference is to check the claims in
section 1 against the evidence, not to trust them because they were revised.
