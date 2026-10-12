# G2 roots handoff: A1 principal root brackets and the full-QP O1, kernel-checked

Status: ready for review. This is **not accepted**. Branch `lean/g2-roots`, forked from
`bgw-e/endpoint` (27a82d3). Nothing is merged.

**Outcome: intermediate exit (explicitly allowed by the brief).** Kernel-checked:

- the two principal isolating brackets, X0 (X, 4.19439 eV) and L0 (L, 4.12540 eV);
- the principal-root O1 in [68.9856742, 68.9856744] meV, and O1 > 0.

Not done:

- the interval-exclusion cover of the rest of [-1e4, 1e4] eV (items 2a and 2b of the brief);
- the two low-weight brackets X1 and L1.

So the Lean result is **existence and uniqueness of the root in each principal bracket**.
It is not "exactly two roots in the window". The window statement remains Python-only
(qp_unique.py). The cost measurement is in the section below.

## Statements (namespace `GW.Endpoint.Kernel.R`, target GWKernelData)

`E` is the energy in eV. `den = 10^8 * 2^92`, and `Ca.. / den` are exact rationals. The
statements refer to stage 3's `gl`, `stX`, `stL` and `Etrue`, the TRUE eps⁻¹.

```
rootX0 (vb oq) (hvb : VbHyp vbT eg.SV vb) (hoq : VbHyp oqT eg.SV oq) :
  SrcDefOn gl Etrue vb oq stX (CaX0/den) (CbX0/den) ∧
  (∀ E ∈ [CaX0/den, CbX0/den], cXv*DX00v - 1 ≤ dfQP … E ∧ dfQP … E ≤ cXv*DX01v - 1) ∧
  ∀ cv : Bool,
    IsolatingBracket (fQP gl Etrue vb oq stX cv) (dfQP gl Etrue vb oq stX) (CcX0/den) (CdX0/den) ∧
    (∃! E, E ∈ [CaX0/den, CbX0/den] ∧ fQP … cv E = 0) ∧
    ∀ E ∈ [CaX0/den, CbX0/den], fQP … cv E = 0 → E ∈ [CcX0/den, CdX0/den]
rootL0 : the same for L
o1_fullQP (vb oq hvb hoq) (cv) (EX EL) (hX : EX ∈ [CaX0/den, CbX0/den] ∧ fQP … stX cv EX = 0)
    (hL : EL ∈ [CaL0/den, CbL0/den] ∧ fQP … stL cv EL = 0) :
  EX - EL ∈ [689856742/10^10, 689856744/10^10] ∧ 0 < EX - EL
roots_exist : each bracket contains exactly one zero, for either cv
o1_fullQP_irr, roots_exist_irr : the same with glI, stXI, stLI, EIrr
    (inputs computed from the irreducible WFN data by the G2 unfolding)
```

Numbers (exporter mirror, exact):

- X0: [Ea, Eb] = [4.194290070040299, 4.194490070040299] eV, i.e. qp_unique's bracket moved
  outward by < 1e-17 eV.
  - Sign points [Ec, Ed] = [4.19439006974996, 4.194390069829961].
  - f(Ec) ∈ [3.65e-11, 5.86e-11] and f(Ed) ∈ [-5.68e-11, -3.47e-11].
  - f' ∈ [-1.16550916, -1.16549556] on the whole bracket, so Z ∈ [0.857994, 0.858004].
- L0: [4.1253043955518685, 4.125504395551868] eV and [Ec, Ed] = [4.125404395440342, 4.125404395520342].
  - f' ∈ [-1.17003607, -1.17001236], so Z ∈ [0.854675, 0.854692].
- The derived enclosure is O1 ∈ [68.98567423, 68.98567439] meV. It lies inside qp_cert's
  [68.9856742, 68.9856744] meV, which is the stated bound.

## Definitions (GW target, audited in GW/Audit.lean END section)

- `RootSpec.lean`:
  - `wxE t n1 E = E - e_n1(k-q)`, with the |wx| < TOL_Zero → TOL_Zero replacement. It is
    common to the multiplet's bands, as in qp_cert.py.
  - `PqE`: stage 3's `Pq` with `wxE`.
  - `SigE a E`: stage 3's Xq, CSq and ACq plus Σ_n1 PqE.
  - `fQP cv E = emf + avg_a SigE a E · RYD - E`.
  - The formal derivatives `dschM`, `dcertSsx`, `dssxM`, `dwx`, `dPqE` and
    `dfQP = avg(Σ dPqE)·RYD - 1`. They follow the kernel_d formulas.
  - `SrcDefOn`: no point of the interval has wx = wtilde, or wx = -wtilde (occupied), for
    any kept mode.
  - `FixedOn F F' a b`: continuous on [a,b] with HasDerivAt F' on (a,b). It is closed under
    sums, scalar multiples, translation and congruence. `fixed_div_sub`, `fixed_div_sq` and
    `fixed_div_add` cover the branch functions.
- **Convention freedom.** At wx = wtilde the source divides 0/0; IEEE gives 0, while the
  continuous extension gives -I/4. `ssxMc cv` takes either value, and every theorem holds
  for both `cv`. At wx = -wtilde the value is the clamp value 0. The certified brackets
  contain neither point: `SrcDefOn` is a conclusion, derived from dOK's `x ≠ ±w` on the
  whole interval. So nothing depends on the convention. Endpoint values use `nOK`
  (the `ssxM` convention). They are equal to `ssxMc cv` because the sign points lie in
  the bracket (`tPc_eq`).
- `RootCheck.lean` (ℕ-only, as stage 3):
  - `mkEnP` gives point energies.
  - `mkEI` gives the wx interval. It must have one sign and |wx| ≥ TOL_Zero throughout.
  - `subI`, `addI`, `sq2I` are interval differences.
  - `dschK`, `dssxK` (derivative kernels) decide **every** branch and clamp condition on
    the whole interval. An undecided condition fails the check. So does x = ±w being
    possible.
  - `dOK` runs over all entries, zero weights included.
- Soundness chain:
  - `dschK_spec`, `dssxK_spec` (RootKernel): FixedOn, x ≠ ±w, derivative enclosure.
  - `dcontrib_spec` → `dOK_sound` (RootHot).
  - `mkEnP_spec`, `mkEI_spec`, `quad_scaled`, `P_scaled`, then `rq_n`: one (state, q) from
    stage 3's `StqOK` + dOK + nOK at Ec and Ed (RootStq).
  - `root_bracket` (RootAsm): sums, strict antitonicity via QPUnique's
    `strictAntiOn_Icc_of_hasDerivAt_neg`, IVT through `IsolatingBracket.existsUnique`,
    uniqueness on [Ea, Eb].
- Data (generated, `kernel_export.py --roots`):
  - `RH{X0,L0}`: brackets and claims.
  - `RD*` / `RP*`: 864 modules, one `decide +kernel` each (dOK or nOK per (q, band, n1)),
    in one serial import chain.
  - `R{X0,L0}`: RqOK per q, totals `LtZ` / `DtZ` by kernel, numeric side conditions by
    norm_num.
  - `RO1`, `RIrr`, `RTamper`.

## Trust (unchanged from stage 3 + unfolding)

- The Coulomb boxes are hypotheses (VbHyp).
- The exporter's literal extraction.
- The modelling claim that SigmaSpec, and now `fQP`, is BerkeleyGW's GPP QP equation.
- qp_unique's window/uniqueness claim is **not** kernel-checked: the cover was not done.

## Measurements

- Per check, q=3 (92 G), warm:
  - one dOK: 16 s, 4.4 GB;
  - one nOK (two point energies): 27 s, 5.9 GB.
  - Six pairs in one module peaked at 9.3 GB, which is over the 7 GB limit. Hence one
    check per module.
- Full R* chain (864 checks + RH/R/RO1), one serial `nice lake build GW.Endpoint.Kernel.Data.RO1`:
  **3 h 10 min wall, 11463 CPU-s, peak RSS 5.95 GB** (the other worktree's Lean job ran
  concurrently part of the time). RTamper + RIrr: 36 s, 4.8 GB.
- `lake build GWKernelData`: PASS. `lake build GW`: PASS; `lake env lean GW/Audit.lean`: the 15
  new QP entries depend on `[propext, Classical.choice, Quot.sound]` or a subset.
- `lake env lean GW/Endpoint/Kernel/AuditRoots.lean`: all 19 entries use `[propext, Classical.choice,
  Quot.sound]`.
- `lake build Main && lake env lean scripts/CheckAxioms.lean`: **AXIOM AUDIT PASSED: 9778 theorems**
  (7874 before), 878 new modules covered (35:55 wall, 3.2 GB).
- The exporter regenerates all 871 committed R* files byte-identically (deterministic RNG).
- Extrapolation for the cover. One box needs a full Σ interval evaluation: all 288 (X) or
  144 (L) (q, band, n1) checks. Each costs about one nOK, ~20–27 s.
  - That is ≈ 1.6 CPU-h (X) or 0.8 CPU-h (L) per box.
  - ~1350 boxes per state gives ≈ 3000 CPU-hours. This is far beyond the 6 CPU-h budget,
    so the brief's intermediate exit was taken.
  - Cheaper cover designs (not attempted) are listed in "Next action".

## Negative controls (`Data/RTamper.lean`, each `= false` by the kernel)

- `tamper_wide`: the X0 bracket widened by 1 meV to the left. At q-point 1, inner band 2,
  a sexcut clamp switches inside the interval, so dOK rejects it. This is the reason
  qp_cert's 1e-3 bracket was not continuous.
- `tamper_der`: the derivative claim's upper end moved below its lower end.
- `tamper_pt`: the Ec point claim collapsed to its lower end.
- `tamper_tz`: an energy interval around e_n1(k-q), where |wx| < TOL_Zero is possible.
  mkEI rejects it.

## Commands

```
cd .claude/worktrees/lean-roots && source scripts/env.sh
S=<scratch>
python3 bgw/endpoint/kernel_export.py --sigma-pkl $S/s3/SIGCAP.pkl --roots X0,L0 --lean   # ~80 s,
    # prints brackets, f(Ec), f(Ed), f', Z, O1 and asserts the certificate; deterministic
nice lake build GWKernelData        # R* chain ~3 h 10 min, one serial chain
lake env lean GW/Endpoint/Kernel/AuditRoots.lean
nice lake build GW && lake env lean GW/Audit.lean
lake build Main && lake env lean scripts/CheckAxioms.lean
```

## Failed attempts / pitfalls

- `dssxK_spec` hit the default heartbeat limit and needs `maxHeartbeats 2000000`. The
  assembly theorems need 1000000.
- In `root_bracket`, `set X := Nq gl * vol gl` hid terms from linarith, because hypotheses
  from `rq_n` keep the unfolded form. The fix was to drop `set`.
- A single `rw [sum_comm]` rewrote only the first of two sums, which timed out in
  unification. It is now done separately per goal.
- RIrr: rewriting `stX_eq`/`stL_eq` in both hypotheses at once failed (each hypothesis mentions
  only one state); fixed by separate rewrites.
- The first generator put 6 (dOK, nOK) pairs per module: 3:52 wall and 9.3 GB peak.
- The O1 decimal was first written as /10^13. The mirror caught it (it printed `False`).
- The assembly was pre-checked with sorry stubs of the 864 checks. They were temporary,
  deleted and never committed. `grep sorry` over the new files finds nothing.

## Next action

Review:

- `fQP` against qp_cert.py (multiplet-common wx; Emf; RYD);
- the `cv` convention statement;
- the use of stage 3's hints (sh, xs) in the new checks.

Remaining parts of A1:

1. X1, L1 brackets: the same generator with `--roots X1,L1`, ≈ the same cost as X0 + L0.
2. The cover. It needs a new design, because per-box full Σ evaluation is too costly
   (≈ 3000 CPU-h). Options:
   - a coarse a-priori bound: |Σ(E) - Σ_static| is bounded by per-(q, n1) mode sums of
     |weights|·max|kernel| (sch ≤ 2 wtilde |I|, ssx bounded by its clamps). This excludes
     |E| large with a few checks;
   - aggregation of the weights over bands (Σ_a W^a_i W^a_j) and over entries sharing one
     mode;
   - hull soundness via a select lemma (the `CertInterval.select_mem` analogue) for the
     undecided branches.
