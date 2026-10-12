# Roadmap: from one identity to a Lean-verifiable BerkeleyGW core — ARCHIVED (2026-10-01): superseded by docs/LIN_LINDSEY_ROADMAP.md, then docs/ENDPOINT.md; kept, not extended, outside the fast gate. See docs/CODEMAP.md.

> **Status 2026-09-22: superseded in practice, kept as a record.** Work has
> followed [`LIN_LINDSEY_ROADMAP.md`](LIN_LINDSEY_ROADMAP.md) since
> 2026-09-14. A four-agent audit on 2026-09-22 found none of the exit criteria
> below met:
> - **Stage 1** (mechanized transcription): not started.
> - **Stage 2** (whole-kernel coverage): not started.
> - **Stage 2b** (the outer `ryd/ndeg` and `neq` factors): not started.
> - **Stage 3** (a proved floating-point bound for the merged GPP form):
>   sidestepped rather than met. BGW-M2…M5 instead prove instance
>   certificates with a-priori rounding models. BGW-M5 bounds one production
>   mode of `sigma_gpp_cpu` against `GW.GPP.occupiedTerm`, but proves no
>   general binary64 bound.
> - **Stage 4** (physically honest witness): not met.
>
> The measured-situation table is also stale. The current Lean size and audit
> counts are in `artifacts/verification.json` after
> `bash scripts/verify.sh`. See `.agent/STATE.md` for the ledger.

Audience: a human or an agent picking this up cold. Every stage below has a
**falsifiable exit criterion** -- a command that passes or fails -- so progress
cannot be claimed by assertion. Stages are ordered by how much they change what
we can honestly say, not by how much work they look like.

## The measured situation

| Quantity | Value | How to re-measure |
| --- | --- | --- |
| BerkeleyGW 4.0 Fortran | ~199,556 lines | `find . -name '*.f90' -o -name '*.F90' \| xargs cat \| wc -l` |
| `Sigma/` directory | 15,832 lines | `cat Sigma/*.f90 \| wc -l` |
| `Sigma/mtxel_cor.f90` | 3,968 lines | `wc -l Sigma/mtxel_cor.f90` |
| **`sigma_gpp_cpu`, the kernel we target** | **247 lines** (`:1685-1931`) | `sed -n '1685,1931p' ... \| wc -l` |
| The kernel as a share of BGW | **0.12%** | 247 / 199556 |
| Our Lean | 1,481 lines, 72 named theorems | `wc -l GW/**/*.lean` |
| Theorems under exhaustive axiom audit | 181 | `grep 'AXIOM AUDIT PASSED' artifacts/axioms.log` |

## The one thing that matters most

Claim **C3** in `bgw/weighted_audit/REVIEW_PACKET.md` -- that the Fortran's
generic branch *is* the Lean identity's left side under the stated mapping --
has strength **"read"**. A human transcribed 247 lines of Fortran into Lean and
another human checked the transcription.

Everything else rests on that. The proofs are kernel-checked, the numbers agree
to 2.08 ulps, the branch predicate is closed-form -- and all of it would still
be true of a *faithful transcription of the wrong subroutine*. Nothing
mechanical connects `GW/GPP/BerkeleyGWMap.lean` to `mtxel_cor.f90`.

So Stage 1 is not "more theorems". It is closing that gap.

---

## Stage 1 — Mechanize the transcription  *(highest value, tractable)*

Generate the Lean definitions FROM the Fortran source instead of hand-writing
them, for the 247-line kernel only.

* **Build**: a parser for the subset of Fortran-90 expression syntax that
  appears in `sigma_gpp_cpu` (arithmetic, `if/else`, array reads, intrinsics).
  It emits the Lean definitions currently written by hand.
* **Exit criterion**: `python3 scripts/transcribe.py Sigma/mtxel_cor.f90
  --lines 1685-1931 > /tmp/gen.lean && diff /tmp/gen.lean GW/GPP/Generated.lean`
  exits 0, wired into the scientific gate. Editing one operator in the pinned
  Fortran must break the gate.
* **Buys**: C3 moves from **read** to **mechanically derived**. A source change
  we did not notice becomes impossible to miss.
* **Does not buy**: any guarantee the parser is correct. The parser becomes the
  new trusted base -- but it is ~1k lines of reviewable code instead of a human
  reading 247 lines of Fortran once.
* **Rough size**: weeks, one person. The grammar subset is small because the
  kernel is arithmetic-heavy and control-flow-light.

## Stage 2 — Cover the whole kernel, not one identity

Today we formalize the branch cancellation. The kernel also contains the
`sexcut` clamp, the occupation factor, the `invalid_gpp_mode` policies, the
frequency loop, and accumulation into `asxtemp`/`achtemp`.

* **Exit criterion**: a coverage test that walks every assignment statement in
  `:1685-1931` and fails if any has no corresponding Lean definition. Report
  the percentage; require 100% or an explicit, justified exclusion list.
* **Buys**: statements about *the kernel*, not about one identity inside it.
* **Does not buy**: anything about the ~3,700 other lines of `mtxel_cor.f90`,
  let alone `Sigma/`.
* **Rough size**: comparable to Stage 1, and much easier after it.

## Stage 3 — Prove a floating-point bound

The packet says plainly: *"No floating-point error bound is proved."* We
measure 2.0839804 ulps of agreement; we do not prove any bound.

* **Build**: interval or Flocq-style reasoning in Lean over the binary64
  evaluation of the merged form.
* **Exit criterion**: a kernel-checked theorem giving an explicit error bound,
  plus a test asserting the *measured* 2.0839804 ulps lies inside the *proved*
  bound. A proof that does not cover the observed data is wrong.
* **Buys**: the last "measured, not proved" item in the core claim set.
* **Rough size**: the hardest of 1-3. Floating-point proofs are slow going.

## Stage 4 — A physically honest witness

Blocked, and the blocker is now precisely known (see
`.agent/handoffs/T-006-CAPABILITY-SCOUT.md`): `MeanField/EPM/epm2bgw.f90:456`
assigns one scalar `ifmax` to every k-point, so `ncrit > 0` is unreachable via
EPM for any material. Complex flavor and HDF5 are NOT the blocker; both build in
hours.

* **Exit criterion**: a BerkeleyGW run reporting
  `Number of partially occ. conduction bands: > 0` **without** a manual Fermi
  shift, and with `RHO` charge matching the occupations.
* **Needs**: a DFT code and a pseudopotential -- a new mean-field calculation,
  not a flavor or a library.
* **Buys**: removes the standing "charge-inconsistent stress witness" caveat
  that qualifies every measured number in the packet.
* **Cheaper half-step**: the EPM `"El"` free-electron case gives a
  symmetry-protected band touching. Better than the current witness, worse than
  graphene-at-K. Jellium is not a material; say so if it is used.

## Stage 2b — The outer factors  *(added after review; see note below)*

**Why this was missing.** Stage 2 scoped "the kernel" as `mtxel_cor.f90:1685-1931`.
That boundary is arbitrary, and drawing it there hides the fact that the
factors which make our headline number uninterpretable live just outside it:

| Factor | Where | Size |
| --- | --- | --- |
| `fact = ryd/dble(ndeg(ii))` | `Sigma/shiftenergy.f90:113`, subspaces built at `:69` | **207 lines total** |
| `neq(irq)` q-star weights | `Sigma/sigma_main.f90:1586-1587`, `:1860-1861` | inside 2,597 lines |

The packet's "missing outer factors" table is, read literally, **an enumeration
of code we chose to strip rather than verify**. It is the reason `1.056%` must
be called a pre-outer-factor diagnostic and not a physical error. Verifying
`shiftenergy.f90` is therefore not busywork on the periphery: it is the step
that would let the headline number mean something.

* **Exit criterion**: Lean definitions for the degeneracy averaging and q-star
  weighting, mechanically derived as in Stage 1, plus a test that the weighted
  audit can reconstruct a diagonal accumulator *including* `ryd` and `1/ndeg`
  and match the program's own output.
* **Buys**: removes the largest qualifier on the only quantitative result the
  project has.
* **Rough size**: small -- 207 lines plus two call sites. Disproportionately
  cheap for what it unblocks.

## Stage 5 — Beyond one kernel  *(scope honesty)*

`freq_dep` full-frequency, COHSEX, the GPU path, and complex flavor are each a
SEPARATE kernel needing its own Stage 1-2.

**A correction to an earlier draft of this file.** It said the remaining ~180k
lines "are MPI, I/O and eigensolvers, not arithmetic identities". That was
wrong twice over, and the error mattered enough to record rather than silently
fix:

| Directory | Lines | What it actually is |
| --- | --- | --- |
| `Common` | 43,328 | genuinely plumbing: `bgw_mpi` 3,644, `evecs` 3,003, `hdf5_io_data` 2,252, `accel_fft`, `accel_memory`, `timing` |
| `BSE` | 27,380 | **other physics** (Bethe-Salpeter), not plumbing |
| `Epsilon` | 17,439 | **other physics** (dielectric matrix), not plumbing |
| `Sigma` | 15,832 | the module we target |

So ~44k lines are *different physics deliberately out of scope*, which is a
scope decision, not a statement that the code is trivial. And as Stage 2b
records, some physics arithmetic sits outside the kernel boundary entirely.

The defensible version of the original claim is narrower, and splits three
ways:

1. **Not BerkeleyGW's code.** BLAS, LAPACK, FFTW and HDF5 are called through.
   Verifying those is a separate decades-long field; no project here includes
   it.
2. **Plumbing.** MPI wrappers, I/O, timing, GPU memory. Lean is the wrong tool:
   these fail by deadlock, buffer size and file format. The caveat is that MPI
   reduction order changes floating-point summation order, which IS a
   correctness concern -- handled here by serial-versus-parallel comparison,
   not by proof.
3. **Physics arithmetic outside the chosen kernel.** Small, and previously
   excluded only because it fell outside lines 1685-1931. See Stage 2b.

**"Lean-verifiable BerkeleyGW" as a literal goal is not reachable** and should
not be claimed as the target. The reachable and still-valuable target is:

> a verified arithmetic core -- a handful of kernels whose Lean statements are
> mechanically derived from the pinned source and whose floating-point
> behaviour is bounded -- with conventional testing around everything else.

Stages 1-3 deliver exactly that for one kernel. Stage 5 is repetition.

---

## How to audit progress without trusting a report

1. `bash scripts/verify.sh` must exit 0. `--gate scientific` is the physics.
2. `grep 'AXIOM AUDIT PASSED' artifacts/axioms.log` -- theorem count, and only
   `propext`, `Classical.choice`, `Quot.sound` are permitted.
3. `grep -rn 'sorry\|admit\|native_decide' GW/` must find nothing.
4. Check the **strength** column in the packet's claim table. Words mean things:
   `kernel-checked` > `measured` > `read` > `not determined`. A stage that does
   not upgrade some claim's strength has not advanced the science.
5. `python3 scripts/make_manifest.py <manifest>` must report `0 refreshed`.
   Anything else means the evidence does not match the files.

The correction table in the packet (35 rows, mixed attribution) is the honest
record of how often claims here have been wrong on first writing. Read it
before trusting anything above.
