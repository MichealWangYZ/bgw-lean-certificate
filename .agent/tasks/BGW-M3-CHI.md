# BGW-M3-CHI — one chi entry's transition-sum provenance, then STOP

**Self-written scope note, not a reviewer brief.** The owner authorized this
stage directly (2026-09-19) without a committed brief, after I said I could not
manufacture one for myself. This file exists so my boundaries are reviewable
against something written BEFORE the work, not inferred from the result
afterwards. A reviewer should treat every boundary here as my proposal.

Base: `00c9db8` on `bgw-m2/rounding-aware` (PR #17, M2-R3). Branched from the
PR rather than `main` because `main` (`bbf6a6c`) has neither M1 nor M2, and
this stage reuses `bgw/m2_screening/extract.py` primitives and the same run.

## 1. Question

For ONE nontrivial entry of the chi matrix already certified downstream in M2,
can the exported value be reconstructed from its physical operands -- the
unweighted plane-wave matrix elements, the occupations, the energy
denominators and the declared prefactors -- with the reconstruction certified
in Lean against the actual exported bytes?

## 2. Why this and not another screening instance

M2 took `chi` as an INPUT. Everything upstream of the export point is
provenance there, not verified physics. This stage moves the boundary one step
up. It does NOT reach wavefunctions, the FFT, or the plane-wave basis
construction; those remain inputs here exactly as `chi` was in M2.

## 3. The gap this must not reproduce

BerkeleyGW does not accumulate `chi` from `M` and a denominator separately.
Traced in the pinned source:

    Epsilon/mtxel.f90:926    "In the static case, we lump sqrt(eden) into the
                              matrix elements gme."
    Epsilon/mtxel.f90:858    pol%gme *= sqrt(-1D0*eden)
    Epsilon/mtxel.f90:918    eden = occ_diff / (eval - econd), else 0
    Epsilon/mtxelmultiply.f90:64,95   negfact = -fact; chilocal = negfact * gmetempr . gmetempc^T

so the weighting is already inside `gme` before the GEMM. Exporting `gme` and
calling the product a derivation from physical operands would hide exactly the
step this stage exists to check. **The export must therefore be taken BEFORE
the `sqrt(-eden)` multiply**, together with `eden`, `occ_v`, `occ_c`, `eval`,
`econd`, `kfact`, `fact` and the phases, each separately.

## 4. Input boundary (declare before comparing)

Exported, per transition, for one q and the retained basis:
unweighted `tmparray`/`gme` before weighting; `eval`, `econd`, `occ_v`,
`occ_c`; `eden` as the code computed it; `kfact`; `fact`; `pht` phases and
`indt` index map; the k-point inventory and `nst`; spin. Plus the final
exported `chi` entry, which is the target, never an input to the reference.

Reference: exact rational reconstruction from the unweighted operands. The
comparison target is one nontrivial OFF-DIAGONAL entry plus one diagonal
entry, at the same q index 2 as M2.

## 5. Required endpoints

1. A complete transition inventory: every (k, v, c, spin) the code summed,
   with the skipped ones and the reason they were skipped. A partial sum that
   happens to match is not a reconstruction.
2. Exact rational reconstruction of the two chosen entries, with a rounding
   certificate in the M2 style: a budget fixed from operand counts and unit
   roundoff BEFORE the comparison, never from the observed difference.
3. A Lean module certifying the finite sum for the encoded data, included in
   the build and the exhaustive audit. No `sorry`, no new axioms, no
   `native_decide`.
4. Pristine/instrumented A/B neutrality on the whole `epsmat`, as in M2.
5. Mutations: a dropped transition, a wrong occupation difference, a swapped
   `eval`/`econd`, and a phase dropped from one side only. The unmodified
   control must pass the same rule.

## 6. Explicit non-goals

Wavefunction accuracy, the FFT, convergence, the frequency-dependent path
(`freq_dep != 0`), spinors, the head/wing q->0 limits, self-consistency, GPP,
and any claim about BerkeleyGW as a program. Degenerate and partially occupied
cases are in scope only insofar as this run exercises them; if it does not,
that is a stated limitation, not a proved absence.

## 7. Budget and exits

**6 cumulative active hours.** Terminal statuses as in BGW-M2:
CHECKPOINT_READY, ROUTE_REFUTED, BLOCKED, BUDGET_STOP. Write
`.agent/handoffs/BGW-M3-CHI.md` at any terminal status and stop. Commit and
push are covered by standing authorization; merging, starting another
milestone and any upstream contact are not.
