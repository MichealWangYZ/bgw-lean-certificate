# Source-level GPP branch-boundary and occupation sweep (T-005)

## What this is

`branch_boundary.f90` is a standalone real-flavor Fortran driver that
re-executes the arithmetic statements of the inner `ig` loop of
`sigma_gpp_cpu` from BerkeleyGW 4.0, `Sigma/mtxel_cor.f90`
(SHA-256 `8914dc00ac8d80d99e78f9b76a6d398491240bf147fa8714a65fed4ce5daf1dd`,
3968 lines), at inputs we choose. Every copied region is marked `!>BGW` with
its source lines:

| region | source |
| --- | --- |
| GPP setup: `TOL_Small` cycle and the `invalid_gpp_mode` policy | `Sigma/mtxel_cor.f90:772-795` |
| `limitone`, `limittwo` | `Sigma/mtxel_cor.f90:1698-1699` |
| `wx` clamp at `TOL_Zero` | `Sigma/mtxel_cor.f90:1746` |
| `delw`/`delwr`/`wdiffr`, predicate, both branches, `ssxcutoff` | `Sigma/mtxel_cor.f90:1810-1848` |
| accumulation weights and `-occ*SX + CH` | `Sigma/mtxel_cor.f90:1854-1855, 1906-1916` |
| `gpp_broadening = 0.5`, `gpp_sexcutoff = 4.0` | `Sigma/inread.f90:151-152` |
| `TOL_Small`, `TOL_Zero`, `RYD` | `Common/nrtype.f90:155, 161-162` |

Declared kinds are reproduced, not repaired: `Omega2`, `wtilde2`, `ssx`, `sch`
are `SCALAR` = `real(DP)` in the real flavor while `wtilde`, `delw`, `wdiff`,
`cden` are `complex(DPC)`, so several assignments are complex-to-real and keep
the real part. The real-flavor macro `MYCONJG(x)` expands to `(x)`, not to
`conjg(x)` (`Common/f_defs.h:48`), so the near-pole branch squares `cden`
rather than taking its modulus; the driver spells it the same way. Under the
restriction to positive real modes `cden` is real, so the two spellings happen
to agree numerically here.

## What this is not

This is **not a BerkeleyGW run**. The G/G' loops, matrix elements, Coulomb
factor, MPI and OpenMP are all removed, so the reported values are per-`(ig,igp)`
local values of `-occ*ssx + 0.5*sch` with the common factor
`aqsntemp*MYCONJG(aqsmtemp)*vcoul(igp)` divided out. They are dimensionless;
the energy dimension of the self-energy is carried by `vcoul`, which is not
part of this kernel. No BerkeleyGW tree is modified, rebuilt or executed.

Nothing here establishes a production-material impact, a self-energy error, or
an error in any published BerkeleyGW result. The half-occupation discrepancy
reported below is a property of the two formulas the source selects between; it
becomes a physical statement only for a run that actually reaches partial
occupation in a physically self-consistent state, which this project has not
demonstrated. The same applies to the clamp-induced jump at full occupation
reported in finding 5: it is an observation about this driver's local
accumulator at chosen inputs, and says nothing about whether those inputs
occur, or how they are weighted, in any real calculation.

## Running it

```bash
python3 bgw/branch_boundary/run_sweep.py            # rebuild artifacts/t005/
python3 bgw/branch_boundary/run_sweep.py --check    # rebuild, compare, write nothing
python3 -m unittest tests.test_branch_boundary -v
```

`run_sweep.py` takes the compiler and options from `bgw/export/arch.mk`
(`F90free`, `FOPTS`), builds under `/tmp`, and writes only
`artifacts/t005/raw_sweep.txt` and `artifacts/t005/summary.json`.
`analyze.py` is pure parsing and analysis and never compiles or runs anything.

## The experiment

The complete predicate at line 1828 is a conjunction:

```
wdiffr > limittwo        with limittwo = gamma^2 = 0.25
delwr  < limitone        with limitone = 1/(4*TOL_Small) = 250000
```

Writing `d = wxt - wtilde`, in exact arithmetic these are `|d| > gamma` and
`|d| > 2*sqrt(TOL_Small)*|wtilde|`. With the defaults the second is redundant
whenever `|wtilde| <= gamma/(2*sqrt(TOL_Small)) = 250`. The sweep therefore
uses four cases:

| case | `I_eps` | `wtilde` | deciding conjunct | surface | `wxt` sign | `sexcut` clamp |
| --- | --- | --- | --- | --- | --- | --- |
| `A+` | 1 | 1 | `wdiffr` | `d = +0.5` | `> 0` | cannot fire |
| `A-` | 1 | 1 | `wdiffr` | `d = -0.5` | `> 0` | cannot fire |
| `B+` | 1 | 300 | `delwr` | `d = +0.6` | `> 0` | cannot fire |
| `C-` | 1 | 0.26 | `wdiffr` | `d = -0.5` | `< 0` | **active** |

`wtilde = 300` is a numerical construction chosen only to separate the two
surfaces; it is not a claim about physical mode energies.

The `sexcut` clamp at line 1848 needs `wxt < 0` **and**
`|ssx| > sig%sexcut*|I_eps|`, so no row of `A+`, `A-` or `B+` can reach it.
`C-` is placed on the other side: `wtilde = 0.26` is a source-valid positive
real mode (`wtilde2 = 0.0676`, far above `TOL_Small`, so line 774 does not
cycle it) and the negative `|d| = gamma` surface then sits at
`wxt ~ -0.24`, where `|wxt| ~ wtilde` makes both `ssx` candidates
`~ 6.5 * |I_eps|`, above the cutoff of `4 * |I_eps|`. The clamp fires on all
six representable neighbours of the surface; it switches off again at the
`+-1e-1` offsets, where `|ssx|` falls below the cutoff. Clamped and unclamped
rows are reported and tested separately and are never mixed.

Every row records `ssx` and the accumulated value both **before** and
**after** the clamp, for the selected branch and for both forced candidates,
together with the clamp condition itself (`cut_sel`, `cut_gen`, `cut_np`) as
evaluated by the source expression. Pre-clamp behaviour is therefore never
inferred from a post-clamp zero.

Each surface is located by bisecting on the binary64 bit patterns of `wxt`
until the last predicate-false and first predicate-true values are adjacent
representable numbers. That pair is the exact machine boundary; no decimal
approximation is used anywhere. The sweep then records the two neighbours on
each side plus offsets of 1e-12 through 1e-1 on both sides, at `occ = 1` and
`occ = 0.5`, storing inputs, `wdiffr`, `delwr`, both conjuncts, the selected
branch, `ssx` before and after the `sexcut` clamp, `sch`, the local value, and
the two counterfactual candidates (generic and near-pole evaluated
unconditionally at the same inputs, kept separate from the selected result).

Sign convention throughout: the branch discrepancy is

```
Delta(occ) = generic candidate - near-pole candidate
```

which is the orientation of `GW.GPP.BGW4.branch_mismatch`. That theorem is used
only as a comparison target and is not changed by this task.

## Findings

1. **The machine surface is not always the decimal one.** For `A+` the last
   predicate-false point is exactly `wxt = 1.5`, where `d*d = 0.25` is exactly
   `limittwo` and the strict `>` fails. For `A-` the subtraction
   `wdiff = wxt - wtilde` is outside the Sterbenz range, so the last
   predicate-false point is one ULP *below* `wxt = 0.5` and still reports
   `d = -0.5` exactly. The surface is displaced by the rounding of the
   subtraction, not by the comparison.

2. **At full occupation the crossing is continuous at the local floating
   scale, for the unclamped cases.** The one-ULP step across the surface
   changes the local value by no
   more than ordinary adjacent-point variation within a single branch:
   5.6e-17 versus 2.2e-16 for `A+` and `A-`, and 9.8e-13 versus 6.6e-12 for
   `B+`. The `B+` scale is five orders of magnitude coarser because
   `-ssx + 0.5*sch` there subtracts two numbers of size ~250 to produce ~0.25.
   This is a floating-point observation about this driver, not a proof and not
   an accuracy claim about BerkeleyGW.

3. **At half occupation the same one-ULP step is a finite discontinuity**
   (again for the unclamped cases).
   `A+` jumps by +0.500, `A-` by -0.500, and `B+` by +125.0, in each case
   matching the closed form of `branch_mismatch` at those inputs to within
   1e-11 relative. The sign follows the side of the mode: the
   `Omega2/((x-wt)(x+wt))` term changes sign across `x = wt` while
   `Omega2/(2*wt*(x+wt))` does not. This is a discrepancy between two formulas
   in a dimensionless local accumulator, not a material self-energy error.

4. **The discrepancy is linear in `1 - occ`.** At four fixed nonsingular points
   away from overflow and from the `sexcut` clamp, `Delta(occ)/(1-occ)` is
   constant across `occ = 0.75, 0.5, 0.25` to at most 1.3e-15 relative (under
   8 ULP), and `Delta(1)` is at the rounding floor (<= 1.7e-16 absolute)
   rather than exactly zero. The measured `Delta(occ)` agrees with the
   `branch_mismatch` closed form to better than 1e-14 relative.

5. **With the clamp active, full occupation is *not* continuous.** On the
   `C-` surface the clamp fires on both sides. It zeroes `ssx` on both, but
   the generic branch keeps `sch = delw*I_eps = -0.520`, while the near-pole
   branch has `sch = 0` by construction. The local value therefore steps from
   `0` to `-0.260` between two adjacent representable `wxt`, at `occ = 1`,
   where the unclamped algebra is continuous to `2.3e-14` on a scale of
   `6.500` (3.6e-15 relative). The clamp, not the branch algebra, creates this
   jump. Nothing was tuned to recover continuity.

   Because `ssx` is zero on both sides afterwards, the occupation factor
   multiplies nothing and the post-clamp jump is `-0.260` at `occ = 0.5` as
   well — identical to `occ = 1`, and **not** proportional to `1 - occ`. The
   `branch_mismatch` closed form predicts `-0.130` at `occ = 0.5`; it matches
   the *pre*-clamp discrepancy there to `1.2e-14`, and it is not a prediction
   for the post-clamp result. `closed_form_applies` in the summary records
   exactly which crossings it may be compared against.

6. **The third branch: two separate statements.**

   *No surviving positive-real mode can reach it.* Branch 3 needs
   `wdiffr <= limittwo` and `delwr <= TOL_Zero`, i.e. `|wdiff| <= gamma = 0.5`
   and `wtilde <= sqrt(TOL_Zero)*|wdiff| <= 5e-7`, simultaneously. A mode
   survives `Sigma/mtxel_cor.f90:774` only if `|wtilde2| >= TOL_Small`, and if
   `wtilde2 > 0` then line 793 gives `wtilde = sqrt(wtilde2) >= 1e-3`. The two
   bounds are a factor 2000 apart, so the conjunction is unsatisfiable. The
   `minmode` row is the extremal witness and lands in branch 2 with
   `delwr = 4e-6`, six orders above `TOL_Zero`.

   *A zero mode is nonetheless reachable, by policy.* Line 774 filters on
   `abs(wtilde2)`, so a sufficiently **negative** `wtilde2` passes it. Lines
   779-782 then hit `sig%invalid_gpp_mode = 0`, "skip invalid GPP mode", which
   assigns `wtilde = (0d0,0d0)`. That zero mode reaches branch 3 whenever
   `|wxt| <= gamma`, and contributes exactly zero — which is what skipping the
   mode means, not evidence that the state cannot occur. The other policies at
   the same `wtilde2 = -1` give nonzero modes (`1` a purely imaginary
   `wtilde = i`, even in the real flavor; `2` gives `2 Ry`; `3` and the default
   give `1/TOL_Zero`) and all select branch 1. The `BRANCH3` rows walk all of
   them, plus both signs of a cycled sub-`TOL_Small` mode.

   The original T-005 text said only that branch 3 "needs a zero mode that line
   774 cycles away". That was wrong about the invalid-mode path and is
   superseded here.

7. **Secondary invariances hold.** A common energy-zero shift
   `E -> E + C`, `eps -> eps + C` leaves the result bit-identical for
   `C` up to 1e16 and fails at 1e17, where `(E+C) - (eps+C)` rounds to zero and
   `wxt` hits the `TOL_Zero` clamp; that is a limit of constructing the input,
   not an asymmetry of the kernel. Scaling `I_eps` by 2, 1/4, -1 and -3.5
   scales both candidates and their discrepancy by the same factor to within
   3.2e-16 relative.

## Files

- `branch_boundary.f90` — the driver, with `!>BGW` markers on every copied statement.
- `run_sweep.py` — compile (pinned `arch.mk` compiler, build under `/tmp`), run, save.
- `analyze.py` — parse the table and compute the summary; no subprocesses.
- `../../artifacts/t005/raw_sweep.txt` — deterministic raw table, 17 significant digits.
- `../../artifacts/t005/summary.json` — summary plus compiler, command, digests, parameters.
- `../../tests/test_branch_boundary.py` — provenance, boundary, occupation and reproducibility tests.
