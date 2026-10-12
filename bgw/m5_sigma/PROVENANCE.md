# BGW-M5 provenance: one production self-energy mode — ARCHIVED (2026-10-01): BGW-M4/M5 lineage, superseded by GW.Endpoint.Kernel.SigmaSpec and Data.S3*; kept, not extended, outside the fast gate. See docs/CODEMAP.md.

Supports `GW/BGW/M5Sigma.lean` and `tests/test_bgw_m5.py`. The kernel-checked
claims are the Lean theorems; everything below is source reading and
recorded execution. The task and its frozen selection rule are in
`.agent/tasks/BGW-M5.md`, committed before this run.

## Run

Same pinned archive, toolchain, inputs and `epsmat` as BGW-M4-R1. A fresh tree
was patched by `instrument_m5.py`, which applies the M4-R1 exports and adds,
in `sigma_gpp_cpu` (`Sigma/mtxel_cor.f90`, real flavor, occupied bands), one
export per (n1, iw) for the consumer (ig, igp) given by `M5_IG`/`M5_IGP`
(here 2, 1). The only non-write line is `m5_ssx0 = ssx`, which saves the
pre-`sexcut` value in a new variable. Results, all in
`evidence/ab-neutrality.log`:
- The six Sigma outputs are byte-identical to the pristine run.
- The M4-R1 records of this run are byte-identical to the committed M4-R1
  dump.
- The export contains 1824 kernel records.

## What the kernel does with the mode (`mtxel_cor.f90:1685-1931`)

For an occupied band, frequency `wx = e_lk + dw*(iw-2) - e_n1kq`, and a
setup pole `wtilde`:

```
wtilde2 = wtilde**2;  Omega2 = wtilde2 * I_eps
generic branch (wdiffr > gamma^2 and delwr < 1/(4 TOL_Small)):
  sch = wtilde * I_eps / (wx - wtilde)          (as wtilde*conj(c)*(1/|c|^2) * I_eps)
  ssx = Omega2 / (wx^2 - wtilde2)                (as Omega2*conj(c)*(1/|c|^2))
sexcut: ssx = 0 if |ssx| > sexcut*|I_eps| and wx < 0
asx -= ssx*occ*vcoul(igp)*aqsn(ig)*aqsm(igp);  ach += 0.5*sch*vcoul(igp)*aqsn*aqsm
```

So the mode's weighted contribution is `v*aqsn*aqsm*(-occ*ssx + sch/2)`. The
exact identity `-ssx* + sch*/2 = occupiedTerm(O, x, w)` (specification S1,
`GW.GPP.occupiedTerm`, coefficient `A = O = w^2 I`) is what the Lean module
proves.

## Checks in `sigma_mode.py`

| Check | Scope |
| --- | --- |
| The non-kernel records equal the committed M4-R1 dump, and `bridge.run` reproduces the M4 target | whole dump |
| The kernel's `wtilde`/`I_eps` equal the setup's `wtilde`/`I_epsggp` bits; `imag(wtilde) = 0` | the target's Sigma call |
| `wtilde2`, `Omega2`, `wdiff`, `delw`, `sch`, pre-clamp `ssx`, and `wx` (at iw = 2, including the `TOL_Zero` replacement) equal their binary64 re-evaluation | all 1824 records |
| Frozen rule: first occupied n1 at iw = 2; generic branch; not clamped, otherwise BLOCKED | selected: n1 = 1 |

## The pole

`sqrt_checks` proves `(w-δ)^2 ≤ wtilde2 ≤ (w+δ)^2` exactly, with `δ = 2u·w`,
so `|w − sqrt(wtilde2)| ≤ δ`. This checks the rounded square root the program
actually returned, not an IEEE model. `sqrt_bound` then carries M4's
`|wtilde2 − PStar| ≤ BP` through `|√a − √b| ≤ |a−b|/√a`, which gives
`|wtilde − √PStar| ≤ δ + BP/(w−δ)`.

## Budgets

The model was fixed in `sigma_mode.py` before any M5 residual was computed,
and a test pins it. The local rounding for `sch` and `ssx` is
`|value|·(γ₈ + γ_k·(sum of magnitudes)/|denominator|)`, where k = 2 for
`x − w` and k = 4 for `x² − w²` (the cancellation terms). Propagation from
production operands to exact references is proved by `quot_hat`, using M4's
`ieps_bound` and `wtilde2_bound`. `BPup` and `BIup` are short rational upper
bounds on M4's Lean budgets, proved by `BP_le` and `BI_le`.

| | measured | budget |
| --- | --- | --- |
| `|wtilde − √PStar|` | 7.8e-16 | 1.0e-10 (dominated by M4's `BP/w`) |
| `|sch − sch*|` | 2.7e-18 | 6.6e-13 |
| `|ssx − ssx*|` | 1.1e-17 | 7.3e-13 |
| `|(−ssx + sch/2) − occupiedTerm|` | 9.7e-18 | 1.1e-12 (`mode_endpoint`) |

Values (Ry): `wtilde ≈ 29.72`, `wx ≈ −2.310`, `sch ≈ 0.06577`,
`ssx ≈ 0.07131`, `occupiedTerm ≈ −0.03843`.

## Not established

- The weights `aqsn`, `aqsm`, `vcoul(igp)`, `occ`, which are exported but not
  certified.
- Any sum over modes, bands, q, or frequency.
- The static-remainder CH correction (`exact_static_ch 1`).
- Quasiparticle energies.
- The empty-band CH-only path.
- The q→0 block.
- The compiler.
- Physical accuracy.

## Regenerate

```bash
python3 bgw/m5_sigma/sigma_mode.py
python3 bgw/m5_sigma/make_lean_m5.py --check
python3 -m unittest tests.test_bgw_m5
source scripts/env.sh && python3 bgw/m5_sigma/mutate.py
```
