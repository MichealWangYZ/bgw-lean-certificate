# A2-cd handoff: independent reproduction of BerkeleyGW's CD self-energy

2026-09-23. **Ready for review, not accepted.** Branch `a2/cd-repro`
(worktree `.claude/worktrees/a2-cd`), based on `bgw-e/endpoint` at 3391a7a.
All numbers are float64 evidence. Nothing here is certified.

## Scope and files (all new, except for one line in scripts/gates.py)

- `bgw/endpoint/spec_cd.py`: the CD reproducer. It adds the frequency-dependent
  parts to spec.py and reuses spec.py's readers, unfolding, `Screening.mapping`
  (last-match op), `mtxel`, and the Monte Carlo Coulomb/oneoverq replicas. Every
  convention it follows has its source line in the module docstring.
  It also contains `read_eps_ff` and `epsinv_ff`. These are copies of the
  **uncommitted** versions in the bgw-e worktree (`bgwio.py`/`spec.py` there
  have local modifications). They are copied so that this branch does not
  depend on uncommitted work. The only change is einsum -> tensordot in
  `epsinv_ff`.
- `bgw/endpoint/a2_repro.py`: Step 1. It covers the full table, the three
  variant runs and 7 counterfactuals. Output: `data/a2_repro.json`.
- `bgw/endpoint/a2_exact.py`: Step 2 (exact-frequency residue, converged
  imaginary-axis quadrature, eta scan). Output: `data/a2_exact.json`.
- `bgw/endpoint/a2_summary.py`: the Step 2 and Step 3 tables. Output:
  `data/a2_summary.json`.
- `tests/test_endpoint_a2.py` (6 tests, about 140 s). It is registered in
  `scripts/gates.py` SCIENTIFIC. It skips when the pristine tree or
  ~/bgw-e-runs/a2-cd is missing.
- spec.py, cert.py, iv.py and bgwio.py are untouched.

## Commands

```
python3 bgw/endpoint/a2_repro.py   --out bgw/endpoint/data/a2_repro.json    # ~10 min (8 threads)
python3 bgw/endpoint/a2_exact.py   --out bgw/endpoint/data/a2_exact.json    # ~2 min
python3 bgw/endpoint/a2_summary.py --out bgw/endpoint/data/a2_summary.json  # instant
python3 -m unittest tests.test_endpoint_a2 -v                               # 6 tests OK, 141 s
python3 -m unittest tests.test_gate_partition                               # OK
```

## Step 1: layer 1 for the CD path (reproduced to print precision)

Production run: ~/bgw-e-runs/a2-cd (pristine sigma.real.x, eta = 0.05 eV,
400 real frequencies with step 0.1 eV, 30 imaginary frequencies,
cd_int_method 0, exact_static_ch 1, nfreqeval = 241).

- **Full diagonal table.** This is 3 k-points x bands 1-8 (14 multiplets),
  every column: X, Re Res, Im Res, Re Int, Re Cor, Re Sig and the primed
  Int`, Cor`, Sig`.
  - Worst |ours - printed| is 4.98e-7 eV on the unprimed columns, which are
    printed to 1e-6.
  - It is 4.83e-6 eV on the primed columns, which are printed to 1e-5.
  - Every entry is within half a print unit.
  - The Gamma valence bands exercise the occupied (wx < 0) residue branch.
- **X and L.** Our value, with the printed value in parentheses:

  | state | Res | Int | Cor | Sig |
  | --- | --- | --- | --- | --- |
  | X | -5.1750122 (-5.175012) | 0.9540446 (0.954045) | -4.2209676 (-4.220968) | -8.4286430 (-8.428643) |
  | L | -5.6650874 (-5.665087) | 1.2991169 (1.299117) | -4.3659705 (-4.365971) | -9.2853004 (-9.285300) |

  Im Res is -2.2e-9 for X (printed -0.000000) and -0.0002148 for L (printed
  -0.000215).
- **O1 correlation contribution.** Sigma_c(X) - Sigma_c(L) = **145.00294 meV**
  (printed values give 145.003 meV).
- **Variant runs.** Each variant was reproduced against its own eps files for
  X and L, all columns within half a print unit:

  | run | settings | worst unprimed diff (eV) |
  | --- | --- | --- |
  | a2-cd-brd0.1 | eta 0.1 | 4.8e-7 |
  | a2-cd-fine | eta 0.02, step 0.05, 60 imaginary frequencies | 4.7e-7 |
  | a2-cd-nimag15 | 15 imaginary frequencies | 4.2e-7 |

- **Counterfactuals** (`data/a2_repro.json`). Each changes one transcribed
  convention. All 7 move some printed column by more than half a print unit:

  | counterfactual | max ratio to half print unit |
  | --- | --- |
  | nearest-grid residue instead of linear | 252 |
  | +1e-12 instead of +TOL_SMALL in freq0 | 1.5 (marginal) |
  | E = Eo - 1e-6, which drops the wx = 0 residues | 1e7 |
  | last cd_int_method-0 interval not mirrored | 4.4 |
  | trapezoid instead of atan weights | 1e12 |
  | no q != 0 wing scaling | 4.9e3 |
  | first-match symmetry op instead of last | 1.2e3 |

  The TOL_SMALL offset is only just distinguishable. Replacing it by an exact
  0 would be indistinguishable: wx = 0.0 falls on the same side, and Fortran's
  atan(x/0) = pi/2.
- **Supporting checks.**
  - The direct eps^-1 (`epsinv_ff`, from WFN/WFNq) matches the file at real
    and imaginary grid frequencies to <= 4.1e-11 (q0) and <= 1.1e-13 (q != 0).
  - The symmetry phase products are real to 6e-16.
  - Im sW on the imaginary axis is <= 6e-21.

Conventions, with source lines in the spec_cd docstring:
- The evaluation point is freq0 = e_lk - step (n-1)/2 + TOL_SMALL, so "E = Eo"
  is actually Eo + 1e-6 eV.
- Residue selection is `(wx >= 0) .eqv. flag_occ` -> skip, with
  occ_sign = sign(wx).
- W is interpolated linearly on the real grid at |wx|, using the last
  bracketing interval.
- cd_int_method 0: piecewise-constant sW with atan weights and the last
  interval mirrored. Int = sint/pi.
- Imaginary frequencies are Im(dFreqGrid + dFreqBrd) of the |grid| < TOL_ZERO
  block, excluding index 1.
- fixwings_dyn at every frequency: q0 wings are zeroed and the **head is left
  unchanged**, because there is no W averaging in the FF branch.
- The static remainder uses Re eps^-1 at grid point 1 (omega = 0 + i eta) in
  both the exact and the partial static CH.

## Step 2: BerkeleyGW's numerical approximations versus the exact CD formula

The exact evaluation (`a2_exact.py`) is the same formula, the same q/band
sums and the same wings, with two changes:
- **Residue.** W is taken at exactly |wx| + i eta, from a direct eps^-1.
- **Imaginary-axis integral.** sW(i w) is computed directly at every node.
  - The integral is written as sW(0) sgn(wx)/2 plus
    (1/pi) int [sW(iw) - sW(0)] wx/(wx^2 + w^2) dw.
  - That integral uses Gauss-Legendre panels in u = ln w on [w_lo, w_hi],
    with closed-form end pieces.
  - Refinement uses three rules: (1e-4, 1e5 eV, 2 panels/decade, 8 nodes),
    (1e-4, 1e5, 4, 12) and (1e-6, 1e6, 6, 16).
  - The three agree to 2.5e-12 eV per state and to 2e-13 eV on O1.
  - The rule reproduces a closed-form test integral to 2e-12 for |wx| from
    1e-6 to 30 eV.

Residue frequencies: X has only wx = +1e-6 terms (12 of them). L has +1e-6
and 0.628219 eV (= E_L - E_X), 10 in all. Both lie far below the lowest chi0
transition, 2.93 eV (3.29 eV at q0). So W is analytic and real there, and
Im Res is O(eta).

At eta = 0.05 (meV; production minus exact):

| | total | residue interpolation | imaginary quadrature |
| --- | --- | --- | --- |
| X, per state | -0.5488 | -0.0000022 | -0.5488 |
| L, per state | -0.5578 | -0.0072 | -0.5506 |
| **O1_c = X - L** | **+0.0090** | +0.0072 | +0.0018 |

- The 30-point piecewise-constant quadrature is off by about 0.55 meV per
  state. The error is almost identical for X and L, so on O1_c it cancels to
  1.8 micro-eV.
- The residue interpolation error is 7 micro-eV on O1_c (from L's 0.628 eV
  term).
- The same comparison against the variant production runs (production minus
  exact at the same eta):

  | run | production minus exact on O1_c (meV) |
  | --- | --- |
  | eta 0.1 | +0.0089 |
  | fine, eta 0.02 | +0.0071 |
  | 15 imaginary frequencies | -0.233 |

  The 15-point grid is the only setting where BerkeleyGW's quadrature matters
  at the 0.1 meV level.

Eta dependence of the exact CD O1_c (meV). The static remainder is taken at
the same eta; the integral does not depend on eta.

| eta (eV) | 0.1 | 0.05 | 0.02 | 0.01 |
| --- | --- | --- | --- | --- |
| O1_c exact | 144.96915 | 144.99395 | 145.00089 | 145.00188 |

- The fit v0 - a eta^2 through the two smallest eta values gives
  v0 = **145.00221 meV** and a = 3.31 meV/eV^2.
- The fit residuals are 8e-6 meV at eta = 0.1 and 4e-7 meV at 0.05.
- The eta -> 0 limit is regular here, and eta is a 0.03 meV effect on O1_c at
  E = Eo. This holds because every residue frequency lies below the chi0
  continuum.
- Per state, from eta = 0.05 to 0.01: Cor(X) moves by -0.065 meV and Cor(L) by
  -0.073 meV.

## Step 3: plasmon-pole model error at E = Eo

- **GPP run.** Standard static-GPP run (~/bgw-e-runs/e0-default, same mean
  field, 18 bands, 7 Ry; the input files differ only in the FF keys).
  Sigma_c = SX-X + CH (unprimed, which includes the static remainder):
  - X = -4.316769430 eV
  - L = -4.430183194 eV
  - O1_c(GPP) = **+113.414 meV**
- **CD, exact formula, eta -> 0:** O1_c = **+145.002 meV**. Production CD at
  eta 0.05 gives 145.003.
- **PPM error on Sigma_c(X) - Sigma_c(L) at E = Eo: GPP - CD = -31.588 meV.**
  - Per state: X -96.29 meV, L -64.70 meV.
  - The size of this error is not an artefact of BerkeleyGW's CD numerics:
    those numerics contribute 0.009 meV, and eta contributes 0.03 meV.
- **Evaluation energy.** GPP evaluates at E = Eo; CD at Eo + 1e-6 eV
  (TOL_SMALL). The effect is about 1e-7 eV, which is negligible.

## Failed attempts and pitfalls

- **Stale base.** `git worktree add ... bgw-e/endpoint` first checked out
  43a567c. The local branch had moved to 3391a7a, whose commit adds the A2
  paragraph of ENDPOINT.md. I reset the new branch to 3391a7a before any
  work.
- **Missing functions.** `spec.epsinv_ff` and `bgwio.read_eps_ff` do not exist
  in any commit. They exist only as uncommitted edits in the bgw-e worktree,
  which I did not touch. They are copied into spec_cd.py.
- **Lost first repro run.** The first `a2_repro.py` run crashed at
  json.dumps, because nFreq is a numpy int64. It was fixed with int() and
  `default=float`, then rerun.
- **Waits that never ended.** Several `until ! pgrep -f a2_exact.py` waits
  never ended, because pgrep matched the waiting shell's own command line.
  The exact run itself took about 2 minutes. This had no effect on results.
- **First TOL_SMALL counterfactual.** Subtracting TOL_SMALL made wx exactly
  0.0, and numpy's atan(x/0) gave NaN. It was replaced by +1e-12.

## Exact limits of the claims

- **Float, not certified.** Agreement with production is at print precision
  (1e-6 eV). A tighter comparison would need an instrumented build; none was
  needed, because nothing disagreed.
- **Step 1 covers what was exercised, and nothing wider.** It covers E = Eo
  (iw = iwlda) only: not the other 240 evaluation frequencies, not the
  off-diagonal elements, not Eqp1.
- **"Exact" means the CD formula as BerkeleyGW writes it**, evaluated without
  interpolation and with a converged quadrature. It still includes the
  following, all as in production:
  - the finite-k chi0 (32 k-points), 18 bands and 7 Ry;
  - the Monte Carlo Coulomb averages;
  - the one-direction q0 treatment;
  - the static remainder.
  None of these are removed.
- **Scope of the PPM error.** The PPM error is at E = Eo, not at the QP
  energies. It is also a statement about this finite calculation (layer 3
  within layer-2 truncation), not about converged Si.

## Next

Review. If accepted, the supervisor may add a pointer paragraph in
docs/ENDPOINT.md ("A2 at a well-defined energy"). That file is outside this
task's write scope.
