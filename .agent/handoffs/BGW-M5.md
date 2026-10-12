# BGW-M5 handoff: one production GPP self-energy mode, connected to the GPP core

**Status: CHECKPOINT_READY (ready for review, not accepted).** Task:
`.agent/tasks/BGW-M5.md`, committed with its frozen selection rule before
the run. Worker: Claude (Opus 5.5), 2026-09-22, branch `bgw-m4/gpp-preflight`.

## Result, in plain terms

The number that M4-R1 certified (one squared GPP pole) is now carried one
step further, into the self-energy kernel, for one (mode, band, energy):

- **Pole.** Sigma's `wtilde = fl(sqrt(wtilde2))` is within 1.0e-10 of the
  exact `sqrt(PStar)`. The measured distance is 7.8e-16. The rounded root is
  checked by exact squaring, and M4's error on `wtilde2` is carried through.
- **SX and CH.** The kernel's per-mode `ssx` and `sch` for band 1 at
  `E = e_lk` are each within ~7e-13 of exact references built from M4's
  certified `Omega2`, `I_eps` and pole. The measured errors are about 1e-17.
- **The GPP core, instantiated on production data for the first time.**
  Lean proves the exact references combine into the specification's merged
  occupied term: `-ssx* + sch*/2 = GW.GPP.occupiedTerm OStar x* sqrt(PStar)`.
  `mode_endpoint` bounds the production combination against it (1.1e-12).
- The kernel took the generic branch, and `sexcut` did not zero the value.
  Both are checked on the decoded values.

## Commands and results

```
python3 bgw/m5_sigma/instrument_m5.py <fresh tree>; make sigma           rc 0
sigma.real.x (M5_IG=2 M5_IGP=1): 6 outputs IDENTICAL to pristine;
  M4-R1 records IDENTICAL to the committed M4-R1 dump; 1824 kernel records
python3 bgw/m5_sigma/sigma_mode.py                                     OK (n1=1, iw=2)
python3 bgw/m5_sigma/make_lean_m5.py --check                           OK
lake env lean GW/BGW/M5Sigma.lean                                      0 errors
python3 bgw/m5_sigma/mutate.py                                         control + 5/5 exact
python3 -m unittest tests.test_bgw_m5                                  15 OK
bash scripts/verify.sh                                                 PASS (all): 528 scientific (2 skipped) + 14 workflow,
                                                                       328 named audits, 903 theorems exhaustive
```

## Failed attempts and corrections

1. The `wx` check first failed at `iw ≠ 2`. `wx` there includes
   `dw*(iw-2)`, and `dw` is not exported. The check is now restricted to
   iw = 2, where that term is exactly zero.
2. After widening the local check to all 1824 records, one record failed.
   `e_lk = e_n1kq` there, and the source replaces |wx| < TOL_Zero with
   TOL_Zero. That replacement is now modelled, not skipped.
3. The first versions of four rejection tests edited a kernel record from a
   different Sigma call, which the target-call link check rightly ignores.
   The tests now edit the target call.
4. The wrong-root mutant first also failed `mode_identity` for a tactic
   reason (`Real.sq_sqrt` does not match `-sqrt`). The identity is
   algebraically true for either root, so the proof now uses `neg_sq`. The
   branch is pinned only by `sqrt_bound`, and the mutant now fails exactly
   there.
5. A module-name collision (`make_lean`) between M4 and M5; the M5 generator
   is now `make_lean_m5.py`.

## Independent review (Opus agent, read-only, 2026-09-22)

Verdict: ready_for_review. The reviewer confirmed:
- the source reading (sign/weight convention, `-ssx + sch/2 = rawOccupied`,
  the positive root, the branch/clamp predicates);
- the timeline: the task file was committed at 14:40, the instrumented tree
  was created at 14:41 and the run began at 14:42;
- the measured errors, recomputed at 60 digits.

Findings and what was done:
1. `occ = 1` was assumed, not checked. **Fixed:** `select()` now reports
   BLOCKED unless the selected record's occ bits are exactly 1.0, and a test
   covers occ = 0.5.
2. The link was sequence-based, and `(in, il)` does not identify a call: the
   offdiag (1,8,1) call also exports in = il = 1. **Hardened:** between the
   target setup and its kernel block, every setup `COL` must advance `my_igp`;
   a restart means another call, which is refused. A test injects one.
3. `mode_identity` is algebra only. That is intended: the production content
   is in the bound theorems and `mode_endpoint`.
4. The certified values come from the instrumented binary. Neutrality is shown
   on the six outputs, not on pristine intermediates (stated as empirical).

## Judgment calls for review

1. **Local rounding counts** (8, and 2 or 4 for the cancellation terms) are
   an a-priori model, as in M4. The Lean inequalities hold on the actual
   numbers either way; the counts decide only whether the budgets are
   honest.
2. **The selection rule** was written in the task file before the run. It
   picked band 1, which is generic and unclamped. No other band was
   examined for convenience.
3. **Units.** The quantities are BerkeleyGW internal Ry, while the
   specification uses eV. `occupiedTerm` is unit-agnostic, and no conversion
   is claimed.
4. The weights `aqsn`, `aqsm`, `vcoul(igp)` and `occ` are exported but not
   certified. The endpoint is the per-mode combination before weighting.

## Next action

Codex review. After that, the smallest next step toward a quasiparticle
number: the same certificate for one complete (G, G') block sum at this band,
including the weights, and the empty-band CH path. Not started.
