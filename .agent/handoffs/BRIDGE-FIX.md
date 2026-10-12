# BRIDGE-FIX handoff: E14 order dependence, and the origin of the non-cubic RHO

Worker: Claude (implementer). Branch `bridge-fix/work`, worktree
`.claude/worktrees/bridge-fix`, based on `bridge/theory-to-bgw` 3387327.

Status: **CHECKPOINT_READY**, meaning ready for review. It is NOT accepted; Codex owns
acceptance. This pass made no Lean edits and did not run `scripts/verify.sh`. A full
verify was running elsewhere on the machine, so all runs here used `nice`.

## Files

Edited:
* `bgw/endpoint/cert.py`: `main` calls `STATS.clear()` on entry and reports
  `dict(STATS)`. Adds a comment on why `STATS` is module state.
* `bgw/endpoint/qp_cert.py`: `main` calls `cert.STATS.clear()` on entry and reports
  `dict(cert.STATS)`.
* `tests/test_endpoint_e1.py`: `certified()` seeds `cert.STATS["undecided_stale_sentinel"] = 1`
  before `cert.main`. E14 asserts that the sentinel is absent from `branch_stats`, in
  addition to the existing "no undecided branch" assertion.
* `docs/BRIDGE.md`: one new final section, "BRIDGE-FIX".
* this handoff (new).

There is no new test module, so `scripts/gates.py` is unchanged. None of the edited
files is vouched for in `bgw/weighted_audit/PROVENANCE-R6.txt`, so nothing was re-signed.
Committed data (`bgw/endpoint/data/cert_o1.json`, `qp_cert.json`) is unchanged. Each
was generated in a fresh process, where clearing an empty dict makes no difference.

## Task 1: E14 fails in `pytest tests` but passes alone

Reproduction before the fix:
* `python3 -m pytest -q -x tests` gave `FAILED test_endpoint_e1.py::E14Certified::test_o1_enclosure_and_layer1_bound`
  at `assertTrue(all(v == 0 for undecided…))`. The O1 enclosure printed was the
  correct one, [0.015405752349, 0.015405753673] eV.
* `pytest tests/test_endpoint_a.py tests/test_endpoint_e1.py::E14Certified::test_o1_enclosure_and_layer1_bound`
  gave 1 failed, 5 passed. So `test_endpoint_a` alone is enough to pollute.
* In-process probe (scratch): after only `A1Linearisation.test_full_qp_roots_certified`,
  `cert.STATS` holds `{'undecided_sexcut': 6}`.

Root cause: shared module state. `cert.STATS` is a module-global dict that
`SigmaIV.kernel` increments through `count()`. `cert.main` returned it as
`branch_stats` and never reset it. `qp_cert.certify_root` deliberately tries
brackets that have undecided branches, records them as `continuity=False`, and moves
on. Those counts stay in `cert.STATS`. Pytest collects files alphabetically
(`test_endpoint_a` < `test_endpoint_e1`), and `test_endpoint_a` imports `cert` under
the same top-level name, so E14's `cert.main` reported A1's leftovers as its own. The
certificate itself was never wrong. Only its branch-count report was cumulative.
`qp_cert.main` had the same defect.

The fix is at the root: each `main` reports its own invocation. The polluter
(`test_endpoint_a`) is unchanged and still tests the same things: certified roots,
continuity attempts, uniqueness and cover. `qp_unique` and `certify_root` work with
deltas of `cert.STATS` inside one call, so clearing on `main` entry does not affect
them. E14 is stricter, not looser. It now plants a stale undecided counter first, so
it fails deterministically if `cert.main` ever stops resetting, whatever the test
order. Without the fix, the seeded E14 would fail even when run alone.

After the fix:
* pair (`test_endpoint_a.py` + E14): 6 passed (171.9 s)
* E14 alone: 1 passed (54.5 s)
* full list `python3 -m pytest -q tests`: see "Full run" below

**How `scripts/verify.py` runs the Python gate.** At lines 141-148 it runs
`python -m unittest -v *gates.SCIENTIFIC` in one process, followed by a separate
process for `gates.WORKFLOW`. `unittest` keeps the given module order. In
`gates.SCIENTIFIC`, `tests.test_endpoint_e1` comes before `tests.test_endpoint_a`.
The only earlier modules that touch `cert` are the `tests.test_bridge*` modules, and
running them in-process left `cert.STATS` empty (78 tests, OK, `STATS = {}`).
So the verify gate did NOT hit this failure, which matches the passing E14 in
`.claude/worktrees/bgw-e/artifacts/tests-scientific.log`. It was latent: any reordering
of `SCIENTIFIC`, or a future test that calls the kernel before E1, would have triggered it.

## Task 2: Si-EPM RHO is not cubic

Verdict: **(c), a consequence of the testsuite input, enabled by an undocumented
limitation of the converter.** It is not documented (a). Calling it a bug (b) is
arguable: `CalculateDensity` is correct only for a symmetry-closed k-list, and the
code neither says so nor checks for it. Evidence (BerkeleyGW-4.0 tree at
`~/bgw-src/pristine/BerkeleyGW-4.0`, unmodified):

* `MeanField/EPM/pwHamMod.f90:501-550` `CalculateDensity`: `do k = 1, numKPoints;
  do n = 1, numOccupiedBands` accumulates `|ψ|² * kPointWeights(k)` (lines 523-533).
  It has no symmetry loop and no star sum. It FFTs back and extracts ρ(G) by identity
  index (lines 536-543).
* `MeanField/EPM/epm2bgw.f90:431` `get_symmetries` finds 48 ops. They are used only
  for `check_inversion` (:440) and written into the headers (:531-535, :612-616).
  `CalculateDensity` is called at :582 without them. Line :593 scales by `2/nspin`.
  The RHO header carries `ntran = 48` while the data has lower symmetry.
* `MeanField/EPM/kPointsMod.f90:178-215`: `KPointsList` reads the points and their
  weights and normalises the weights. It never unfolds by symmetry.
* `testsuite/Si-EPM/WFN_co.in:39-45` (byte-identical to `bgw/export/WFN_co.in`):
  `KPointsList 3` with Γ (w 1), (0,0,½) (w 4), (0,½,½) (w 3). These are IBZ
  representatives with star weights. The weights suit the IBZ consumers, Epsilon and
  Sigma. They are wrong for a density that is never star-summed: the (0,0,½) state
  singles out b3.
* `testsuite/Si-EPM/Si.test:31-36` checks only WFN_co eigenvalues. Lines 399 and 635
  rename WFN_co to WFN_inner for Sigma. No RHO component is ever checked.
  `MeanField/EPM/README` has no word on density symmetry.
* Numerical confirmation (scratch script, `bgwio`): `~/bgw-src/runs/sig-pristine/RHO`
  has ρ(±b3) = 1.704457829838, ρ(±b1), ρ(±b2), ρ(±(b1+b2+b3)) = ±1.900883506577,
  `ntran 48`. Recomputing `2 Σ_k w_k Σ_{v≤4} |ψ_vk|²` from `WFN_inner` with weights
  0.125, 0.5, 0.375 on a 48³ FFT reproduces every RHO component to 7.1e-15. This
  agrees with BRIDGE-Q0's 3.6e-15.

Sigma does not symmetrise RHO:
* `Common/read_rho_vxc.f90:124-215` `read_rho`: header check (:163), raw data read
  (:173). Only these checks follow: ρ(0) real (:186-188, CPLX), ρ(0) > 0 (:198-201),
  and a WARNING if `c(G) ≠ c(-G)*` (:203-210, function :218-). It does no
  symmetrisation and no use of `syms` beyond `check_header`.
* `Sigma/input.f90:875` calls `read_rho` for GPP (`freq_dep 1`) only.
* `Sigma/wpeff.f90:158-161`: `ρ(G-G')` is looked up directly with the components of
  the rotated full-BZ `q`'s G vectors. The asymmetric ρ therefore enters `Ω²`
  differently for symmetry-equivalent q, which is the Q-6 effect.

Not done: the fix this suggests for production inputs, a full-grid `KPointsList` or a
star-symmetrised RHO, was not applied to any committed run. Changing inputs is an owner
decision. BRIDGE-Q0 already measured the O1 effect (15.406 → 15.781 meV).

## Commands

```
python3 -m pytest -q -x -p no:cacheprovider tests                       # repro: E14 FAILED
python3 -m pytest -q -p no:cacheprovider tests/test_endpoint_a.py \
  tests/test_endpoint_e1.py::E14Certified::test_o1_enclosure_and_layer1_bound   # repro pair
python3 scratch/stats.py        # cert.STATS after A1 only: {'undecided_sexcut': 6}
python3 scratch/gateorder.py    # bridge modules (gate prefix) leave cert.STATS = {}
python3 scratch/rho.py          # RHO first shell + reproduction from WFN_inner (7.1e-15)
```

## Full run

`python3 -m pytest -q -p no:cacheprovider tests` after the fix gives 596 passed, 2 skipped,
40 failed, 34 errors in 688 s. **Every** failure and error is in `test_ll_c2a/c2b/c3/c4`
and is a `FileNotFoundError` for a Lean-generated artifact
(`artifacts/ll-c2a/structural_values.json` 7, `ll-c2b/screening_values.json` 29,
`ll-c3/wick_values.json` 20, `ll-c4/electronic_values.json` 18). `scripts/verify.py`
produces these before the Python gate (lines 109-139). They were left alone as
instructed. All of `test_endpoint_a` and `test_endpoint_e1`, including E14, pass in
the full list.

## Next action

Codex review. Optional: decide whether production inputs should use a
symmetry-closed k-list for WFN_co's RHO. That is an input change, not a code change.
