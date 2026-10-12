# REVIEW-28 — adversarial review of `main` after PR #28 (d783e18)

Reviewer: Codex (owns acceptance per `AGENTS.md`). Written by the Claude supervisor
of PRs #27/#28, i.e. by the party under review — weigh it accordingly and depart from
it wherever you judge the scope wrong. Read-only review: report, do not fix.

## 1. The claim under review (the only one made)

For the BerkeleyGW 4.0 Si-EPM testsuite run:

1. BerkeleyGW's production GPP output agrees with its own finite equations ("spec A",
   `GW/Endpoint/Kernel/{EpsSpec,SigmaSpec}.lean`) to 5.21 µeV in O1 (PR #27,
   `docs/ENDPOINT.md`), and spec A's O1 is kernel-certified in
   [15.40575235, 15.40575367] meV.
2. Spec A equals G0W0 with the Hybertsen–Louie GPP on plane waves, derived from a
   general finite fermion system, up to the departures listed in `docs/BRIDGE.md`
   (`GW.Bridge.sigA_eps_eq_theory_q0`, `sigA_eq_theory`, `epsSpec_eq_theory`).

Everything else is either a finding (section 4) or explicitly not claimed.

## 2. Where to attack (highest value first)

Lean has checked the proofs; it cannot check that definitions MEAN what the prose
says. Spend most effort here:

1. **Transcription, Fortran → spec A.** `GW/Endpoint/Kernel/EpsSpec.lean`,
   `SigmaSpec.lean`, `GW/Endpoint/CertSexcut.lean` against BerkeleyGW 4.0
   (`~/bgw-src/pristine/BerkeleyGW-4.0`; line ranges in the docstrings and
   `docs/review/index.html`). Signs, factors of 2, units (Ry vs eV, `RYD`), the
   wing rule, thresholds, branch conditions.
2. **Independence of the theory side.** The bridge is only meaningful if the theory
   definitions were not copied from spec A. Check `GW/Bridge/Bloch.lean` (`OmT` — the
   HL Ω² is written from the paper but uses spec helpers `factW`, `rhoF`, `dotB`,
   `vec`; `thK`), `GW/Bridge/FreqIntegral.lean` (`sigt`, `sigt_limit`),
   `GW/Bridge/EpsChi0.lean` (`chiF_limit`) against Hybertsen–Louie 1986 / Hedin and the
   existing `GW/Endpoint/ManyBody/GWSecond.lean`.
3. **Hypotheses that carry weight.** `ModeOK`, `specMode` (`Compare.lean`),
   `EpsBlock.OK` (`EpsCompare.lean`: `ResOK`, `TROK`, `Bands`, `vol`), `KPRay`
   (`EpsQ0.lean`: the k·p slope is assumed), `CompleteK` (`Cor.lean`). Are any vacuous,
   unsatisfiable, or stronger than the prose claims? (Known: `Bloch.Complete` is
   unsatisfiable on stored data — section 4.)
4. **Rigour of the Python numbers that the claim cites.** `bgw/endpoint/iv.py`
   (outward rounding), `cert.py` (5.21 µeV link), `bgw/bridge_measure/measure.py`,
   `bgw/bridge_cor/cor.py`, `bgw/bridge_disc/disc.py`, `bgw/bridge_q0/q0.py`: does each
   number labelled "rigorous" really come from intervals?
5. **The departure table** (`docs/BRIDGE.md`): is any row's status (proved equal /
   named approximation / shared / DISCREPANCY) wrong or missing?

## 3. Out of scope — please do not raise these as findings

* Convergence in bands/k-points/cutoffs as such (owner decision 2026-09-23). The
  band-truncation *finding* is already recorded (section 4).
* Archived code (`docs/CODEMAP.md` "Archived"): style, duplication, missing tests.
  Raise only if a canonical result depends on it.
* Theorem count, file size, generated `GW/Endpoint/Kernel/Data/` contents (checked
  by the kernel; review the generator `bgw/endpoint/kernel_export.py` instead if at all).
* Lean style, naming, proof length, performance (unless a gate is wrong).
* New science, new features, more samples (freeze, `.agent/STATE.md`).
* Items already listed as open decisions in `.agent/STATE.md` — comment on the
  recommendation if you disagree, but they are not new findings.

## 4. Already known (do not re-report; do challenge if you think it is mis-stated)

* O1 = 15.4 meV is a band-truncation artefact; all-band ≈ −3.8 meV (BerkeleyGW at 164
  bands: −3.761 meV). The static remainder's ½ moves O1 by ±117 meV (BRIDGE-COR).
* RHO input not cubic (EPM `CalculateDensity`, IBZ-only k-list); +0.38 meV (BRIDGE-Q0,
  BRIDGE-FIX).
* Occupied `x = w̃`: spec 0 vs theory I/4 — the one undocumented departure.
* `sigA_eq_theory_complete` / `Bloch.Complete` unsatisfiable on stored data.
* GPP kernel discontinuity at (0,0) — harmless here (BRIDGE-DISC).
* Process: parallel agents with overlapping writes (BRIDGE-DISC/Q0/COR), recorded in
  `AGENTS.md`; the supervisor wrote its own task briefs.
* Trusted, not proved: binary reader / float→dyadic export; transcription; production
  vs spec A link (Python); symmetry unfolding; "exactly two QP roots" (Python).

## 5. Reporting

For each finding: severity —
* **BLOCKER**: the claim in section 1 is false or unsupported as stated;
* **MAJOR**: a stated result, hypothesis or number is wrong but the claim survives in
  a weaker, statable form;
* **MINOR**: wording, a mislabelled status, a missing caveat.

Give file:line, a concrete failing case or counter-example where possible, and the
smallest fix. Mark anything you could not verify as UNVERIFIED rather than guessing.
Cap MINOR findings at ~10, most important first. End with an explicit verdict on
claims 1 and 2 separately: holds / holds with corrections (list) / does not hold.

## 6. Starting points and commands

Read: `.agent/STATE.md`, `docs/CODEMAP.md`, `docs/ENDPOINT.md`, `docs/BRIDGE.md`,
`THIRD_PARTY_NOTICES.md`; handoffs `.agent/handoffs/BRIDGE*.md`, `G2-*.md`,
`LEAN-CERT.md`, `BGW-E1.md`.

```
source scripts/env.sh
bash scripts/verify.sh --gate fast      # ~1 min warm: registry, build, memoized audit
bash scripts/verify.sh                  # full: ~5 h cold (GWKernelData), ~1 h warm
python3 -m pytest -q tests/test_bridge*.py
```

Last full gate: PASS at b46a826 (34285 theorems, 655 scientific + 14 workflow tests).
