# BGW-A handoff — the GW approximation layer (in progress)

2026-09-23. Ready for review, not accepted. Branch `bgw-e/endpoint`
(worktree `.claude/worktrees/bgw-e`). Owner scope decision of 2026-09-23:
convergence (layer 2) is out of scope; bounds on the GW approximations
(layer 3) are in scope. Plan and results: `docs/ENDPOINT.md`, sections
"Scope change" and "A — the approximation layer".

## Results so far (O1 = Eqp1(X,c) - Eqp1(L,c), C1: O1 > 0)

| treatment | O1 | evidence | file |
| --- | --- | --- | --- |
| G0W0-GPP linearised (production) | +15.4 meV | E1: certified, <= 5.21 µeV to spec A | data/cert_o1.json |
| G0W0-GPP full QP equation (sexcut) | +68.986 meV | A1: certified roots | data/qp_cert.json |
|   same, production's own Sigma(E) | +68.971 meV | production (fdf -3) | data/a1_production_check.json |
| G0W0-GPP full QP, sexcut off | ~+154 meV, roots not unique | float | (docs) |
| G0W0 full-frequency RPA (CD) | +58.3 (brd 0.05) / +67.2 (0.1) meV; 2 X roots at 0.02 | production | data/a2_cd_*.inp |
| evGW0-GPP | +137.87 meV | production | data/evgw0.json |
| evGW-GPP | +134.20 ± 0.03 meV | production | data/evgw.json |
| leading vertex term (SOX, 2nd order, on evGW0 spectrum) | +1.98 meV | estimate | data/second_order_evgw0.json |

Reading: C1 holds everywhere well-defined; the magnitude spans ~9x within
GW. Root cause: Vxc = 0 (EPM) puts the QP energies ~7 eV from Emf, inside
Sigma's pole structure, so one-shot G0W0's premise fails; self-consistency
stabilises O1 at ~134-138 meV.

## 2026-09-23 (second pass): what Lean now proves, and what changed

Owner-approved plan: items 1-4 of "what can be Lean-proved but wasn't".

1. Certificate mathematics (branch lean/cert-lemmas, merged; handoff
   LEAN-CERT.md): interval-operation enclosure under a named rounding
   hypothesis, componentwise Neumann enclosure + balancing (`inverse_cw_sound`),
   sexcut test equivalence (`certSsx_eq_srcSsx`). Its findings, all fixed here
   and re-certified (O1 and roots unchanged beyond the last digit):
   - near-pole sexcut threshold was 2w/sexcut, correct is w/sexcut (found by
     me while writing the Lean spec; commit 7a4b7a5; latent);
   - at wdiff = 0 exactly production gives ssx = 0 (NaN branch tests),
     cert.py gave -I/4: fixed in cert.kernel and CertSexcut `certSsx_at_w`;
   - power-of-two (un)balancing was not outward-rounded for subnormals: now
     an interval multiply; inverse_cw asserts down(1 - beta) > 0.
2. QP roots (`qp_unique.py`, Lean `QPUnique.lean`): complete enumeration in
   [-1e4, 1e4] eV, two roots per state -- principal (Z 0.86) and a
   low-weight one near 30 eV (Z ~0.04). "Uniqueness" was a window artefact.
   C1 holds for the principal-solution choice (the other pairing: -537 meV).
3. Dimer Sigma_c derived from i G0 W_c in the time domain (branch
   lean/dimer-sigma, merged; handoff A3-dimer-2.md).
4. Dimer U^2 coefficients exact: GW error = -SOX + O(U^3) = U^2/(8t).

Commands (new):
```
python3 bgw/endpoint/qp_unique.py RUN --out data/qp_unique.json   # ~30 min, 1 core
python3 bgw/endpoint/a3_dimer/second_order_dimer.py               # dimer numerics, ALL OK
```
Failed attempts: the first uniqueness run died at the TOL_Zero clamp of the
lowest band (-2.552 eV; fixed with the non-strict hull evaluation), then at a
jump of f across 0 (29.03 eV, X; branch split, first rejected because the
degenerate pair gives two identical undecided conditions -- accepted when the
kernel inputs are bit-identical), then at the genuine second root (29.92 eV).
Twice `pkill -f PATTERN` killed its own shell (the pattern is in its own
command line): use pgrep first.

## Commands

```
python3 bgw/endpoint/qp_full.py RUN [--de 0.1]                    # float scan of the QP equation
python3 bgw/endpoint/qp_cert.py RUN --guess-X 4.19443 --guess-L 4.12556 --out F   # certified roots (~50 s)
python3 bgw/endpoint/a1_production_check.py GRID_RUN RUN          # roots from production spectrum.dat
python3 bgw/endpoint/evgw0.py RUN OUT --iters 25                   # ~10 min
python3 bgw/endpoint/evgw.py RUN OUT --iters 25                    # ~25 min
python3 bgw/endpoint/second_order.py RUN [--eqp EQP1_DAT]          # ~1.5 min
```
CD inputs: data/a2_cd_epsilon.inp, data/a2_cd_sigma.inp (run in a copy of
a pinned run directory). Gate: tests/test_endpoint_a.py (A1).

## Changes to E1 machinery made here

cert.kernel decides sexcut without division (equivalent for |I| > 0), so
the hole-branch SX poles (wx = -w) that production clamps are handled; the
E1 certificate is bit-identical (checked).

## Open

- A3(b): DONE (merged from a3/hubbard-dimer, re-checked): Lean bound
  |gap_GW - gap_exact| <= U^2/(8t) for the Hubbard dimer; see
  `.agent/handoffs/A3-dimer.md`.
- A2: DONE as float evidence (merged from a2/cd-repro): CD reproduced to
  print precision; BerkeleyGW's CD numerics +0.009 meV; plasmon-pole error at
  Eo -31.588 meV; see `.agent/handoffs/A2-cd.md`.
- A3(a): formal structure of the GW error in a finite fermion model (first
  order exact, second-order exchange missing) — not started.
- A2 is float evidence, not certified (an interval version of spec_cd.py
  would certify it).
- Still unproved correspondences: numpy code = the Lean formulas (tested);
  Fortran NaN behaviour at wdiff = 0 / wx = -w (argued); the closed-shell
  second-order formula (textbook); A3(a), the general finite-fermion theorem.
- Not committed as tests: evGW/evGW0/CD/second-order runs (minutes each);
  their outputs are committed under bgw/endpoint/data/.
