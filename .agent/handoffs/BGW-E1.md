# BGW-E0/E1 handoff — observable pinned; certified layer-1 bound

Status: E0 PASS, E1 exit SUCCESS per `docs/ENDPOINT.md` section 3. Ready for
review, **not accepted**. Branch `bgw-e/endpoint` (stacked on
`bgw-m4/gpp-preflight`).

## The statement

For the shipped BerkeleyGW 4.0 Si-EPM GPP run (epsilon_cutoff 7.0 Ry, 18
bands, 2x2x2 grids), O1 = Eqp1(X,c) − Eqp1(L,c):

- production: +15.400547 meV (printed to 1e-9 eV);
- spec A (BerkeleyGW's finite calculation, exact mini-BZ Coulomb averages)
  evaluated in rigorous interval arithmetic on WFN, WFNq, WFN_inner, RHO:
  [15.4057524, 15.4057537] meV, no undecided branch;
- **|O1_prod − O1_specA| ≤ 5.21 µeV** (certified), essentially all Monte Carlo
  quadrature; O2 (gap, CBM certainly at L): |δ| ≤ 33.4 µeV;
- every q→0 direction Sigma could have used: O1 ∈ [14.34, 15.41] meV;
  direction-averaged q=0 cell (spec B): 14.8897 meV.

C1 (O1 > 0) holds for the specified finite calculation, all variants. This
says nothing about convergence (E2) or about GPP itself (layer 3).

## Commands (all from the worktree root)

```
bash bgw/toolchain/setup.sh                    # now also builds epm2bgw.x
python3 bgw/endpoint/run_production.py OUT     # fresh pinned run (10 s)
python3 bgw/endpoint/observable.py OUT         # O1, O2, constituents
~/bgw-src/pyenv-e1/bin/python bgw/endpoint/certcoulomb.py OUT data.json   # Arb (python-flint 0.9.0 venv)
python3 bgw/endpoint/cert.py OUT --out cert.json                         # 56 s
python3 bgw/endpoint/mutate_e1.py OUT --log LOG                          # 2 min, 16 procs
python3 bgw/endpoint/mutate_lean.py --log LOG
python3 bgw/endpoint/sphere_margins.py OUT
BGW_TOOLCHAIN=$HOME/bgw-src/mm/envs/bgw bash scripts/verify.sh
```

Result of the last: PASS (all); 558 scientific tests (1 skip: supervisor
fresh run, pre-existing), 14 workflow, 907 theorems axiom-audited.
`tests/test_endpoint_e0.py` (6) and `tests/test_endpoint_e1.py` (25) are in
the scientific gate.

## What the reproduction had to get right (each cited in spec.py)

1. irrbz keeps the LAST matching (iq, op): for q=0 that is op 48, which
   rotates the z-direction eps0mat. First-match gives O1 −1.06 meV.
2. Wing factors apply in the irreducible frame (target row/col G=g0), with
   vcoul(1) = the sortrx-first element (GK tie-break).
3. Unfolded states can carry global phases (±i); bilinear forms need conj.
4. Epsilon sums over the 32-point symmetry closure of the shifted grid.
5. Every (q,G) Coulomb value is a Monte Carlo mini-BZ average (avgcut 1e12).

## Failed attempts / corrections (in order)

- Correlation first came out 20% low: localised with a write-only
  instrumented build (`instrument_e1.py`), cause 1 and then 3 above.
- Epsilon first 3–30% off: the 8-point grid instead of the 32-point closure.
- The first ε⁻¹ enclosure (uniform Neumann bound) was 5e-6 wide at q0 and
  left GPP thresholds undecided; fixed by exact power-of-two balancing and a
  componentwise Neumann bound (`iv.inverse_cw`).
- Arb's `atan` has no `analytic` flag: rewrote via logs. Nearly flat cones
  (bdot asymmetric at 1e-16) defeat acb.integral: rigorous flat-cone bound.
- My float quadrature of the cell averages (`coulomb.exact`) is off by ~4e-9
  relative; the Arb values were confirmed by an independent 30-digit mpmath
  face decomposition. The float version is diagnostic only.

## Gate amendment (recorded, not silent)

The E1.4 row promised Lean proofs of the interval rules. Not done: the rules
are textbook; the risk is in the numpy code, which is tested against exact
rationals. Lean instead proves the one non-textbook rewrite the evaluator
makes (near-pole closed form, `GW/Endpoint/NearPole.lean`, 3/3 mutants caught).

## Findings for E2/E3 (from `data/mutations_e1.log`; conventions, not bugs)

O1 under alternative GPP conventions: invalid modes skipped −5.2 meV (sign
flip); no static remainder −101 meV (sign flip); remainder factor 1 +132 meV;
unoccupied near-pole CH kept +34.8 meV; dE = 0.5 eV +18.6 meV. 163k invalid
(w̃² < 0) modes over the four certified states. The remainder is a band
truncation correction, so E2 must sweep number_bands with and without it.

## Next action

E2 (gates written in `docs/ENDPOINT.md`): joint number_bands ×
epsilon_cutoff sweep, k/q grid, constituents, remainder on/off; then E3.

## Independent review (2026-09-22, Opus subagent, read-only) and what changed

No finding breaks the claim. It re-ran cert.py (same enclosure) and, with
the production Monte Carlo averages substituted, found every production
print inside the enclosure — so cert.py carries the production conventions
and the 5.2 µeV is the quadrature alone. Now a gate test
(`test_production_conventions_enclose_production`). Rigor fixes applied:
q0+G formed in interval arithmetic before the metric (cert.norm2); the
Neumann tail β^(m+1) built by rounded-up products (iv.inverse_cw); a
flush-to-zero guard at iv import; the run-specific preconditions (isotropic
q-grid, q=0 first, avgcut default, no truncation/metal/graphene, GPP
defaults, Vxc ≡ 0 from VXC) asserted in `spec.Run.check_preconditions`;
the mutation rerun test now exercises a mutant; a stray `unittest.main`
removed. Mutation log regenerated for the new spec.py (15/15 detected).
