# G3 handoff: exact self-energy of the Hubbard dimer, and the textbook second-order formula

Status: **ready for review. Not accepted.** Branch `lean/g3-dimer-exact-sigma`,
forked from `bgw-e/endpoint` at c1a834f. Worktree `.claude/worktrees/lean-g3`.

## What was missing and what is now proved

`HubbardDimerSecondOrder.lean` defined the second-order self-energy
`sig2dir + sig2x` by the textbook closed-shell formula, with spin factors 2 and
−1, and used it without deriving it. This task derives the exact self-energy of
the dimer from the many-body problem. It then proves that the exact self-energy
equals that formula, with those spin factors.

The result is stronger than second order. For this model the HF-referenced
exact self-energy **equals** `sig2dir + sig2x`, with HF denominators, at every
U. The equality holds off the poles and zeros of G. The O(U³) remainder of the
U-expansion comes only from expanding the HF denominator `ω − 3t − U/2`.
Numerics found this before the proof (see below). It is a known feature of the
half-filled dimer. It is not a general fact about second-order perturbation
theory.

## Plain-math statements (t > 0; file `GW/Endpoint/HubbardDimerExactSigma.lean`, namespace `GW.Endpoint.HubbardDimer`)

**Setup.** The setup is built from the Jordan–Wigner Fock operators of
`HubbardDimerFock.lean`.

- Operators: `annO p = Σ_i φ_p(i) c_{i↑}` and `creO p`. p = 0 is bonding B and
  p = 1 is antibonding A. The orbitals are `orb` from `HubbardDimerSecondOrder`.
- Spin-up only. The explicit 16×16 matrices of `c_0`, `c_2`, `c†_0`, `c†_2` are
  kernel-checked against the JW definition with `decide +kernel`.

**Eigenstates.**

- `ev1` and `ev3` are orthogonal eigenbases of the full N = 1 and N = 3
  sectors. The N = 1 energies are (−t, t, −t, t). The N = 3 energies are
  (U+t, U−t, U+t, U−t).
- Proved for each basis: `ev*_eigen`, `ev*_sector`, `ev*_orth` and
  `ev*_complete`. Completeness means every in-sector vector is the sum of its
  components.
- `psi0` is the N = 2 ground state and `E0 = (U − r)/2`, with r = √(U²+16t²).
- `psi0_ground` shows that `psi0` is the sector ground state
  (`IsSectorGround`, from `ground_two`).
- `psi0_unique` shows it is **nondegenerate**: every N = 2 eigenvector with
  eigenvalue E0 is a multiple of `psi0`.

**Green's function.**

- `GL t U ψ E p q ω` is the Lehmann sum over **all 4+4** N±1 eigenstates. The
  matrix elements `(m · c†_q ψ)` and `(m · c_p ψ)` are computed from the
  operator matrices (`creB_psi0`, `creA_psi0`, `annB_psi0`, `annA_psi0`), not
  transcribed.
- `Gex = GL(psi0, E0)`.
- `GL_ground_eq`: G is the same for ANY nonzero ground eigenvector with the
  sector ground energy, so it does not depend on normalisation or phase.
- `Gex_resolvent` and `Gex_resolvent_exists`: the Lehmann sum equals
  `(⟨c†_p ψ0, xP⟩ + ⟨c_q ψ0, xH⟩)/|ψ0|²` for ANY in-sector solutions of
  `(ω + E0 − H) xP = c†_q ψ0` and `(ω − E0 + H) xH = c_p ψ0`, and such solutions
  exist. The poles must be excluded. The proof uses `sector_resolvent`, which
  gives uniqueness in the sector, and `H_symm`.
- `Gex_offdiag`: G_BA = G_AB = 0 for all ω (**parity**).
- `Gex_BB`: G_BB(ω) = w₋/(ω − (U+t−E0)) + w₊/(ω − (E0+t)).
- `Gex_AA`: G_AA(ω) = w₊/(ω − (U−t−E0)) + w₋/(ω − (E0−t)).
- `weights_eq`: w± = (1 ± 4t/r)/2.
- `Gex_BB_rat` and `Gex_AA_rat`: rational forms, where G_BB vanishes only at
  ω = 3t + U/2 and G_AA only at ω = U/2 − 3t.
- `Gex_U0`: at U = 0, G_pp = 1/(ω − eps0_p) = G0. The reference propagator is
  itself the Lehmann G of the non-interacting ground state.

**Self-energy convention (chosen and stated).**

- `sigEx p ω = (ω − eps0_p) − 1/G_pp(ω)`. This is Dyson's equation with the
  U = 0 reference G0, with `eps0 = (−t, t)`.
- `hf_shift`: `epsOrb_p − eps0_p = U/2`, which is the HF shift of the GW files
  (`fock_eq`). So `sigEx − (epsOrb − eps0)` is Σ_exact − Σ_HF, in the files'
  conventions, and plugs directly into `HubbardDimerSecondOrder`.

**Key theorems.**

- **`sigEx_B`**: Σ_B(ω) = (epsOrb_B − eps0_B) + sig2dir t U 0 ω + sig2x t U 0 ω
  for all U. Hypotheses: ω ≠ E0+t, ω ≠ U+t−E0, ω ≠ 3t+U/2.
- **`sigEx_A`**: the same statement for A. Hypotheses: ω ≠ E0−t, ω ≠ U−t−E0,
  ω ≠ U/2−3t.
- `sig2dir` and `sig2x` are **imported** from `HubbardDimerSecondOrder.lean`,
  not restated.
- Closed forms, valid for all E:
  - `sig2dir_B_eq`: `sig2dir_B(E) = (U²/2)/(E − 3t − U/2)`
  - `sig2x_B_eq`: `sig2x_B(E) = −(U²/4)/(E − 3t − U/2)`
  - `sig2dir_A_eq` and `sig2x_A_eq`: the same with E + 3t − U/2
  - `sig2_B_eq` and `sig2_A_eq`: the sums
- `sig2x_eq_neg_half_dir`: SOX = −½ · direct, exactly.

**U-expansion at fixed ω.**

- **`sigEx_B_expansion`**: `|Σ_B(ω) − (U·½ + U²·1/(4(ω−3t)))| ≤ |U|³/(4(ω−3t)²)`
  for every U with 2|U| < |ω−3t| and |U| < |ω+t|. On that neighbourhood all
  pole and zero hypotheses are derived, not assumed. The proof uses
  `kEx_near: |k − 2t| ≤ |U|`.
- **`sigEx_A_expansion`**: `|Σ_A − (U/2 + U²/(4(ω+3t)))| ≤ |U|³/(4(ω+3t)²)` for
  2|U| < |ω−t| and |U| < |ω+3t|.
- `sigEx_B_U2_limit` and `sigEx_A_U2_limit`: (Σ_p − U/2)/U² → Σ2_p as U → 0.
  The limit is two-sided (`𝓝[≠] 0`).
- `sig2_B_U2_limit` and `sig2_A_U2_limit`: (sig2dir + sig2x)/U² → the same Σ2_p.
- So **Σ1 = ½ = HF**, and the exact U² coefficient equals the textbook
  second-order coefficient, including its spin factors.

**Negative results.** `sigEx_B_ne_direct_only` and `sigEx_A_ne_direct_only`:
for U ≠ 0, off the poles, Σ_exact ≠ HF + sig2dir. The direct (ring, GW-like)
term alone is wrong. Its U² coefficient is twice the exact one.

Helpers: `annR`, `creR`, `ann0_eq`, `ann2_eq`, `cre0_eq`, `cre2_eq`, `*_mulVec`,
`annO_mulVec`, `creO_mulVec`, `kEx_pos`, `kEx_rel`, `psi0_*`, `nrm_pos`,
`E0_eq`, `sum_ev1`, `sum_ev3`, `s2_weight`, `rem_bound`,
`tendsto_of_abs_le_mul`, `div_sq_bound`, `hopZ_symm`, `dblZ_symm`, `H_symm`,
`sum_sector`, `creO_psi0_sector`, `annO_psi0_sector`.

## Not proved / limitations

- **Spin-up only.** Spin-down G is the mirror image and is not formalised.
  Spin-mixed G_{↑↓} = 0 is not stated.
- The Lehmann form over the explicitly given eigenbases is the definition of G.
  Its connection to the resolvent is proved (`Gex_resolvent`, with uniqueness
  in the sector). There is no time-domain or Fourier derivation for the
  interacting G. That was done only for G0 and W in `HubbardDimerSigma.lean`.
  Nothing is at finite temperature.
- The explicit eigenvectors are supplied by hand and checked (eigen,
  orthogonal, complete). They are not computed by a certified diagonaliser.
- "Second order is exact" is specific to this two-site half-filled model with
  the restricted-HF reference. Nothing general about Wick or diagrammatics is
  proved. The textbook formula is shown to coincide with the exact Σ for this
  model. It is not derived from Wick's theorem.
- Real division is totalised. Every Σ statement carries explicit off-pole
  hypotheses, or a U-neighbourhood on which they are proved to hold.
- Out of scope, as before: the doc notes in `HubbardDimerSecondOrder.lean` and
  `.agent/handoffs/A3-dimer-2.md` say "the Σ2 formula ... is taken as a
  definition". That is now supplemented by this file. I did not edit them.
  Suggested note: "shown equal to the exact Σ − Σ_HF of the dimer in
  `HubbardDimerExactSigma.lean` (`sigEx_B`, `sigEx_A`)".

## Commands and results (worktree root)

```
python3 bgw/endpoint/a3_dimer/exact_sigma_dimer.py     # ALL OK (run BEFORE the proofs)
source scripts/env.sh
nice lake env lean GW/Endpoint/HubbardDimerExactSigma.lean   # clean, no warnings (~35 s)
nice lake build GW                                           # Build completed successfully (3m49s)
nice lake env lean GW/Audit.lean                             # 75 new lines, all [propext, Classical.choice, Quot.sound]
python3 -m unittest tests.test_endpoint_a3                   # Ran 7 tests, OK
grep -c "sorry\|admit\|native_decide\|^axiom" GW/Endpoint/HubbardDimerExactSigma.lean   # 0
```

I did not run `scripts/verify.sh` in full. Expected known failure:
`tests.test_provenance_committed` pins sha256 digests of `GW.lean` and
`GW/Audit.lean` in `bgw/weighted_audit/PROVENANCE-R6.txt`. Both files changed,
and the manifest is outside my write scope. The supervisor must re-sign it.

Numeric script `bgw/endpoint/a3_dimer/exact_sigma_dimer.py`. It is independent
of the Lean closed forms: it does numpy ED of the 16×16 JW Hamiltonian, then
Lehmann G, then Σ by inversion.

- Parity: G_BA, G_AB ≤ 1.5e-15.
- Lehmann G vs the closed form: ≤ 1.6e-13.
- Σ_exact − U/2 vs sig2dir + sig2x, with ERIs from an einsum of the site
  tensor: ≤ 9.3e-15 at 4 (t, U, ω) points, including U = 2.5.
- Finite differences at U = 0: dΣ/dU = ½ (2e-8) and ½ d²Σ/dU² = 1/(4(ω∓3t))
  (6e-9).
- Negative controls: direct-only gives a U² coefficient 2× the exact one.
  An exchange factor of −2 breaks the identity by 5.9e-2.

## Hand mutations (scratch copies, `lake env lean`; not committed)

| Mutation | Result |
| --- | --- |
| A. exchange spin factor −1 → −2 (local copy of `sig2x`) | `sig2x_B_eq` and `sig2x_A_eq` fail |
| A'. same, and the closed-form lemmas restated to the mutated values | `sig2_B_eq`, `sig2_A_eq` and `sig2x_eq_neg_half_dir` fail |
| B. direct spin factor 2 → 1 | `sig2dir_B_eq` and `sig2dir_A_eq` fail. With restated closed forms (B'), `sig2_*_eq` and `sig2x_eq_neg_half_dir` fail |
| B2. drop exchange (factor 0, GW-like) | `sig2x_*_eq` fail. Also refuted positively by `sigEx_*_ne_direct_only` |
| C. Lehmann hole denominator `ω − (E − E_m)` → `ω − (E_m − E)` | `Gex_BB`, `Gex_AA` and `Gex_resolvent` fail |
| D. N = 3 energies swapped (U±t) | `ev3_eigen`, `Gex_BB` and `Gex_AA` fail |

The key theorems `sigEx_B` and `sigEx_A` go through the stated closed-form
lemmas. A wrong spin factor is therefore caught at the first lemma whose
statement fixes the value (A, A', B, B'). The identity itself is false under
those mutations: see the numeric control, and `sigEx_*_ne_direct_only` for
B2. These mutations were not added to `mutate_lean.py`.

## Failed attempts / notes

- `simp` on `fin_cases` goals over `![...]` literals sometimes leaves
  `True ∨ …` or `x = y ∨ s2 = 0`. `first | ring1 | exact Or.inl (by ring)` fixes
  this. A `first | ...` alternative list split over lines with a leading `|`
  did not parse as I expected. Put each alternative on its own line after
  `first`.
- `field_simp` would not clear the denominators when a hypothesis was stated as
  `ω − (3t + U/2) ≠ 0` and it normalised the goal to `ω*2 − (…)`. I used
  explicit `div_add_div`, `div_eq_div_iff` and `mul_div_cancel_right₀` instead.
- For identities modulo r² = U²+16t², or k² + kU = 4t², I computed the
  `linear_combination` coefficients by polynomial division in sympy. The
  helper is in the scratchpad, not the repo.
- This Mathlib has no `Matrix.mulVec_sum` or `dotProduct_sum`, and
  `Finset.sum_div` is not imported. I expanded `Fin.sum_univ_four` instead.

## Commits

- 694a841: WIP checkpoint (G, Σ, expansion)
- the resolvent section
- 4296ca8: header, `GW.lean` import, Audit
- the final commit adds this handoff and the script negative control

## Next action

Supervisor review. Re-sign `PROVENANCE-R6.txt`. Optionally:

- update the "taken as a definition" notes (see above)
- add `exact_sigma_dimer.py` to a gate
- add the spin-down mirror
