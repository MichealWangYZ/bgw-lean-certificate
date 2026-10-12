# Source Correspondence — ARCHIVED (2026-10-01): Specification.md v0.1 demo lineage, superseded by GW.Endpoint.Kernel.SigmaSpec and GW.Bridge; kept, not extended, outside the fast gate. See docs/CODEMAP.md.

## Paper Evidence

Source: Deslippe et al., [BerkeleyGW methods paper, arXiv:1111.4429](https://arxiv.org/pdf/1111.4429),
printed pp. 18-19, Eqs. 21, 22, and 26 (PDF pages 18-19, one-based).
Checked September 10, 2026.

Eqs. 21-22 give occupied-state screened exchange and all-state Coulomb hole.
Eq. 26 combines their factors near the occupied positive pole. Our scalar
restriction sets `x = E - E_inner`, `w = w_tilde > 0`, and absorbs matrix
factors, Coulomb factors, and `Omega^2*(1-i*tan(phi))` into a real `A`.
The static delta term is separated into the external `sigmaX`.

The paper also describes small-factor cutoffs, complex quantities, and additional
singular cases interpreted through full-frequency integrals. This demo implements
none of those policies. Its rejection of the surviving denominators is a domain
restriction of the scalar model, not a claim about all BerkeleyGW branches.

## What Is Verified Separately

| Link | Evidence | Status |
| --- | --- | --- |
| Scalar identity to Lean theorem | Explicit formulas and hypotheses in S1 | Kernel checked |
| Exact finite evaluator to real model | Cast and checked-evaluation theorems in S2 | Kernel checked |
| Synthetic fixture to evaluator output | Independent exact oracle and Lean run | Passed |
| Scalar model to paper | Restricted reading above | Documented interpretation |
| Scalar model to production code | BerkeleyGW 4.0 archive `1a85b03b...`, CPU GPP positive-real-mode expressions at full occupation | Hand mapping documented; exact-real algebra kernel checked |
| Genuine local kernel outputs to S1 | Si-EPM export: 48 nonzero modes and 48 separate zero placeholders | Checked numerically; fresh-run reproduction passed on this host |
| Full unitful coefficients to material self-energy | Matrix and outer weights not exported; no full scalar-term conversion | Pending |
| GW approximation to experiment | Outside this demo | Not claimed |

## BerkeleyGW Comparison Boundary

The source pin, path, units, occupation rules, cutoffs, capture locations, and
regeneration recipe are recorded in [BerkeleyGW 4.0 GPP](BERKELEYGW_4.0_GPP.md).
The original source is identified by archive SHA-256, not a claimed VCS commit.
The export comes from the Si empirical-pseudopotential test, not experiment.

The correspondence covers nonsingular positive-real-mode branch expressions
at full occupation, before extra clamps; the unoccupied formula is mapped
algebraically but has no unoccupied run export. Fractional occupation, complex
modes, GPU paths, and omitted cutoff policies remain outside the claim.
S1's continuous extension at an exact pole is not the value of the transcribed
Fortran expression there. Numerical agreement is not a proof of BerkeleyGW.

Threading-sensitive upstream inputs are a measured reproducibility limit.
The accepted comparison is exact text-output reproduction on this host, not a
portable byte-identity or physics claim. See section 7.8 of the source note.

## Requirements for Further Comparisons

Record source repository, immutable revision, file/function and branch, input
units and precision, occupancy, weights, cutoffs, broadening, dielectric mode,
and static contribution. Export an actual tiny intermediate sample; retain its
checksum and generating command. Explain any conversion into scalar terms.
Compare individual terms before totals. Do not fabricate a revision, export,
benchmark, or agreement tolerance when these inputs are unavailable.
