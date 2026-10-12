# Adversarial core-claim review of PR 28

Repository: `MichealWangYZ/physics_lean_bgw`  
Reviewed revision: `d783e188211bcaa477171b98cc96853badf334e6`  
Assignment: `.agent/tasks/REVIEW-28.md`, read from `review/pr28-brief`  
Review date: October 2, 2026

## Decision

Publish as a scoped formalization and numerical-certification research artifact after correcting the scientific descriptions identified below. Do not use the unqualified claim **“we formally verified the core physics of BerkeleyGW.”**

Claim 1 (the specified finite calculation and the reported 5.21 micro-eV production comparison) is supported, subject to the already declared input/transcription/production trust boundaries and the replay limitation below. Claim 2 is not established as an end-to-end statement about one physically identified finite fermion system instantiated on the certified run. Its conditional algebraic and Fourier-transform results remain substantial and useful.

This rejection does not require proving that the GW approximation is exact, that silicon is experimentally described by the EPM, or that numerical cutoffs are converged. Approximate physical models can legitimately be formally verified. The issue is what objects are identified by the actual theorem statements and whether their hypotheses apply.

## Execution and evidence boundary

This was a read-only source review through the GitHub connector. It examined the review brief, PR metadata, canonical endpoint and bridge documentation, the relevant bridge definitions and theorem statements/proofs, the endpoint specification and interval evaluator, the final S3 numerical statement, and the axiom-audit implementation. It was not an exhaustive audit of every imported theorem.

No local checkout or Lean toolchain was available. Git access failed, and the official BerkeleyGW source archive could not be downloaded in this environment. Consequently this review did **not** replay `lake build`, `GWKernelData`, the full test suite, a BerkeleyGW executable, or an independent pristine-Fortran-to-spec comparison. The recorded full-gate PASS remains author-supplied evidence, not a fresh PASS issued by this reviewer.

The accompanying `counterexamples.py` was executed. It independently checks rational arithmetic witnesses reconstructed from the reviewed definitions. It is not a Lean witness, a repository mutation test, or a rerun of the numerical pipeline.

## Claim 1: what the numerical certificate actually supports

Location: `GW/Endpoint/Kernel/Data/S3Check.lean:1010–1062`, especially `o1_enclosure`; `bgw/endpoint/data/cert_o1.json:1–90`; `docs/ENDPOINT.md` E1 result.

The theorem is about the real-valued `Sig.O1 gl stX stL Etrue vb oq`, not a detached constant. Its displayed interval is the exact dyadic interval

```
[8880811588953599 / 2^59, 8880812351936001 / 2^59] eV.
```

The epsilon input is assembled from the inverses of the explicitly defined static-RPA matrices. The S3 statement itself assumes the Coulomb boxes; the separate Coulomb development is intended to discharge those hypotheses. The project also supplies an irreducible-input/unfolding endpoint. Those stronger roots were not independently replayed here.

Taking the documented production O1 as 0.015400547 eV gives a maximum distance from the displayed interval of approximately 5.2066726482 micro-eV. Even allowing an additional 1 neV for a difference of two energies printed to 1 neV, the distance is at most 5.2076726482 micro-eV, below 5.21 micro-eV. This calculation was checked with exact rational arithmetic.

The distinction is important: the Lean theorem certifies an exact-real specification on fixed data; the production comparison is a separate measured/certified calculation with its own trusted implementation. The specification uses exact mini-BZ Coulomb integrals whereas the production run uses Monte Carlo estimates. No theorem inspected here proves the Fortran executable correct on every input or proves that its floating-point execution stays within 5.21 micro-eV for arbitrary runs.

**Verdict: holds with the stated trust boundary; not independently replayed in this review.** No counterexample to the inspected numerical statement was found.

## F1 — BLOCKER for the broad physics claim: no instantiated common-system bridge

Locations: `GW/Bridge/EpsCompare.lean:180–230`; `GW/Bridge/EpsQ0Sigma.lean:230–280`; `GW/Bridge/EpsBloch.lean:1–160`; `GW/Bridge/FreqIntegral.lean:1–175`; `GW/Endpoint/ManyBody/GWSecond.lean:1–170`.

The named composed theorem takes `gl`, `st`, and `bs : Nat -> EpsBlock kappa` independently. The screening system is `(bs iq).B`; the propagator and pair densities used in the self-energy are built from `gl` and `st`. `EpsBlock.OK` checks properties internal to each screening block. Its fields do not identify that block's orbitals, energies, occupations, density, geometry, and interaction with the ones used by the self-energy. In particular, there is no common-system compatibility field in the displayed composed theorem.

The separate many-body GW development does use the same `epsilon`, `v`, and `O` in its second-order construction. Importing that module, and proving agreement with its scalar `G0t` formula, does not by itself instantiate all the later screening, self-energy, and density inputs with that common system.

An adversarial interface test is to keep `bs` fixed and change self-energy energies in `st`, away from the branch boundaries so the mode conditions persist. The theorem's algebraic comparison still describes a self-energy built with the old screening and the new propagator. That does not establish that both were derived from the same chosen mean-field system. This is a statement about the interface; no compiled Lean counterexample is claimed.

There is a second applicability issue. The bridge is conditional on `hC`, wing conditions, `hX`, and `ModeOK`. The documentation explicitly says important versions of these conditions fail on the production inputs. That is an honest disclosure, not a newly discovered bug. But a true implication with unfulfilled premises cannot be used as an instantiated proof of the stronger run-specific conclusion. Characterizing the excluded cases separately does not automatically supply one composed, run-specific theorem or a combined error bound.

**Effect:** the inspected bridge supports conditional formal-model identities, not the advertised end-to-end finite-fermion-system-to-run claim.

**Minimum release correction:** state the conditional scope and the trusted cross-system identifications explicitly. Do not say that the hypotheses have been discharged on the certified run. Supporting the stronger claim would require a compatible common-system construction and applicable bridge theorem, not merely more tests of the existing identity.

## F2 — MAJOR scope gap: the physical oscillator-strength formula is supplied, not derived by the displayed f-sum theorem

Locations: `GW/Bridge/Bloch.lean:1–120` (`OmT`, `blochSys`); `GW/Bridge/GPPModel.lean:103–119` (`fsum_moment`); `GW/Endpoint/Kernel/SigmaSpec.lean:120–195` (`wpsq`, `factW`, `Om2S`).

The GPP development proves meaningful facts: static matching, the high-frequency tail, existence/uniqueness of a positive pole under the specified conditions, and the frequency-transform algebra. However, its `fsum_moment` is the identity

```
-pi * (O / (2*w)) * w = -(pi/2) * O,  w != 0.
```

That theorem establishes a moment once the oscillator strength O is supplied. It is not a derivation that the density response of the same underlying fermion Hamiltonian has the oscillator strength used by `OmT`.

`OmT` uses `factW`, `rhoF`, `dotB`, and `vec` from the endpoint specification. Reusing mathematical helpers is not inherently circular. The precise missing independence is the physical identification of their combination with the system's response moment. A common change to a shared normalization helper can change both sides while leaving their algebraic correspondence intact.

This review has **not** shown that the actual 16*pi normalization or the HL formula in the repository is wrong. The finding is that the displayed formal evidence does not independently verify that part of the physical identification.

**Minimum release correction:** say “formal properties and consequences of the specified HL ansatz, conditional on its oscillator-strength prescription,” rather than “the physical f-sum rule was derived from the general fermion system.” A stronger claim needs an independently anchored identification of that prescription under appropriate Hamiltonian/basis assumptions.

## F3 — MAJOR: CompleteK is not a tolerance certificate for the actual missing finite-basis eigenvectors

Locations: `GW/Bridge/Cor.lean:350–520` (`Compl`, `CompleteK`, `tailK_eq`); `bgw/bridge_cor/cor.py:210–245` (`kappa`); `docs/BRIDGE.md:510–650` (BRIDGE-COR).

The new condition is exact:

```
R^T R + C^T C = kappa I.
```

It allows an arbitrary number of real completion rows. It is not the condition that the actual finite-basis eigenvector matrix is approximately orthonormal.

The Python routine chooses kappa as an outward-padded Gershgorin bound. If kappa is strictly greater than the largest eigenvalue of R^T R, the defect `kappa I - R^T R` is positive definite and has rank N. Therefore any exact completion factor C needs at least N rows. A physical completion of m already computed eigenvectors in an N-dimensional basis has only N-m missing rows, whose Gram matrix has rank at most N-m.

A two-dimensional exact witness is

```
R = [1, 0], kappa = 1 + epsilon, epsilon > 0,
kappa I - R^T R = diag(epsilon, 1+epsilon).
```

The right-hand side has rank two. One missing physical eigenvector contributes an outer product of rank at most one. This mismatch persists however tiny epsilon is. The accompanying script verifies the positive determinant with epsilon = 2^-40.

Thus the repair gives a valid abstract scaled-frame completion problem, but does not by itself provide applicability to the actual omitted eigenvectors of the original finite Hamiltonian. The existing consistency theorem `sigAall_of_state` does not fix this: it identifies expressions for an appended data set, but does not prove that its rows satisfy `CompleteK` at the selected kappa.

The documentation does contain an important disclaimer that the table is for a completion, not a physical error bar. That disclaimer should control every stronger description, including “exact finite-basis all-band value.” This finding is not a disproof of the reported -3.8 meV diagnostic or its independent BerkeleyGW cross-check, and it does not invalidate the 18-band S3 certificate.

**Minimum release correction:** consistently label the theorem as a conditional enclosure for an abstract `CompleteK` completion. Do not describe kappa as having certified the true finite-basis omitted bands. A genuine tolerance repair would need a bound on the closure defect of the relevant eigenvectors and propagation of that defect, or a certified nearby orthonormal system with an explicit input-perturbation bound.

## F4 — MAJOR: “all bands, static remainder zero” is stronger than SigAall and the closure hypotheses prove

Locations: `GW/Bridge/Cor.lean:350–520` (`SigAall`) and `:640–820` (`sigA_split`, `sigAall_of_state`); `GW/Endpoint/Kernel/SigmaSpec.lean:195–302` (`ACq`, `CSq`, `SigA`); `docs/BRIDGE.md:510–650`.

`SigAall` is `SigA` plus omitted-band contributions of `ACq + Pq`. `sigAall_of_state` identifies it with the larger state's `SigA`. Neither statement alone says that the remaining static remainder is zero.

There are two independent obstructions. With scaled closure and otherwise matching geometry, the exact static-density term remains proportional to one while the completed band sum is proportional to kappa. For one normalized channel with I_eps = I, the residual is

```
COR_all = -I/4 + kappa*I/4 = (kappa-1)*I/4,
```

not zero for kappa != 1.

Even at kappa = 1, a complete finite wavefunction sphere need not be closed under the plane-wave shifts used by the density identity. A minimal example has WFN sphere {0}, its complete orbital c(0)=1, epsilon sphere {0,1}, unit Coulomb weights, and I_eps diagonal (0,1/2), so the supplied inverse dielectric matrix is nonsingular. Pair densities are M(0)=1 and M(1)=0 but rho_aa(0)=1. Then CS=-1/8 and the complete finite-band AC sum is zero. The static remainder is still -1/8. The script checks this rational witness.

The earlier complete-band bridge correctly requires shift closure and Gch coverage. The BRIDGE-COR prose should not drop those requirements when interpreting its different theorem. Indeed the same documentation reports a 4–7 meV shift-closure defect in the static quantities.

**Effect:** the conditional inequalities can remain true while the description of the target quantity is wrong. They enclose the defined extended specification, not automatically an all-band expression with the static remainder removed.

**Minimum release correction:** retain and name the residual closure/static term, or state the extra conditions under which it vanishes. Correct the “static remainder 0” descriptions in both the Lean documentation and BRIDGE-COR presentation. A near-zero estimate is not an exact cancellation theorem.

## What this review does not use as a rejection reason

The disclosed band-count sign change, non-cubic RHO, exact occupied x=w discrepancy, and the GPP discontinuity are not presented as new discoveries. The question is whether they are described with the right evidence status and whether the formal statements are applied within their domains. No additional convergence campaign, material-accuracy proof, code cleanup, or theorem-count target is required by this review.

## Suggested public wording

> We formalized selected mathematical components of the real-valued G0W0/Hybertsen–Louie GPP workflow in Lean and developed kernel-checkable numerical certificates for a fixed BerkeleyGW 4.0 Si-EPM specification. The project contains conditional theory-to-specification identities and documents the assumptions, implementation conventions, and exceptional cases at their boundaries. For the pinned calculation, the recorded production O1 differs from the certified specification enclosure by at most 5.21 micro-eV. Binary decoding/export, source-to-specification correspondence, production execution, and the remaining physical identifications are not all end-to-end formally verified.

A suitable title is **“Formalized G0W0/GPP components and certified numerical evaluation of a BerkeleyGW Si-EPM benchmark.”**

The README currently describes the old scalar demo and should be replaced with an accurate scope summary linking the canonical endpoint and bridge documents. This is a claim-presentation correction, not a request for more scientific scope.

**Bottom line:** the formalization is more substantial than a rerun or a collection of renamed equations. Its strongest numerical result survives this source review. Its proof boundaries do not support the proposed broad headline, and the CompleteK/static-remainder descriptions need correction before that material is presented as a completed physical bridge.
