# C3/C4 R1: technical sign-off and next-task authorization

Date: 2026-09-16. Reviewer: ChatGPT (AI-assisted technical review).
Reviewed repair: `36c33b95859a2220dfb25eb7d21f9f6ac9c834e8`.
Current-main baseline observed: `bbf6a6c44800f4c54f43b8757fac30ea267fdbe3`.

**Decision: ACCEPT_REPAIR_FOR_INTERNAL_PROGRESSION.** Retain C3.1 as conditional
first-order pairing/Hartree–Fock algebra and C4.1 as a specified finite static
response/formal-screening prototype. The original general C3 and end-to-end C4
objectives remain open. This does not certify Gaussian integration, the general
skeleton theorem, electronic GW self-energy, or BerkeleyGW as a whole.

**Owner-authorized next task: BGW-M1 only**, as specified in
`../tasks/BGW-M1.md`. The owner requested sign-off and continuation if warranted;
this record supplies that scoped approval. No further activation question is
needed when Claude receives the task. Nothing here launches a process by itself.

## Verification supporting the decision

Fresh GitHub reads confirm that PR 11 is already merged. The current main contains
the repair commit as an ancestor; its differences from that commit are added review
files, not further changes to the scientific implementation. The earlier quoted
“all PRs unmerged / main pre-C2A” status is therefore stale. The reviewer did not
perform any merge, retargeting, branch deletion or local-worktree inspection.

Inspected the repair diff and the new definitions/proofs:

- `electronic_kernel_eq_AL`, `geoP_electronic_eq_PL`, and
  `electronicW_eq_classical_W` prove the conditional signed/scaled identification.
  `chi0_eq_neg_half_bubble_witness` supplies admissible noncommuting data. This
  repairs the overstrong non-transferability interpretation without deleting the
  true diagonal-sign lemmas.
- `select_length`, `pairingsAux_fuel`, `pairings_cons`, and `wickMoment_cons`
  supply the general recursion previously mentioned but absent. The separate
  pairing/involution correspondence remains arity-six only.
- The early-truncation test now compares with the required-order partial sum and
  finite residual, not the unrelated exact static solution.
- Source, pairing-count and impossible-Hadamard-fixture corrections are recorded.
  Formal coefficients are no longer presented as a convergent static solver.

Executed fresh targeted exact Python checks using reference bytes matched to:

| Reference | Git blob SHA |
|---|---|
| `ll/electronic_reference.py` | `7506e8aadcde818a2b9e9a2a9a7d6a5d22de9e41` |
| `ll/wick_reference.py` | `05af7dab5db84ea933521edd37ae0f53735ea01d` |

Observed: signed/scaled kernel equality on the admissible noncommuting witness;
coefficient agreement at orders 0..6; premature truncation differs from the correct
order while replacing the mutant with the unmutated target is NOT detected as an
error; different orders have different finite residuals; det(v chi0)=20 on the
first fixture while its exact static solve exists; 94 recursive-versus-enumerated
Wick moment comparisons agree, including empty/odd lists and repeated indices.
These are reviewer-input calculations, not newly generated Lean output or a run
of the entire submitted test suite.

**Not independently executed:** Lean/Lake, candidate executables, the full gate,
BerkeleyGW, or the worker's claimed six-worktree cleanliness check. Lean/Lake are
absent in the reviewer container; a fresh DNS probe failed. The commit's reported
363 scientific / 14 workflow tests and 646 exhaustive audits remain worker evidence.
BGW-M1 must freshly build the project baseline rather than inherit those claims.

## Remaining boundaries, not another repair-only round

Some historical PR prose and a local diagonal-lemma comment still read too broadly.
This sign-off and the repaired conditional equalities govern the interpretation:
opposite signs rule out a naive general equality, not a properly signed/scaled
physical correspondence. The GPP result is a scalar static-matching identity;
it still does not connect to the frequency convolution or `sigmaChecked`.
Do not spend a new milestone policing old wording or adding caveat-only tests.

The useful next result is a production interface comparison. No more isolated
formula families are authorized as a substitute. A Python-only comparison would
be useful preliminary evidence, but BGW-M1's complete success also requires a
Lean-checked connection for the represented finite input, as its brief specifies.

## Signature and authority

Technical sign-off: **ChatGPT, 2026-09-16**, at the owner's request.
This is not a human-maintainer signature, DCO attestation, cryptographic signature,
or an assertion of independently repeated kernel verification. Human ownership
and destination-community rules remain required for any eventual upstream work.
The approval permits one bounded downstream experiment, not publication, another
merge, stack cleanup, upstream contact, paid resource use, or automatic continuation.
