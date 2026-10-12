import GW.Endpoint.Kernel.Data.CoulTab
import GW.Endpoint.Kernel.Data.RIrr

/-!
Headline statements of the certified numerical evaluation (target `GWKernelData`).

Each theorem below composes two existing kernel-checked results and adds no new
mathematics:

* the irreducible-data theorems `U.o1_enclosure_irr`, `U.o1_pos_irr`, `R.roots_exist_irr`
  and `R.o1_fullQP_irr`. Their Σ and ε inputs are computed in Lean, by the symmetry
  unfolding, from the irreducible WFN / WFNq / WFN_inner literals (`U.glI`, `U.stXI`,
  `U.stLI`, `U.EIrr`). Those theorems keep the Coulomb-box hypotheses `VbHyp`;
* `Coul.vb_hyp` and `Coul.oq_hyp`, which discharge those boxes for the exact mini-BZ
  averages `vbTrue` and `oqTrue` (Lebesgue integrals over the Wigner-Seitz cell of the
  q-grid).

The results carry no Coulomb-box (`VbHyp`) hypothesis. The full-QP statement is about the
unique roots in the two brackets (`roots_exist_irr_unconditional`); that these are the
principal roots is a Python certificate. What they are about is the Lean specification
(`SigmaSpec`, `EpsSpec`, `RootSpec`) evaluated on literals that `kernel_export.py` decoded
from the run files. The following remain trusted, not proved:
* the decoding and export of those literals;
* the correspondence between the BerkeleyGW Fortran and the specification;
* the production execution.

`o1_pos_irr_unconditional` compares X and L only. That the conduction-band minimum among
ALL sampled k-points (Γ included) is at L is a Python interval result
(`cert_o1.json`, `CBM_certainly_at_L`), not a Lean theorem.

Post-review R2 (2026-10-03).
-/

namespace GW.Endpoint.Kernel.Headline

open GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps GW.Endpoint.Kernel.Sig GW.Endpoint.Kernel.QP
  GW.Endpoint.Kernel.S3 GW.Endpoint.Kernel.U GW.Endpoint.Kernel.R GW.Endpoint.Coulomb Set

/-- **O1 of spec A from the irreducible data, unconditional.** -/
theorem o1_enclosure_irr_unconditional :
    O1 glI stXI stLI EIrr vbTrue oqTrue ∈
      Icc ((8880811588953599 : ℝ) / 2 ^ 59) ((8880812351936001 : ℝ) / 2 ^ 59) :=
  U.o1_enclosure_irr vbTrue oqTrue Coul.vb_hyp Coul.oq_hyp

/-- `Eqp1(X) > Eqp1(L)` for spec A, from the irreducible data, unconditional. The theorem
compares X and L only. -/
theorem o1_pos_irr_unconditional : 0 < O1 glI stXI stLI EIrr vbTrue oqTrue :=
  U.o1_pos_irr vbTrue oqTrue Coul.vb_hyp Coul.oq_hyp

/-- The two full-QP roots exist and are unique in their brackets (irreducible data,
unconditional, both `cv` conventions). -/
theorem roots_exist_irr_unconditional (cv : Bool) :
    (∃! E, E ∈ Icc ((CaX0 : ℝ) / (10 ^ 8 * 2 ^ 92 : ℝ)) ((CbX0 : ℝ) / (10 ^ 8 * 2 ^ 92 : ℝ)) ∧
        fQP glI EIrr vbTrue oqTrue stXI cv E = 0) ∧
    (∃! E, E ∈ Icc ((CaL0 : ℝ) / (10 ^ 8 * 2 ^ 92 : ℝ)) ((CbL0 : ℝ) / (10 ^ 8 * 2 ^ 92 : ℝ)) ∧
        fQP glI EIrr vbTrue oqTrue stLI cv E = 0) :=
  R.roots_exist_irr vbTrue oqTrue Coul.vb_hyp Coul.oq_hyp cv

/-- **The full-QP O1 of spec A from the irreducible data, unconditional**: for the unique
roots in the two brackets (`roots_exist_irr_unconditional`), `EX - EL` lies in
`[68.9856742, 68.9856744]` meV. That these brackets hold the principal roots (largest
renormalisation) is a Python certificate, not part of the theorem. -/
theorem o1_fullQP_irr_unconditional (cv : Bool) (EX EL : ℝ)
    (hX : EX ∈ Icc ((CaX0 : ℝ) / (10 ^ 8 * 2 ^ 92 : ℝ)) ((CbX0 : ℝ) / (10 ^ 8 * 2 ^ 92 : ℝ)) ∧
      fQP glI EIrr vbTrue oqTrue stXI cv EX = 0)
    (hL : EL ∈ Icc ((CaL0 : ℝ) / (10 ^ 8 * 2 ^ 92 : ℝ)) ((CbL0 : ℝ) / (10 ^ 8 * 2 ^ 92 : ℝ)) ∧
      fQP glI EIrr vbTrue oqTrue stLI cv EL = 0) :
    EX - EL ∈ Icc ((689856742 : ℝ) / 10 ^ 10) ((689856744 : ℝ) / 10 ^ 10) ∧ 0 < EX - EL :=
  R.o1_fullQP_irr vbTrue oqTrue Coul.vb_hyp Coul.oq_hyp cv EX EL hX hL

end GW.Endpoint.Kernel.Headline

#print axioms GW.Endpoint.Kernel.Headline.o1_enclosure_irr_unconditional
#print axioms GW.Endpoint.Kernel.Headline.o1_pos_irr_unconditional
#print axioms GW.Endpoint.Kernel.Headline.roots_exist_irr_unconditional
#print axioms GW.Endpoint.Kernel.Headline.o1_fullQP_irr_unconditional
