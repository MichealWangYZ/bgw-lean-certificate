/-
Axiom audit for every theorem exported by this project (T-001 section D,
Specification.md S5).

No proofs are defined in this file: it only runs `#print axioms` on each
exported theorem. The allowed foundational dependencies are `propext`,
`Classical.choice`, and `Quot.sound`. Any other axiom, any `sorry`, and any
`native_decide` shortcut fails acceptance.

Check with:  lake env lean GW/Audit.lean

Required named theorems of Specification.md S5, in this project:

| S5 requirement                       | Theorem                                     |
| ------------------------------------ | ------------------------------------------- |
| algebraic cancellation               | `GW.GPP.rawOccupied_eq_occupiedTerm`        |
| extension value                      | `GW.GPP.occupiedTerm_at_pole`               |
| continuity                           | `GW.GPP.continuousAt_occupiedTerm`          |
| punctured limit                      | `GW.GPP.tendsto_rawOccupied_nhdsWithin_ne`  |
| rational-to-real term correspondence | `GW.GPP.Term.valueUnchecked_cast`           |
| rational-to-real finite sum          | `GW.GPP.Data.sigmaUnchecked_cast`           |
| checked evaluation soundness         | `GW.GPP.Data.sigmaChecked_ok_eq_real`       |
| checked evaluation domain validity   | `GW.GPP.Data.sigmaChecked_ok_valid`         |

Additional theorems relating the S1 branches to the transcribed BerkeleyGW 4.0
`sigma_gpp_cpu` arithmetic are audited at the end of this file. They are real-
number identities about hand-transcribed formulas, not a verification of the
Fortran source; see `docs/BERKELEYGW_4.0_GPP.md`.

`GW/GPP/PoleDomain.lean` adds domain-carrying types. It is purely additive: no
theorem listed above was changed, and its own theorems are audited at the end of
this file.

`Main.lean` declares no theorems. `GW.lean` is an import-only root module.
-/
import GW


/-! ## `GW/GPP/PoleCancellation.lean` -- S1: algebraic cancellation and removable singularity -/

#print axioms GW.GPP.raw_eq_occupied_field
#print axioms GW.GPP.rawOccupied_eq_occupiedTerm
#print axioms GW.GPP.pole_ne_pole
#print axioms GW.GPP.occupiedTerm_at_pole
#print axioms GW.GPP.occupied_denom_ne_zero_at_pole
#print axioms GW.GPP.continuousAt_occupiedTerm
#print axioms GW.GPP.rawOccupied_eventuallyEq_occupiedTerm
#print axioms GW.GPP.tendsto_rawOccupied_nhdsWithin_ne
#print axioms GW.GPP.empty_denom_zero_at_pole

/-! ## `GW/GPP/FiniteSelfEnergy.lean` -- S2: exact finite evaluator and real model -/

#print axioms GW.GPP.Term.denom_cast
#print axioms GW.GPP.Term.valueUnchecked_cast
#print axioms GW.GPP.list_sum_valueUnchecked_cast
#print axioms GW.GPP.Data.sigmaUnchecked_cast
#print axioms GW.GPP.Term.check_ok_omega_pos
#print axioms GW.GPP.Term.check_ok_denom_ne_zero
#print axioms GW.GPP.Term.check_ok_eq
#print axioms GW.GPP.checkedValues_ok_valid
#print axioms GW.GPP.checkedValues_ok_eq
#print axioms GW.GPP.Data.sigmaChecked_ok_valid
#print axioms GW.GPP.Data.sigmaChecked_ok_eq_unchecked
#print axioms GW.GPP.Data.sigmaChecked_ok_eq_real
#print axioms GW.GPP.Data.sigmaChecked_nil
#print axioms GW.GPP.Term.check_occupied_at_pole

/-! ## `GW/Examples.lean` -- S3: synthetic fixture sample facts -/

#print axioms GW.Examples.term1_value
#print axioms GW.Examples.term2_value
#print axioms GW.Examples.term3_value
#print axioms GW.Examples.fixtureTermValues_eq
#print axioms GW.Examples.fixture_sigma
#print axioms GW.Examples.emptyFixture_sigma
#print axioms GW.Examples.term3_at_removable_pole
#print axioms GW.Examples.probe_at_pole
#print axioms GW.Examples.probe_at_pole_general
#print axioms GW.Examples.reordered_sigma
#print axioms GW.Examples.duplicated_sigma
#print axioms GW.Examples.reject_zero_omega
#print axioms GW.Examples.reject_negative_omega
#print axioms GW.Examples.reject_occupied_pole
#print axioms GW.Examples.reject_empty_pole
#print axioms GW.Examples.reject_zero_coefficient_zero_omega
#print axioms GW.Examples.reject_zero_coefficient_pole
#print axioms GW.Examples.reject_model_with_invalid_term
#print axioms GW.Examples.mutant_branch_ne
#print axioms GW.Examples.mutant_coefficient_ne
#print axioms GW.Examples.mutant_sign_ne
#print axioms GW.Examples.mutant_missing_term_ne
#print axioms GW.Examples.mutant_static_ne
#print axioms GW.Examples.fixture_sigmaReal

/-! ## `GW/GPP/BerkeleyGWMap.lean` -- BerkeleyGW 4.0 `sigma_gpp_cpu` correspondence -/

#print axioms GW.GPP.BGW4.ch_term_eq
#print axioms GW.GPP.BGW4.occupiedGeneric_eq_rawOccupied
#print axioms GW.GPP.BGW4.occupiedNearPole_eq_occupiedTerm
#print axioms GW.GPP.BGW4.emptyBranch_eq_emptyTerm
#print axioms GW.GPP.BGW4.branches_agree
#print axioms GW.GPP.BGW4.tendsto_occupiedGeneric
#print axioms GW.GPP.BGW4.occupiedNearPole_limit_value
#print axioms GW.GPP.BGW4.exact_pole_transcription_not_extension
#print axioms GW.GPP.BGW4.delwComment_eq
#print axioms GW.GPP.BGW4.commentFormula_eq_occupiedTerm
#print axioms GW.GPP.BGW4.branch_mismatch
#print axioms GW.GPP.BGW4.branch_mismatch_zero_of_occ_one
#print axioms GW.GPP.BGW4.branch_mismatch_nonzero_at_half_occupation

/-! ## `GW/GPP/PoleDomain.lean` -- additive domain-carrying denominator types

These theorems restate nothing: each is derived from the theorems above, and
`GW.GPP.rawOccupied_eq_occupiedTerm_of_bundled` derives the original unbundled
cancellation back out of the bundled one. -/

#print axioms GW.GPP.PoleEnergy.ofPos_w
#print axioms GW.GPP.PoleEnergy.sq_pos
#print axioms GW.GPP.PoleEnergy.pole_ne_negPole
#print axioms GW.GPP.PoleEnergy.denom_ne_zero_at_pole
#print axioms GW.GPP.PoleEnergy.merged_at_pole
#print axioms GW.GPP.PoleEnergy.continuousAt_merged
#print axioms GW.GPP.PoleEnergy.tendsto_raw
#print axioms GW.GPP.PoleEnergy.ch_term_eq
#print axioms GW.GPP.PoleEnergy.emptyBranch_eq
#print axioms GW.GPP.PoleEnergy.occupiedGeneric_eq_raw
#print axioms GW.GPP.PoleEnergy.eventually_admissible
#print axioms GW.GPP.PoleEnergy.eventuallyEq_raw_merged
#print axioms GW.GPP.AdmissiblePole.mk'_x
#print axioms GW.GPP.AdmissiblePole.mk'_w
#print axioms GW.GPP.AdmissiblePole.x_sub_w_ne_zero
#print axioms GW.GPP.AdmissiblePole.x_add_w_ne_zero
#print axioms GW.GPP.AdmissiblePole.raw_denom_ne_zero
#print axioms GW.GPP.AdmissiblePole.sx_denom_ne_zero
#print axioms GW.GPP.AdmissiblePole.merged_denom_ne_zero
#print axioms GW.GPP.AdmissiblePole.raw_eq
#print axioms GW.GPP.AdmissiblePole.merged_eq
#print axioms GW.GPP.AdmissiblePole.emptyValue_eq
#print axioms GW.GPP.AdmissiblePole.raw_eq_merged
#print axioms GW.GPP.AdmissiblePole.merged_eq_zero_iff
#print axioms GW.GPP.AdmissiblePole.merged_ne_zero
#print axioms GW.GPP.AdmissiblePole.branches_agree
#print axioms GW.GPP.AdmissiblePole.occupiedNearPole_eq_merged
#print axioms GW.GPP.AdmissiblePole.commentFormula_eq_merged
#print axioms GW.GPP.AdmissiblePole.branch_mismatch
#print axioms GW.GPP.AdmissiblePole.eta
#print axioms GW.GPP.AdmissiblePole.toPoleEnergy_w
#print axioms GW.GPP.rawOccupied_eq_occupiedTerm_of_bundled
#print axioms GW.GPP.Term.rawSplitAdmissible_iff
#print axioms GW.GPP.Term.toAdmissiblePole_w
#print axioms GW.GPP.Term.toAdmissiblePole_x
#print axioms GW.GPP.Term.valueReal_eq_merged
#print axioms GW.GPP.Term.valueReal_eq_raw
#print axioms GW.GPP.Term.rawSplitAdmissible_denom_ne_zero
#print axioms GW.GPP.Term.check_ok_rawSplitAdmissible_false
#print axioms GW.GPP.Term.check_error_rawSplitAdmissible_false

/-! ## LL-C1: Lin-Lindsey finite ring diagrams

These concern the classical real Gibbs model of arXiv:1809.02900v1, NOT
electronic GW and NOT BerkeleyGW. They are additive: nothing above depends on
them. -/

#print axioms GW.LL.contraction_ring0
#print axioms GW.LL.contraction_ring1
#print axioms GW.LL.contraction_ring2
#print axioms GW.LL.symmetry_ring0
#print axioms GW.LL.symmetry_ring1
#print axioms GW.LL.symmetry_ring2
#print axioms GW.LL.ring2_forces_id_site
#print axioms GW.LL.ring2_forces_id_int
#print axioms GW.LL.ring2_prop_card
#print axioms GW.LL.contribution_ring0
#print axioms GW.LL.contribution_ring1
#print axioms GW.LL.contribution_ring2
#print axioms GW.LL.contraction_ratCast
#print axioms GW.LL.contribution_ratCast
#print axioms GW.LL.sum4_reverse
#print axioms GW.LL.FeynDiagram.contribution_eq_of_card
#print axioms GW.LL.FeynDiagram.contribution_eq_amplitude_div
#print axioms GW.LL.selfLoopWitness_compressed_card

/-! ### LL-C2A: the arbitrary finite ring family -/

#print axioms GW.LL.ring_zero
#print axioms GW.LL.ring_one
#print axioms GW.LL.ring_two
#print axioms GW.LL.edgeProd_ringProps
#print axioms GW.LL.edgeProd_ringInts_succ
#print axioms GW.LL.edgeProd_ringInts_peel
#print axioms GW.LL.sum_peel
#print axioms GW.LL.ringPart_succ
#print axioms GW.LL.ringPart_eq_chain
#print axioms GW.LL.contraction_ring

/-! ### LL-C2A: the arbitrary finite ring family, structural -/

#print axioms GW.LL.ringInts_length
#print axioms GW.LL.ringProps_length
#print axioms GW.LL.mem_ringProps
#print axioms GW.LL.mem_ringInts_succ
#print axioms GW.LL.sigma_fixes_aS_zero
#print axioms GW.LL.sigma_fixes_bS
#print axioms GW.LL.sigma_fixes_aS_succ
#print axioms GW.LL.sigma_fixes_all
#print axioms GW.LL.sigma_eq_one
#print axioms GW.LL.ringInts_nodup
#print axioms GW.LL.rho_eq_one
#print axioms GW.LL.props_pair_eq
#print axioms GW.LL.pi_fixes_external
#print axioms GW.LL.pi_bubble_mem
#print axioms GW.LL.pi_pIdx2_of_pIdx1
#print axioms GW.LL.flipIdx_involutive
#print axioms GW.LL.isAut_flipPerm
#print axioms GW.LL.card_aut_ring
#print axioms GW.LL.contribution_ring
#print axioms GW.LL.aut_no_bubble_exchange
#print axioms GW.LL.aut_no_intra_bubble_exchange
#print axioms GW.LL.ring_no_self_loop

/-! ### LL-C2A section 3.3: ring-only half-edge fidelity -/

#print axioms GW.LL.RingFlag.mate_mate
#print axioms GW.LL.RingFlag.mate_ne
#print axioms GW.LL.int_at_extI
#print axioms GW.LL.int_at_bS
#print axioms GW.LL.int_at_aS
#print axioms GW.LL.prop_at_aS
#print axioms GW.LL.prop_at_extI
#print axioms GW.LL.flagAut_chain
#print axioms GW.LL.flagAut_sites
#print axioms GW.LL.flagAut_sigma_eq_one
#print axioms GW.LL.flagAut_fixes_int
#print axioms GW.LL.flagAut_fixes_extProp
#print axioms GW.LL.flagAut_bub
#print axioms GW.LL.isFlagAut_flagPerm
#print axioms GW.LL.ringHalfEdgeEquivAut_bits
#print axioms GW.LL.card_ringHalfEdgeAut
#print axioms GW.LL.contribution_ring_eq_contributionOf

/-! ### LL-C2B: formal screening for the ring family -/

#print axioms GW.LL.constantCoeff_PL
#print axioms GW.LL.constantCoeff_PR
#print axioms GW.LL.PL_mul_SL
#print axioms GW.LL.SL_mul_PL
#print axioms GW.LL.PR_mul_SR
#print axioms GW.LL.SR_mul_PR
#print axioms GW.LL.C_v_mul_PR
#print axioms GW.LL.PL_mul_W
#print axioms GW.LL.W_mul_PR
#print axioms GW.LL.W_eq_C_v_mul_SR
#print axioms GW.LL.PL_mul_Wexp
#print axioms GW.LL.Wexp_eq_W
#print axioms GW.LL.coeff_W
#print axioms GW.LL.coeff_W_zero
#print axioms GW.LL.coeff_W_succ
#print axioms GW.LL.coeff_W_succ'
#print axioms GW.LL.hadamardSeries_add
#print axioms GW.LL.hadamardSeries_not_multiplicative
#print axioms GW.LL.coeff_T
#print axioms GW.LL.T_eq_neg_hadamardSeries_W
#print axioms GW.LL.constantCoeff_Tcoupling
#print axioms GW.LL.constantCoeff_Wcoupling
#print axioms GW.LL.coeff_succ_Tcoupling
#print axioms GW.LL.coeff_one_Wcoupling

/-! ### LL-C3: finite Wick pairings, normalized first order, Hartree/Fock

Wick's theorem is a DEFINITION in `GW/LL/Wick.lean`, not a result. These audits
cover what is proved downstream of that definition. -/

#print axioms GW.LL.pairings_length_six
#print axioms GW.LL.pairings_six_fpf_involutive
#print axioms GW.LL.pairings_six_nodup
#print axioms GW.LL.pairings_six_complete
#print axioms GW.LL.wickMoment_pair
#print axioms GW.LL.wickMoment_quartic
#print axioms GW.LL.wick6_split
#print axioms GW.LL.disconnected_cancels
#print axioms GW.LL.hartreeMatrix_apply
#print axioms GW.LL.fockMatrix_apply
#print axioms GW.LL.firstOrder_eq_hartree_fock
#print axioms GW.LL.ring0Matrix_eq
#print axioms GW.LL.dressed_ring0_eq_neg_fock
#print axioms GW.LL.firstOrder_eq_dressed_ring0_add_hartree
#print axioms GW.LL.hartreeMatrix_ne_zero

/-! ### LL-C4: finite static electronic RPA screening

The electronic conventions are a SPECIFICATION (see `GW/LL/Electronic.lean`),
not a derivation, and not BerkeleyGW's. These audits cover what is proved. -/

#print axioms GW.LL.geoP_mul_geoS
#print axioms GW.LL.geoS_mul_geoP
#print axioms GW.LL.geoP_mul_geoW
#print axioms GW.LL.coeff_geoW
#print axioms GW.LL.classical_geoP_eq
#print axioms GW.LL.classical_W_eq_geoW
#print axioms GW.LL.neg_pow_smul
#print axioms GW.LL.coeff_electronicW
#print axioms GW.LL.coeff_electronicW_eq_neumannCoeff
#print axioms GW.LL.dielectric_mul_partialScreened
#print axioms GW.LL.chi0_apply
#print axioms GW.LL.chi0_isSymm
#print axioms GW.LL.quadForm_add
#print axioms GW.LL.quadForm_contrib
#print axioms GW.LL.chi0_quadForm_nonpos
#print axioms GW.LL.chi0_diag_nonpos
#print axioms GW.LL.bubble_diag_nonneg
#print axioms GW.LL.bubble_chi0_diag_witness
#print axioms GW.LL.gpp_static_limit

/-! ### LL-C3/C4 review corrections

The general Wick recursion (previously a dangling reference), and the proved
counterexample showing that opposite diagonal signs do NOT establish
non-transferability of the classical screening content. -/

#print axioms GW.LL.select_length
#print axioms GW.LL.pairingsAux_fuel
#print axioms GW.LL.pairings_cons
#print axioms GW.LL.wickMoment_cons
#print axioms GW.LL.electronic_kernel_eq_AL
#print axioms GW.LL.geoP_electronic_eq_PL
#print axioms GW.LL.electronicW_eq_classical_W
#print axioms GW.LL.chi0_eq_neg_half_bubble_witness

/-! ### BGW-M1: one matched-input production screening certificate

`E`, `V` and `Rref` are exact rational encodings of doubles exported from a real
BerkeleyGW 4.0 static epsilon run; the two product theorems are checked by
kernel arithmetic on that data. The general lemmas carry the uniqueness step. -/

#print axioms GW.BGW.eq_of_left_inv
#print axioms GW.BGW.unique_solution
#print axioms GW.BGW.Rref_mul_E
#print axioms GW.BGW.E_mul_Rref
#print axioms GW.BGW.Rref_unique
#print axioms GW.BGW.E_mul_Wref
#print axioms GW.BGW.Wref_unique

/-! ### BGW-M2: exported chi to a certified screening reference

The general algebra (`inverse_shift`, `screened_shift`) plus concrete
certificates on exact rational decodings of one production run's operands. -/

#print axioms GW.BGW.M2.absQ_eq
#print axioms GW.BGW.M2.inverse_shift
#print axioms GW.BGW.M2.screened_shift
#print axioms GW.BGW.M2.Estar_eq
#print axioms GW.BGW.M2.formation_bound
#print axioms GW.BGW.M2.Rstar_mul_Estar
#print axioms GW.BGW.M2.Estar_mul_Rstar
#print axioms GW.BGW.M2.Rstar_unique
#print axioms GW.BGW.M2.Estar_mul_Wstar
#print axioms GW.BGW.M2.Rhat_mul_Ehat
#print axioms GW.BGW.M2.inverse_shift_instance
#print axioms GW.BGW.M2.screened_shift_instance
#print axioms GW.BGW.M2.rowAbsSum_eq
#print axioms GW.BGW.M2.nrmEhat_bounds
#print axioms GW.BGW.M2.nrmRhat_bounds
#print axioms GW.BGW.M2.nrmRstar_bounds
#print axioms GW.BGW.M2.bForm_bounds
#print axioms GW.BGW.M2.inv_error_bound
#print axioms GW.BGW.M2.shift_error_bound
#print axioms GW.BGW.M2.total_error_bound

/-! ### BGW-M3: one chi entry's transition-sum provenance

The exported production entries against the sum rebuilt from the UNWEIGHTED
matrix elements, before the code folds `sqrt(-eden)` into them, with the
denominator transfer discharged for the pinned data. -/

#print axioms GW.BGW.M3.absQ_eq
#print axioms GW.BGW.M3.list_transfer
#print axioms GW.BGW.M3.sum_map_const_mul_nat
#print axioms GW.BGW.M3.sum_map_const_mul_int
#print axioms GW.BGW.M3.int_sum_split
#print axioms GW.BGW.M3.abs_int_cast_eq
#print axioms GW.BGW.M3.abs_sub_div_le
#print axioms GW.BGW.M3.row_bound
#print axioms GW.BGW.M3.table_transfer
#print axioms GW.BGW.M3.recon_eval
#print axioms GW.BGW.M3.transfer_eval
#print axioms GW.BGW.M3.products_correct
#print axioms GW.BGW.M3.rows11_eq_rawRows11
#print axioms GW.BGW.M3.rows12_eq_rawRows12
#print axioms GW.BGW.M3.rows_ok11
#print axioms GW.BGW.M3.rows_ok12
#print axioms GW.BGW.M3.transition_count
#print axioms GW.BGW.M3.posSum11_eq
#print axioms GW.BGW.M3.negSum11_eq
#print axioms GW.BGW.M3.transferNum11_eq
#print axioms GW.BGW.M3.chiRecon11_eq
#print axioms GW.BGW.M3.transferBudget11_eq
#print axioms GW.BGW.M3.entry11_within_budget
#print axioms GW.BGW.M3.transfer_bound11
#print axioms GW.BGW.M3.entry11_endpoint
#print axioms GW.BGW.M3.posSum12_eq
#print axioms GW.BGW.M3.negSum12_eq
#print axioms GW.BGW.M3.transferNum12_eq
#print axioms GW.BGW.M3.chiRecon12_eq
#print axioms GW.BGW.M3.transferBudget12_eq
#print axioms GW.BGW.M3.entry12_within_budget
#print axioms GW.BGW.M3.transfer_bound12
#print axioms GW.BGW.M3.entry12_endpoint


/-! ### BGW-M4-R1: one production squared GPP pole connected to the M2 certificate

Generated module; see bgw/m4_gpp/PROVENANCE.md. -/

#print axioms GW.BGW.M4.quotient_transfer
#print axioms GW.BGW.M4.m2_entry_bound
#print axioms GW.BGW.M4.xhat_entry
#print axioms GW.BGW.M4.rstar_entry
#print axioms GW.BGW.M4.map_bound
#print axioms GW.BGW.M4.formation_bound
#print axioms GW.BGW.M4.ieps_bound
#print axioms GW.BGW.M4.omega_bound
#print axioms GW.BGW.M4.div_bound
#print axioms GW.BGW.M4.budget_half
#print axioms GW.BGW.M4.IStar_ne
#print axioms GW.BGW.M4.PStar_pos
#print axioms GW.BGW.M4.wtilde2_bound
#print axioms GW.BGW.M4.survives

/-! ### BGW-M5: one production GPP self-energy mode connected to the GPP core

Generated module; see bgw/m5_sigma/PROVENANCE.md. -/

#print axioms GW.BGW.M5.sqrt_near
#print axioms GW.BGW.M5.sqrt_diff
#print axioms GW.BGW.M5.quot_hat
#print axioms GW.BGW.M5.BI_le
#print axioms GW.BGW.M5.BP_le
#print axioms GW.BGW.M5.sqrt_checks
#print axioms GW.BGW.M5.sqrt_bound
#print axioms GW.BGW.M5.x_bound
#print axioms GW.BGW.M5.sch_local
#print axioms GW.BGW.M5.ssx_local
#print axioms GW.BGW.M5.sch_gap
#print axioms GW.BGW.M5.ssx_gap
#print axioms GW.BGW.M5.ieps_up
#print axioms GW.BGW.M5.sch_bound
#print axioms GW.BGW.M5.OStar_eq
#print axioms GW.BGW.M5.ssx_bound
#print axioms GW.BGW.M5.xStar_sq_ne
#print axioms GW.BGW.M5.mode_identity
#print axioms GW.BGW.M5.mode_endpoint
#print axioms GW.BGW.M5.generic_branch
#print axioms GW.BGW.M5.unclamped

-- Endpoint E1.4: the certified evaluator's near-pole closed form equals the source formula
#print axioms GW.Endpoint.ssxNear_eq
#print axioms GW.Endpoint.delw_half_ne_zero_iff

-- A3(b): Hubbard dimer, exact vs G0W0@HF gap (GW/Endpoint/HubbardDimer*.lean)
#print axioms GW.Endpoint.HubbardDimer.car_anti
#print axioms GW.Endpoint.HubbardDimer.car_ann
#print axioms GW.Endpoint.HubbardDimer.two_dbl_eq_normal_ordered
#print axioms GW.Endpoint.HubbardDimer.hop_conserves
#print axioms GW.Endpoint.HubbardDimer.dbl_conserves
#print axioms GW.Endpoint.HubbardDimer.numZ_diag
#print axioms GW.Endpoint.HubbardDimer.hopZ_eq
#print axioms GW.Endpoint.HubbardDimer.dblZ_eq
#print axioms GW.Endpoint.HubbardDimer.H_mulVec
#print axioms GW.Endpoint.HubbardDimer.eigen_ge
#print axioms GW.Endpoint.HubbardDimer.IsSectorGround.unique
#print axioms GW.Endpoint.HubbardDimer.quad_form
#print axioms GW.Endpoint.HubbardDimer.ground_one
#print axioms GW.Endpoint.HubbardDimer.ground_two
#print axioms GW.Endpoint.HubbardDimer.ground_three
#print axioms GW.Endpoint.HubbardDimer.sector_grounds
#print axioms GW.Endpoint.HubbardDimer.exact_gap
#print axioms GW.Endpoint.HubbardDimer.orbitals_orthonormal
#print axioms GW.Endpoint.HubbardDimer.h0_orbitals
#print axioms GW.Endpoint.HubbardDimer.fock_eq
#print axioms GW.Endpoint.HubbardDimer.hf_selfconsistent
#print axioms GW.Endpoint.HubbardDimer.chi0_eq
#print axioms GW.Endpoint.HubbardDimer.rpa_solves
#print axioms GW.Endpoint.HubbardDimer.rpa_det
#print axioms GW.Endpoint.HubbardDimer.W_eq_inv
#print axioms GW.Endpoint.HubbardDimer.Wc_single_pole
#print axioms GW.Endpoint.HubbardDimer.sigmaC_orbital
#print axioms GW.Endpoint.HubbardDimer.Dgw_sq
#print axioms GW.Endpoint.HubbardDimer.Dgw_ge
#print axioms GW.Endpoint.HubbardDimer.qp_removal
#print axioms GW.Endpoint.HubbardDimer.Erem_side
#print axioms GW.Endpoint.HubbardDimer.qp_addition
#print axioms GW.Endpoint.HubbardDimer.Eadd_side
#print axioms GW.Endpoint.HubbardDimer.gw_gap_of_qp
#print axioms GW.Endpoint.HubbardDimer.gapGW_zero
#print axioms GW.Endpoint.HubbardDimer.gapHF_eq
#print axioms GW.Endpoint.HubbardDimer.polyX
#print axioms GW.Endpoint.HubbardDimer.polyY
#print axioms GW.Endpoint.HubbardDimer.core_bounds
#print axioms GW.Endpoint.HubbardDimer.exact_sqrt_bounds
#print axioms GW.Endpoint.HubbardDimer.gw_error_bounds
#print axioms GW.Endpoint.HubbardDimer.gw_error_abs
#print axioms GW.Endpoint.HubbardDimer.hf_error_bounds
#print axioms GW.Endpoint.HubbardDimer.gw_beats_hf
#print axioms GW.Endpoint.HubbardDimer.no_cubic_bound
#print axioms GW.Endpoint.HubbardDimer.gw_error_leading
#print axioms GW.Endpoint.HubbardDimer.hf_error_leading
#print axioms GW.Endpoint.HubbardDimer.gw_gap_error_main
#print axioms GW.Endpoint.HubbardDimer.dot_self_pos
#print axioms GW.Endpoint.HubbardDimer.norm_sq
#print axioms GW.Endpoint.HubbardDimer.rEx_sq
#print axioms GW.Endpoint.HubbardDimer.rEx_gt
#print axioms GW.Endpoint.HubbardDimer.s2_sq
#print axioms GW.Endpoint.HubbardDimer.s2_mul
#print axioms GW.Endpoint.HubbardDimer.hRPA_sq
#print axioms GW.Endpoint.HubbardDimer.hRPA_pos
#print axioms GW.Endpoint.HubbardDimer.s2_pow4
#print axioms GW.Endpoint.HubbardDimer.pw_pos
#print axioms GW.Endpoint.HubbardDimer.qw_pos
#print axioms GW.Endpoint.HubbardDimer.Xup_Ylo_nonneg
#print axioms GW.Endpoint.HubbardDimer.exists_scale

-- A1 uniqueness: logic of the QP-root uniqueness certificate (GW/Endpoint/QPUnique.lean)
#print axioms GW.Endpoint.strictAntiOn_Icc_of_hasDerivAt_neg
#print axioms GW.Endpoint.qp_root_unique
#print axioms GW.Endpoint.qp_root_mem_subbracket
#print axioms GW.Endpoint.strictMonoOn_Icc_of_hasDerivAt_pos
#print axioms GW.Endpoint.IsolatingBracket.existsUnique
#print axioms GW.Endpoint.qp_roots_enumerated
/-! ### Endpoint E1.4 certificate soundness (LEAN-CERT): interval arithmetic,
componentwise Neumann inverse with balancing, and the sexcut clamp test
(`GW/Endpoint/CertInterval.lean`, `CertInverse.lean`, `CertSexcut.lean`).
Real-number statements of what `bgw/endpoint/iv.py` and `cert.py` compute;
the IEEE rounding hypothesis and the Python-to-Lean correspondence are named
gaps (see `.agent/handoffs/LEAN-CERT.md`). -/
#print axioms GW.Endpoint.Cert.IV.neg_mem
#print axioms GW.Endpoint.Cert.IV.add_mem
#print axioms GW.Endpoint.Cert.IV.sub_mem
#print axioms GW.Endpoint.Cert.IV.min4_le_mul
#print axioms GW.Endpoint.Cert.IV.mul_le_max4
#print axioms GW.Endpoint.Cert.IV.mul_mem
#print axioms GW.Endpoint.Cert.IV.sqr_mem
#print axioms GW.Endpoint.Cert.IV.recip_mem
#print axioms GW.Endpoint.Cert.IV.div_mem
#print axioms GW.Endpoint.Cert.IV.sqrt_mem
#print axioms GW.Endpoint.Cert.IV.abs_le_mag
#print axioms GW.Endpoint.Cert.IV.abs_mem
#print axioms GW.Endpoint.Cert.IV.hull_mem
#print axioms GW.Endpoint.Cert.IV.select_mem
#print axioms GW.Endpoint.Cert.IV.certainly_lt_sound
#print axioms GW.Endpoint.Cert.IV.certainly_le_sound
#print axioms GW.Endpoint.Cert.IV.certainly_gt_sound
#print axioms GW.Endpoint.Cert.IV.certainly_ge_sound
#print axioms GW.Endpoint.Cert.IV.ne_zero_of_not_contains_zero
#print axioms GW.Endpoint.Cert.IV.sum_le_sumUp
#print axioms GW.Endpoint.Cert.IV.sumDown_le_sum
#print axioms GW.Endpoint.Cert.IV.sum_mem
#print axioms GW.Endpoint.Cert.IV.sum_le_matmulUpAcc
#print axioms GW.Endpoint.Cert.Dom.nonneg
#print axioms GW.Endpoint.Cert.dom_absM
#print axioms GW.Endpoint.Cert.dom_mono
#print axioms GW.Endpoint.Cert.dom_mul
#print axioms GW.Endpoint.Cert.dom_one
#print axioms GW.Endpoint.Cert.dom_pow
#print axioms GW.Endpoint.Cert.dom_add
#print axioms GW.Endpoint.Cert.dom_sum
#print axioms GW.Endpoint.Cert.matMul_nonneg
#print axioms GW.Endpoint.Cert.matMul_le_matMul_left
#print axioms GW.Endpoint.Cert.matPow_nonneg
#print axioms GW.Endpoint.Cert.rowLe_mul
#print axioms GW.Endpoint.Cert.rowLe_pow_mul
#print axioms GW.Endpoint.Cert.entry_le_rowSum
#print axioms GW.Endpoint.Cert.det_one_sub_ne_zero
#print axioms GW.Endpoint.Cert.neumann_cw
#print axioms GW.Endpoint.Cert.neumann_cw_set
#print axioms GW.Endpoint.Cert.pow_le_of_chain
#print axioms GW.Endpoint.Cert.inverse_cw_sound
#print axioms GW.Endpoint.Cert.balance_eq
#print axioms GW.Endpoint.Cert.det_balance
#print axioms GW.Endpoint.Cert.balance_inv
#print axioms GW.Endpoint.Cert.balance_mem
#print axioms GW.Endpoint.Cert.inv_mem_of_balanced
#print axioms GW.Endpoint.Cert.sexcut_generic_iff
#print axioms GW.Endpoint.Cert.sexcut_near_iff
#print axioms GW.Endpoint.Cert.sexcut_nearSource_iff
#print axioms GW.Endpoint.Cert.clamp_congr
#print axioms GW.Endpoint.Cert.certSsx_eq_srcSsx
#print axioms GW.Endpoint.Cert.certSsx_at_neg
#print axioms GW.Endpoint.Cert.certSsx_at_w
-- A3 dimer part 2: Sigma_c derived from i G0 W_c (HubbardDimerSigma.lean) and the
-- U^2 coefficients / second-order exchange (HubbardDimerSecondOrder.lean)
#print axioms GW.Endpoint.HubbardDimer.list_sum_mul_left
#print axioms GW.Endpoint.HubbardDimer.list_sum_map_add
#print axioms GW.Endpoint.HubbardDimer.ofReal_list_sum
#print axioms GW.Endpoint.HubbardDimer.setIntegral_expList
#print axioms GW.Endpoint.HubbardDimer.integral_Ioi_osc
#print axioms GW.Endpoint.HubbardDimer.integral_Iic_osc
#print axioms GW.Endpoint.HubbardDimer.ftDamped_twoSided
#print axioms GW.Endpoint.HubbardDimer.ftDamped_twoSided_limit
#print axioms GW.Endpoint.HubbardDimer.list_sum_mul_right
#print axioms GW.Endpoint.HubbardDimer.I_mul_negI
#print axioms GW.Endpoint.HubbardDimer.negI_mul_I_div
#print axioms GW.Endpoint.HubbardDimer.I_mul_negI_div
#print axioms GW.Endpoint.HubbardDimer.WcTime_eq
#print axioms GW.Endpoint.HubbardDimer.G0time_eq
#print axioms GW.Endpoint.HubbardDimer.sigmaTime_eq
#print axioms GW.Endpoint.HubbardDimer.sigmaSinglePole_eq_limit
#print axioms GW.Endpoint.HubbardDimer.sigmaC_eq_limit
#print axioms GW.Endpoint.HubbardDimer.sigmaOrbitalFT_limit
#print axioms GW.Endpoint.HubbardDimer.sigBB_sigAA_eq_limit
#print axioms GW.Endpoint.HubbardDimer.WcTime_limit
#print axioms GW.Endpoint.HubbardDimer.G0time_limit
#print axioms GW.Endpoint.HubbardDimer.g0HF_resolvent
#print axioms GW.Endpoint.HubbardDimer.eri_eq
#print axioms GW.Endpoint.HubbardDimer.sig2dir_B
#print axioms GW.Endpoint.HubbardDimer.sig2dir_A
#print axioms GW.Endpoint.HubbardDimer.sig2x_B
#print axioms GW.Endpoint.HubbardDimer.sig2x_A
#print axioms GW.Endpoint.HubbardDimer.gap2dir_eq
#print axioms GW.Endpoint.HubbardDimer.gap2x_eq
#print axioms GW.Endpoint.HubbardDimer.tendsto_div_sq_of_bound
#print axioms GW.Endpoint.HubbardDimer.hf_U2_coeff
#print axioms GW.Endpoint.HubbardDimer.exact_expansion
#print axioms GW.Endpoint.HubbardDimer.exact_U2_coeff
#print axioms GW.Endpoint.HubbardDimer.gw_U2_coeff
#print axioms GW.Endpoint.HubbardDimer.gw_error_is_minus_sox
#print axioms GW.Endpoint.HubbardDimer.hRPA_continuous
#print axioms GW.Endpoint.HubbardDimer.hRPA_zero
#print axioms GW.Endpoint.HubbardDimer.sigBB_second_order
#print axioms GW.Endpoint.HubbardDimer.sigAA_second_order
-- G3: exact dimer Green's function (Lehmann, full N+-1 spectra) and exact self-energy
-- = HF + second-order direct + exchange (HubbardDimerExactSigma.lean)
#print axioms GW.Endpoint.HubbardDimer.ann0_eq
#print axioms GW.Endpoint.HubbardDimer.cre0_eq
#print axioms GW.Endpoint.HubbardDimer.ann2_eq
#print axioms GW.Endpoint.HubbardDimer.cre2_eq
#print axioms GW.Endpoint.HubbardDimer.annR0_mulVec
#print axioms GW.Endpoint.HubbardDimer.annR2_mulVec
#print axioms GW.Endpoint.HubbardDimer.creR0_mulVec
#print axioms GW.Endpoint.HubbardDimer.creR2_mulVec
#print axioms GW.Endpoint.HubbardDimer.annO_mulVec
#print axioms GW.Endpoint.HubbardDimer.creO_mulVec
#print axioms GW.Endpoint.HubbardDimer.ev1_eigen
#print axioms GW.Endpoint.HubbardDimer.ev3_eigen
#print axioms GW.Endpoint.HubbardDimer.ev1_sector
#print axioms GW.Endpoint.HubbardDimer.ev3_sector
#print axioms GW.Endpoint.HubbardDimer.ev1_orth
#print axioms GW.Endpoint.HubbardDimer.ev3_orth
#print axioms GW.Endpoint.HubbardDimer.ev1_complete
#print axioms GW.Endpoint.HubbardDimer.ev3_complete
#print axioms GW.Endpoint.HubbardDimer.kEx_pos
#print axioms GW.Endpoint.HubbardDimer.kEx_rel
#print axioms GW.Endpoint.HubbardDimer.psi0_eigen
#print axioms GW.Endpoint.HubbardDimer.psi0_sector
#print axioms GW.Endpoint.HubbardDimer.psi0_ne
#print axioms GW.Endpoint.HubbardDimer.psi0_ground
#print axioms GW.Endpoint.HubbardDimer.psi0_norm
#print axioms GW.Endpoint.HubbardDimer.psi0_unique
#print axioms GW.Endpoint.HubbardDimer.creB_psi0
#print axioms GW.Endpoint.HubbardDimer.creA_psi0
#print axioms GW.Endpoint.HubbardDimer.annB_psi0
#print axioms GW.Endpoint.HubbardDimer.annA_psi0
#print axioms GW.Endpoint.HubbardDimer.GL_smul
#print axioms GW.Endpoint.HubbardDimer.GL_ground_eq
#print axioms GW.Endpoint.HubbardDimer.sum_ev3
#print axioms GW.Endpoint.HubbardDimer.sum_ev1
#print axioms GW.Endpoint.HubbardDimer.s2_weight
#print axioms GW.Endpoint.HubbardDimer.Gex_BB
#print axioms GW.Endpoint.HubbardDimer.Gex_AA
#print axioms GW.Endpoint.HubbardDimer.Gex_offdiag
#print axioms GW.Endpoint.HubbardDimer.nrm_pos
#print axioms GW.Endpoint.HubbardDimer.E0_eq
#print axioms GW.Endpoint.HubbardDimer.weights_eq
#print axioms GW.Endpoint.HubbardDimer.Gex_BB_rat
#print axioms GW.Endpoint.HubbardDimer.Gex_AA_rat
#print axioms GW.Endpoint.HubbardDimer.sig2dir_B_eq
#print axioms GW.Endpoint.HubbardDimer.sig2x_B_eq
#print axioms GW.Endpoint.HubbardDimer.sig2dir_A_eq
#print axioms GW.Endpoint.HubbardDimer.sig2x_A_eq
#print axioms GW.Endpoint.HubbardDimer.sig2_B_eq
#print axioms GW.Endpoint.HubbardDimer.sig2_A_eq
#print axioms GW.Endpoint.HubbardDimer.Gex_U0
#print axioms GW.Endpoint.HubbardDimer.sigEx_B
#print axioms GW.Endpoint.HubbardDimer.sigEx_A
#print axioms GW.Endpoint.HubbardDimer.hf_shift
#print axioms GW.Endpoint.HubbardDimer.kEx_near
#print axioms GW.Endpoint.HubbardDimer.rem_bound
#print axioms GW.Endpoint.HubbardDimer.sigEx_B_expansion
#print axioms GW.Endpoint.HubbardDimer.sigEx_A_expansion
#print axioms GW.Endpoint.HubbardDimer.tendsto_of_abs_le_mul
#print axioms GW.Endpoint.HubbardDimer.div_sq_bound
#print axioms GW.Endpoint.HubbardDimer.sigEx_B_U2_limit
#print axioms GW.Endpoint.HubbardDimer.sigEx_A_U2_limit
#print axioms GW.Endpoint.HubbardDimer.sig2_B_U2_limit
#print axioms GW.Endpoint.HubbardDimer.sig2_A_U2_limit
#print axioms GW.Endpoint.HubbardDimer.sig2x_eq_neg_half_dir
#print axioms GW.Endpoint.HubbardDimer.sigEx_B_ne_direct_only
#print axioms GW.Endpoint.HubbardDimer.sigEx_A_ne_direct_only
#print axioms GW.Endpoint.HubbardDimer.hopZ_symm
#print axioms GW.Endpoint.HubbardDimer.dblZ_symm
#print axioms GW.Endpoint.HubbardDimer.H_symm
#print axioms GW.Endpoint.HubbardDimer.sector_resolvent
#print axioms GW.Endpoint.HubbardDimer.sum_sector
#print axioms GW.Endpoint.HubbardDimer.creO_psi0_sector
#print axioms GW.Endpoint.HubbardDimer.annO_psi0_sector
#print axioms GW.Endpoint.HubbardDimer.Gex_resolvent
#print axioms GW.Endpoint.HubbardDimer.Gex_resolvent_exists
-- G2 stage 1: kernel checker for the eps^-1 certificate (GW/Endpoint/Kernel/).
-- The per-q theorems `GW.Endpoint.Kernel.Q{0,1,2}.epsinv_enclosure_q{0,1,2}` live in
-- the slow non-default target `GWKernelData`; audit them with
-- `lake env lean GW/Endpoint/Kernel/AuditData.lean` after `lake build GWKernelData`.
#print axioms GW.Endpoint.Kernel.comb_getD
#print axioms GW.Endpoint.Kernel.all2_spec
#print axioms GW.Endpoint.Kernel.Cert.mul_le
#print axioms GW.Endpoint.Kernel.Cert.e_int
#print axioms GW.Endpoint.Kernel.Cert.dom_E
#print axioms GW.Endpoint.Kernel.Cert.row_spec
#print axioms GW.Endpoint.Kernel.Cert.tail_real
#print axioms GW.Endpoint.Kernel.Cert.sound

-- A3(a) G4: general finite fermion system, exact self-energy through second order
-- and the G0W0 error structure (GW/Endpoint/ManyBody/*.lean). Key results:
-- sigma_coeff0, sigma1_eq_HF, sigma2_eq, sigma2_eq_direct_add_sox(_add_relax),
-- gw2_limit, gw_error_first_order, gw_error_second_order(_brillouin), gw_error_coeff2.
-- ManyBody/Fock.lean
#print axioms GW.Endpoint.ManyBody.sgn_sq
#print axioms GW.Endpoint.ManyBody.sgn_insert_self
#print axioms GW.Endpoint.ManyBody.sgn_erase_self
#print axioms GW.Endpoint.ManyBody.sgn_insert
#print axioms GW.Endpoint.ManyBody.sgn_erase
#print axioms GW.Endpoint.ManyBody.ann_mulVec
#print axioms GW.Endpoint.ManyBody.cre_mulVec
#print axioms GW.Endpoint.ManyBody.ext_mulVec
#print axioms GW.Endpoint.ManyBody.ann_mul_cre_add
#print axioms GW.Endpoint.ManyBody.ann_mul_ann_add
#print axioms GW.Endpoint.ManyBody.cre_mul_cre_add
#print axioms GW.Endpoint.ManyBody.cre_transpose
#print axioms GW.Endpoint.ManyBody.ann_transpose
#print axioms GW.Endpoint.ManyBody.ann_mul_cre
#print axioms GW.Endpoint.ManyBody.ann_mul_ann
#print axioms GW.Endpoint.ManyBody.cre_mul_cre
#print axioms GW.Endpoint.ManyBody.ann_mul_self
#print axioms GW.Endpoint.ManyBody.cre_mul_self
#print axioms GW.Endpoint.ManyBody.num_mulVec
#print axioms GW.Endpoint.ManyBody.num_eq_diagonal
#print axioms GW.Endpoint.ManyBody.H0_eq_diagonal
#print axioms GW.Endpoint.ManyBody.numOp_eq_diagonal
#print axioms GW.Endpoint.ManyBody.num_mul_cre
#print axioms GW.Endpoint.ManyBody.num_mul_ann
#print axioms GW.Endpoint.ManyBody.H0_mul_cre
#print axioms GW.Endpoint.ManyBody.H0_mul_ann
#print axioms GW.Endpoint.ManyBody.IsEig.cre
#print axioms GW.Endpoint.ManyBody.IsEig.ann
#print axioms GW.Endpoint.ManyBody.IsEig.add
#print axioms GW.Endpoint.ManyBody.IsEig.smul
#print axioms GW.Endpoint.ManyBody.IsEig.zero
#print axioms GW.Endpoint.ManyBody.IsEig.sum
#print axioms GW.Endpoint.ManyBody.IsEig.diagonal_mulVec
-- ManyBody/Slater.lean
#print axioms GW.Endpoint.ManyBody.ann_cre_mulVec
#print axioms GW.Endpoint.ManyBody.cre_ann_mulVec
#print axioms GW.Endpoint.ManyBody.ann_ann_mulVec
#print axioms GW.Endpoint.ManyBody.cre_cre_mulVec
#print axioms GW.Endpoint.ManyBody.ann_self_mulVec
#print axioms GW.Endpoint.ManyBody.cre_self_mulVec
#print axioms GW.Endpoint.ManyBody.dot_ite_zero
#print axioms GW.Endpoint.ManyBody.ite_zero_dot
#print axioms GW.Endpoint.ManyBody.mulVec_ite_zero
#print axioms GW.Endpoint.ManyBody.cre_dot
#print axioms GW.Endpoint.ManyBody.ann_dot
#print axioms GW.Endpoint.ManyBody.mulVec_dot_of_symm
#print axioms GW.Endpoint.ManyBody.ann_phi
#print axioms GW.Endpoint.ManyBody.cre_phi
#print axioms GW.Endpoint.ManyBody.phi_dot_phi
#print axioms GW.Endpoint.ManyBody.phi_isEig
#print axioms GW.Endpoint.ManyBody.phi_isEig_num
#print axioms GW.Endpoint.ManyBody.ann_ann_phi_of_not_mem
#print axioms GW.Endpoint.ManyBody.cre_ann_phi_of_mem
#print axioms GW.Endpoint.ManyBody.lemA
#print axioms GW.Endpoint.ManyBody.lemB
#print axioms GW.Endpoint.ManyBody.lemC
#print axioms GW.Endpoint.ManyBody.lemD
#print axioms GW.Endpoint.ManyBody.dot_cre_phi
#print axioms GW.Endpoint.ManyBody.dot_ann_phi
#print axioms GW.Endpoint.ManyBody.gram_2h
#print axioms GW.Endpoint.ManyBody.gram_2p1h
#print axioms GW.Endpoint.ManyBody.gram_2h1p
#print axioms GW.Endpoint.ManyBody.orth_1p_2p1h
#print axioms GW.Endpoint.ManyBody.orth_1h_2h1p
#print axioms GW.Endpoint.ManyBody.cc_a_phi
#print axioms GW.Endpoint.ManyBody.c_aa_phi
#print axioms GW.Endpoint.ManyBody.c_a_phi
-- ManyBody/Interaction.lean
#print axioms GW.Endpoint.ManyBody.sum_mulVec'
#print axioms GW.Endpoint.ManyBody.mulVec_sum'
#print axioms GW.Endpoint.ManyBody.dot_sum'
#print axioms GW.Endpoint.ManyBody.sum_dot'
#print axioms GW.Endpoint.ManyBody.quartic_comm_right
#print axioms GW.Endpoint.ManyBody.quartic_comm_left
#print axioms GW.Endpoint.ManyBody.cubic_anticomm
#print axioms GW.Endpoint.ManyBody.ann_cre_add'
#print axioms GW.Endpoint.ManyBody.cre_cre_add'
#print axioms GW.Endpoint.ManyBody.ann_ann_add'
#print axioms GW.Endpoint.ManyBody.term_comm_cre
#print axioms GW.Endpoint.ManyBody.vop_mul_cre
#print axioms GW.Endpoint.ManyBody.term_comm_ann
#print axioms GW.Endpoint.ManyBody.ann_mul_vop
#print axioms GW.Endpoint.ManyBody.asym_swap12
#print axioms GW.Endpoint.ManyBody.asym_swap34
#print axioms GW.Endpoint.ManyBody.asym_herm
#print axioms GW.Endpoint.ManyBody.term_anticomm
#print axioms GW.Endpoint.ManyBody.ann_ccre
#print axioms GW.Endpoint.ManyBody.quartic_transpose
#print axioms GW.Endpoint.ManyBody.sum4_swap
#print axioms GW.Endpoint.ManyBody.vop_transpose
#print axioms GW.Endpoint.ManyBody.IsEig.congr
#print axioms GW.Endpoint.ManyBody.vop_isEig_num
-- ManyBody/Decomp.lean
#print axioms GW.Endpoint.ManyBody.sum_univ_eq_sum_of
#print axioms GW.Endpoint.ManyBody.sum_ite_mem_univ
#print axioms GW.Endpoint.ManyBody.sum_ite_not_mem_univ
#print axioms GW.Endpoint.ManyBody.sum_sum_ite_and
#print axioms GW.Endpoint.ManyBody.ccre_mulVec
#print axioms GW.Endpoint.ManyBody.cann_mulVec
#print axioms GW.Endpoint.ManyBody.ccre_phi
#print axioms GW.Endpoint.ManyBody.cann_phi
#print axioms GW.Endpoint.ManyBody.dot_mulVec_cre
#print axioms GW.Endpoint.ManyBody.phi_vop_1p1h
-- ManyBody/Feshbach.lean
#print axioms GW.Endpoint.ManyBody.feshbach
-- ManyBody/Series.lean
#print axioms GW.Endpoint.ManyBody.coeff0_mul
#print axioms GW.Endpoint.ManyBody.coeff1_mul
#print axioms GW.Endpoint.ManyBody.coeff2_mul
#print axioms GW.Endpoint.ManyBody.coeff_C'
#print axioms GW.Endpoint.ManyBody.coeff_X_mul'
#print axioms GW.Endpoint.ManyBody.coeff_X2_mul
#print axioms GW.Endpoint.ManyBody.cf_apply
#print axioms GW.Endpoint.ManyBody.cf_add
#print axioms GW.Endpoint.ManyBody.cf_sub
#print axioms GW.Endpoint.ManyBody.cf_neg
#print axioms GW.Endpoint.ManyBody.cf_zero
#print axioms GW.Endpoint.ManyBody.cf_transpose
#print axioms GW.Endpoint.ManyBody.cf_one
#print axioms GW.Endpoint.ManyBody.cf_lift
#print axioms GW.Endpoint.ManyBody.cf0_smul
#print axioms GW.Endpoint.ManyBody.cf1_smul
#print axioms GW.Endpoint.ManyBody.cf2_smul
#print axioms GW.Endpoint.ManyBody.cf0_mul
#print axioms GW.Endpoint.ManyBody.cf1_mul
#print axioms GW.Endpoint.ManyBody.cf2_mul
#print axioms GW.Endpoint.ManyBody.cfv_add
#print axioms GW.Endpoint.ManyBody.cfv_sub
#print axioms GW.Endpoint.ManyBody.cfv_liftv
#print axioms GW.Endpoint.ManyBody.cfv0_smul
#print axioms GW.Endpoint.ManyBody.cfv1_smul
#print axioms GW.Endpoint.ManyBody.cfv2_smul
#print axioms GW.Endpoint.ManyBody.cfv0_mulVec
#print axioms GW.Endpoint.ManyBody.cfv1_mulVec
#print axioms GW.Endpoint.ManyBody.cfv2_mulVec
#print axioms GW.Endpoint.ManyBody.coeff0_dot
#print axioms GW.Endpoint.ManyBody.coeff1_dot
#print axioms GW.Endpoint.ManyBody.coeff2_dot
#print axioms GW.Endpoint.ManyBody.isUnit_det_of_cf0
#print axioms GW.Endpoint.ManyBody.cf0_inv
#print axioms GW.Endpoint.ManyBody.coeff_inv_T
-- ManyBody/Perturb.lean
#print axioms GW.Endpoint.ManyBody.phi_dot
#print axioms GW.Endpoint.ManyBody.phi_dot_Rr
#print axioms GW.Endpoint.ManyBody.IsEig.diagonal
#print axioms GW.Endpoint.ManyBody.H0_Rr
#print axioms GW.Endpoint.ManyBody.vphi_num
#print axioms GW.Endpoint.ManyBody.psi1_num
#print axioms GW.Endpoint.ManyBody.phi_dot_psi1
#print axioms GW.Endpoint.ManyBody.phi_dot_psi2
#print axioms GW.Endpoint.ManyBody.eig_order0
#print axioms GW.Endpoint.ManyBody.eig_order1
#print axioms GW.Endpoint.ManyBody.eig_order2
-- ManyBody/Dyn.lean
#print axioms GW.Endpoint.ManyBody.state2p_isEig
#print axioms GW.Endpoint.ManyBody.state2h_isEig
#print axioms GW.Endpoint.ManyBody.Dp_state
#print axioms GW.Endpoint.ManyBody.Dm_state
#print axioms GW.Endpoint.ManyBody.smul_sum'
#print axioms GW.Endpoint.ManyBody.sum3_rotate
#print axioms GW.Endpoint.ManyBody.dyn_particle
#print axioms GW.Endpoint.ManyBody.dyn_hole
-- ManyBody/Static.lean
#print axioms GW.Endpoint.ManyBody.sig1_symm
#print axioms GW.Endpoint.ManyBody.Rr_transpose
#print axioms GW.Endpoint.ManyBody.Rr_1p1h
#print axioms GW.Endpoint.ManyBody.Rr_phi
#print axioms GW.Endpoint.ManyBody.dot_1p1h_vphi
#print axioms GW.Endpoint.ManyBody.dot_psi1_1p1h
#print axioms GW.Endpoint.ManyBody.fop_mulVec
#print axioms GW.Endpoint.ManyBody.psi1_dot_phi
#print axioms GW.Endpoint.ManyBody.psi1_dot_ca
#print axioms GW.Endpoint.ManyBody.static_left
#print axioms GW.Endpoint.ManyBody.static_right
#print axioms GW.Endpoint.ManyBody.static_eq
#print axioms GW.Endpoint.ManyBody.relax_eq_zero_of_brillouin
-- ManyBody/Exact.lean
#print axioms GW.Endpoint.ManyBody.colM_apply
#print axioms GW.Endpoint.ManyBody.mul_colM
#print axioms GW.Endpoint.ManyBody.colM_transpose_mul_colM
#print axioms GW.Endpoint.ManyBody.lift_mul
#print axioms GW.Endpoint.ManyBody.lift_add
#print axioms GW.Endpoint.ManyBody.lift_sub
#print axioms GW.Endpoint.ManyBody.lift_smul
#print axioms GW.Endpoint.ManyBody.lift_one
#print axioms GW.Endpoint.ManyBody.lift_zero
#print axioms GW.Endpoint.ManyBody.lift_transpose
#print axioms GW.Endpoint.ManyBody.lift_mulVec
#print axioms GW.Endpoint.ManyBody.cf_lift_mul_eq
#print axioms GW.Endpoint.ManyBody.cfv_lift_mulVec
#print axioms GW.Endpoint.ManyBody.cfv_psiT
#print axioms GW.Endpoint.ManyBody.coeff_ET
#print axioms GW.Endpoint.ManyBody.cf_KT
#print axioms GW.Endpoint.ManyBody.cf0_KT
#print axioms GW.Endpoint.ManyBody.cf1_KT
#print axioms GW.Endpoint.ManyBody.cf2_KT
#print axioms GW.Endpoint.ManyBody.cfv0_psiT
#print axioms GW.Endpoint.ManyBody.cfv1_psiT
#print axioms GW.Endpoint.ManyBody.cfv2_psiT
#print axioms GW.Endpoint.ManyBody.sub_smul_one_mulVec
#print axioms GW.Endpoint.ManyBody.resid_cf
-- ManyBody/Bridge.lean
#print axioms GW.Endpoint.ManyBody.H0_transpose
#print axioms GW.Endpoint.ManyBody.KT_transpose
#print axioms GW.Endpoint.ManyBody.cf0_Cω_smul
#print axioms GW.Endpoint.ManyBody.cf_Cω_smul_succ
#print axioms GW.Endpoint.ManyBody.cf0_MpT
#print axioms GW.Endpoint.ManyBody.cf0_MmT
#print axioms GW.Endpoint.ManyBody.diag_inv_mul
#print axioms GW.Endpoint.ManyBody.MpT_det
#print axioms GW.Endpoint.ManyBody.MmT_det
#print axioms GW.Endpoint.ManyBody.MmT_inv_transpose
#print axioms GW.Endpoint.ManyBody.lift_ann_cre_add
#print axioms GW.Endpoint.ManyBody.dot_mulVec_T
#print axioms GW.Endpoint.ManyBody.creT_transpose
#print axioms GW.Endpoint.ManyBody.annT_transpose
#print axioms GW.Endpoint.ManyBody.AT_gram
#print axioms GW.Endpoint.ManyBody.omega_sub_HHT
#print axioms GW.Endpoint.ManyBody.resolvent_XT
#print axioms GW.Endpoint.ManyBody.greenT_eq
#print axioms GW.Endpoint.ManyBody.coeff0_dT
#print axioms GW.Endpoint.ManyBody.dT_inv_mul
#print axioms GW.Endpoint.ManyBody.greenT_inv
#print axioms GW.Endpoint.ManyBody.energy_insert
#print axioms GW.Endpoint.ManyBody.energy_erase
#print axioms GW.Endpoint.ManyBody.omega_ne_eps
#print axioms GW.Endpoint.ManyBody.green0_inv
#print axioms GW.Endpoint.ManyBody.sigmaT_eq
-- ManyBody/Doubled.lean
#print axioms GW.Endpoint.ManyBody.colM_mul_diagonal
#print axioms GW.Endpoint.ManyBody.colM_mul
#print axioms GW.Endpoint.ManyBody.colM_add
#print axioms GW.Endpoint.ManyBody.colM_sub
#print axioms GW.Endpoint.ManyBody.colM_zero
#print axioms GW.Endpoint.ManyBody.A0_gram
#print axioms GW.Endpoint.ManyBody.H0r_A0
#print axioms GW.Endpoint.ManyBody.Hr_transpose
#print axioms GW.Endpoint.ManyBody.H0mE0_transpose
#print axioms GW.Endpoint.ManyBody.A0_H0r
#print axioms GW.Endpoint.ManyBody.A0_Y2
#print axioms GW.Endpoint.ManyBody.fromRows_add'
#print axioms GW.Endpoint.ManyBody.fromRows_sub'
#print axioms GW.Endpoint.ManyBody.Hr_mul_Ar
#print axioms GW.Endpoint.ManyBody.Ar_mul
#print axioms GW.Endpoint.ManyBody.first_order_part
#print axioms GW.Endpoint.ManyBody.first_order_hole
#print axioms GW.Endpoint.ManyBody.first_order_cols
#print axioms GW.Endpoint.ManyBody.H0mE0_diag
#print axioms GW.Endpoint.ManyBody.Dk_mul
#print axioms GW.Endpoint.ManyBody.omega_ne_zero
#print axioms GW.Endpoint.ManyBody.proj_inverse
#print axioms GW.Endpoint.ManyBody.L0_mul_N0
#print axioms GW.Endpoint.ManyBody.L0_Y2
#print axioms GW.Endpoint.ManyBody.Y2_Dk_Y2
-- ManyBody/Static2.lean
#print axioms GW.Endpoint.ManyBody.static_ring
#print axioms GW.Endpoint.ManyBody.lift_H0_mul_cre
#print axioms GW.Endpoint.ManyBody.lift_vop_mul_cre
#print axioms GW.Endpoint.ManyBody.KT_mul_cre
#print axioms GW.Endpoint.ManyBody.scalar_central
#print axioms GW.Endpoint.ManyBody.lift_ann_ccre
#print axioms GW.Endpoint.ManyBody.static_op
#print axioms GW.Endpoint.ManyBody.mulVec_dot_T
#print axioms GW.Endpoint.ManyBody.ST_entry
-- ManyBody/SelfEnergy.lean
#print axioms GW.Endpoint.ManyBody.cf_fromRows
#print axioms GW.Endpoint.ManyBody.cf_fromBlocks
#print axioms GW.Endpoint.ManyBody.cf_colM
#print axioms GW.Endpoint.ManyBody.cf_AT
#print axioms GW.Endpoint.ManyBody.cf_HHT
#print axioms GW.Endpoint.ManyBody.cf0_AT
#print axioms GW.Endpoint.ManyBody.cf1_AT
#print axioms GW.Endpoint.ManyBody.cf0_HHT
#print axioms GW.Endpoint.ManyBody.cf1_HHT
#print axioms GW.Endpoint.ManyBody.coeff1_dT
#print axioms GW.Endpoint.ManyBody.coeff_dinv
#print axioms GW.Endpoint.ManyBody.phi_fop_phi
#print axioms GW.Endpoint.ManyBody.coeff_resid_left
#print axioms GW.Endpoint.ManyBody.coeff_resid_right
#print axioms GW.Endpoint.ManyBody.coeff_ST
#print axioms GW.Endpoint.ManyBody.cf0_ST
#print axioms GW.Endpoint.ManyBody.cf1_ST
#print axioms GW.Endpoint.ManyBody.cf2_ST
-- ManyBody/Sigma.lean
#print axioms GW.Endpoint.ManyBody.kernel_symm
#print axioms GW.Endpoint.ManyBody.QT_transpose
#print axioms GW.Endpoint.ManyBody.QT_idem
#print axioms GW.Endpoint.ManyBody.NT_QT_comm
#print axioms GW.Endpoint.ManyBody.cf0_QT
#print axioms GW.Endpoint.ManyBody.cf0_NT
#print axioms GW.Endpoint.ManyBody.NT_det
#print axioms GW.Endpoint.ManyBody.cf0_NT_inv
#print axioms GW.Endpoint.ManyBody.NT_inv_QT
#print axioms GW.Endpoint.ManyBody.JT_eq
#print axioms GW.Endpoint.ManyBody.cf0_JT
#print axioms GW.Endpoint.ManyBody.cf1_JT
#print axioms GW.Endpoint.ManyBody.KKT_eq
#print axioms GW.Endpoint.ManyBody.cf_dyn
#print axioms GW.Endpoint.ManyBody.sigma_cf
#print axioms GW.Endpoint.ManyBody.cf_diag_C
#print axioms GW.Endpoint.ManyBody.sigma_coeff0
#print axioms GW.Endpoint.ManyBody.sigma1_eq_HF
#print axioms GW.Endpoint.ManyBody.sigma2_eq
-- ManyBody/DirectSOX.lean
#print axioms GW.Endpoint.ManyBody.sig2p_split
#print axioms GW.Endpoint.ManyBody.sig2h_split
#print axioms GW.Endpoint.ManyBody.sig2_eq_dir_add_sox
#print axioms GW.Endpoint.ManyBody.sigma2_eq_direct_add_sox_add_relax
#print axioms GW.Endpoint.ManyBody.sigma2_eq_direct_add_sox
-- ManyBody/GWSecond.lean
#print axioms GW.Endpoint.ManyBody.gw1_eq_HF
#print axioms GW.Endpoint.ManyBody.list_sum_triples
#print axioms GW.Endpoint.ManyBody.sigGW2t_eq
#print axioms GW.Endpoint.ManyBody.ftDamped_congr_ne_zero
#print axioms GW.Endpoint.ManyBody.occ_mem
#print axioms GW.Endpoint.ManyBody.occ_not_mem
#print axioms GW.Endpoint.ManyBody.sum_occ_restrict
#print axioms GW.Endpoint.ManyBody.sum_occ_restrict'
#print axioms GW.Endpoint.ManyBody.gw2_value
#print axioms GW.Endpoint.ManyBody.gw2_limit
-- ManyBody/GWError.lean
#print axioms GW.Endpoint.ManyBody.gw_error_first_order
#print axioms GW.Endpoint.ManyBody.gw_error_second_order
#print axioms GW.Endpoint.ManyBody.gw_error_second_order_brillouin
#print axioms GW.Endpoint.ManyBody.gw_error_coeff2
-- G2 stage 2: eps from the wavefunction coefficients (GW/Endpoint/Kernel/Eps*.lean).
-- The q1 theorems `GW.Endpoint.Kernel.E1.{eps_in_box, epsinv_true_q1}` live in the slow
-- non-default target `GWKernelData`; audit them with
-- `lake env lean GW/Endpoint/Kernel/AuditEps.lean` after `lake build GWKernelData`.
#print axioms GW.Endpoint.Kernel.Eps.digit_int
#print axioms GW.Endpoint.Kernel.Eps.kron_prod
#print axioms GW.Endpoint.Kernel.Eps.Cfg.slot_iff
#print axioms GW.Endpoint.Kernel.Eps.kOK_sound
#print axioms GW.Endpoint.Kernel.Eps.accRows_spec
#print axioms GW.Endpoint.Kernel.Eps.row_digits
#print axioms GW.Endpoint.Kernel.Eps.u_bounds
#print axioms GW.Endpoint.Kernel.Eps.Y_bound
#print axioms GW.Endpoint.Kernel.Eps.combine
#print axioms GW.Endpoint.Kernel.Eps.sound_rows
-- G2 stage 3: spec A's Sigma / Eqp1 / O1 (GW/Endpoint/Kernel/Sigma*.lean). The composed
-- theorem `GW.Endpoint.Kernel.S3.o1_enclosure` lives in the slow non-default target
-- `GWKernelData`; audit it with `lake env lean GW/Endpoint/Kernel/AuditSigma.lean`.
#print axioms GW.Endpoint.Kernel.Sig.schK_spec
#print axioms GW.Endpoint.Kernel.Sig.ssxK_spec
#print axioms GW.Endpoint.Kernel.Sig.nOK_sound
#print axioms GW.Endpoint.Kernel.Sig.tget_find
#print axioms GW.Endpoint.Kernel.Sig.ieBox_spec
#print axioms GW.Endpoint.Kernel.Sig.om2_spec
#print axioms GW.Endpoint.Kernel.Sig.entChk_sound
#print axioms GW.Endpoint.Kernel.Sig.mkEn_spec
#print axioms GW.Endpoint.Kernel.Sig.vbOK_sound
#print axioms GW.Endpoint.Kernel.Sig.wingOK_sound
#print axioms GW.Endpoint.Kernel.Sig.exOK_sound
#print axioms GW.Endpoint.Kernel.Sig.csOK_sound
#print axioms GW.Endpoint.Kernel.Sig.stq_n
#print axioms GW.Endpoint.Kernel.Sig.stq_x
#print axioms GW.Endpoint.Kernel.Sig.stq_cs
#print axioms GW.Endpoint.Kernel.Sig.sig_bounds
#print axioms GW.Endpoint.Kernel.Sig.eqp1_bounds
#print axioms GW.Endpoint.Kernel.Sig.EHyp_block
-- G2 unfolding: the symmetry unfolding of the irreducible WFN data (GW/Endpoint/Kernel/
-- Unfold.lean, UnfoldPhase.lean). The composed theorems `GW.Endpoint.Kernel.U.epsinv_irr_q*`
-- and `GW.Endpoint.Kernel.U.o1_enclosure_irr` live in the slow non-default target
-- `GWKernelData`; audit them with `lake env lean GW/Endpoint/Kernel/AuditUnfold.lean`.
#print axioms GW.Endpoint.Kernel.Unf.Dy.enc_val
#print axioms GW.Endpoint.Kernel.Unf.Dy.encN_val
#print axioms GW.Endpoint.Kernel.Unf.Dy.flip_val
#print axioms GW.Endpoint.Kernel.Unf.map_eq_of_getD
#print axioms GW.Endpoint.Kernel.Unf.list_eq_of_getD
#print axioms GW.Endpoint.Kernel.Unf.Input.eq_of
#print axioms GW.Endpoint.Kernel.Unf.St.eq_of
#print axioms GW.Endpoint.Kernel.Unf.Gl.eq_of
#print axioms GW.Endpoint.Kernel.Unf.phase_half
#print axioms GW.Endpoint.Kernel.Unf.flipG_phase
#print axioms GW.Endpoint.Kernel.Unf.rot_coef
#print axioms GW.Endpoint.Kernel.Unf.tOK1_sound
#print axioms GW.Endpoint.Kernel.Unf.flipG_neg

-- G4-analytic: the actual self-energy lambda -> Sigma(omega; lambda) of the true ground
-- state agrees with the formal coefficients to O(lambda^3) (GW/Endpoint/ManyBody/{Jet,GroundState,Analytic}.lean).
-- ManyBody/Jet.lean
#print axioms GW.Endpoint.ManyBody.tr2_continuous
#print axioms GW.Endpoint.ManyBody.tr2_zero
#print axioms GW.Endpoint.ManyBody.cube_tendsto
#print axioms GW.Endpoint.ManyBody.cube_isBigO_one
#print axioms GW.Endpoint.ManyBody.tr2_isBigO_one
#print axioms GW.Endpoint.ManyBody.cube_mul_isBigO
#print axioms GW.Endpoint.ManyBody.Jet.tendsto
#print axioms GW.Endpoint.ManyBody.Jet.isBigO_one
#print axioms GW.Endpoint.ManyBody.jet_const
#print axioms GW.Endpoint.ManyBody.jet_X
#print axioms GW.Endpoint.ManyBody.jet_zero
#print axioms GW.Endpoint.ManyBody.jet_one
#print axioms GW.Endpoint.ManyBody.jet_add
#print axioms GW.Endpoint.ManyBody.jet_neg
#print axioms GW.Endpoint.ManyBody.jet_sub
#print axioms GW.Endpoint.ManyBody.jet_mul
#print axioms GW.Endpoint.ManyBody.jet_inv
#print axioms GW.Endpoint.ManyBody.jet_sum
#print axioms GW.Endpoint.ManyBody.Jet.bound
#print axioms GW.Endpoint.ManyBody.jet_of_mem
#print axioms GW.Endpoint.ManyBody.liftJ_map_evJ
#print axioms GW.Endpoint.ManyBody.liftJ_map_sndJ
#print axioms GW.Endpoint.ManyBody.jetM_of
#print axioms GW.Endpoint.ManyBody.jetM_const
#print axioms GW.Endpoint.ManyBody.jetM_one
#print axioms GW.Endpoint.ManyBody.JetM.add
#print axioms GW.Endpoint.ManyBody.JetM.sub
#print axioms GW.Endpoint.ManyBody.JetM.smul
#print axioms GW.Endpoint.ManyBody.JetM.mul
#print axioms GW.Endpoint.ManyBody.JetV.mulVec
#print axioms GW.Endpoint.ManyBody.JetV.dot
#print axioms GW.Endpoint.ManyBody.jet_det
#print axioms GW.Endpoint.ManyBody.JetM.adjugate
#print axioms GW.Endpoint.ManyBody.inv_eq_inv_det_smul_adjugate
#print axioms GW.Endpoint.ManyBody.coeff0_det_ne_zero
#print axioms GW.Endpoint.ManyBody.JetM.inv
#print axioms GW.Endpoint.ManyBody.JetM.eventually_det_ne
-- ManyBody/GroundState.lean
#print axioms GW.Endpoint.ManyBody.mnorm_nonneg
#print axioms GW.Endpoint.ManyBody.abs_le_norm
#print axioms GW.Endpoint.ManyBody.norm_mulVec_le
#print axioms GW.Endpoint.ManyBody.abs_mulVec_le
#print axioms GW.Endpoint.ManyBody.norm_le_of_abs_le
#print axioms GW.Endpoint.ManyBody.norm_phi_le
#print axioms GW.Endpoint.ManyBody.aC_nonneg
#print axioms GW.Endpoint.ManyBody.IsGround.nonDeg
#print axioms GW.Endpoint.ManyBody.inSec_iff
#print axioms GW.Endpoint.ManyBody.inSec_phi
#print axioms GW.Endpoint.ManyBody.InSec.vop
#print axioms GW.Endpoint.ManyBody.InSec.add
#print axioms GW.Endpoint.ManyBody.InSec.sub
#print axioms GW.Endpoint.ManyBody.InSec.smul
#print axioms GW.Endpoint.ManyBody.inSec_Rs
#print axioms GW.Endpoint.ManyBody.Rs_apply_self
#print axioms GW.Endpoint.ManyBody.Rs_eq_Rr
#print axioms GW.Endpoint.ManyBody.H0_Rs
#print axioms GW.Endpoint.ManyBody.phi_dot_eq
#print axioms GW.Endpoint.ManyBody.abs_vop_apply_le
#print axioms GW.Endpoint.ManyBody.norm_Fm_le
#print axioms GW.Endpoint.ManyBody.Fm_sub
#print axioms GW.Endpoint.ManyBody.norm_Fm_sub_le
#print axioms GW.Endpoint.ManyBody.exists_fix
#print axioms GW.Endpoint.ManyBody.δ0_pos
#print axioms GW.Endpoint.ManyBody.small_of_le_δ0
#print axioms GW.Endpoint.ManyBody.chi_spec
#print axioms GW.Endpoint.ManyBody.chi_inSec
#print axioms GW.Endpoint.ManyBody.chi_self
#print axioms GW.Endpoint.ManyBody.psiR_inSec
#print axioms GW.Endpoint.ManyBody.psiR_self
#print axioms GW.Endpoint.ManyBody.psiR_ne_zero
#print axioms GW.Endpoint.ManyBody.eig_exact
#print axioms GW.Endpoint.ManyBody.Fm_zero
#print axioms GW.Endpoint.ManyBody.chi_bound1
#print axioms GW.Endpoint.ManyBody.chi_bound2
#print axioms GW.Endpoint.ManyBody.Am_psi1
#print axioms GW.Endpoint.ManyBody.E1_eq
#print axioms GW.Endpoint.ManyBody.E2_eq
#print axioms GW.Endpoint.ManyBody.Fm_expand
#print axioms GW.Endpoint.ManyBody.chi_bound3
#print axioms GW.Endpoint.ManyBody.E_bound
#print axioms GW.Endpoint.ManyBody.exists_gap
#print axioms GW.Endpoint.ManyBody.δ1_pos
#print axioms GW.Endpoint.ManyBody.abs_psiR_apply_le
#print axioms GW.Endpoint.ManyBody.eq_smul_psiR
#print axioms GW.Endpoint.ManyBody.eigval_eq_of_smul
#print axioms GW.Endpoint.ManyBody.groundPair_psiR
#print axioms GW.Endpoint.ManyBody.groundPair_unique
-- ManyBody/Analytic.lean
#print axioms GW.Endpoint.ManyBody.greenR_smul
#print axioms GW.Endpoint.ManyBody.sigmaR_smul
#print axioms GW.Endpoint.ManyBody.eventually_le_δ0
#print axioms GW.Endpoint.ManyBody.jetV_psiR
#print axioms GW.Endpoint.ManyBody.jet_ER
#print axioms GW.Endpoint.ManyBody.jetM_Hl
#print axioms GW.Endpoint.ManyBody.jetM_K
#print axioms GW.Endpoint.ManyBody.jetM_Mp
#print axioms GW.Endpoint.ManyBody.jetM_Mm
#print axioms GW.Endpoint.ManyBody.jetM_greenR
#print axioms GW.Endpoint.ManyBody.isUnit_det_greenT
#print axioms GW.Endpoint.ManyBody.jetM_green0
#print axioms GW.Endpoint.ManyBody.isUnit_det_green0
#print axioms GW.Endpoint.ManyBody.jetM_sigmaR
#print axioms GW.Endpoint.ManyBody.tr2_sigmaT
#print axioms GW.Endpoint.ManyBody.sigma_exact_expansion
#print axioms GW.Endpoint.ManyBody.sigma_exact_minus_gw
#print axioms GW.Endpoint.ManyBody.sigma_exact_minus_gw_brillouin
-- G2-coulomb: the mini-BZ Coulomb averages (GW/Endpoint/Coulomb/*.lean). The table theorems
-- `GW.Endpoint.Kernel.Coul.{vb_hyp, oq_hyp, o1_enclosure_unconditional}` live in the slow
-- non-default target `GWKernelData`; audit them with
-- `lake env lean GW/Endpoint/Kernel/Data/CoulAudit.lean`.
#print axioms GW.Endpoint.Coulomb.cW_taylor
#print axioms GW.Endpoint.Coulomb.lV_taylor
#print axioms GW.Endpoint.Coulomb.integral_T2_monomial
#print axioms GW.Endpoint.Coulomb.integral_T2_split
#print axioms GW.Endpoint.Coulomb.rule_exact
#print axioms GW.Endpoint.Coulomb.leaf_bound
#print axioms GW.Endpoint.Coulomb.treeChk_sound
#print axioms GW.Endpoint.Coulomb.lintegral_cone
#print axioms GW.Endpoint.Coulomb.Tet.lintegral_signed
#print axioms GW.Endpoint.Coulomb.Tet.real_signed
#print axioms GW.Endpoint.Coulomb.geom_ok
#print axioms GW.Endpoint.Coulomb.cell_eq_union
#print axioms GW.Endpoint.Coulomb.volume_cell
#print axioms GW.Endpoint.Coulomb.cell_lintegral
#print axioms GW.Endpoint.Coulomb.cavg_formula
#print axioms GW.Endpoint.Coulomb.cavg_bound
#print axioms GW.Endpoint.Coulomb.cavg_symm
#print axioms GW.Endpoint.Coulomb.tab_sound
#print axioms GW.Endpoint.Coulomb.rep_of_faces
-- G2 roots: the full GPP QP equation as a function of E and the root-bracket soundness chain
-- (GW/Endpoint/Kernel/Root*.lean). The data theorems `GW.Endpoint.Kernel.R.rootX0`, `rootL0`,
-- `o1_fullQP` live in the slow non-default target `GWKernelData`; audit them with
-- `lake env lean GW/Endpoint/Kernel/AuditRoots.lean`.
#print axioms GW.Endpoint.Kernel.QP.FixedOn.sum
#print axioms GW.Endpoint.Kernel.QP.FixedOn.congr
#print axioms GW.Endpoint.Kernel.QP.FixedOn.comp_sub
#print axioms GW.Endpoint.Kernel.QP.fixed_div_sub
#print axioms GW.Endpoint.Kernel.QP.fixed_div_sq
#print axioms GW.Endpoint.Kernel.QP.fixed_div_add
#print axioms GW.Endpoint.Kernel.QP.dschK_spec
#print axioms GW.Endpoint.Kernel.QP.dssxK_spec
#print axioms GW.Endpoint.Kernel.QP.dcontrib_spec
#print axioms GW.Endpoint.Kernel.QP.dOK_sound
#print axioms GW.Endpoint.Kernel.QP.mkEnP_spec
#print axioms GW.Endpoint.Kernel.QP.mkEI_spec
#print axioms GW.Endpoint.Kernel.QP.quad_scaled
#print axioms GW.Endpoint.Kernel.QP.rq_n
#print axioms GW.Endpoint.Kernel.QP.root_bracket

/-! ## BRIDGE (`GW/Bridge/*.lean`): BerkeleyGW's GPP Sigma derived from G0W0 and compared
with `Kernel/SigmaSpec.lean` up to named departures (`docs/BRIDGE.md`). -/
-- GW/Bridge/FreqIntegral.lean
#print axioms GW.Bridge.g0_eq_G0t
#print axioms GW.Bridge.sigt_eq
#print axioms GW.Bridge.sigt_limit
#print axioms GW.Bridge.wct_limit
#print axioms GW.Bridge.term_occ
#print axioms GW.Bridge.term_emp
#print axioms GW.Bridge.sigc_eq_terms
#print axioms GW.Bridge.sigc_eq_sx_ch
-- GW/Bridge/GPPModel.lean
#print axioms GW.Bridge.gppC_eq_gppInvEps
#print axioms GW.Bridge.gppC_pole_form
#print axioms GW.Bridge.gppC_static
#print axioms GW.Bridge.tail_helper
#print axioms GW.Bridge.singlePole_tail
#print axioms GW.Bridge.gppC_tail
#print axioms GW.Bridge.fsum_moment
#print axioms GW.Bridge.matchTail_iff
#print axioms GW.Bridge.singlePole_zero
#print axioms GW.Bridge.matchStatic_iff
#print axioms GW.Bridge.single_pole_exists_iff
#print axioms GW.Bridge.single_pole_unique
#print axioms GW.Bridge.valid_neg_weight
#print axioms GW.Bridge.invalid_of_one_zero
#print axioms GW.Bridge.bgw_invalid_mode
#print axioms GW.Bridge.bgw_dropped
#print axioms GW.Bridge.static_pole_limit
#print axioms GW.Bridge.sch_static_limit
#print axioms GW.Bridge.ssx_static_limit
#print axioms GW.Bridge.sch_static_error
-- GW/Bridge/Bloch.lean
#print axioms GW.Bridge.vBareK_key
#print axioms GW.Bridge.omT_head
#print axioms GW.Bridge.quad_sub
#print axioms GW.Bridge.quad_smul
#print axioms GW.Bridge.quad_congr
#print axioms GW.Bridge.quad_eq_wgt
#print axioms GW.Bridge.bloch_sigc_eq
#print axioms GW.Bridge.bloch_limit
#print axioms GW.Bridge.bloch_wcFreq
#print axioms GW.Bridge.screened_entry
#print axioms GW.Bridge.pd_neg
#print axioms GW.Bridge.pd_closure
-- GW/Bridge/Compare.lean
#print axioms GW.Bridge.TS_pos
#print axioms GW.Bridge.keep_facts
#print axioms GW.Bridge.mode_eq
#print axioms GW.Bridge.emp_near_zero
#print axioms GW.Bridge.occ_generic_clamp
#print axioms GW.Bridge.occ_near_clamp
#print axioms GW.Bridge.occ_pole_point
#print axioms GW.Bridge.discrepancy_witness
#print axioms GW.Bridge.wxS_eq
#print axioms GW.Bridge.wxS_close
#print axioms GW.Bridge.epsS_eq
#print axioms GW.Bridge.wing_factors_point
#print axioms GW.Bridge.om2S_eq
#print axioms GW.Bridge.Pq_eq_quad
#print axioms GW.Bridge.sigA_eq_theory
#print axioms GW.Bridge.cor_eq
#print axioms GW.Bridge.chpart_sum_eq_exact
#print axioms GW.Bridge.sigA_eq_theory_complete
#print axioms GW.Bridge.eqp1_linear

/-! ## BRIDGE-EPS (`GW/Bridge/Eps*.lean`): the static RPA dielectric matrix derived from
the time-ordered `G0` and compared with `Kernel/EpsSpec.lean` (`docs/BRIDGE.md`). -/
-- GW/Bridge/EpsChi0.lean
#print axioms GW.Bridge.gF_eq_G0t
#print axioms GW.Bridge.chi0F_eq_chi0t
#print axioms GW.Bridge.sum_pairs_toList
#print axioms GW.Bridge.chi0F_pos
#print axioms GW.Bridge.chi0F_neg
#print axioms GW.Bridge.chiF_eq
#print axioms GW.Bridge.f_mem
#print axioms GW.Bridge.f_not_mem
#print axioms GW.Bridge.chiF_limit
#print axioms GW.Bridge.sum_split
#print axioms GW.Bridge.chiW_zero
#print axioms GW.Bridge.chiS_diag_nonpos
#print axioms GW.Bridge.excOff_zero
#print axioms GW.Bridge.chiW_continuousAt
-- GW/Bridge/EpsBloch.lean
#print axioms GW.Bridge.compl_prod_univ
#print axioms GW.Bridge.spin_chiS
#print axioms GW.Bridge.split_img
#print axioms GW.Bridge.bloch_chi
#print axioms GW.Bridge.rem_zero
#print axioms GW.Bridge.chi_eq_triples
#print axioms GW.Bridge.epsSpec_chi_eq_theory
#print axioms GW.Bridge.epsSpec_chi_eq_theory_bands
#print axioms GW.Bridge.factor_two_wrong
-- GW/Bridge/EpsRPA.lean
#print axioms GW.Bridge.epsM_chi0_eq_dielectric
#print axioms GW.Bridge.WM_entry
#print axioms GW.Bridge.rpa_solve
#print axioms GW.Bridge.rpa_unique
#print axioms GW.Bridge.rpa_dyson
#print axioms GW.Bridge.partialScreened_eq_coeff_sum
#print axioms GW.Bridge.rpa_neumann
#print axioms GW.Bridge.chiMat_eq_chi0
#print axioms GW.Bridge.theory_eps_eq_dielectric
#print axioms GW.Bridge.chiMatW_zero
#print axioms GW.Bridge.wDyn_tendsto
#print axioms GW.Bridge.sqD_mul_sqD
#print axioms GW.Bridge.epsM_mul_sq
#print axioms GW.Bridge.det_sqD_ne
#print axioms GW.Bridge.det_epsSym
#print axioms GW.Bridge.sym_W
#print axioms GW.Bridge.WM_symm
-- GW/Bridge/EpsCompare.lean
#print axioms GW.Bridge.one_fin_apply
#print axioms GW.Bridge.epsSpec_eq_theory_rem
#print axioms GW.Bridge.epsSpec_eq_theory
#print axioms GW.Bridge.spin_excOff
#print axioms GW.Bridge.epsTheory_entry_limit
#print axioms GW.Bridge.Espec_eq_Etheory
#print axioms GW.Bridge.etheory_W
#print axioms GW.Bridge.sigA_eps_eq_theory
#print axioms GW.Bridge.sigA_eps_eq_theory_complete

/-! ## BRIDGE-Q0 (`GW/Bridge/EpsQ0*.lean`): the `q → 0` limit of the RPA screening and
SigmaSpec's `q = 0` rule against it (`docs/BRIDGE.md`). -/
-- GW/Bridge/EpsQ0.lean
#print axioms GW.Bridge.KPRay.ne_eventually
#print axioms GW.Bridge.KPRay.M_div_tendsto
#print axioms GW.Bridge.KPRay.den_tendsto
#print axioms GW.Bridge.KPRay.M_tendsto
#print axioms GW.Bridge.KPRay.head_tendsto
#print axioms GW.Bridge.KPRay.wing_tendsto
#print axioms GW.Bridge.KPRay.wing'_tendsto
#print axioms GW.Bridge.KPRay.body_tendsto
#print axioms GW.Bridge.KPRay.head_coef_nonpos
#print axioms GW.Bridge.scv_ne
#print axioms GW.Bridge.eps_conj
#print axioms GW.Bridge.diag_inv
#print axioms GW.Bridge.diag_inv'
#print axioms GW.Bridge.inv_scaled
#print axioms GW.Bridge.coulomb_head
#print axioms GW.Bridge.vSc_off
#print axioms GW.Bridge.q0_limit
#print axioms GW.Bridge.chiSc_tendsto
#print axioms GW.Bridge.schur_body
#print axioms GW.Bridge.schur_head
#print axioms GW.Bridge.sgn_sq
#print axioms GW.Bridge.chi0s_neg
#print axioms GW.Bridge.parity_inv
#print axioms GW.Bridge.inv_perturb
#print axioms GW.Bridge.entry_le_linfty
#print axioms GW.Bridge.q0_error
-- GW/Bridge/EpsQ0Sigma.lean
#print axioms GW.Bridge.wTilde_neg
#print axioms GW.Bridge.thK_odd
#print axioms GW.Bridge.thK_zeroO
#print axioms GW.Bridge.sum_odd_zero
#print axioms GW.Bridge.integral_odd_zero
#print axioms GW.Bridge.wing_avg_zero
#print axioms GW.Bridge.wing_sum_zero
#print axioms GW.Bridge.head_avg
#print axioms GW.Bridge.head_avg_spec
#print axioms GW.Bridge.vec_zero
#print axioms GW.Bridge.dotB_zero_left
#print axioms GW.Bridge.omT_wing
#print axioms GW.Bridge.specMode_zeroI
#print axioms GW.Bridge.epsS_wing
#print axioms GW.Bridge.epsS_off
#print axioms GW.Bridge.sigA_eq_theory_q0
#print axioms GW.Bridge.sigA_eps_eq_theory_q0
#print axioms GW.Bridge.epsSpec_q0_scaled
#print axioms GW.Bridge.vT_head
/-! ## BRIDGE-DISC (`GW/Bridge/Disc.lean`): the GPP kernel discontinuity at
`(x, Ω²) = (0, 0)` and the ideal-metric zeros of `Ω²` (`docs/BRIDGE.md`). -/
-- GW/Bridge/Disc.lean
#print axioms GW.Bridge.wTilde_param
#print axioms GW.Bridge.valid_param
#print axioms GW.Bridge.thK_emp_param
#print axioms GW.Bridge.thK_occ_param
#print axioms GW.Bridge.thK_emp_eq
#print axioms GW.Bridge.thK_occ_eq
#print axioms GW.Bridge.thK_emp_x0
#print axioms GW.Bridge.thK_occ_x0
#print axioms GW.Bridge.thK_zero_strength
#print axioms GW.Bridge.validSide_neBot
#print axioms GW.Bridge.thK_x0_tendsto
#print axioms GW.Bridge.thK_O0_tendsto
#print axioms GW.Bridge.wTilde_tendsto_zero
#print axioms GW.Bridge.thK_tendsto_zero_of_ne
#print axioms GW.Bridge.thK_not_continuousAt
#print axioms GW.Bridge.thK_not_continuousAt_occ
#print axioms GW.Bridge.thK_cluster
#print axioms GW.Bridge.residue_eq
#print axioms GW.Bridge.emp_as_pole
#print axioms GW.Bridge.occ_as_pole
#print axioms GW.Bridge.residue_tendsto_zero
#print axioms GW.Bridge.gppC_zero_strength
#print axioms GW.Bridge.singlePole_zero_strength
#print axioms GW.Bridge.gppC_limit_off0
#print axioms GW.Bridge.blochSys_R_zero
#print axioms GW.Bridge.dotB_eq_dotM
#print axioms GW.Bridge.dotM_ideal
#print axioms GW.Bridge.dotM_ideal_int
#print axioms GW.Bridge.ideal_gap
#print axioms GW.Bridge.vec_half
#print axioms GW.Bridge.ideal_gap_vec
#print axioms GW.Bridge.dotM_perturb
#print axioms GW.Bridge.cExp_eq
#print axioms GW.Bridge.cExp_pos
#print axioms GW.Bridge.bExp_sub_ideal
#print axioms GW.Bridge.bExp_close
#print axioms GW.Bridge.omB_bd
#print axioms GW.Bridge.om2S_eq_omB
#print axioms GW.Bridge.omB_ideal_eq_zero_iff
#print axioms GW.Bridge.omB_ideal_zero
#print axioms GW.Bridge.om2S_orth_bound
#print axioms GW.Bridge.drop_eq_ideal
#print axioms GW.Bridge.disc_mode
#print axioms GW.Bridge.sigA_eq_theory_disc
/-! ## BRIDGE-COR (`GW/Bridge/Cor.lean`): a proved enclosure of the omitted-band dynamic
Coulomb-hole tail replacing the empirical `½` of the static remainder (`docs/BRIDGE.md`). -/
-- GW/Bridge/Cor.lean
#print axioms GW.Bridge.theta_pos
#print axioms GW.Bridge.theta_le_one
#print axioms GW.Bridge.theta_anti
#print axioms GW.Bridge.theta_lower
#print axioms GW.Bridge.thK_empty_ratio
#print axioms GW.Bridge.thK_empty_enclosure
#print axioms GW.Bridge.thK_empty_invalid
#print axioms GW.Bridge.thK_empty_abs
#print axioms GW.Bridge.mid_enclose
#print axioms GW.Bridge.rK_nonneg
#print axioms GW.Bridge.abs_neg_half
#print axioms GW.Bridge.thK_tail_mode
#print axioms GW.Bridge.wtM_pos
#print axioms GW.Bridge.schM_tail_ratio
#print axioms GW.Bridge.rS_nonneg
#print axioms GW.Bridge.specK_tail_mode
#print axioms GW.Bridge.psi_eq
#print axioms GW.Bridge.psi_pos
#print axioms GW.Bridge.psi_anti
#print axioms GW.Bridge.rKd_nonneg
#print axioms GW.Bridge.thK_diff_mode
#print axioms GW.Bridge.rSd_nonneg
#print axioms GW.Bridge.specK_diff_mode
#print axioms GW.Bridge.pd_eq_amp
#print axioms GW.Bridge.pd_closure_amp
#print axioms GW.Bridge.cloP_eq_rho
#print axioms GW.Bridge.tail_core
#print axioms GW.Bridge.sum_prod_expand
#print axioms GW.Bridge.xR_one
#print axioms GW.Bridge.tailK_eq
#print axioms GW.Bridge.tail_sum
#print axioms GW.Bridge.sigT_tail_enclose
#print axioms GW.Bridge.sigT_all_bands
#print axioms GW.Bridge.sigT_diff_all_bands
#print axioms GW.Bridge.sigA_all_bands
#print axioms GW.Bridge.sigA_diff_all_bands
#print axioms GW.Bridge.trunc_kq
#print axioms GW.Bridge.getD_take
#print axioms GW.Bridge.xS_trunc
#print axioms GW.Bridge.xT_trunc
#print axioms GW.Bridge.wxS_trunc
#print axioms GW.Bridge.nbq_trunc
#print axioms GW.Bridge.Xq_trunc
#print axioms GW.Bridge.PT_trunc
#print axioms GW.Bridge.ACq_trunc
#print axioms GW.Bridge.Pq_trunc
#print axioms GW.Bridge.CSq_trunc
#print axioms GW.Bridge.quad_add
#print axioms GW.Bridge.xT_one
#print axioms GW.Bridge.TZ_lt_half
#print axioms GW.Bridge.sigT_split
#print axioms GW.Bridge.sigA_split
#print axioms GW.Bridge.acq_pq_tail
#print axioms GW.Bridge.mR_complOf
#print axioms GW.Bridge.xR_complOf
#print axioms GW.Bridge.quadR_complOf
#print axioms GW.Bridge.completeK_of_complete
#print axioms GW.Bridge.sigTall_of_state
#print axioms GW.Bridge.sigAall_of_state

/-! ## REVIEW-28 corrections: R28-F1 (`GW/Bridge/Common.lean`), R28-F4
(`GW/Bridge/CorResidual.lean`). -/
#print axioms GW.Bridge.Common.sigA_common
#print axioms GW.Bridge.Common.sigA_compat
#print axioms GW.Bridge.Common.MF.blk_ok
#print axioms GW.Bridge.Common.compat_st_unique
#print axioms GW.Bridge.Common.compat_energy_shift
#print axioms GW.Bridge.Common.inp_pins
#print axioms GW.Bridge.Common.coulomb_same
#print axioms GW.Bridge.Common.omT_dens
#print axioms GW.Bridge.Common.Espec_q0_input
#print axioms GW.Bridge.Common.compat_self
#print axioms GW.Bridge.Common.offgrid_loophole
#print axioms GW.Bridge.Common.MF.tr_fixed
#print axioms GW.Bridge.Common.compat_selfpaired_no_TR
#print axioms GW.Bridge.Common.hyps_unsat_of_unpaired
#print axioms GW.Bridge.Common.hyps_unsat_of_selfpaired
#print axioms GW.Bridge.sigAall_static_split
#print axioms GW.Bridge.cor_all_decomp
#print axioms GW.Bridge.corScale_one
#print axioms GW.Bridge.corShift_eq_zero
#print axioms GW.Bridge.corGch_eq_zero
#print axioms GW.Bridge.cor_all_eq_zero
#print axioms GW.Bridge.sigAall_of_closure
#print axioms GW.Bridge.cor_decomp_complete
#print axioms GW.Bridge.COR_decomp_complete
#print axioms GW.Bridge.cor_eq_zero_of_closure
#print axioms GW.Bridge.corAll_of_state
#print axioms GW.Bridge.wit_cor
#print axioms GW.Bridge.wit_shift
#print axioms GW.Bridge.nn_corAll_zero
#print axioms GW.Bridge.nn_scale_fails
#print axioms GW.Bridge.nn_not_shiftClosed
#print axioms GW.Bridge.nn_weighted
#print axioms GW.Bridge.nn_gch_misses
#print axioms GW.Bridge.sc_corAll

/-! ## REVIEW-28 correction R28-F3 (`GW/Bridge/CorPerturb*.lean`). -/
#print axioms GW.Bridge.Lowdin.lowdin
#print axioms GW.Bridge.Lowdin.lowdin_nat
#print axioms GW.Bridge.Lowdin.exists_completion_nat
#print axioms GW.Bridge.exists_true_rows
#print axioms GW.Bridge.exists_compl
#print axioms GW.Bridge.tailP_eq
#print axioms GW.Bridge.tailP_close
#print axioms GW.Bridge.tailP_sum
#print axioms GW.Bridge.specKc_abs_le
#print axioms GW.Bridge.sigA_all_bands_true
#print axioms GW.Bridge.sigA_diff_all_bands_true
#print axioms GW.Bridge.sigT_all_bands_true
#print axioms GW.Bridge.sigT_diff_all_bands_true
#print axioms GW.Bridge.sigA_all_bands_lowdin
#print axioms GW.Bridge.f3_witness
#print axioms GW.Bridge.f3_witness_one
