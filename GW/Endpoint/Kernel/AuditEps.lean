/-
Axiom audit of the G2 stage-2 theorems (non-default target `GWKernelData`). Run after
`lake build GWKernelData`:
  lake env lean GW/Endpoint/Kernel/AuditEps.lean
Expected: `propext`, `Classical.choice`, `Quot.sound` at most (the `decide +kernel`
data theorems add no axioms).
-/
import GW.Endpoint.Kernel.Data.E0Check
import GW.Endpoint.Kernel.Data.E1Check
import GW.Endpoint.Kernel.Data.E2Check
import GW.Endpoint.Kernel.Data.E0Tamper
import GW.Endpoint.Kernel.Data.E1Tamper
import GW.Endpoint.Kernel.Data.E2Tamper

#print axioms GW.Endpoint.Kernel.E0.epsinv_true_q0
#print axioms GW.Endpoint.Kernel.E2.epsinv_true_q2

#print axioms GW.Endpoint.Kernel.E1.epsinv_true_q1
#print axioms GW.Endpoint.Kernel.E1.eps_in_box
#print axioms GW.Endpoint.Kernel.E1.kall
#print axioms GW.Endpoint.Kernel.E1.kok0
#print axioms GW.Endpoint.Kernel.E1.glob
#print axioms GW.Endpoint.Kernel.E1.rows0
#print axioms GW.Endpoint.Kernel.E1.tamper_coef
#print axioms GW.Endpoint.Kernel.E1.tamper_box
