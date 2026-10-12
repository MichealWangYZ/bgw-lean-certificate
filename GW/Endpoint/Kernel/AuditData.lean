/-
Axiom audit of the kernel-checked eps⁻¹ enclosures (non-default target
`GWKernelData`). Run after `lake build GWKernelData`:
  lake env lean GW/Endpoint/Kernel/AuditData.lean
Expected: each depends on `propext`, `Classical.choice`, `Quot.sound` at most
(the `decide +kernel` row theorems add no axioms).
-/
import GW.Endpoint.Kernel.Data.Q0Check
import GW.Endpoint.Kernel.Data.Q1Check
import GW.Endpoint.Kernel.Data.Q2Check

#print axioms GW.Endpoint.Kernel.Q0.epsinv_enclosure_q0
#print axioms GW.Endpoint.Kernel.Q1.epsinv_enclosure_q1
#print axioms GW.Endpoint.Kernel.Q2.epsinv_enclosure_q2
#print axioms GW.Endpoint.Kernel.Q1.e_0
