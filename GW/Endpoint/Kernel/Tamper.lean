/-
G2 stage 1: negative controls. The checker must REJECT a tampered q1
certificate (each theorem states a check evaluates to `false`, by kernel
reduction). Part of the non-default target `GWKernelData`.
-/
import GW.Endpoint.Kernel.Data.Q1

namespace GW.Endpoint.Kernel.Q1
open GW.Endpoint.Kernel

/-- Claimed enclosure too narrow (lower end replaced by the upper end). -/
theorem tamper_out : ({ cert with outLo := cert.outHi }).chkRow 0 = false := by decide +kernel

/-- `F` hint too small (replaced by the far smaller `T2`). -/
theorem tamper_F : ({ cert with F := cert.T2 }).chkE 0 = false := by decide +kernel

/-- `T1` hint too small (replaced by `T2`). -/
theorem tamper_T1 : cert.chkMul cert.K cert.T0 cert.T2 0 = false := by decide +kernel

/-- Tail dropped. -/
theorem tamper_tail : ({ cert with tail := 0 }).chkGlobal = false := by decide +kernel

/-- eps lower endpoints changed without updating the ℕ encodings `mid2`, `rad2`. -/
theorem tamper_eps : ({ cert with epsLo := cert.epsHi }).chkRow 0 = false := by decide +kernel

end GW.Endpoint.Kernel.Q1
