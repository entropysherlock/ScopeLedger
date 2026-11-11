import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B2_convert_rfl : SL003FC.MonochromaticQuantumGraph.SL003.targetProp := by
  unfold SL003FC.MonochromaticQuantumGraph.SL003.targetProp
  have h := @QuantumLean.FormalConjecturesWrappers.eqSystem8_no_solution_d3_int
  convert h using 3 <;> rfl
