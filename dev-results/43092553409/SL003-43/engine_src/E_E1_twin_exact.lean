import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E1_twin_exact : SL003FC.MonochromaticQuantumGraph.SL003.targetProp := by
  unfold SL003FC.MonochromaticQuantumGraph.SL003.targetProp
  with_unfolding_all exact @QuantumLean.FormalConjecturesWrappers.eqSystem8_no_solution_d3_trinary_int
