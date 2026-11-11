import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E2_iff_mp : SL003FC.MonochromaticQuantumGraph.SL003.targetProp := by
  unfold SL003FC.MonochromaticQuantumGraph.SL003.targetProp
  first | exact (@QuantumLean.FormalConjecturesWrappers.eqSystem8_no_solution_d3_trinary_int).mp trivial | with_unfolding_all exact (@QuantumLean.FormalConjecturesWrappers.eqSystem8_no_solution_d3_trinary_int).mp trivial
