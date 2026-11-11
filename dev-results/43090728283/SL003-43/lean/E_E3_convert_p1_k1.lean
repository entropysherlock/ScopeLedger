import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E3_convert_p1_k1 : SL003FC.MonochromaticQuantumGraph.SL003.targetProp := by
  unfold SL003FC.MonochromaticQuantumGraph.SL003.targetProp
  have h := (@QuantumLean.FormalConjecturesWrappers.eqSystem8_no_solution_d3_trinary_int).1
  convert h using 1 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp))
