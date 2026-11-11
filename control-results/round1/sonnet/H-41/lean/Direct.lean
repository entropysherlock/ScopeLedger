import SL003Target

theorem SL003.direct : SL003FC.MonochromaticQuantumGraph.SL003.targetProp := by
  unfold SL003FC.MonochromaticQuantumGraph.SL003.targetProp
  exact @QuantumLean.FormalConjecturesWrappers.eqSystem8_no_solution_d3_int
