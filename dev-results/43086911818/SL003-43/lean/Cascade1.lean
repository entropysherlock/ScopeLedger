import SL003Target

theorem SL003.cascade1 : SL003FC.MonochromaticQuantumGraph.SL003.targetProp := by
  unfold SL003FC.MonochromaticQuantumGraph.SL003.targetProp
  exact_mod_cast @QuantumLean.FormalConjecturesWrappers.eqSystem8_no_solution_d3_trinary_int
