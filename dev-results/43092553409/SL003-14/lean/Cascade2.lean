import SL003Target

theorem SL003.cascade2 : SL003FC.MonochromaticQuantumGraph.SL003.targetProp := by
  unfold SL003FC.MonochromaticQuantumGraph.SL003.targetProp
  simpa [EqSystemN, Witness4_d2, Witness4_d3, Witness6_d2, allEqual, allEqualList, mkEdge, pmSumList, pmSumListAux, pmSumN, vertices] using @QuantumLean.FormalConjecturesWrappers.eqSystem6_no_solution_d3_trinary_int
