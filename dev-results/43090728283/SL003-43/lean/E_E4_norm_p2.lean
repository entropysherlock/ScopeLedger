import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E4_norm_p2 : SL003FC.MonochromaticQuantumGraph.SL003.targetProp := by
  unfold SL003FC.MonochromaticQuantumGraph.SL003.targetProp
  have h := (@QuantumLean.FormalConjecturesWrappers.eqSystem8_no_solution_d3_trinary_int).2
  simp only [true_iff, iff_true, Filter.eventually_atTop, ge_iff_le, gt_iff_lt, exists_prop, and_imp, not_not, Set.mem_setOf_eq] at h ⊢
  first
    | exact h
    | with_unfolding_all exact h
    | (convert h using 2 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp)))
    | (convert h using 4 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp)))
