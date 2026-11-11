import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E4_norm_p0 : SL003FC.OeisA397588.SL003.targetProp := by
  unfold SL003FC.OeisA397588.SL003.targetProp
  have h := @A397588.a_three_dvd
  simp only [true_iff, iff_true, Filter.eventually_atTop, ge_iff_le, gt_iff_lt, exists_prop, and_imp, not_not, Set.mem_setOf_eq] at h ⊢
  first
    | exact h
    | with_unfolding_all exact h
    | (convert h using 2 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp)))
    | (convert h using 4 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp)))
