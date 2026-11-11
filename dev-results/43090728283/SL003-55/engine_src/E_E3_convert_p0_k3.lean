import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E3_convert_p0_k3 : SL003FC.Erdos841.SL003.targetProp := by
  unfold SL003FC.Erdos841.SL003.targetProp
  have h := @Erdos841.erdos841_lower_bound_explicit
  convert h using 3 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp))
