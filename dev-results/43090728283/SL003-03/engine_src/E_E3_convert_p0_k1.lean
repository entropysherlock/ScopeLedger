import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E3_convert_p0_k1 : SL003FC.Erdos581.SL003.targetProp := by
  unfold SL003FC.Erdos581.SL003.targetProp
  have h := @Erdos581.erdos_581
  convert h using 1 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp))
