import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E3_convert_p0_k4 : SL003FC.OeisA397588.SL003.targetProp := by
  unfold SL003FC.OeisA397588.SL003.targetProp
  have h := @A397588.a_three_dvd
  convert h using 4 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp))
