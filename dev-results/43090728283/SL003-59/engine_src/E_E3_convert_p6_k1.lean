import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E3_convert_p6_k1 : SL003FC.OeisA397588.SL003.targetProp := by
  unfold SL003FC.OeisA397588.SL003.targetProp
  have h := (@A397588.a_three_dvd).2.2.2
  convert h using 1 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp))
