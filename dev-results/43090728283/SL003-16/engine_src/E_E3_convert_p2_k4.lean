import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E3_convert_p2_k4 : SL003FC.Erdos690.SL003.targetProp := by
  unfold SL003FC.Erdos690.SL003.targetProp
  have h := (@Erdos690.erdos_690).2
  convert h using 4 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp))
