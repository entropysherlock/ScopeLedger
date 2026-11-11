import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E3_convert_p2_k3 : SL003FC.Erdos525.SL003.targetProp := by
  unfold SL003FC.Erdos525.SL003.targetProp
  have h := (@Erdos525.erdos_525).2
  convert h using 3 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp))
