import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B2_convert_rfl : SL003FC.SL003.targetProp := by
  unfold SL003FC.SL003.targetProp
  have h := @Erdos499.erdos_499
  convert h using 3 <;> rfl
