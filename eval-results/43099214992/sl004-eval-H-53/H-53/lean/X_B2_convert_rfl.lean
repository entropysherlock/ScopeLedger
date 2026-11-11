import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B2_convert_rfl : SL003FC.Erdos109.SL003.targetProp := by
  unfold SL003FC.Erdos109.SL003.targetProp
  have h := @Erdos109.erdos_109
  convert h using 3 <;> rfl
