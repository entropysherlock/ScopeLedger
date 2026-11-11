import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B2_convert_rfl : SL003FC.Erdos667.SL003.targetProp := by
  unfold SL003FC.Erdos667.SL003.targetProp
  have h := @Erdos667.variants.monotoneOn
  convert h using 3 <;> rfl
