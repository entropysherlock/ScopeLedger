import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B2_convert_rfl : SL003FC.Erdos673.SL003.targetProp := by
  unfold SL003FC.Erdos673.SL003.targetProp
  have h := @Erdos673.erdos_673
  convert h using 3 <;> rfl
