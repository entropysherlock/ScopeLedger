import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B2_convert_rfl : SL003FC.Erdos522.SL003.targetProp := by
  unfold SL003FC.Erdos522.SL003.targetProp
  have h := @E522.erdos_522_zero_one_solved
  convert h using 3 <;> rfl
