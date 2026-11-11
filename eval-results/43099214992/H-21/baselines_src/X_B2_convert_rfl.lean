import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B2_convert_rfl : SL003FC.Erdos841.SL003.targetProp := by
  unfold SL003FC.Erdos841.SL003.targetProp
  have h := @Erdos841.erdos841_many_small_values_global
  convert h using 3 <;> rfl
