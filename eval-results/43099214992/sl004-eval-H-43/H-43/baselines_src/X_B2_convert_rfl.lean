import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B2_convert_rfl : SL003FC.Erdos261.SL003.targetProp := by
  unfold SL003FC.Erdos261.SL003.targetProp
  have h := @Erdos261.Palomar.borwein_loring
  convert h using 3 <;> rfl
