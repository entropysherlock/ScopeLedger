import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B2_convert_rfl : SL003FC.OeisA361033.SL003.targetProp := by
  unfold SL003FC.OeisA361033.SL003.targetProp
  have h := @A361033.a_odd_iff
  convert h using 3 <;> rfl
