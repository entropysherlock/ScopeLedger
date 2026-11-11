import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B3_aesop : SL003FC.OeisA361033.SL003.targetProp := by
  unfold SL003FC.OeisA361033.SL003.targetProp
  have h := @A361033.a_odd_iff
  aesop
