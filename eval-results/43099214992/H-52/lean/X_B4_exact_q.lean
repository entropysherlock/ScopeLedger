import SL003Target

set_option maxHeartbeats 2000000 in
theorem SL004.bridge_B4_exact_q : SL003FC.OeisA361033.SL003.targetProp := by
  unfold SL003FC.OeisA361033.SL003.targetProp
  have h := @A361033.a_odd_iff
  exact?
