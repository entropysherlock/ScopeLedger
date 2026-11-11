import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E1_twin_exact : SL003FC.OeisA397588.SL003.targetProp := by
  unfold SL003FC.OeisA397588.SL003.targetProp
  with_unfolding_all exact @A397588.a_three_dvd
