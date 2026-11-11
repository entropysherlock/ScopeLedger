import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B3_aesop : SL003FC.SL003.targetProp := by
  unfold SL003FC.SL003.targetProp
  have h := @Erdos499.erdos_499
  aesop
