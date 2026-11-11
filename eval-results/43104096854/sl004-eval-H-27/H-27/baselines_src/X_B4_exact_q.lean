import SL003Target

set_option maxHeartbeats 2000000 in
theorem SL004.bridge_B4_exact_q : SL003FC.Erdos865.SL003.targetProp := by
  unfold SL003FC.Erdos865.SL003.targetProp
  have h := @Erdos865.erdos865
  exact?
