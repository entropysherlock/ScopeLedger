import SL003Target

set_option maxHeartbeats 2000000 in
theorem SL004.bridge_B4_exact_q : SL003FC.Erdos354.SL003.targetProp := by
  unfold SL003FC.Erdos354.SL003.targetProp
  have h := @Dyadic354.UpstreamBridge.erdos354_strong_upstream
  exact?
