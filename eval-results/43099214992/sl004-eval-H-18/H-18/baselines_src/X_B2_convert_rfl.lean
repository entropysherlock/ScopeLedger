import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B2_convert_rfl : SL003FC.Erdos354.SL003.targetProp := by
  unfold SL003FC.Erdos354.SL003.targetProp
  have h := @Dyadic354.UpstreamBridge.erdos354_strong_upstream
  convert h using 3 <;> rfl
