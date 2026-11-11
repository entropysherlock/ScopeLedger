import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E2_iff_mp : SL003FC.Erdos354.SL003.targetProp := by
  unfold SL003FC.Erdos354.SL003.targetProp
  first | exact (@Dyadic354.UpstreamBridge.erdos354_strong_upstream).mp trivial | with_unfolding_all exact (@Dyadic354.UpstreamBridge.erdos354_strong_upstream).mp trivial
