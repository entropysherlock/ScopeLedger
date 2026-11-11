import SL003Target

theorem SL003.cascade1 : SL003FC.Erdos354.SL003.targetProp := by
  unfold SL003FC.Erdos354.SL003.targetProp
  exact_mod_cast @Dyadic354.UpstreamBridge.erdos354_strong_upstream
