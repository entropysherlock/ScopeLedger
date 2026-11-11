import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos354.SL003.targetProp := by
  unfold SL003FC.Erdos354.SL003.targetProp
  simpa [FloorMultiples, FloorMultiples.interleave] using @Dyadic354.UpstreamBridge.erdos354_strong_upstream
