import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos667.SL003.targetProp := by
  unfold SL003FC.Erdos667.SL003.targetProp
  simpa [H, LocallyDense, c] using @Erdos667.variants.monotoneOn
