import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos742.variants.SL003.targetProp := by
  unfold SL003FC.Erdos742.variants.SL003.targetProp
  simpa [IsDiameter2Critical] using @Erdos742.erdos_742
