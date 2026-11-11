import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos49.SL003.targetProp := by
  unfold SL003FC.Erdos49.SL003.targetProp
  simpa [f, g] using @Erdos49.erdos_49_quantitative
