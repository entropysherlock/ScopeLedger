import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos525.SL003.targetProp := by
  unfold SL003FC.Erdos525.SL003.targetProp
  simpa [eval, exceptional, m, prob] using @Erdos525.erdos_525
