import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos841.SL003.targetProp := by
  unfold SL003FC.Erdos841.SL003.targetProp
  simpa [t] using @Erdos841.erdos841_lower_bound_explicit
