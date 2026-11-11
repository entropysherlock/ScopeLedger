import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos1196.SL003.targetProp := by
  unfold SL003FC.Erdos1196.SL003.targetProp
  simpa [IsPrimitive] using @Erdos1196.erdos_1196
