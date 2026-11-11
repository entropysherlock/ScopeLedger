import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos1195.SL003.targetProp := by
  unfold SL003FC.Erdos1195.SL003.targetProp
  simpa [HasSet, IntegerRatioFree, IsGrowthRate, countingFunction, erdos_1195.answer] using @Erdos1195.erdos_1195
