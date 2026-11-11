import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos235.SL003.targetProp := by
  unfold SL003FC.Erdos235.SL003.targetProp
  simpa [N, coprimeList, countGaps, gaps, proportion] using @Erdos235.erdos_235
