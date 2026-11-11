import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos877.SL003.targetProp := by
  unfold SL003FC.Erdos877.SL003.targetProp
  simpa [IsMaximalSumFree, fm] using @Erdos877.erdos_877_exponential_bound
