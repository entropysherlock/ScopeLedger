import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos690.SL003.targetProp := by
  unfold SL003FC.Erdos690.SL003.targetProp
  simpa [IsUnimodalOnPrimes, kthPrimeFactorSet] using @Erdos690.erdos_690
