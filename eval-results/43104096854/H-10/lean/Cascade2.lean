import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos534.SL003.targetProp := by
  unfold SL003FC.Erdos534.SL003.targetProp
  simpa [IsAdmissible, ahlswedeKhachatrian, maxCard, primePrefix] using @Erdos534.erdos_534
