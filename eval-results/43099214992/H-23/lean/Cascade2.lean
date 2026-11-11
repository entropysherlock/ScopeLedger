import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos1180.SL003.targetProp := by
  unfold SL003FC.Erdos1180.SL003.targetProp
  simpa [C, Represents] using @Erdos1180.Palomar.erdos_1180_variants_shparlinski
