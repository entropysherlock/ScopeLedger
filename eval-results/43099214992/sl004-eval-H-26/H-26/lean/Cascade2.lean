import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos987.SL003.targetProp := by
  unfold SL003FC.Erdos987.SL003.targetProp
  simpa [A] using @Erdos987.erdos_987.variants.sup_limsup_infty
