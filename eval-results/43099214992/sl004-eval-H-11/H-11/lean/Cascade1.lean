import SL003Target

theorem SL003.cascade1 : SL003FC.Erdos667.SL003.targetProp := by
  unfold SL003FC.Erdos667.SL003.targetProp
  exact_mod_cast @Erdos667.variants.monotoneOn
