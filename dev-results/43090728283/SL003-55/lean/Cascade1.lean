import SL003Target

theorem SL003.cascade1 : SL003FC.Erdos841.SL003.targetProp := by
  unfold SL003FC.Erdos841.SL003.targetProp
  exact_mod_cast @Erdos841.erdos841_lower_bound_explicit
