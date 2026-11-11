import SL003Target

theorem SL003.cascade1 : SL003FC.MovingSofa.SL003.targetProp := by
  unfold SL003FC.MovingSofa.SL003.targetProp
  exact_mod_cast @FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa
