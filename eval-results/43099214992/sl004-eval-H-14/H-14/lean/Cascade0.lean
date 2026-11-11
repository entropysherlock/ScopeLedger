import SL003Target

theorem SL003.cascade0 : SL003FC.MovingSofa.SL003.targetProp := by
  unfold SL003FC.MovingSofa.SL003.targetProp
  simpa using @FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa
