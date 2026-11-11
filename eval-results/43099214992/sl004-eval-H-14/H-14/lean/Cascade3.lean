import SL003Target

theorem SL003.cascade3 : SL003FC.MovingSofa.SL003.targetProp := by
  unfold SL003FC.MovingSofa.SL003.targetProp
  exact (@FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa).1
