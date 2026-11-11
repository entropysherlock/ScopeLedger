import SL003Target

theorem SL003.cascade2 : SL003FC.MovingSofa.SL003.targetProp := by
  unfold SL003FC.MovingSofa.SL003.targetProp
  simpa [A, ABφθSpec, B, gerversSofa, hallway, horizontalHallway, p, r, rotateTranslate, sofaConstant, sofaConstant_eq.answer, sofaOfRotateTranslatePath, unitSquare, verticalHallway, x, y, θ, φ] using @FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa
