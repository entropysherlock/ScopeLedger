import SL003Target

/-! SL-004 dev, SL003-15 (Borwein sine series). The cited theorem is conditional. The justified
relationship is directional: `PiIrrBound → target`. This is a relation, not a proof of the target. -/

theorem SL004.relation15 : PiIrrBound → SL003FC.BorweinSineSeries.SL003.targetProp := by
  intro h
  unfold SL003FC.BorweinSineSeries.SL003.targetProp
  exact borwein_sine_series h
