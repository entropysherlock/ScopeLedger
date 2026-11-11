import SL003Target

theorem SL003.cascade3 : SL003FC.BorweinSineSeries.SL003.targetProp := by
  unfold SL003FC.BorweinSineSeries.SL003.targetProp
  exact (@borwein_sine_series).1
