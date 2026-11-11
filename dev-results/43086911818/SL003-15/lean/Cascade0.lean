import SL003Target

theorem SL003.cascade0 : SL003FC.BorweinSineSeries.SL003.targetProp := by
  unfold SL003FC.BorweinSineSeries.SL003.targetProp
  simpa using @borwein_sine_series
