import SL003Target

theorem SL003.cascade1 : SL003FC.BorweinSineSeries.SL003.targetProp := by
  unfold SL003FC.BorweinSineSeries.SL003.targetProp
  exact_mod_cast @borwein_sine_series
