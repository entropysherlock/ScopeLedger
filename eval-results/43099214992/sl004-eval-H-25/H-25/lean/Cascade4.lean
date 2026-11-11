import SL003Target

theorem SL003.cascade4 : SL003FC.SpectralSetProduct.SL003.targetProp := by
  unfold SL003FC.SpectralSetProduct.SL003.targetProp
  exact (@ProductInterval.fc_three_dimensional).2
