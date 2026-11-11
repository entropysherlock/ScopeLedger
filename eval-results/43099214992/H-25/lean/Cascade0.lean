import SL003Target

theorem SL003.cascade0 : SL003FC.SpectralSetProduct.SL003.targetProp := by
  unfold SL003FC.SpectralSetProduct.SL003.targetProp
  simpa using @ProductInterval.fc_three_dimensional
