import SL003Target

theorem SL003.cascade1 : SL003FC.SpectralSetProduct.SL003.targetProp := by
  unfold SL003FC.SpectralSetProduct.SL003.targetProp
  exact_mod_cast @ProductInterval.fc_three_dimensional
