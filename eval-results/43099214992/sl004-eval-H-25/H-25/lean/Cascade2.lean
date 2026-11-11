import SL003Target

theorem SL003.cascade2 : SL003FC.SpectralSetProduct.SL003.targetProp := by
  unfold SL003FC.SpectralSetProduct.SL003.targetProp
  simpa [productSet, spectralProductImpliesRightSpectral] using @ProductInterval.fc_three_dimensional
