import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos482.SL003.targetProp := by
  unfold SL003FC.Erdos482.SL003.targetProp
  simpa [a, alpha, beta, binaryDigit, generalRecurrence, stollBinary] using @LeanGallery.NumberTheory.Erdos482.Statement.statement_cor33_unconditional
