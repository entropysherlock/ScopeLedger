import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B2_convert_rfl : SL003FC.Erdos482.SL003.targetProp := by
  unfold SL003FC.Erdos482.SL003.targetProp
  have h := @LeanGallery.NumberTheory.Erdos482.Statement.statement_cor33_unconditional
  convert h using 3 <;> rfl
