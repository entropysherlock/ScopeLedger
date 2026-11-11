import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B3_aesop : SL003FC.Erdos482.SL003.targetProp := by
  unfold SL003FC.Erdos482.SL003.targetProp
  have h := @LeanGallery.NumberTheory.Erdos482.Statement.statement_cor33_unconditional
  aesop
