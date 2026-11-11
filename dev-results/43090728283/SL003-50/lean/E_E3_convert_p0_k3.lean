import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E3_convert_p0_k3 : SL003FC.Erdos482.SL003.targetProp := by
  unfold SL003FC.Erdos482.SL003.targetProp
  have h := @LeanGallery.NumberTheory.Erdos482.Statement.statement_erdos_482_verbatim
  convert h using 3 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp))
