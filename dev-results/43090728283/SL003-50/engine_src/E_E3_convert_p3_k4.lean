import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E3_convert_p3_k4 : SL003FC.Erdos482.SL003.targetProp := by
  unfold SL003FC.Erdos482.SL003.targetProp
  have h := (@LeanGallery.NumberTheory.Erdos482.Statement.statement_erdos_482_verbatim).2.1
  convert h using 4 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp))
