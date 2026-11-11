import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E2_iff_mp : SL003FC.Erdos482.SL003.targetProp := by
  unfold SL003FC.Erdos482.SL003.targetProp
  first | exact (@LeanGallery.NumberTheory.Erdos482.Statement.statement_erdos_482_verbatim).mp trivial | with_unfolding_all exact (@LeanGallery.NumberTheory.Erdos482.Statement.statement_erdos_482_verbatim).mp trivial
