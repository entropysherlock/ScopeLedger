import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E2_iff_mp : SL003FC.Kourovka.«21.149».SL003.targetProp := by
  unfold SL003FC.Kourovka.«21.149».SL003.targetProp
  first | exact (@KourovkaNotebook.Solution21_149.kourovka_21_149).mp trivial | with_unfolding_all exact (@KourovkaNotebook.Solution21_149.kourovka_21_149).mp trivial
