import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E3_convert_p2_k1 : SL003FC.Erdos501.SL003.targetProp := by
  unfold SL003FC.Erdos501.SL003.targetProp
  have h := (@erdos501_closed_infinite).2
  convert h using 1 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp) | (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩) | (with_unfolding_all (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩)) | (apply funext; intro; first | with_unfolding_all rfl | (with_unfolding_all (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩))))
