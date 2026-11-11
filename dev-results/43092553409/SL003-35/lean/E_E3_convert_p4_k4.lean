import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E3_convert_p4_k4 : SL003FC.Erdos737.SL003.targetProp := by
  unfold SL003FC.Erdos737.SL003.targetProp
  have h := (@Erdos737.eventually_cycles_through_fixed_edge).2.2
  convert h using 4 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp) | (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩) | (with_unfolding_all (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩)) | (apply funext; intro; first | with_unfolding_all rfl | (with_unfolding_all (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩))))
