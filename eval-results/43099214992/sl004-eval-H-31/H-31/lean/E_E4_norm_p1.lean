import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E4_norm_p1 : SL003FC.Erdos136.SL003.targetProp := by
  unfold SL003FC.Erdos136.SL003.targetProp
  have h := (@Erdos136.erdos_136).1
  simp only [true_iff, iff_true, Filter.eventually_atTop, ge_iff_le, gt_iff_lt, exists_prop, and_imp, not_not, Set.mem_setOf_eq] at h ⊢
  first
    | exact h
    | with_unfolding_all exact h
    | (convert h using 2 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp) | (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩) | (with_unfolding_all (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩)) | (apply funext; intro; first | with_unfolding_all rfl | (with_unfolding_all (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩)))))
    | (convert h using 4 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp) | (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩) | (with_unfolding_all (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩)) | (apply funext; intro; first | with_unfolding_all rfl | (with_unfolding_all (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩)))))
