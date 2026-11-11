import SL003Target

theorem SL004.bridge_main : SL003FC.Erdos865.SL003.targetProp := by
  obtain ⟨C, hC⟩ := Erdos865.erdos865
  refine ⟨(C : ℝ) / 8 + 1, by positivity, Filter.Eventually.of_forall fun N A hA hcard => ?_⟩
  by_contra hne
  have hT : ¬ Erdos865.HasTriple A := hne
  have h1 := hC N A hA hT
  have h2 : (8 * (A.card : ℝ)) ≤ 5 * (N : ℝ) + (C : ℝ) := by exact_mod_cast h1
  linarith
