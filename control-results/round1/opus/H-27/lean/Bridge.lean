import SL003Target

/-! Bridge for H-27 (Erdős 865): from `Erdos865.erdos865`.

If `8 |A| ≤ 5 N + C` for every triple-free `A ⊆ [1, N]`, then every `A ⊆ [1, N]` with
`|A| ≥ (5/8) N + (C/8 + 1)` contains a triple. -/

theorem SL004.bridge_main : SL003FC.Erdos865.SL003.targetProp := by
  unfold SL003FC.Erdos865.SL003.targetProp
  obtain ⟨C, hC⟩ := Erdos865.erdos865
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
  refine ⟨(C : ℝ) / 8 + 1, by linarith, Filter.Eventually.of_forall ?_⟩
  intro N A hA hcard
  by_contra h
  have hle := hC N A hA h
  have hle' : (8 : ℝ) * (A.card : ℝ) ≤ 5 * (N : ℝ) + (C : ℝ) := by exact_mod_cast hle
  linarith
