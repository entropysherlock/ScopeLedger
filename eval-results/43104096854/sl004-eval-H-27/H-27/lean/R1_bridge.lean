import SL003Target

/-! SL-004 Layer B round 1 (Claude), H-27 (Erdős 865). Class L: the cited bound `8|A| ≤ 5N + C₀` for
triple-free `A` gives FC's statement by contraposition with `C = C₀/8 + 1 > 0`; the project's
`IsTripleFree A` is `¬ HasTriple A`, FC's triple condition. -/

theorem SL004.bridgeH27 : SL003FC.Erdos865.SL003.targetProp := by
  unfold SL003FC.Erdos865.SL003.targetProp
  obtain ⟨C₀, hC₀⟩ := Erdos865.erdos865
  refine ⟨(C₀ : ℝ) / 8 + 1, by positivity, Filter.Eventually.of_forall fun N A hA hcard => ?_⟩
  by_contra hno
  have hfree : Erdos865.IsTripleFree A := by
    unfold Erdos865.IsTripleFree
    intro ht
    apply hno
    with_unfolding_all exact ht
  have h := hC₀ N A hA hfree
  have h' : (8 : ℝ) * A.card ≤ 5 * N + C₀ := by exact_mod_cast h
  linarith
