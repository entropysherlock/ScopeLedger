import SL003Target

/-! Bridge for H-18 (Erdős 354, part i): from
`Dyadic354.UpstreamBridge.erdos354_strong_upstream` to the transported target.

Strong completeness of the set of nonzero values gives (taking the empty exceptional set)
completeness of that set; a finite set of distinct values is the image of a finite set of
indices, so every subset sum of the value set is a subsequence sum. -/

theorem SL004.bridge_main : SL003FC.Erdos354.SL003.targetProp := by
  unfold SL003FC.Erdos354.SL003.targetProp
  intro α hα β hβ hirr
  have hS := Dyadic354.UpstreamBridge.erdos354_strong_upstream α β hα hβ hirr
  have hC : IsAddComplete (Set.range (Erdos354.FloorMultiples.interleave α β 2) \ {0}) := by
    have h0 := hS Set.finite_empty
    rwa [Set.diff_empty] at h0
  have hw : SL003FC.Erdos354.FloorMultiples.interleave α β 2 =
      Erdos354.FloorMultiples.interleave α β 2 := rfl
  show ∀ᶠ k in Filter.atTop, k ∈ subseqSums' (SL003FC.Erdos354.FloorMultiples.interleave α β 2)
  rw [hw]
  unfold IsAddComplete at hC
  filter_upwards [hC] with k hk
  obtain ⟨B, hBsub, rfl⟩ := hk
  classical
  have hpick : ∀ b ∈ B, ∃ j, Erdos354.FloorMultiples.interleave α β 2 j = b :=
    fun b hb => (hBsub hb).1
  choose! f hf using hpick
  refine ⟨B.image f, ?_⟩
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl (fun b hb => (hf b hb).symm)
  · intro x hx y hy hxy
    rw [← hf x hx, ← hf y hy, hxy]
