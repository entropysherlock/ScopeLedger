import SL003Target

theorem SL004.sub_sums (w : ℕ → ℤ) (k : ℤ)
    (hk : k ∈ subsetSums (Set.range w \ {0})) : k ∈ subseqSums' w := by
  obtain ⟨B, hB, rfl⟩ := hk
  have h : ∀ b ∈ B, ∃ n, w n = b := fun b hb => (hB hb).1
  choose! f hf using h
  refine ⟨B.image f, ?_⟩
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl (fun b hb => (hf b hb).symm)
  · intro a ha b hb hab
    have ha' : a ∈ B := by simpa using ha
    have hb' : b ∈ B := by simpa using hb
    calc a = w (f a) := (hf a ha').symm
      _ = w (f b) := by rw [hab]
      _ = b := hf b hb'

theorem SL004.interleave_eq (α β γ : ℝ) :
    SL003FC.Erdos354.FloorMultiples.interleave α β γ = Erdos354.FloorMultiples.interleave α β γ := by
  first
    | rfl
    | (funext n
       simp [SL003FC.Erdos354.FloorMultiples.interleave, Erdos354.FloorMultiples.interleave,
         SL003FC.Erdos354.FloorMultiples, Erdos354.FloorMultiples])

theorem SL004.bridge_main : SL003FC.Erdos354.SL003.targetProp := by
  intro α hα β hβ hirr
  have h := Dyadic354.UpstreamBridge.erdos354_strong_upstream α β hα hβ hirr
  have h0 := h (Set.finite_empty : (∅ : Set ℤ).Finite)
  rw [SL004.interleave_eq]
  refine Filter.Eventually.mono h0 (fun k hk => ?_)
  apply SL004.sub_sums
  rwa [Set.diff_empty] at hk
