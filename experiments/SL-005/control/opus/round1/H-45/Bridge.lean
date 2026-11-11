import SL003Target

/-! Bridge for H-45 (Erdős 49, Tao's variant): from `Erdos49.erdos_49_quantitative`.

`g N` is a supremum of a nonempty set of naturals bounded by `N`, hence attained by some
admissible set `A`, to which the cited uniform bound applies. -/

theorem SL004.bridge_main : SL003FC.Erdos49.SL003.targetProp := by
  unfold SL003FC.Erdos49.SL003.targetProp
  obtain ⟨C, hC, hb⟩ := Erdos49.erdos_49_quantitative
  refine ⟨C, hC, fun N hN => ?_⟩
  have hne : ({k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ MonotoneOn Nat.totient (A : Set ℕ) ∧
      A.card = k} : Set ℕ).Nonempty := by
    refine ⟨0, ∅, Finset.empty_subset _, ?_, rfl⟩
    intro a ha
    simp at ha
  have hbdd : BddAbove ({k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      MonotoneOn Nat.totient (A : Set ℕ) ∧ A.card = k} : Set ℕ) := by
    refine ⟨N, ?_⟩
    rintro k ⟨A, hA, -, rfl⟩
    simpa using Finset.card_le_card hA
  have hmem : SL003FC.Erdos49.g N ∈ ({k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      MonotoneOn Nat.totient (A : Set ℕ) ∧ A.card = k} : Set ℕ) :=
    Nat.sSup_mem hne hbdd
  obtain ⟨A, hA, hmono, hcard⟩ := hmem
  have hbound := hb N hN A ⟨hA, hmono⟩
  rw [← hcard]
  unfold Erdos49.taoRate at hbound
  exact hbound
