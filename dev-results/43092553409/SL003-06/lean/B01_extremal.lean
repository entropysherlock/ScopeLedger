import SL003Target

/-! SL-004 dev, SL003-06 (Erdős 441). Correspondence: FC's `g N = sSup {card A | A admissible}` equals
the project's `g N = (candidates N).sup card`. Bridge: the cited theorem gives, for some `N ≥ 1`, a
gap `card (construction N) < g N`, refuting FC's equality claim. -/

theorem SL004.corr06_g (N : ℕ) : SL003FC.Erdos441.g N = Erdos441.g N := by
  have hmem : ∀ A : Finset ℕ, A ∈ Erdos441.candidates N ↔
      A ⊆ Finset.Icc 1 N ∧ ∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N := by
    intro A
    simp only [Erdos441.candidates, Erdos441.LcmBounded, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨h.1, h⟩
  have hbdd : BddAbove {k | ∃ A ⊆ Finset.Icc 1 N, (∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) ∧ A.card = k} := by
    refine ⟨N, ?_⟩
    rintro k ⟨A, hA, -, rfl⟩
    simpa using Finset.card_le_card hA
  have hne : ({k | ∃ A ⊆ Finset.Icc 1 N, (∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) ∧ A.card = k} : Set ℕ).Nonempty :=
    ⟨0, ∅, Finset.empty_subset _, by simp, Finset.card_empty⟩
  unfold SL003FC.Erdos441.g Erdos441.g
  apply le_antisymm
  · apply csSup_le hne
    rintro k ⟨A, hA, hl, rfl⟩
    exact Finset.le_sup (f := Finset.card) ((hmem A).2 ⟨hA, hl⟩)
  · obtain ⟨A, hA, hAeq⟩ := Finset.exists_mem_eq_sup (Erdos441.candidates N)
      ⟨∅, (hmem ∅).2 ⟨Finset.empty_subset _, by simp⟩⟩ Finset.card
    rw [hAeq]
    exact le_csSup hbdd ⟨A, ((hmem A).1 hA).1, ((hmem A).1 hA).2, rfl⟩

theorem SL004.bridge06 : SL003FC.Erdos441.SL003.targetProp := by
  unfold SL003FC.Erdos441.SL003.targetProp
  intro H
  obtain ⟨-, hgap⟩ := Erdos441.not_erdos_441
  obtain ⟨N, hN, hlt⟩ := hgap 1
  have h1 := H N hN
  rw [SL004.corr06_g] at h1
  have hc : SL003FC.Erdos441.erdosConstruction N = Erdos441.erdosConstruction N := rfl
  rw [hc] at h1
  omega
