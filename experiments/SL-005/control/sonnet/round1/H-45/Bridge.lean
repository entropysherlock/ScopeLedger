import SL003Target

theorem SL004.bridge_main : SL003FC.Erdos49.SL003.targetProp := by
  obtain ⟨C, hC, h⟩ := Erdos49.erdos_49_quantitative
  refine ⟨C, hC, fun N hN => ?_⟩
  have hne : {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ MonotoneOn Nat.totient (A : Set ℕ) ∧
      A.card = k}.Nonempty := by
    refine ⟨0, ∅, by simp, ?_, by simp⟩
    intro a ha
    simp at ha
  have hbdd : BddAbove {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ MonotoneOn Nat.totient (A : Set ℕ) ∧
      A.card = k} := by
    refine ⟨N, ?_⟩
    rintro k ⟨A, hA, -, rfl⟩
    simpa using Finset.card_le_card hA
  have hmem := Nat.sSup_mem hne hbdd
  obtain ⟨A, hA, hmono, hcard⟩ := hmem
  have hadm : Erdos49.MonotoneAdmissible N A :=
    ⟨hA, fun m hm n hn hmn => hmono (Finset.mem_coe.mpr hm) (Finset.mem_coe.mpr hn) hmn⟩
  have hb := h N hN A hadm
  have hg : SL003FC.Erdos49.g N = A.card := hcard.symm
  rw [hg]
  exact hb
