import SL003Target

/-! SL-004 Layer B round 1 (Claude), H-45 (Erdős 49, Tao's bound). Class C3 bounded supremum: FC's
`g N = sSup {card A | A ⊆ [1, N], φ monotone on A}` is attained (`Nat.sSup_mem`: the set is nonempty
and bounded by N), so the cited uniform bound for every `MonotoneAdmissible` set applies to it; the
project's `taoRate` is FC's error term. -/

theorem SL004.bridgeH45 : SL003FC.Erdos49.SL003.targetProp := by
  unfold SL003FC.Erdos49.SL003.targetProp
  obtain ⟨C, hC, hb⟩ := Erdos49.erdos_49_quantitative
  refine ⟨C, hC, fun N hN => ?_⟩
  have hne : ({k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ MonotoneOn Nat.totient (A : Set ℕ) ∧
      A.card = k} : Set ℕ).Nonempty := ⟨0, ∅, Finset.empty_subset _, by simp, rfl⟩
  have hbdd : BddAbove ({k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ MonotoneOn Nat.totient (A : Set ℕ) ∧
      A.card = k} : Set ℕ) := by
    refine ⟨N, ?_⟩
    rintro k ⟨A, hA, -, rfl⟩
    simpa using Finset.card_le_card hA
  obtain ⟨A, hA, hmono, hcard⟩ := Nat.sSup_mem hne hbdd
  unfold SL003FC.Erdos49.g
  rw [← hcard]
  have h := hb N hN A ⟨hA, by with_unfolding_all exact hmono⟩
  unfold Erdos49.taoRate at h
  exact h
