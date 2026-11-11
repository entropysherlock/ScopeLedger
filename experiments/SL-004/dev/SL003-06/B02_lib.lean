import SL003Target
import SL004Lib

/-! SL-004 dev, SL003-06 via the library: FC's `sSup` equals the project's `Finset.sup` because the
latter is the greatest element of FC's set (`SL004Lib.isGreatest_finset_sup`, `IsGreatest.csSup_eq`). -/

theorem SL004.corr06_lib (N : ℕ) : SL003FC.Erdos441.g N = Erdos441.g N := by
  unfold SL003FC.Erdos441.g Erdos441.g
  apply IsGreatest.csSup_eq
  have := SL004Lib.isGreatest_finset_sup (Erdos441.candidates N)
    (fun A => A ⊆ Finset.Icc 1 N ∧ ∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) Finset.card
    (fun A => by
      simp only [Erdos441.candidates, Erdos441.LcmBounded, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩)
    ⟨∅, by simp [Erdos441.candidates, Erdos441.LcmBounded]⟩
  convert this using 1
  all_goals (try (ext k; simp only [Set.mem_setOf_eq, and_assoc]))
