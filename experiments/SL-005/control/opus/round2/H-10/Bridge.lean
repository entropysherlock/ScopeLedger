import SL003Target

/-! Bridge for H-10 (Erdős 534): from `Erdos534.erdos_534` to the transported target. -/

namespace SL004.H10

theorem admissible_iff (N : ℕ) (A : Finset ℕ) :
    SL003FC.Erdos534.IsAdmissible N A ↔ Erdos534.Admissible N A := Iff.rfl

theorem candidate_eq (N q : ℕ) :
    Erdos534.candidate N q = SL003FC.Erdos534.ahlswedeKhachatrian N q := by
  ext m
  simp only [Erdos534.candidate, SL003FC.Erdos534.ahlswedeKhachatrian, Finset.mem_filter,
    Erdos534.interval, Erdos534.prefixProduct, Erdos534.primePrefix,
    SL003FC.Erdos534.primePrefix]
  first
    | (constructor <;> intro h <;> rw [Finset.mem_filter] at h ⊢ <;> exact h)
    | (constructor <;> intro h <;> convert h)
    | (constructor <;> intro h <;> simp only [Finset.mem_filter] at h ⊢ <;> exact h)

end SL004.H10

theorem SL004.bridge_main : SL003FC.Erdos534.SL003.targetProp := by
  unfold SL003FC.Erdos534.SL003.targetProp
  intro N hN
  obtain ⟨q, hq, hadm, hmax⟩ := Erdos534.erdos_534 N hN
  have heq := SL004.H10.candidate_eq N q
  have hadm' : SL003FC.Erdos534.IsAdmissible N (Erdos534.candidate N q) :=
    (SL004.H10.admissible_iff N _).2 hadm
  refine ⟨q, hq, ?_, ?_⟩
  · rw [← heq]
    exact hadm'
  · rw [← heq]
    unfold SL003FC.Erdos534.maxCard
    apply le_antisymm
    · apply csSup_le
      · exact ⟨_, Erdos534.candidate N q, hadm', rfl⟩
      · rintro n ⟨A, hA, rfl⟩
        exact hmax A ((SL004.H10.admissible_iff N A).1 hA)
    · apply le_csSup
      · refine ⟨(Erdos534.candidate N q).card, ?_⟩
        rintro n ⟨A, hA, rfl⟩
        exact hmax A ((SL004.H10.admissible_iff N A).1 hA)
      · exact ⟨Erdos534.candidate N q, hadm', rfl⟩
