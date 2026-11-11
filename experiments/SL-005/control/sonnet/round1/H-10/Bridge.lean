import SL003Target

theorem SL004.ak_eq (N q : ℕ) :
    SL003FC.Erdos534.ahlswedeKhachatrian N q = Erdos534.candidate N q := by
  first
    | rfl
    | (ext m
       simp only [SL003FC.Erdos534.ahlswedeKhachatrian, Erdos534.candidate,
         Finset.mem_filter, SL003FC.Erdos534.primePrefix, Erdos534.primePrefix,
         Erdos534.prefixProduct, Erdos534.interval])
    | (ext m
       simp [SL003FC.Erdos534.ahlswedeKhachatrian, Erdos534.candidate,
         SL003FC.Erdos534.primePrefix, Erdos534.primePrefix,
         Erdos534.prefixProduct, Erdos534.interval])

theorem SL004.adm_iff (N : ℕ) (A : Finset ℕ) :
    SL003FC.Erdos534.IsAdmissible N A ↔ Erdos534.Admissible N A := Iff.rfl

theorem SL004.bridge_main : SL003FC.Erdos534.SL003.targetProp := by
  intro N hN
  obtain ⟨q, hq, hadm, hmax⟩ := Erdos534.erdos_534 N hN
  refine ⟨q, hq, ?_, ?_⟩
  · rw [SL004.ak_eq]
    exact (SL004.adm_iff _ _).mpr hadm
  · rw [SL004.ak_eq]
    unfold SL003FC.Erdos534.maxCard
    apply IsGreatest.csSup_eq
    constructor
    · exact ⟨_, (SL004.adm_iff _ _).mpr hadm, rfl⟩
    · rintro k ⟨A, hA, rfl⟩
      exact hmax A ((SL004.adm_iff _ _).mp hA)
