import SL003Target

/-! SL-004 Layer B round 1 (Claude), H-10 (Erdős 534). Class T1 + C1: FC's `IsAdmissible` and
`ahlswedeKhachatrian` unfold to the project's `Admissible` and `candidate` (`interval N := Icc 1 N`,
`prefixProduct := ∏ primePrefix`); FC's `maxCard` (an `sSup`) is the cited candidate's card because the
cited theorem makes it the greatest admissible size (`IsGreatest.csSup_eq`). -/

theorem SL004.corrH10_adm (N : ℕ) (A : Finset ℕ) :
    SL003FC.Erdos534.IsAdmissible N A ↔ Erdos534.Admissible N A := by
  with_unfolding_all exact Iff.rfl

theorem SL004.corrH10_ak (N q : ℕ) :
    SL003FC.Erdos534.ahlswedeKhachatrian N q = Erdos534.candidate N q := by
  with_unfolding_all rfl

theorem SL004.bridgeH10 : SL003FC.Erdos534.SL003.targetProp := by
  unfold SL003FC.Erdos534.SL003.targetProp
  intro N hN
  obtain ⟨q, hq, hadm, hmax⟩ := Erdos534.erdos_534 N hN
  rw [SL004.corrH10_ak]
  refine ⟨q, hq, (SL004.corrH10_adm N _).2 hadm, ?_⟩
  unfold SL003FC.Erdos534.maxCard
  apply IsGreatest.csSup_eq
  refine ⟨⟨_, (SL004.corrH10_adm N _).2 hadm, rfl⟩, ?_⟩
  rintro n ⟨A, hA, rfl⟩
  exact hmax A ((SL004.corrH10_adm N A).1 hA)
