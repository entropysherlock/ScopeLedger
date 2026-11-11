import SL003Target

/-! SL-004 dev, SL003-59: the twin-definition principle. FC's `a` and the project's `a` are
separately compiled well-founded definitions of the same source. Their compiled terms are
`WellFounded.fix` of the same functional, so they are definitionally equal once irreducibility is
ignored (the kernel never respects it). -/

theorem SL004.corr59_twin : SL003FC.OeisA397588.a = A397588.a := by
  with_unfolding_all rfl

theorem SL004.bridge59_twin : SL003FC.OeisA397588.SL003.targetProp := by
  unfold SL003FC.OeisA397588.SL003.targetProp
  intro n hn
  rw [SL004.corr59_twin]
  exact A397588.a_three_dvd hn
