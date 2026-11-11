import SL003Target

/-! Bridge for H-20 (Erdős 522, 0/1 variant): from `E522.erdos_522_zero_one_solved`.

The transported `KacCoefficients` structure is a field-by-field copy of the one used by the cited
theorem, so a transported sequence of coefficients is repackaged with the same fields. -/

universe u

theorem SL004.bridge_main : SL003FC.Erdos522.SL003.targetProp.{u} := by
  unfold SL003FC.Erdos522.SL003.targetProp
  intro Ω _ _ n hn f
  have key := (E522.erdos_522_zero_one_solved.1 trivial) hn
    (⟨f.toFun, f.h_indep, f.h_unif⟩ : Erdos522.KacCoefficients ({0, 1} : Set ℂ) Ω)
  exact key
