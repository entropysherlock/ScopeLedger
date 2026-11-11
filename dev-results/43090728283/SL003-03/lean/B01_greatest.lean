import SL003Target

/-! SL-004 dev, SL003-03 (Erdős 581). Correspondence by characterisation: the project proves its
`f m` is the greatest `k` with `Guarantees m k` (`f_spec`, `le_f_of_guarantees`), and `Guarantees m`
is FC's set predicate, so FC's `sSup` equals the project's `Nat.findGreatest` (`IsGreatest.csSup_eq`).
-/

theorem SL004.corr03_f (m : ℕ) : SL003FC.Erdos581.f m = Erdos581.f m := by
  unfold SL003FC.Erdos581.f
  apply IsGreatest.csSup_eq
  exact ⟨Erdos581.f_spec m, fun k hk => Erdos581.le_f_of_guarantees hk⟩

theorem SL004.bridge03 : SL003FC.Erdos581.SL003.targetProp := by
  unfold SL003FC.Erdos581.SL003.targetProp
  have h := Erdos581.erdos_581
  simp only [← SL004.corr03_f] at h
  exact h
