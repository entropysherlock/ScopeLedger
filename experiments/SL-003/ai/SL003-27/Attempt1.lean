import SL003Target

/-! SL-003 AI attempt 1 (Claude). The cited statement has extra conclusions (`1 ≤ C`, `S.Nonempty`)
and `1 ≤ a` where the target has `0 < a`; the bridge drops the first two and converts the third.
No human edits. -/

theorem SL003.ai1 : SL003FC.Erdos310.SL003.targetProp := by
  unfold SL003FC.Erdos310.SL003.targetProp
  intro α hα
  obtain ⟨C, -, hC⟩ := Erdos310.erdos_310 α hα
  refine ⟨C, fun N hN A hA hdens => ?_⟩
  obtain ⟨S, hSA, -, a, b, ha, hab, hbC, hsum⟩ := hC N hN A hA hdens
  exact ⟨S, hSA, a, b, by omega, hab, hbC, hsum⟩
