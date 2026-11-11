import SL003Target

/-! SL-003 AI attempt 1 (Claude). FC's `OeisA397588.a` and the cited `A397588.a` have the same source
text, but two separately compiled well-founded definitions are not definitionally equal. The bridge
proves them equal by strong induction on the equation lemmas, then uses the cited divisibility result
(whose `n` is implicit). No human edits. -/

theorem SL004.bridge_regression59 : SL003FC.OeisA397588.SL003.targetProp := by
  unfold SL003FC.OeisA397588.SL003.targetProp
  have key : ∀ n, SL003FC.OeisA397588.a n = A397588.a n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | _ | n
      · simp [SL003FC.OeisA397588.a, A397588.a]
      · simp [SL003FC.OeisA397588.a, A397588.a]
      · show SL003FC.OeisA397588.a (n + 2) = A397588.a (n + 2)
        rw [SL003FC.OeisA397588.a, A397588.a]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        have hk := Finset.mem_Icc.mp k.2
        rw [ih k.1 (by omega), ih (n + 2 - k.1) (by omega)]
  intro n hn
  rw [key n]
  exact A397588.a_three_dvd hn
