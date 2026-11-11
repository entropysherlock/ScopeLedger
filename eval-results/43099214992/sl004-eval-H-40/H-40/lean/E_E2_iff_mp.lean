import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E2_iff_mp : SL003FC.BeaverMathOlympiad.SL003.targetProp := by
  unfold SL003FC.BeaverMathOlympiad.SL003.targetProp
  first | exact (@Collatz.BMO.Problem3.beaver_math_olympiad_problem_3).mp trivial | with_unfolding_all exact (@Collatz.BMO.Problem3.beaver_math_olympiad_problem_3).mp trivial
