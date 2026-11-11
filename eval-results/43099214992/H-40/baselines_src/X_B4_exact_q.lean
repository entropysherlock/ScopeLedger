import SL003Target

set_option maxHeartbeats 2000000 in
theorem SL004.bridge_B4_exact_q : SL003FC.BeaverMathOlympiad.SL003.targetProp := by
  unfold SL003FC.BeaverMathOlympiad.SL003.targetProp
  have h := @Collatz.BMO.Problem3.beaver_math_olympiad_problem_3
  exact?
