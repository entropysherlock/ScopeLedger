import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B1_exact : SL003FC.BeaverMathOlympiad.SL003.targetProp := by
  unfold SL003FC.BeaverMathOlympiad.SL003.targetProp
  exact @Collatz.BMO.Problem3.beaver_math_olympiad_problem_3
