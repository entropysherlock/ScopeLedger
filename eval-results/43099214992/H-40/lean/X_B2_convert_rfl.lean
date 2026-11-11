import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B2_convert_rfl : SL003FC.BeaverMathOlympiad.SL003.targetProp := by
  unfold SL003FC.BeaverMathOlympiad.SL003.targetProp
  have h := @Collatz.BMO.Problem3.beaver_math_olympiad_problem_3
  convert h using 3 <;> rfl
