import Mathlib
import Collatz.BMO.Problem3

namespace SL003FC

section
namespace BeaverMathOlympiad
end BeaverMathOlympiad

namespace BeaverMathOlympiad

/-- SL-003 transported target: FormalConjectures/Other/BeaverMathOlympiad.lean `beaver_math_olympiad_problem_3`. -/
def SL003.targetProp : Prop :=
  ∀ (a : ℕ → ℕ)
    (a_ini : a 0 = 2)
    (a_rec : ∀ n, a (n + 1) = (a n) + 2 ^ ((padicValNat 2 (a n)) + 2) - 1), ¬ (∃ n k, a n = 4 ^ k)

end BeaverMathOlympiad
end
end SL003FC
