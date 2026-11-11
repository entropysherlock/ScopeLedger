import Mathlib
import LeanGallery.NumberTheory.Erdos1050.Statement

namespace SL003FC

section
namespace Erdos1050
end Erdos1050

namespace Erdos1050

/-- SL-003 transported target: FormalConjectures/ErdosProblems/1050.lean `erdos_1050`. -/
def SL003.targetProp : Prop :=
  Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3))

end Erdos1050
end
end SL003FC
