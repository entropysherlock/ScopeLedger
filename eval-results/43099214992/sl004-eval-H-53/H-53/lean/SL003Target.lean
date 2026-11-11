import Mathlib
import ErdosProblems.Erdos109

namespace SL003FC

section
open Pointwise
namespace Erdos109
end Erdos109

namespace Erdos109

/-- SL-003 transported target: FormalConjectures/ErdosProblems/109.lean `erdos_109`. -/
def SL003.targetProp : Prop :=
  ∀ (A : Set ℕ) (h : A.upperDensity > 0), ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ B + C ⊆ A

end Erdos109
end
end SL003FC
