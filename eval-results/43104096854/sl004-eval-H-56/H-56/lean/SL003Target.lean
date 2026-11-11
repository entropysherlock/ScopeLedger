import Mathlib
import OAI.Analysis.Littlewood.Main

namespace SL003FC

section
open scoped Polynomial
namespace Erdos1150
end Erdos1150

namespace Erdos1150

/-- SL-003 transported target: FormalConjectures/ErdosProblems/1150.lean `erdos_1150`. -/
def SL003.targetProp : Prop :=
  ¬ ∃ c > 0, ∀ᶠ n in Filter.atTop,
      ∀ P : ℂ[X],  (∀ i ≤ P.natDegree, P.coeff i = - 1 ∨ P.coeff i = 1) → P.natDegree = n →
        ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ > (1 + c) * Real.sqrt n

end Erdos1150
end
end SL003FC
