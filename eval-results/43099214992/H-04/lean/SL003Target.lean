import Mathlib
import ErdosProblems.Erdos649

namespace SL003FC

section
namespace Erdos649
end Erdos649

namespace Erdos649

/-- SL-003 transported target: FormalConjectures/ErdosProblems/649.lean `erdos_649.variants.rmm_2020`. -/
def SL003.targetProp : Prop :=
  {p : ℕ | p.Prime ∧ Odd p ∧
      ∀ n : ℕ, n.maxPrimeFac * (n + 1).maxPrimeFac ≠ 2 * p}.Infinite

end Erdos649
end
end SL003FC
