import Mathlib
import ErdosProblems.Erdos501

namespace SL003FC

section
open Set MeasureTheory
open scoped Cardinal ENNReal
namespace Erdos501
end Erdos501

namespace Erdos501

/-- SL-003 transported target: FormalConjectures/ErdosProblems/501.lean `erdos_501.variants.newelski_pawlikowski_seredynski`. -/
def SL003.targetProp : Prop :=
  ∀ (A : ℝ → Set ℝ),
      (∀ x, IsClosed (A x)) →
      (∀ x, volume (A x) < 1) →
      ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y)

end Erdos501
end
end SL003FC
