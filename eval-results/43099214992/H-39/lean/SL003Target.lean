import Mathlib
import ErdosProblems.Erdos1077

namespace SL003FC

section
open Finset Filter SimpleGraph
namespace Erdos1077
end Erdos1077

namespace Erdos1077

/-- SL-003 transported target: FormalConjectures/ErdosProblems/1077.lean `erdos_1077`. -/
def SL003.targetProp : Prop :=
  ¬ ∀ ε > (0 : ℝ), ε < 1 → ∀ α > (0 : ℝ), α < 1 → ∀ᶠ D in atTop, ∀ᶠ n in atTop,
      ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard > (n : ℝ) ^ (1 + α) →
        ∃ (H : Subgraph G),
          letI m := H.verts.ncard
          IsBalanced H.coe D ∧
          m > (n : ℝ) ^ (1 - α) ∧
          H.edgeSet.ncard > ε * m ^ (1 + α)

end Erdos1077
end
end SL003FC
