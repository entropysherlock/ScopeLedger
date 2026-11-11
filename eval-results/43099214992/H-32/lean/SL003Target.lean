import Mathlib
import WOWII144.Main

namespace SL003FC

section
namespace WrittenOnTheWallII.GraphConjecture144
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
end WrittenOnTheWallII.GraphConjecture144

namespace WrittenOnTheWallII.GraphConjecture144

/-- SL-003 transported target: FormalConjectures/WrittenOnTheWallII/GraphConjecture144.lean `conjecture144`. -/
def SL003.targetProp : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤ (largestInducedTreeSize G : ℝ)

end WrittenOnTheWallII.GraphConjecture144
end
end SL003FC
