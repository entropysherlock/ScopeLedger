import Mathlib
import ErdosProblems.Erdos742

namespace SL003FC

section
open SimpleGraph
namespace Erdos742
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A graph is diameter-2-critical if it has diameter $2$ and removing any edge
increases the diameter beyond $2$. -/
def IsDiameter2Critical (G : SimpleGraph V) : Prop :=
  G.diam = 2 ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).diam ≠ 2
namespace variants
end variants
end Erdos742

namespace Erdos742.variants

/-- SL-003 transported target: FormalConjectures/ErdosProblems/742.lean `furedi_bound`. -/
def SL003.targetProp : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V → IsDiameter2Critical G →
      G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4

end Erdos742.variants
end
end SL003FC
