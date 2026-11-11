import Mathlib
import Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5Proof

namespace SL003FC

section
namespace Erdos1007
open scoped EuclideanGeometry
variable {V : Type*}
/-- The complete tripartite graph $K_{1,3,3}$. -/
abbrev K133 := SimpleGraph.completeMultipartiteGraph fun i : Fin 3 => Fin (![1, 3, 3] i)
end Erdos1007

namespace Erdos1007

/-- SL-003 transported target: FormalConjectures/ErdosProblems/1007.lean `erdos_1007.variants.dimension_five`. -/
def SL003.targetProp : Prop :=
  IsLeast {m | ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.HasDimension 5 ∧ G.edgeSet.ncard = m}
      15

end Erdos1007
end
end SL003FC
