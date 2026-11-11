import Mathlib
import ErdosProblems.Erdos737

namespace SL003FC

section
namespace Erdos737
/--
`G` has chromatic number exactly $\aleph_1$: it has a proper colouring by the countable ordinals
(a set of cardinality $\aleph_1$) but no proper colouring by `ℕ`.
-/
def ChromaticNumberAlephOne {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (G.Coloring (Set.Iio (Ordinal.omega.{0} 1))) ∧ IsEmpty (G.Coloring ℕ)
/-- `G` contains a cycle of length `n` that contains the edge `e`. -/
def CycleThroughEdgeOfLength {V : Type*} (G : SimpleGraph V) (e : Sym2 V) (n : ℕ) : Prop :=
  ∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = n ∧ e ∈ c.edges
end Erdos737

namespace Erdos737

/-- SL-003 transported target: FormalConjectures/ErdosProblems/737.lean `erdos_737.variants.uncountable`. -/
def SL003.targetProp : Prop :=
  ∀ (V : Type) (G : SimpleGraph V), IsEmpty (G.Coloring ℕ) →
      ∃ e ∈ G.edgeSet, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        CycleThroughEdgeOfLength G e n

end Erdos737
end
end SL003FC
