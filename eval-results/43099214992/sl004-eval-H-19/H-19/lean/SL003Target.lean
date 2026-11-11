import Mathlib
import ErdosProblems.Erdos1021

namespace SL003FC

section
open Filter Asymptotics
namespace Erdos1021
/-- The graph `G_k`: the bipartite graph between `{y_1, …, y_k}` (the elements of `Fin k`) and
`{z_1, …, z_{k choose 2}}` (the two-element subsets of `Fin k`), each `z` being joined to the two
elements of the corresponding pair. This is the `1`-subdivision of `K_k`. -/
def cliqueSubdivision (k : ℕ) : SimpleGraph (Fin k ⊕ Set.powersetCard (Fin k) 2) where
  Adj x y :=
    match x, y with
    | Sum.inl i, Sum.inr p => i ∈ (p : Finset (Fin k))
    | Sum.inr p, Sum.inl i => i ∈ (p : Finset (Fin k))
    | _, _ => False
  symm := by
    constructor
    intro x y h
    cases x <;> cases y <;> simp_all
  loopless := by
    constructor
    intro x
    cases x <;> simp
end Erdos1021

namespace Erdos1021

/-- SL-003 transported target: FormalConjectures/ErdosProblems/1021.lean `erdos_1021`. -/
def SL003.targetProp : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, 0 < c ∧
      (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
        fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - c)

end Erdos1021
end
end SL003FC
