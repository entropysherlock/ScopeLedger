import Mathlib
import ErdosProblems.Erdos581

namespace SL003FC

section
open SimpleGraph
namespace Erdos581
/-- `f m` is the maximal `k` such that every triangle-free graph on `m` edges contains a
bipartite subgraph with `k` edges. -/
noncomputable def f (m : ℕ) : ℕ :=
  sSup {k | ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    G.edgeSet.ncard = m → ∃ H ≤ G, H.IsBipartite ∧ k ≤ H.edgeSet.ncard}
end Erdos581

namespace Erdos581

/-- SL-003 transported target: FormalConjectures/ErdosProblems/581.lean `erdos_581`. -/
def SL003.targetProp : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ m : ℕ,
    (m : ℝ) / 2 + c₁ * (m : ℝ) ^ (4 / 5 : ℝ) ≤ f m ∧
      (f m : ℝ) ≤ (m : ℝ) / 2 + c₂ * (m : ℝ) ^ (4 / 5 : ℝ)

end Erdos581
end
end SL003FC
