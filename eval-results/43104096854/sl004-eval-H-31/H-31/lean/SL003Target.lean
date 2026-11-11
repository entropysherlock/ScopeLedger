import Mathlib
import ErdosProblems.Erdos136

namespace SL003FC

section
open Filter
open scoped Topology
namespace Erdos136
/-- An edge colouring of `K_n` with `k` colours is a `(4, 5)`-colouring if the six edges of every
copy of `K_4` receive at least five distinct colours. -/
def Is45Coloring {n k : ℕ} (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) : Prop :=
  open scoped Classical in
  ∀ v : Fin 4 ↪ Fin n, 5 ≤ (Finset.univ.image (C.pullback v)).card
/-- `K_n` admits a `(4, 5)`-colouring with `k` colours. -/
def Colorable (n k : ℕ) : Prop :=
  ∃ C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k), Is45Coloring C
/-- `f n` is the least number of colours in a `(4, 5)`-colouring of `K_n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k | Colorable n k}
end Erdos136

namespace Erdos136

/-- SL-003 transported target: FormalConjectures/ErdosProblems/136.lean `erdos_136`. -/
def SL003.targetProp : Prop :=
  Tendsto (fun n : ℕ ↦ (f n : ℝ) / (n : ℝ)) atTop (𝓝 (5 / 6 : ℝ))

end Erdos136
end
end SL003FC
