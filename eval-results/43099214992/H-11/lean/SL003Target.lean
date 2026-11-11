import Mathlib
import Solution

namespace SL003FC

section
open SimpleGraph Filter
namespace Erdos667
/-- A graph `G` on `n` vertices is *`(p, q)`-locally dense* if every set of `p` of its vertices
spans at least `q` edges of `G`; equivalently, every induced subgraph on `p` vertices has at
least `q` edges. -/
def LocallyDense (p q : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : Finset (Fin n), s.card = p → q ≤ (G.induce s).edgeSet.ncard
open Classical in
/-- `H p q n` is `H(n) = H(n; p, q)`: the largest `m` such that *every* `(p, q)`-locally dense
graph on `n` vertices must contain a complete graph on `m` vertices `Kₘ`.

The condition "`G` contains `Kₘ`" is `¬ G.CliqueFree m`. Any `m`-clique needs `m ≤ n` vertices,
and the property is downward closed in `m`, so `Nat.findGreatest _ n` returns the genuine maximum. -/
noncomputable def H (p q n : ℕ) : ℕ :=
  Nat.findGreatest
    (fun m => ∀ G : SimpleGraph (Fin n), LocallyDense p q G → ¬ G.CliqueFree m) n
/-- The growth exponent `c(p, q) = liminf_{n → ∞} (log H(n)) / (log n)`. -/
noncomputable def c (p q : ℕ) : ℝ :=
  liminf (fun n : ℕ => Real.log (H p q n) / Real.log n) atTop
end Erdos667

namespace Erdos667

/-- SL-003 transported target: FormalConjectures/ErdosProblems/667.lean `erdos_667.variants.monotoneOn`. -/
def SL003.targetProp : Prop :=
  ∀ (p : ℕ), MonotoneOn (c p) (Set.Icc 1 (Nat.choose (p - 1) 2 + 1))

end Erdos667
end
end SL003FC
