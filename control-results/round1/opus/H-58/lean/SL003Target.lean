import Mathlib
import Erdos274.Main

namespace SL003FC

section
open scoped Pointwise Cardinal
namespace Erdos274
/-- An exact covering of a group `G` is a finite collection of subgroups `{H_1, ..., H_k}` and
representative `{g_1, ..., g_k}` such that the cosets `g_iH_i` are pairwise disjoint and their
union covers `G`.

Note that this differs from `Partition (α := Subgroup G)` because the covering condition there
invokes `Subgroup.sup` which is subgroup generation and thus stronger than union. This definition
is easier to use in this context than the alternative `Partition (α := Set G)`, which lacks
subgroup definitions such as `Subgroup.index`. -/
structure Group.ExactCovering (G : Type*) [Group G] (ι : Type*) [Fintype ι] where
  parts : ι → Subgroup G
  reps : ι → G
  nonempty (i : ι) : (parts i : Set G).Nonempty
  disjoint : (Set.univ (α := ι)).PairwiseDisjoint fun (i : ι) ↦ reps i • (parts i : Set G)
  covers : ⋃ i, reps i • (parts i : Set G) = Set.univ
end Erdos274

namespace Erdos274

/-- SL-003 transported target: FormalConjectures/ErdosProblems/274.lean `erdos_274.variants.abelian`. -/
def SL003.targetProp : Prop :=
  ∀ {G : Type*} [Fintype G] [CommGroup G]
    (hG : 1 < Fintype.card G) {ι : Type*} [Fintype ι] (P : Group.ExactCovering G ι)
    (hι : 1 < Fintype.card ι), ∃ i j, i ≠ j ∧ #(P.parts i) = #(P.parts j)

end Erdos274
end
end SL003FC
