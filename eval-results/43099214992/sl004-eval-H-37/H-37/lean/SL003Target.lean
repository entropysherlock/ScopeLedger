import Mathlib
import PrimitiveSetsAboveX.FormalConjecturesErdos1196

namespace SL003FC

section
namespace Erdos1196
open scoped Asymptotics
/-- A set is primitive if no non-associated elements of the set divide each other. -/
def IsPrimitive {M : Type*} [CommMonoid M] (A : Set M) : Prop :=
  ∀ᵉ (x ∈ A) (y ∈ A), x ∣ y → Associated x y
end Erdos1196

namespace Erdos1196

/-- SL-003 transported target: FormalConjectures/ErdosProblems/1196.lean `erdos_1196`. -/
def SL003.targetProp : Prop :=
  ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧ ∀ x > (0 : ℕ), ∀ A ⊆ Set.Ici x, IsPrimitive A →
       ∑' (a : A), (1 / ((a.val : ℝ).log * a)) < 1 + o x

end Erdos1196
end
end SL003FC
