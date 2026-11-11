import Mathlib
import ErdosProblems.Erdos1195

namespace SL003FC

section
open Filter MeasureTheory
namespace Erdos1195
/-- The Lebesgue measure $\lvert S\cap (0,x)\rvert$ of $S\cap (0,x)$, as a real number. -/
noncomputable def countingFunction (S : Set ℝ) (x : ℝ) : ℝ :=
  (volume (S ∩ Set.Ioo 0 x)).toReal
/-- `IntegerRatioFree S` says that $x/y$ is not an integer for all distinct $x,y\in S$. Negative
integers are included. Since `x / 0 = 0` in Lean, a set with at least two points cannot contain
`0`; this does not affect measures. -/
def IntegerRatioFree (S : Set ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ∀ z : ℤ, x / y ≠ z
/-- `IsGrowthRate F` says that $F$ is nonnegative and non-decreasing on $[1,\infty)$ and tends to
infinity. We use $F:\mathbb{R}\to\mathbb{R}$; only its values on $[1,\infty)$ matter. -/
def IsGrowthRate (F : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Ici (1 : ℝ), 0 ≤ F x) ∧ MonotoneOn F (Set.Ici 1) ∧ Tendsto F atTop atTop
/-- `HasSet F` says that there is a measurable set $S$ of infinite measure such that $x/y$ is
never an integer for distinct $x,y\in S$, and $\lvert S\cap (0,x)\rvert\geq F(x)$ for all
sufficiently large $x$. -/
def HasSet (F : ℝ → ℝ) : Prop :=
  ∃ S : Set ℝ, MeasurableSet S ∧ volume S = ⊤ ∧ IntegerRatioFree S ∧
    ∀ᶠ x in atTop, F x ≤ countingFunction S x
/-- The answer: the growth rates $F$ with $\int_1^\infty F(x)/x^2\,dx<\infty$. For a non-negative
monotone $F$, `IntegrableOn` is equivalent to this integral being finite. -/
def erdos_1195.answer : Set (ℝ → ℝ) :=
  {F | IsGrowthRate F ∧ IntegrableOn (fun x ↦ F x / x ^ 2) (Set.Ici 1)}
end Erdos1195

namespace Erdos1195

/-- SL-003 transported target: FormalConjectures/ErdosProblems/1195.lean `erdos_1195`. -/
def SL003.targetProp : Prop :=
  {F : ℝ → ℝ | IsGrowthRate F ∧ HasSet F} = erdos_1195.answer

end Erdos1195
end
end SL003FC
