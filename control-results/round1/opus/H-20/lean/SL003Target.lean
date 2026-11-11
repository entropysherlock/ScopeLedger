import Mathlib
import Erdos522StrongLawFC

namespace SL003FC

section
open MeasureTheory Filter
open scoped ProbabilityTheory Topology Real
namespace Erdos522
/--
A sequence of *Kac coefficients* over a subset `S` of a field `k` is a countably infinite sequence
of independent random variables, each uniformly distributed over `S` with respect to the reference
measure `μ`. The default reference measure is the counting measure, so that for a finite set `S`
each coefficient takes every value of `S` with probability `1 / |S|`.

Such a sequence determines a *Kac polynomial* of degree `n` for each `n`, which is the random
polynomial given by `KacCoefficients.polynomial`.
-/
@[ext]
structure KacCoefficients
    {k : Type*} [Field k] [MeasurableSpace k] (S : Set k)
    (Ω : Type*) [MeasureSpace Ω] (μ : Measure k := Measure.count) where
  toFun : ℕ → Ω → k
  h_indep : ProbabilityTheory.iIndepFun toFun ℙ
  h_unif : ∀ i, MeasureTheory.pdf.IsUniform (toFun i) S ℙ μ
variable {k : Type*} [Field k] [MeasurableSpace k] (S : Set k)
    (Ω : Type*) [MeasureSpace Ω] (μ : Measure k := Measure.count)
/--
We can always view a Kac polynomial as a random variable on `ℕ`.
-/
instance : FunLike (KacCoefficients S Ω μ) ℕ (Ω → k) where
  coe P := P.toFun
  coe_injective P Q h := by aesop
namespace KacCoefficients
open scoped Polynomial
variable {S Ω} {μ : Measure k}
/--
The random polynomial associated to a sequence `c : KacCoefficients S Ω μ` of Kac coefficients
given by `∑ i ∈ Finset.range (n + 1), c i z^i`.
-/
noncomputable def polynomial (c : KacCoefficients S Ω μ) (n : ℕ) :
    Ω → k[X] := fun ω => ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (c i ω)
/--
The random multiset of roots associated to a Kac polynomial
-/
noncomputable def roots (c : KacCoefficients S Ω μ) (n : ℕ) : Ω → Multiset k :=
    fun ω => (c.polynomial n ω).roots
/-- Counts the number of roots of a Kac polynomial in the unit disk with multiplicity. -/
noncomputable def numRootsInUnitDisk [PseudoMetricSpace k] (c : KacCoefficients S Ω μ) (n : ℕ)
    (ω : Ω) : ℕ :=
  open scoped Classical in
  (c.roots n ω).countP (· ∈ Metric.closedBall 0 1)
end KacCoefficients
end Erdos522

namespace Erdos522

/-- SL-003 transported target: FormalConjectures/ErdosProblems/522.lean `erdos_522.variants.zero_one`. -/
def SL003.targetProp : Prop :=
  ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {n : ℕ} (hn : 1 ≤ n) (f : KacCoefficients ({0, 1} : Set ℂ) Ω),
      ℙ {ω | atTop.Tendsto (fun n : ℕ ↦ (2 * f.numRootsInUnitDisk n ω : ℝ) / n) (𝓝 1)} = 1

end Erdos522
end
end SL003FC
