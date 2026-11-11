import Mathlib
import ErdosProblems.Erdos690

namespace SL003FC

section
open Filter
namespace Erdos690
/-- The set of positive integers whose `k`-th smallest prime factor is `p`: if
$p_1<p_2<\cdots$ are the primes dividing $n$ then $p_k=p$. -/
def kthPrimeFactorSet (k p : ℕ) : Set ℕ :=
  {n | 0 < n ∧ p ∈ n.primeFactors ∧ (n.primeFactors.filter (· < p)).card = k - 1}
/-- A function on the primes is *unimodular* if it first increases in $p$ until its maximum then
decreases. -/
def IsUnimodalOnPrimes (f : ℕ → ℝ) : Prop :=
  ∃ m, m.Prime ∧ (∀ p q, p.Prime → q.Prime → p ≤ q → q ≤ m → f p ≤ f q) ∧
    ∀ p q, p.Prime → q.Prime → m ≤ p → p ≤ q → f q ≤ f p
end Erdos690

namespace Erdos690

/-- SL-003 transported target: FormalConjectures/ErdosProblems/690.lean `erdos_690`. -/
def SL003.targetProp : Prop :=
  ¬ ∀ k ≥ 1, ∀ d : ℕ → ℝ,
      (∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) → IsUnimodalOnPrimes d

end Erdos690
end
end SL003FC
