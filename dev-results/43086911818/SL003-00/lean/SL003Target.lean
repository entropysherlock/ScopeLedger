import Mathlib
import ErdosProblems.Erdos235

namespace SL003FC

section
open Filter
open scoped Topology
namespace Erdos235
/-- The product of the first `k + 1` primes.
On [erdosproblems.com/235](https://www.erdosproblems.com/235) this is $N_{k+1}=2\cdot 3\cdots p_{k+1}$.
The limit as $k\to\infty$ is the same for either indexing. -/
noncomputable def N (k : ℕ) : ℕ :=
  primorial (Nat.nth Nat.Prime k)
/-- The increasing list of integers `< n` that are coprime to `n`. -/
def coprimeList (n : ℕ) : List ℕ :=
  ({a ∈ Finset.range n | n.Coprime a}).sort (· ≤ ·)
/-- The gaps $a_i - a_{i-1}$ between consecutive entries of `coprimeList n`. -/
def gaps (n : ℕ) : List ℕ :=
  (coprimeList n).zipWith (fun a b ↦ b - a) (coprimeList n).tail
/-- The number of gaps of size at most $c \cdot n / \varphi(n)$. -/
noncomputable def countGaps (n : ℕ) (c : ℝ) : ℕ :=
  (gaps n).countP fun g ↦ decide ((g : ℝ) ≤ c * (n : ℝ) / (n.totient : ℝ))
/-- The proportion appearing in `erdos_235`, for the primorial `N k`. -/
noncomputable def proportion (k : ℕ) (c : ℝ) : ℝ :=
  (countGaps (N k) c : ℝ) / ((N k).totient : ℝ)
end Erdos235

namespace Erdos235

/-- SL-003 transported target: FormalConjectures/ErdosProblems/235.lean `erdos_235`. -/
def SL003.targetProp : Prop :=
  ∃ f : ℝ → ℝ, ContinuousOn f (Set.Ici (0 : ℝ)) ∧
      ∀ c, 0 ≤ c → Tendsto (fun k ↦ proportion k c) atTop (𝓝 (f c))

end Erdos235
end
end SL003FC
