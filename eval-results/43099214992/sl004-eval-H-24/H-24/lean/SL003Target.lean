import Mathlib
import Erdos889V1FiniteFC

namespace SL003FC

section
open Finset Nat Filter Topology
namespace Erdos889
/--
$v(n,k)$ counts the prime factors of $n+k$ which do not divide $n+i$
for all $0 \le i < k$.
-/
def v (n k : ℕ) : ℕ :=
  ((n + k).primeFactors.filter (fun p =>
    ∀ i ∈ range k, ¬ p ∣ n + i)).card
/--
$v_0(n)$ is the supremum of $v(n,k)$ for all $k \ge 0$.
-/
noncomputable def v₀ (n : ℕ) : ℕ∞ :=
  ⨆ k, (v n k : ℕ∞)
/--
$v_l(n)$ is the supremum of $v(n,k)$ for all $k \ge l$
-/
noncomputable def v_l (l n : ℕ) : ℕ∞ :=
  ⨆ k ≥ l, (v n k : ℕ∞)
/--
$V(n,k)$ is the number of primes $p$ such that
$p^\alpha$ exactly divides $n+k$ and
for all $0 \le i < k$, $p^\alpha$ does not divide $n+i$,
where $\alpha$ is the multiplicity of $p$ in the factorization of $n+k$.
-/
def V (n k : ℕ) : ℕ :=
  ((n + k).primeFactors.filter (fun p =>
    ∀ i ∈ range k, ¬ p ^ ((n + k).factorization p) ∣ n + i)).card
/--
$V_l(n)$ is the supremum of $V(n,k)$ for all $k \ge l$
-/
noncomputable def V_l (l n : ℕ) : ℕ∞ :=
  ⨆ k ≥ l, (V n k : ℕ∞)
end Erdos889

namespace Erdos889

/-- SL-003 transported target: FormalConjectures/ErdosProblems/889.lean `erdos_889.variants.V1_eq_1_finite`. -/
def SL003.targetProp : Prop :=
  {n | V_l 1 n = 1}.Finite

end Erdos889
end
end SL003FC
