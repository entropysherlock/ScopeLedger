import Mathlib
import Dyadic354.UpstreamBridge

namespace SL003FC

section
namespace Erdos354
/-- The sequence `⌊a⌋, ⌊γ * a⌋, ⌊γ ^ 2 * a⌋, ..., ⌊γ ^ i * a⌋, ...`. -/
noncomputable def FloorMultiples (a γ : ℝ) (n : ℕ) : ℤ := ⌊γ ^ n * a⌋
/-- The sequence `⌊a⌋, ⌊b⌋, ⌊γ * a⌋, ⌊γ * b⌋, ... ⌊γ ^ i * a⌋, ⌊γ ^ i * b⌋, ...` -/
noncomputable def FloorMultiples.interleave (a b γ : ℝ) (n : ℕ) : ℤ :=
  if n % 2 = 0 then
    FloorMultiples a γ (n / 2)
  else
    FloorMultiples b γ (n / 2)
end Erdos354

namespace Erdos354

/-- SL-003 transported target: FormalConjectures/ErdosProblems/354.lean `erdos_354.parts.i`. -/
def SL003.targetProp : Prop :=
  ∀ᵉ (α > 0) (β > 0), Irrational (α / β) →
    IsAddCompleteNatSeq' (FloorMultiples.interleave α β 2)

end Erdos354
end
end SL003FC
