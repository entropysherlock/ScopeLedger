import Mathlib
import BorweinSineSeries.solution

namespace SL003FC

section
namespace BorweinSineSeries
end BorweinSineSeries

namespace BorweinSineSeries

/-- SL-003 transported target: FormalConjectures/Books/BorweinSineSeries.lean `borwein_sine_series`. -/
def SL003.targetProp : Prop :=
  Summable fun n : ℕ+ ↦ ((2 / 3 + 1 / 3 * Real.sin (n : ℝ)) ^ (n : ℕ)) / (n : ℝ)

end BorweinSineSeries
end
end SL003FC
