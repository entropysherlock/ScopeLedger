import Mathlib
import SpectralProduct3DFC

namespace SL003FC

section
open MeasureTheory
namespace NowhereDenseSpectralSet
end NowhereDenseSpectralSet
namespace SpectralSetProduct
/-- The product $A \times B$, represented by consecutive coordinate blocks. -/
def productSet {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) :
    Set (Fin (n + m) → ℝ) :=
  {x | (fun i ↦ x (Fin.castAdd m i)) ∈ A ∧ (fun j ↦ x (Fin.natAdd n j)) ∈ B}
/-- Spectrality of a product with an `n`-dimensional convex body forces spectrality of its
bounded, measurable `m`-dimensional right factor.

Following [KLM2023, §1.1], a convex body is a compact convex set with nonempty interior;
Mathlib's `ConvexBody` does not require the latter, so it is imposed explicitly here. -/
def spectralProductImpliesRightSpectral (n m : ℕ) : Prop :=
  ∀ (A : ConvexBody (Fin n → ℝ)) (B : Set (Fin m → ℝ)),
    (interior (A : Set (Fin n → ℝ))).Nonempty →
    Bornology.IsBounded B → MeasurableSet B →
      isSpectral (productSet (A : Set (Fin n → ℝ)) B) → isSpectral B
end SpectralSetProduct

namespace SpectralSetProduct

/-- SL-003 transported target: FormalConjectures/Arxiv/2209.04540/SpectralSetsAndWeakTiling.lean `isSpectral_right_of_product_three_dimensional`. -/
def SL003.targetProp : Prop :=
  ∀ (m : ℕ), 0 < m → spectralProductImpliesRightSpectral 3 m

end SpectralSetProduct
end
end SL003FC
