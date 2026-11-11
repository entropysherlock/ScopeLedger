import Mathlib
import Kourovka.Problem_21_149

namespace SL003FC

section
open Filter Topology
namespace Kourovka.«21.149»
/--
An order automorphism $f$ of $\mathbb{R}$ is *locally right $H$-linear* if every point has a
right neighbourhood on which $f$ is affine with slope in $H \le \mathbb{R}_{>0}$.
-/
def IsLocallyRightLinear (H : Subgroup NNRealˣ) (f : ℝ ≃o ℝ) : Prop :=
  ∀ a : ℝ, ∃ ε > (0 : ℝ), ∃ h ∈ H, ∀ x : ℝ, a < x → x < a + ε →
    f x = f a + ((h : NNReal) : ℝ) * (x - a)
/--
$A$ is one of the six Dlab groups with slope group $H$. Each consists of the locally right
$H$-linear order automorphisms $f$ with a condition at the ends.

- Four act on $I = [0, 1]$. An order automorphism of $I$ is identified with its extension to
  $\mathbb{R}$ by the identity, so $f$ fixes every point outside $(0, 1)$. The four groups are
  $D_H(I)$ ($f$ is also the identity near $0$ and near $1$), $D_{H*}(I)$ (near $0$),
  $D_{*H}(I)$ (near $1$) and $\overline{D}_H(I)$ (no further condition).
- Two act on the extended real line $\overline{\mathbb{R}}$, whose order automorphisms are those
  of $\mathbb{R}$. They are $D_H$ ($f$ is the identity near $-\infty$ and near $+\infty$) and
  $D_{H*}$ (near $-\infty$).
-/
def IsDlabGroup (H : Subgroup NNRealˣ) (A : Subgroup (ℝ ≃o ℝ)) : Prop :=
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∧
    (∀ᶠ x in 𝓝 (0 : ℝ), f x = x) ∧ ∀ᶠ x in 𝓝 (1 : ℝ), f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∧
    ∀ᶠ x in 𝓝 (0 : ℝ), f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∧
    ∀ᶠ x in 𝓝 (1 : ℝ), f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ ∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ᶠ x in atBot, f x = x) ∧
    ∀ᶠ x in atTop, f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ ∀ᶠ x in atBot, f x = x)
/--
Dlab's order on a group $G$ of order automorphisms of $\mathbb{R}$: $f < g$ if $f(x) < g(x)$ at
some point $x$ and every point $y$ with $g(y) < f(y)$ lies to the right of $x$. For elements of
a Dlab group, this says that $f$ is below $g$ just after the point where they start to differ.
-/
def DlabLt {G : Subgroup (ℝ ≃o ℝ)} (f g : G) : Prop :=
  ∃ x, (f : ℝ ≃o ℝ) x < (g : ℝ ≃o ℝ) x ∧ ∀ y, (g : ℝ ≃o ℝ) y < (f : ℝ ≃o ℝ) y → x < y
end Kourovka.«21.149»

namespace Kourovka.«21.149»

/-- SL-003 transported target: FormalConjectures/Kourovka/21_149.lean `kourovka_21_149.variants.not_inner`. -/
def SL003.targetProp : Prop :=
  ∃ (K : Subgroup NNRealˣ) (G : Subgroup (ℝ ≃o ℝ)), IsDlabGroup K G ∧
      ∃ α : G ≃* G, (∀ f g : G, DlabLt (α f) (α g) ↔ DlabLt f g) ∧
        ¬ ∃ u : G, ∀ f : G, α f = u⁻¹ * f * u

end Kourovka.«21.149»
end
end SL003FC
