import Breakdown.FracCert.StWeak
import Breakdown.FracCert.StatementsSmooth

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq

def heatField (α τ : ℝ) (φ : Space → Space) (y : Space) : Space :=
  realVec (FourierTransform.fourierInv (fun ξ => Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))) •
    FourierTransform.fourier (fun x => complexifyVec (φ x)) ξ) y)

def NiceHeatStatement : Prop :=
  ∀ α τ : ℝ, 1 < α → 0 ≤ τ → ∀ φ, IsNiceField φ → IsNiceField (heatField α τ φ) ∧
    ∀ x : X, ∫ y, inner ℝ ((velocity (fracHeatX α τ x) : Space → Space) y) (φ y) =
      ∫ y, inner ℝ ((velocity x : Space → Space) y) (heatField α τ φ y)

def NiceAnnihilatorStatement : Prop :=
  ∀ z : X, (∀ φ, IsNiceField φ → ∫ y, inner ℝ ((velocity z : Space → Space) y) (φ y) = 0) → z = 0

def BilinPairingStatement : Prop :=
  ∀ α τ : ℝ, 1 < α → 0 < τ → ∀ u : X, ∀ φ, IsNiceField φ →
    ∫ y, inner ℝ ((velocity (fracBilinX α τ u u) : Space → Space) y) (φ y) =
      -trilinear u u (heatField α τ φ)

def PowerSimAdjStatement : Prop :=
  ∀ α a μ : ℝ, 1 < α → 0 < μ → ∀ φ, IsNiceField φ →
    fractionalPowerAt α (simAdj α a μ φ) = μ • simAdj α a μ (fractionalPowerAt α φ)

def MildOfWeakProfileStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U →
    ∀ F : ScaledMildFramework X (dilExponent α), IsConcreteFrame α F →
    ∀ t : ℝ, 0 < t → t < 1 → F.IsMildOnIcc (fun s => simOp α a (1 - s) U) 0 t

def SimOpComposeStatement : Prop :=
  ∀ α a : ℝ, 1 < α → (∀ x : X, simOp α a 1 x = x) ∧
    ∀ μ ν : ℝ, 0 < μ → 0 < ν → ∀ x : X, simOp α a μ (simOp α a ν x) = simOp α a (μ * ν) x

def SimOpMomentsStatement : Prop :=
  ∀ α a μ : ℝ, 1 < α → 0 < μ → ∀ x : X, HasAllMoments x → HasAllMoments (simOp α a μ x)

def ProfileMomentsStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U

end Breakdown.FracCert
