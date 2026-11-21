import Breakdown.Frac.StProfile

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq

def driftAdjoint (α a : ℝ) (φ : Space → Space) (y : Space) : Space :=
  (1 - 4 * (1 / (2 * α))) • φ y - (1 / (2 * α)) • fderiv ℝ φ y y
    - a • (fderiv ℝ φ y (axialTurn y) - axialTurn (φ y))

def IsWeakRotatingProfile (α a : ℝ) (U : X) : Prop :=
  U ≠ 0 ∧ ∀ φ, IsNiceField φ →
    (∫ y, inner ℝ ((velocity U : Space → Space) y) (driftAdjoint α a φ y)) +
      (∫ y, inner ℝ ((velocity U : Space → Space) y) (fractionalPowerAt α φ y)) +
      trilinear U U φ = 0

def WeakRotatingProfileExists (α : ℝ) : Prop := ∃ (a : ℝ) (U : X), IsWeakRotatingProfile α a U

def WeakToProfileStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → WeakRotatingProfileExists α → RotatingFractionalProfileExists α

def simOp (α a μ : ℝ) : X →L[ℝ] X :=
  (fracDilX α μ⁻¹).comp (rotX (axialRotation (a * Real.log μ))).toContinuousLinearEquiv.toContinuousLinearMap

def simAdj (α a μ : ℝ) (φ : Space → Space) : Space → Space :=
  pushForward (axialRotation (-(a * Real.log μ))) (fun y => μ ^ (4 * (1 / (2 * α)) - 1) • φ (μ ^ (1 / (2 * α)) • y))

def NiceDriftClosedStatement : Prop :=
  ∀ α a : ℝ, 0 < α → ∀ φ, IsNiceField φ → IsNiceField (driftAdjoint α a φ)

def NiceSimAdjClosedStatement : Prop :=
  ∀ α a μ : ℝ, 0 < α → 0 < μ → ∀ φ, IsNiceField φ → IsNiceField (simAdj α a μ φ)

def SimAdjPairingStatement : Prop :=
  ∀ α a μ : ℝ, 1 < α → 0 < μ → ∀ x : X, ∀ φ, IsNiceField φ →
    ∫ y, inner ℝ ((velocity (simOp α a μ x) : Space → Space) y) (φ y) =
      ∫ y, inner ℝ ((velocity x : Space → Space) y) (simAdj α a μ φ y)

def SimAdjDerivStatement : Prop :=
  ∀ α a : ℝ, 1 < α → ∀ x : X, ∀ ψ, IsNiceField ψ → ∀ t : ℝ, t < 1 →
    HasDerivAt (fun τ => ∫ y, inner ℝ ((velocity x : Space → Space) y) (simAdj α a (1 - τ) ψ y))
      (∫ y, inner ℝ ((velocity x : Space → Space) y)
        ((1 - t)⁻¹ • driftAdjoint α a (simAdj α a (1 - t) ψ) y)) t

end Breakdown.FracCert
