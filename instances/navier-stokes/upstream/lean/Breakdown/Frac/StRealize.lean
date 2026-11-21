import Breakdown.FreqTr.Statements
import Breakdown.Frac.ScaledDefs
import Breakdown.Frac.Defs

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown

def scaleField (α μ : ℝ) (f : Space → Space) : Space → Space :=
  fun y => μ ^ (1 - 1 / (2 * α)) • f (μ ^ (1 / (2 * α)) • y)

def dilExponent (α : ℝ) : ℝ := 1 - 3 / (4 * α)

namespace Freq

def fracHeatFactor (α t : ℝ) (ξ : Space) : ℝ := Real.exp (-(max t 0 * (2 * π * ‖ξ‖) ^ (2 * α)))

def fracHeatL2 (α t : ℝ) : L2C →L[ℝ] L2C :=
  fieldOp id (fun ξ => fracHeatFactor α t ξ • ContinuousLinearMap.id ℝ CSpace)

def fracHeatX (α t : ℝ) : X →L[ℝ] X := restrictX (fracHeatL2 α t)

def fracDilL2 (α μ : ℝ) : L2C →L[ℝ] L2C :=
  fieldOp (fun ξ => (μ ^ (-(1 / (2 * α)))) • ξ)
    (fun _ => (μ ^ (1 - 3 / (2 * α))) • ContinuousLinearMap.id ℝ CSpace)

def fracDilX (α μ : ℝ) : X →L[ℝ] X := if 0 < μ then restrictX (fracDilL2 α μ) else 0

def fracPhiFactor (α τ : ℝ) (ξ : Space) : ℝ :=
  2 * π * ‖ξ‖ * Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α)))

def fracPhiX (α τ : ℝ) : X →L[ℝ] L2R :=
  toPhys ∘L fieldOp id (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) ∘L
    Sig.subtypeL

def fracBilinForm (α τ : ℝ) (u v ψ : X) : ℝ :=
  -(1 / 2 : ℝ) * (trilinear u v (fracPhiX α τ ψ) + trilinear v u (fracPhiX α τ ψ))

def FracBilinSpec (α τ : ℝ) (B : X →L[ℝ] X →L[ℝ] X) : Prop :=
  ∀ u v ψ, inner ℝ (B u v) ψ = fracBilinForm α τ u v ψ

open Classical in
def fracBilinX (α τ : ℝ) : X →L[ℝ] X →L[ℝ] X :=
  if h : 0 < τ ∧ ∃ B, FracBilinSpec α τ B then h.2.choose else 0

def fracHeatSolenoidal (α τ : ℝ) : L2R →L[ℝ] X :=
  projX ∘L fieldOp id (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) ∘L
    freqTrR ∘L complexify

def niceField (m : Space → CSpace) : Space → Space :=
  fun x => realVec (FourierTransform.fourierInv m x)

def IsNiceField (φ : Space → Space) : Prop := ∃ m, IsNiceSymbol m ∧ φ = niceField m

def IsFracOf (α : ℝ) (χ ψ : X) : Prop :=
  ∀ᵐ ξ ∂volume, (ψ : L2C) ξ = ((2 * π * ‖ξ‖) ^ (2 * α)) • (χ : L2C) ξ

def FracHeatSemigroup (α : ℝ) : Prop :=
  fracHeatX α 0 = ContinuousLinearMap.id ℝ X ∧
  (∀ s t, 0 ≤ s → 0 ≤ t → fracHeatX α (s + t) = (fracHeatX α s).comp (fracHeatX α t)) ∧
  (∀ t, 0 ≤ t → ‖fracHeatX α t‖ ≤ 1) ∧
  (∀ x, ContinuousOn (fun t => fracHeatX α t x) (Ici 0)) ∧
  (∀ t (x y : X), inner ℝ (fracHeatX α t x) y = inner ℝ x (fracHeatX α t y)) ∧
  (∀ t (x : X), (fracHeatX α t x : L2C) = fracHeatL2 α t x)

def FracDilationAlgebra (α : ℝ) : Prop :=
  (∀ μ, 0 < μ → ∀ x, ‖fracDilX α μ x‖ = μ ^ dilExponent α * ‖x‖) ∧
  fracDilX α 1 = ContinuousLinearMap.id ℝ X ∧
  (∀ μ ν, 0 < μ → 0 < ν → fracDilX α (μ * ν) = (fracDilX α μ).comp (fracDilX α ν)) ∧
  (∀ μ t, 0 < μ → 0 ≤ t →
    (fracDilX α μ).comp (fracHeatX α (μ * t)) = (fracHeatX α t).comp (fracDilX α μ)) ∧
  (∀ μ, 0 < μ → ∀ x : X, (fracDilX α μ x : L2C) = fracDilL2 α μ x)

def FracDilationContinuous (α : ℝ) : Prop :=
  ∀ x : X, ContinuousOn (fun μ => fracDilX α μ x) (Ioi 0)

def FracRotationAlgebra (α : ℝ) : Prop :=
  ∀ R : Space ≃ₗᵢ[ℝ] Space,
    (∀ t x, rotX R (fracHeatX α t x) = fracHeatX α t (rotX R x)) ∧
    (∀ μ x, rotX R (fracDilX α μ x) = fracDilX α μ (rotX R x))

def DecayFieldScale (α : ℝ) : Prop :=
  ∀ μ f, 0 < μ → IsDecayField f → IsDecayField (scaleField α μ f)

def FracEmbedDilate (α : ℝ) : Prop :=
  ∀ μ f, 0 < μ → IsDecayField f → fracDilX α μ (embedX f) = embedX (scaleField α μ f)

def FracVelocityDilate (α : ℝ) : Prop :=
  ∀ μ, 0 < μ → ∀ x : X,
    (velocity (fracDilX α μ x) : Space → Space) =ᵐ[volume] scaleField α μ (velocity x : Space → Space)

def FracPhiBounds (α : ℝ) : Prop :=
  ∃ C : ℝ, ∀ τ, 0 < τ → ∀ ψ : X, MemLp (fracPhiX α τ ψ : Space → Space) 6 volume ∧
    (eLpNorm (fracPhiX α τ ψ : Space → Space) 2 volume).toReal ≤ C * τ ^ (-(1 / (2 * α))) * ‖ψ‖ ∧
    (eLpNorm (fracPhiX α τ ψ : Space → Space) 6 volume).toReal ≤ C * τ ^ (-(1 / α)) * ‖ψ‖

def FracPhiVelocity (α : ℝ) : Prop :=
  ∀ τ, 0 < τ → ∀ ψ h : X, IsSspOf (fracHeatX α τ ψ) h →
    (fracPhiX α τ ψ : Space → Space) =ᵐ[volume] (velocity h : Space → Space)

def FracBilinExists (α : ℝ) : Prop := ∀ τ, 0 < τ → ∃ B, FracBilinSpec α τ B

def FracBilinBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ τ, 0 < τ → ∀ u v : X,
    ‖fracBilinX α τ u v‖ ≤ C * τ ^ (-(3 / (4 * α))) * ‖u‖ * ‖v‖

def FracBilinShift (α : ℝ) : Prop :=
  ∀ s τ, 0 ≤ s → 0 < τ → ∀ u v : X, fracHeatX α s (fracBilinX α τ u v) = fracBilinX α (s + τ) u v

def FracBilinContinuous (α : ℝ) : Prop :=
  ∀ u v : X, ContinuousOn (fun τ => fracBilinX α τ u v) (Ioi 0)

def FracBilinDilate (α : ℝ) : Prop :=
  ∀ μ τ, 0 < μ → 0 < τ → ∀ u v : X,
    μ • fracDilX α μ (fracBilinX α (μ * τ) u v) = fracBilinX α τ (fracDilX α μ u) (fracDilX α μ v)

def FracBilinRotate (α : ℝ) : Prop :=
  ∀ (R : Space ≃ₗᵢ[ℝ] Space) τ (u v : X),
    rotX R (fracBilinX α τ u v) = fracBilinX α τ (rotX R u) (rotX R v)

def FracBilinTestFormula (α : ℝ) : Prop :=
  ∀ φ, IsTestField φ → ∀ τ, 0 < τ → ∀ v : X,
    fracBilinX α τ (embedX φ) v = -(1 / 2 : ℝ) • fracHeatSolenoidal α τ (advectTest φ v)

def FracBilinCompact (α : ℝ) : Prop :=
  ∀ x ∈ testSpan, ∀ τ, 0 < τ → IsCompactOperator (fracBilinX α τ x)

def FracFrameworkSpec (α : ℝ) : Prop :=
  ∃ F : ScaledMildFramework X (dilExponent α),
    F.G = fracHeatX α ∧ F.K = fracBilinX α ∧ F.D = fracDilX α

def FracCommutes (α : ℝ) : Prop :=
  ∀ F : ScaledMildFramework X (dilExponent α), F.G = fracHeatX α → F.K = fracBilinX α →
    F.D = fracDilX α → ∀ R : Space ≃ₗᵢ[ℝ] Space, F.Commutes (rotX R)

def NiceFieldProps (α : ℝ) : Prop :=
  ∀ φ, IsNiceField φ →
    (∃ ψ : SchwartzMap Space Space, (ψ : Space → Space) = φ) ∧ IsDecayField φ ∧
    IsNiceField (negSsp φ) ∧ IsNiceField (fractionalPowerAt α φ) ∧
    fractionalPowerAt α (negSsp φ) = negSsp (fractionalPowerAt α φ)

def NiceEmbedSymbol : Prop :=
  ∀ m, IsNiceSymbol m → (embedX (niceField m) : L2C) =ᵐ[volume] fun ξ => (2 * π * ‖ξ‖) • m ξ

def NicePairingByParts : Prop :=
  ∀ f φ, IsDecayField f → IsNiceField φ → gradientPairing f φ = fieldPairing f (negSsp φ)

def NiceAdvectionTrilinear : Prop :=
  ∀ f w, IsDecayField f → IsNiceField w → advectionPairing f w = trilinear (embedX f) (embedX f) w

def FracNiceGraphDense (α : ℝ) : Prop :=
  ∀ χ ψ : X, IsFracOf α χ ψ → ∀ ε > 0, ∃ φ, IsNiceField φ ∧
    ‖embedX φ - χ‖ < ε ∧ ‖embedX (fractionalPowerAt α φ) - ψ‖ < ε

def FracIsWeakSolution (α : ℝ) (v : ℝ → Space → Space) (a b : ℝ) : Prop :=
  (∀ t ∈ Icc a b, IsDecayField (v t)) ∧
  ContinuousOn (fun t => embedX (v t)) (Icc a b) ∧
  (∀ t ∈ Icc a b, ∀ t' ∈ Icc a b, Integrable (fun x => ‖v t x - v t' x‖ ^ 2)) ∧
  (∀ t₀ ∈ Icc a b, Filter.Tendsto (fun t => ∫ x, ‖v t x - v t₀ x‖ ^ 2)
    (nhdsWithin t₀ (Icc a b)) (nhds 0)) ∧
  (∀ φ, IsNiceField φ → ∀ t ∈ Ioo a b,
    HasDerivAt (fun τ => fieldPairing (v τ) φ)
      (-fieldPairing (v t) (fractionalPowerAt α φ) - advectionPairing (v t) φ) t) ∧
  (∀ φ, IsNiceField φ → ContinuousOn (fun τ => fieldPairing (v τ) φ) (Icc a b))

def FracWeakInX (α : ℝ) : Prop :=
  ∀ v a b, a < b → FracIsWeakSolution α v a b → ∀ φ, IsNiceField φ → ∀ t ∈ Icc a b,
    IntervalIntegrable (fun s => inner ℝ (embedX (v s)) (embedX (fractionalPowerAt α φ)) +
      trilinear (embedX (v s)) (embedX (v s)) (negSsp φ)) volume a t ∧
    inner ℝ (embedX (v t)) (embedX φ) = inner ℝ (embedX (v a)) (embedX φ) -
      ∫ s in a..t, (inner ℝ (embedX (v s)) (embedX (fractionalPowerAt α φ)) +
        trilinear (embedX (v s)) (embedX (v s)) (negSsp φ))

def IsFracMildX (α : ℝ) (u : ℝ → X) (a b : ℝ) : Prop :=
  ContinuousOn u (Icc a b) ∧
    ∀ t ∈ Icc a b, IntervalIntegrable (fun s => fracBilinX α (t - s) (u s) (u s)) volume a t ∧
      u t = fracHeatX α (t - a) (u a) + ∫ s in a..t, fracBilinX α (t - s) (u s) (u s)

def FracMildOfWeak (α : ℝ) : Prop :=
  ∀ v a b, a < b → FracIsWeakSolution α v a b → IsFracMildX α (fun t => embedX (v t)) a b

end Freq

end Breakdown
