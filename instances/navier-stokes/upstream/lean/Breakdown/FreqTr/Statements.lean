import Breakdown.FreqTr.Basic

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

def FieldOpRealized : Prop :=
  ∀ (E : Space ≃L[ℝ] Space) (F : Space → CSpace →L[ℝ] CSpace) (C : ℝ),
    AEStronglyMeasurable F volume → (∀ ξ, ‖F ξ‖ ≤ C) → IsRealizedBy (fieldOp E F) E F

def HeatSemigroup : Prop :=
  heatX 0 = ContinuousLinearMap.id ℝ X ∧
  (∀ s t, 0 ≤ s → 0 ≤ t → heatX (s + t) = (heatX s).comp (heatX t)) ∧
  (∀ t, 0 ≤ t → ‖heatX t‖ ≤ 1) ∧
  (∀ x, ContinuousOn (fun t => heatX t x) (Ici 0)) ∧
  (∀ t (x y : X), inner ℝ (heatX t x) y = inner ℝ x (heatX t y)) ∧
  (∀ t (x : X), (heatX t x : L2C) = heatL2 t x)

def DilationAlgebra : Prop :=
  (∀ μ, 0 < μ → ∀ x, ‖dilX μ x‖ = μ ^ (1 / 4 : ℝ) * ‖x‖) ∧
  dilX 1 = ContinuousLinearMap.id ℝ X ∧
  (∀ μ ν, 0 < μ → 0 < ν → dilX (μ * ν) = (dilX μ).comp (dilX ν)) ∧
  (∀ μ t, 0 < μ → 0 ≤ t → (dilX μ).comp (heatX (μ * t)) = (heatX t).comp (dilX μ)) ∧
  (∀ μ, 0 < μ → ∀ x : X, (dilX μ x : L2C) = dilL2 μ x)

def DilationContinuous : Prop := ∀ x : X, ContinuousOn (fun μ => dilX μ x) (Ioi 0)

def RotationAlgebra : Prop :=
  ∀ R : Space ≃ₗᵢ[ℝ] Space,
    (∀ x : X, (rotX R x : L2C) = rotL2 R x) ∧
    (∀ t x, rotX R (heatX t x) = heatX t (rotX R x)) ∧
    (∀ μ x, rotX R (dilX μ x) = dilX μ (rotX R x))

def EmbedMem : Prop := ∀ f, IsDecayField f → ofGrad f ∈ Sig

def EmbedLinear : Prop :=
  (∀ f g, IsDecayField f → IsDecayField g → embedX (f + g) = embedX f + embedX g) ∧
  (∀ f g, IsDecayField f → IsDecayField g → embedX (f - g) = embedX f - embedX g) ∧
  (∀ (c : ℝ) f, IsDecayField f → embedX (c • f) = c • embedX f)

def EmbedNorm : Prop :=
  ∀ f, IsDecayField f → ‖embedX f‖ ^ 2 = ∫ y, ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2

def EmbedNeZero : Prop := ∀ f, IsDecayField f → (∃ y, f y ≠ 0) → embedX f ≠ 0

def EmbedRot : Prop :=
  ∀ R f, IsDecayField f → rotX R (embedX f) = embedX (pushForward R f)

def EmbedDilate : Prop :=
  ∀ μ f, 0 < μ → IsDecayField f → dilX μ (embedX f) = embedX (dilateField μ f)

def EmbedNegSsp : Prop := ∀ φ, IsTestField φ → IsSspOf (embedX φ) (embedX (negSsp φ))

def TestDenseGraph : Prop :=
  ∀ χ ψ : X, IsSspOf χ ψ → ∀ ε > 0, ∃ φ, IsTestField φ ∧
    ‖embedX φ - χ‖ < ε ∧ ‖embedX (negSsp φ) - ψ‖ < ε

def TestDense : Prop := Dense (testSpan : Set X)

def TestSpanSpec : Prop := ∀ x ∈ testSpan, ∃ φ, IsTestField φ ∧ embedX φ = x

def GradSixDecay : Prop :=
  ∃ S : ℝ, ∀ f, IsDecayField f → MemLp f 6 volume ∧
    (eLpNorm f 6 volume).toReal ≤ S * Real.sqrt (∫ y, ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2)

def VelocityExists : Prop := ∃ V, VelocitySpec V

def VelocityDecay : Prop :=
  ∀ f, IsDecayField f → (velocity (embedX f) : Space → Space) =ᵐ[volume] f

def PartialDecay : Prop :=
  ∀ f, IsDecayField f → ∀ j, (partialX j (embedX f) : Space → Space) =ᵐ[volume] partialField f j

def PartialNormLe : Prop := ∀ h : X, ∑ j : Fin 3, ‖partialX j h‖ ^ 2 ≤ ‖h‖ ^ 2

def VelocityInvertsHalfSsp : Prop :=
  ∀ g h : X, IsHalfSspOf g h → (velocity h : Space → Space) =ᵐ[volume] (toPhys g : Space → Space)

def TrilinearBound : Prop :=
  ∃ C : ℝ, ∀ u v : X, ∀ w : Space → Space, MemLp w 2 volume → MemLp w 6 volume →
    Integrable (fun x => ∑ j : Fin 3,
      (velocity u : Space → Space) x j * inner ℝ ((partialX j v : Space → Space) x) (w x)) volume ∧
    |trilinear u v w| ≤
      C * ‖u‖ * ‖v‖ * Real.sqrt ((eLpNorm w 2 volume).toReal * (eLpNorm w 6 volume).toReal)

def PhiBounds : Prop :=
  ∃ C : ℝ, ∀ τ, 0 < τ → ∀ ψ : X, MemLp (phiX τ ψ : Space → Space) 6 volume ∧
    (eLpNorm (phiX τ ψ : Space → Space) 2 volume).toReal ≤ C * τ ^ (-(1 / 2 : ℝ)) * ‖ψ‖ ∧
    (eLpNorm (phiX τ ψ : Space → Space) 6 volume).toReal ≤ C * τ ^ (-(1 : ℝ)) * ‖ψ‖

def PhiVelocity : Prop :=
  ∀ τ, 0 < τ → ∀ ψ h : X, IsSspOf (heatX τ ψ) h →
    (phiX τ ψ : Space → Space) =ᵐ[volume] (velocity h : Space → Space)

def BilinExists : Prop := ∀ τ, 0 < τ → ∃ B, BilinSpec τ B

def BilinBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ τ, 0 < τ → ∀ u v : X, ‖bilinX τ u v‖ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖u‖ * ‖v‖

def BilinShift : Prop :=
  ∀ s τ, 0 ≤ s → 0 < τ → ∀ u v : X, heatX s (bilinX τ u v) = bilinX (s + τ) u v

def BilinContinuous : Prop := ∀ u v : X, ContinuousOn (fun τ => bilinX τ u v) (Ioi 0)

def BilinDilate : Prop :=
  ∀ μ τ, 0 < μ → 0 < τ → ∀ u v : X,
    μ • dilX μ (bilinX (μ * τ) u v) = bilinX τ (dilX μ u) (dilX μ v)

def BilinRotate : Prop :=
  ∀ (R : Space ≃ₗᵢ[ℝ] Space) τ (u v : X), rotX R (bilinX τ u v) = bilinX τ (rotX R u) (rotX R v)

def BilinCompact : Prop :=
  ∀ x ∈ testSpan, ∀ τ, 0 < τ → IsCompactOperator (bilinX τ x)

def PairingEmbed : Prop :=
  ∀ f g, IsDecayField f → IsDecayField g → inner ℝ (embedX f) (embedX g) = gradientPairing f g

def PairingByParts : Prop :=
  ∀ f φ, IsDecayField f → IsTestField φ → gradientPairing f φ = fieldPairing f (negSsp φ)

def AdvectionTrilinear : Prop :=
  ∀ f w, IsDecayField f → IsTestField w → advectionPairing f w = trilinear (embedX f) (embedX f) w

def IsWeakSolution (v : ℝ → Space → Space) (a b : ℝ) : Prop :=
  (∀ t ∈ Icc a b, IsDecayField (v t)) ∧
  ContinuousOn (fun t => embedX (v t)) (Icc a b) ∧
  (∀ t ∈ Icc a b, ∀ t' ∈ Icc a b, Integrable (fun x => ‖v t x - v t' x‖ ^ 2)) ∧
  (∀ t₀ ∈ Icc a b, Filter.Tendsto (fun t => ∫ x, ‖v t x - v t₀ x‖ ^ 2)
    (nhdsWithin t₀ (Icc a b)) (nhds 0)) ∧
  (∀ φ, IsTestField φ → ∀ t ∈ Ioo a b,
    HasDerivAt (fun τ => fieldPairing (v τ) φ)
      (-gradientPairing (v t) φ - advectionPairing (v t) φ) t) ∧
  (∀ φ, IsTestField φ → ContinuousOn (fun τ => fieldPairing (v τ) φ) (Icc a b))

def WeakInX : Prop :=
  ∀ v a b, a < b → IsWeakSolution v a b → ∀ φ, IsTestField φ → ∀ t ∈ Icc a b,
    IntervalIntegrable (fun s => inner ℝ (embedX (v s)) (embedX (negSsp φ)) +
      trilinear (embedX (v s)) (embedX (v s)) (negSsp φ)) volume a t ∧
    inner ℝ (embedX (v t)) (embedX φ) = inner ℝ (embedX (v a)) (embedX φ) -
      ∫ s in a..t, (inner ℝ (embedX (v s)) (embedX (negSsp φ)) +
        trilinear (embedX (v s)) (embedX (v s)) (negSsp φ))

def IsMildX (u : ℝ → X) (a b : ℝ) : Prop :=
  ContinuousOn u (Icc a b) ∧
    ∀ t ∈ Icc a b, IntervalIntegrable (fun s => bilinX (t - s) (u s) (u s)) volume a t ∧
      u t = heatX (t - a) (u a) + ∫ s in a..t, bilinX (t - s) (u s) (u s)

def MildOfWeak : Prop :=
  ∀ v a b, a < b → IsWeakSolution v a b → IsMildX (fun t => embedX (v t)) a b

def gradHat (f : Space → Space) (k : Fin 3) : L2C := freqTrR (complexify (toLpOrZero 2 (partialField f k)))

def GradCompatible : Prop :=
  ∀ f, IsDecayField f → ∀ j k : Fin 3,
    ∀ᵐ ξ ∂volume, (ξ k : ℝ) • (gradHat f j : L2C) ξ = (ξ j : ℝ) • (gradHat f k : L2C) ξ

def FreqTrConjSym : Prop := ∀ g : L2R, reflConj (freqTrR (complexify g)) = freqTrR (complexify g)

def IsNiceSymbol (m : Space → CSpace) : Prop :=
  ContDiff ℝ ∞ m ∧ HasCompactSupport m ∧ (∃ r > 0, ∀ ξ : Space, ‖ξ‖ < r → m ξ = 0) ∧
    (∀ ξ, m (-ξ) = conjVec (m ξ)) ∧ (∀ ξ, ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * m ξ i = 0)

def NiceDense : Prop :=
  ∀ χ ψ : X, IsSspOf χ ψ → ∀ ε > 0, ∃ m, IsNiceSymbol m ∧
    (eLpNorm (fun ξ => m ξ - (χ : L2C) ξ) 2 volume).toReal < ε ∧
    (eLpNorm (fun ξ => sspFactor ξ • m ξ - (ψ : L2C) ξ) 2 volume).toReal < ε

def NiceApprox : Prop :=
  ∀ m, IsNiceSymbol m → ∀ ε > 0, ∃ φ, IsTestField φ ∧
    (eLpNorm (fun ξ => (embedX φ : L2C) ξ - m ξ) 2 volume).toReal < ε ∧
    (eLpNorm (fun ξ => (embedX (negSsp φ) : L2C) ξ - sspFactor ξ • m ξ) 2 volume).toReal < ε

def FreqTrL1L2 : Prop :=
  ∀ g : Space → CSpace, MemLp g 1 volume → MemLp g 2 volume →
    (freqTrL2 (toLpOrZero 2 g) : Space → CSpace) =ᵐ[volume] FourierTransform.fourier g

def FreqTrInvL1L2 : Prop :=
  ∀ g : Space → CSpace, MemLp g 1 volume → MemLp g 2 volume →
    (freqTrL2.symm (toLpOrZero 2 g) : Space → CSpace) =ᵐ[volume] FourierTransform.fourierInv g

def projX : L2C →L[ℝ] X := Sig.orthogonalProjectionOnto

def heatDivFree (τ : ℝ) : L2R →L[ℝ] X :=
  projX ∘L fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) ∘L freqTrR ∘L complexify

def advectTest (φ : Space → Space) (v : X) : L2R :=
  toLpOrZero 2 (fun x => ∑ j : Fin 3, (φ x j • (partialX j v : Space → Space) x +
    (velocity v : Space → Space) x j • partialField φ j x))

def BilinTestFormula : Prop :=
  ∀ φ, IsTestField φ → ∀ τ, 0 < τ → ∀ v : X,
    bilinX τ (embedX φ) v = -(1 / 2 : ℝ) • heatDivFree τ (advectTest φ v)

def VelocityInjective : Prop := ∀ x : X, (velocity x : Space → Space) =ᵐ[volume] 0 → x = 0

def VelocityRotate : Prop :=
  ∀ (R : Space ≃ₗᵢ[ℝ] Space) (x : X),
    (velocity (rotX R x) : Space → Space) =ᵐ[volume] pushForward R (velocity x : Space → Space)

def VelocityDilate : Prop :=
  ∀ μ, 0 < μ → ∀ x : X,
    (velocity (dilX μ x) : Space → Space) =ᵐ[volume] dilateField μ (velocity x : Space → Space)

end Breakdown.Freq
