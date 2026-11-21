import Breakdown.FracCert.DriftPower

open scoped ContDiff ENNReal SchwartzMap FourierTransform
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

def DriftAdjointPhysicalStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    MemLp (driftField α a v G) 2 volume → ∀ ψ Φ : 𝓢(Space, Freq.CSpace),
    (∀ ξ, Φ ξ = flowAdjoint α a ψ ξ) →
    ∫ y, inner ℝ (driftField α a v G y) (Freq.realVec ((𝓕⁻ ψ) y)) =
      ∫ y, inner ℝ (v y) (Freq.realVec ((𝓕⁻ Φ) y))

def VelocitySecondPhysicalStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ Ψ Φ : 𝓢(Space, Freq.CSpace), (∀ ξ, Φ ξ = freqPow 2 ξ • Ψ ξ) →
    ∫ y, inner ℝ (v y) (Freq.realVec ((𝓕⁻ Φ) y)) =
      ∫ y, inner ℝ (negSecondTrace H y) (Freq.realVec ((𝓕⁻ Ψ) y))

def SecondTracePairingStatement : Prop :=
  ∀ (k : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField k v G H →
    ∀ φ : SchwartzMap Space Space,
    ∫ y, inner ℝ (v y) (Freq.negSsp φ y) = ∫ y, inner ℝ (negSecondTrace H y) (φ y)

def transportAdjoint (α a : ℝ) (χ : Space → Space) (y : Space) : Space :=
  (1 - 4 * (1 / (2 * α))) • χ y - (1 / (2 * α)) • fderiv ℝ χ y y - a • fderiv ℝ χ y (axialTurn y)
    + a • axialTurn (χ y)

def DriftTransportPairingStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    MemLp (driftField α a v G) 2 volume → ∀ χ : 𝓢(Space, Space),
    ∫ y, inner ℝ (driftField α a v G y) (χ y) = ∫ y, inner ℝ (v y) (transportAdjoint α a χ y)

def FlowAdjointInverseStatement : Prop :=
  ∀ (α a : ℝ) (ψ Φ : 𝓢(Space, Freq.CSpace)), (∀ ξ, Φ ξ = flowAdjoint α a ψ ξ) →
    ∀ y, Freq.realVec ((𝓕⁻ Φ) y) = transportAdjoint α a (fun x => Freq.realVec ((𝓕⁻ ψ) x)) y

def LinearTransportPairStatement : Prop :=
  ∀ (k : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField k v G H →
    ∀ (θ : 𝓢(Space, Space)) (W : Space →L[ℝ] Space),
    Integrable (fun y => inner ℝ (v y) (θ y)) ∧ Integrable (fun y => inner ℝ (G y (W y)) (θ y)) ∧
    Integrable (fun y => inner ℝ (v y) (fderiv ℝ θ y (W y)
      + (∑ j : Fin 3, inner ℝ (W (unitVector j)) (unitVector j)) • θ y)) ∧
    ∫ y, inner ℝ (G y (W y)) (θ y) = -∫ y, inner ℝ (v y) (fderiv ℝ θ y (W y)
      + (∑ j : Fin 3, inner ℝ (W (unitVector j)) (unitVector j)) • θ y)

end SteadyCert

end Breakdown
