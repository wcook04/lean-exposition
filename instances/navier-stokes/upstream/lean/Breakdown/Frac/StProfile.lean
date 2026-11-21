import Breakdown.Frac.StRealize
import Breakdown.Frac.ScaledStatements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown

def axialRotationFormula (θ : ℝ) (y : Space) : Space :=
  EuclideanSpace.single 0 (Real.cos θ * y 0 - Real.sin θ * y 1) +
    EuclideanSpace.single 1 (Real.sin θ * y 0 + Real.cos θ * y 1) + EuclideanSpace.single 2 (y 2)

open Classical in
def axialRotation (θ : ℝ) : Space ≃ₗᵢ[ℝ] Space :=
  if h : ∃ E : Space ≃ₗᵢ[ℝ] Space, ∀ y, E y = axialRotationFormula θ y then h.choose
  else LinearIsometryEquiv.refl ℝ Space

def AxialRotationSpec : Prop :=
  (∀ θ y, axialRotation θ y = axialRotationFormula θ y) ∧
  axialRotation 0 = LinearIsometryEquiv.refl ℝ Space ∧
  (∀ θ θ' y, axialRotation (θ + θ') y = axialRotation θ (axialRotation θ' y)) ∧
  (∀ θ, (axialRotation θ).symm = axialRotation (-θ)) ∧
  (∀ y, Continuous (fun θ => axialRotation θ y)) ∧
  (∀ θ y, HasDerivAt (fun θ' => axialRotation θ' y) (axialTurn (axialRotation θ y)) θ)

structure IsRotatingProfile (α a ν : ℝ) (U : Space → Space) (P : Space → ℝ) : Prop where
  pos : 0 < ν
  smooth : ContDiff ℝ ∞ U
  smooth_pressure : ContDiff ℝ ∞ P
  smooth_power : ContDiff ℝ ∞ (fractionalPowerAt α U)
  residual : ∀ y, rotatingProfileResidual α a ν U P y = 0
  div : ∀ y, divergenceAt U y = 0
  nonzero : ∃ y, U y ≠ 0
  decay : ∀ j : ℕ, ∃ C : ℝ, ∀ y : Space,
    ‖iteratedFDeriv ℝ j U y‖ ≤ C * (1 + ‖y‖) ^ (-(2 * α - 1 + j)) ∧
    ‖iteratedFDeriv ℝ (j + 1) P y‖ ≤ C * (1 + ‖y‖) ^ (-(4 * α - 1 + j)) ∧
    ‖iteratedFDeriv ℝ j (fractionalPowerAt α U) y‖ ≤ C * (1 + ‖y‖) ^ (-(4 * α - 1 + j))

def ProfileExistsIff : Prop :=
  ∀ α : ℝ, RotatingFractionalProfileExists α ↔ ∃ U P a ν, IsRotatingProfile α a ν U P

def UnitViscosity : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a ν : ℝ) (U : Space → Space) (P : Space → ℝ),
    IsRotatingProfile α a ν U P →
    IsRotatingProfile α a 1 (fun y => ν ^ (-(1 / (2 * α))) • U (ν ^ (1 / (2 * α)) • y))
      (fun y => ν ^ (-(1 / α)) * P (ν ^ (1 / (2 * α)) • y))

def rotatingSlice (a : ℝ) (U : Space → Space) (s : ℝ) : Space → Space :=
  pushForward (axialRotation (-(a * s))) U

def selfSimilarField (α a : ℝ) (U : Space → Space) (s₀ t : ℝ) : Space → Space :=
  scaleField α ((1 - t)⁻¹) (rotatingSlice a U (s₀ - Real.log (1 - t)))

def selfSimilarPressure (α a : ℝ) (P : Space → ℝ) (s₀ t : ℝ) : Space → ℝ :=
  fun x => ((1 - t)⁻¹) ^ (2 - 1 / α) *
    P (axialRotation (a * (s₀ - Real.log (1 - t))) (((1 - t)⁻¹) ^ (1 / (2 * α)) • x))

def RotatingSliceDecay : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ),
    IsRotatingProfile α a 1 U P → ∀ s, IsDecayField (rotatingSlice a U s) ∧
      ∀ j ≤ 3, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ j (rotatingSlice a U s) y‖ ≤ C

def RotatingSliceContinuous : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ),
    IsRotatingProfile α a 1 U P → Continuous (fun s => Freq.embedX (rotatingSlice a U s))

def SelfSimilarMomentum : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ),
    IsRotatingProfile α a 1 U P → ∀ s₀ t : ℝ, t < 1 → ∀ x : Space,
      HasDerivAt (fun τ => selfSimilarField α a U s₀ τ x)
        (-fractionalPowerAt α (selfSimilarField α a U s₀ t) x
          - advectionAt (selfSimilarField α a U s₀ t) x
          - gradientAt (selfSimilarPressure α a P s₀ t) x) t

def SelfSimilarTimeBound : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ),
    IsRotatingProfile α a 1 U P → ∀ s₀ T : ℝ, T < 1 → ∃ K : ℝ,
      ∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T, ∀ x : Space,
        ‖selfSimilarField α a U s₀ t x - selfSimilarField α a U s₀ t' x‖ ≤
          K * |t - t'| * (1 + ‖x‖) ^ (-(4 * α - 1))

def SelfSimilarWeak : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ),
    IsRotatingProfile α a 1 U P → ∀ s₀ T : ℝ, 0 < T → T < 1 →
      Freq.FracIsWeakSolution α (selfSimilarField α a U s₀) 0 T

def ScaledDilateJointContinuous : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] (κ : ℝ)
    (F : ScaledMildFramework X κ), ContinuousOn (fun p : ℝ × X => F.D p.1 p.2) (Ioi 0 ×ˢ univ)

def ScaledFlowOfMild : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] (κ : ℝ)
    (F : ScaledMildFramework X κ) (w u : ℝ → X) (s₀ s : ℝ), s₀ < s →
    F.IsMildOnIcc u 0 (1 - exp (-(s - s₀))) →
    (∀ r ∈ Icc 0 (1 - exp (-(s - s₀))), u r = F.D (1 - r)⁻¹ (w (s₀ - Real.log (1 - r)))) →
      IntervalIntegrable (fun σ => F.Ks (s - σ) (w σ) (w σ)) volume s₀ s ∧
      w s = F.S (s - s₀) (w s₀) + ∫ σ in s₀..s, F.Ks (s - σ) (w σ) (w σ)

def FracProfileOrbit : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ),
    IsRotatingProfile α a 1 U P →
    ∀ F : ScaledMildFramework Freq.X (dilExponent α), F.G = Freq.fracHeatX α →
      F.K = Freq.fracBilinX α → F.D = Freq.fracDilX α → ∀ P' : ℝ, 0 < P' →
      F.IsOrbit (Freq.rotX (axialRotation (-(a * P')))) (fun s => Freq.embedX (rotatingSlice a U s)) P'

def FracMildBlowup : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → RotatingFractionalProfileExists α →
    ∃ (a : ℝ) (U : Space → Space) (P : Space → ℝ), IsRotatingProfile α a 1 U P ∧
    ∃ F : ScaledMildFramework Freq.X (dilExponent α),
      F.G = Freq.fracHeatX α ∧ F.K = Freq.fracBilinX α ∧ F.D = Freq.fracDilX α ∧
      ∀ ε : ℝ, 0 < ε → ∃ (φ : Space → Space) (u : ℝ → Freq.X),
        IsTestField φ ∧ u 0 = Freq.embedX φ ∧ ‖u 0 - Freq.embedX U‖ < ε ∧ F.IsMildOn u 0 1 ∧
        ∃ C κ' : ℝ, 0 < κ' ∧ ∀ t ∈ Ico (0 : ℝ) 1,
          ‖F.D (1 - t) (u t) - Freq.embedX (rotatingSlice a U (-Real.log (1 - t)))‖ ≤
            C * (1 - t) ^ κ'

end Breakdown
