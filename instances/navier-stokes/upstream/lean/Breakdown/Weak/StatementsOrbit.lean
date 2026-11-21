import Breakdown.Weak.StatementsTime
import Breakdown.Profile.Orbit

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

def GlobalRepresentative : Prop :=
  ∀ x : ℝ → X, (∀ a b : ℝ, a < b → ∃ c : ℝ → X, ContinuousOn c (Ioo a b) ∧
      ∀ᵐ σ ∂(volume.restrict (Ioo a b)), c σ = x σ) →
    ∃ w : ℝ → X, Continuous w ∧ ∀ᵐ σ, w σ = x σ

def TimeChangeNull : Prop :=
  ∀ (s₀ : ℝ) (p : ℝ → Prop),
    (∀ᵐ σ, p σ) ↔ ∀ᵐ t ∂(volume.restrict (Iio 1)), p (s₀ - Real.log (1 - t))

def PhysicalCurveMeasurable : Prop :=
  ∀ (s₀ : ℝ) (x : ℝ → X), AEStronglyMeasurable x volume →
    AEStronglyMeasurable (physicalCurve x s₀) (volume.restrict (Iio 1))

def WeakOrbitOfParts : Prop :=
  PairingVelocity → VelocityWeakGradient → ZeroGradientSix → GradientFreqTr → SliceEmbedding →
  AdvectionByParts → PairingDilate → TrilinearDilate → SliceMeasurable → ScaledTestField →
  SliceIntegrand → SimilarityIdentity → PhysicalIdentity → ConstOfWeakDeriv → GoodTimes →
  BilinIntegrable → VarConstInner → VarConstGood → ContinuousVarConst → MildFromGood →
  GlobalRepresentative → TimeChangeNull → PhysicalCurveMeasurable →
  WeakPeriodicSimilarityProfileExists →
    ∃ (w : ℝ → X) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space), realization.F.IsOrbit (realization.rot R) w P

end Breakdown.WeakProfile
