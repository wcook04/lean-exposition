import Breakdown.Base.Realization

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

def DecayFieldSub : Prop :=
  ∀ f g : Space → Space, IsDecayField f → IsDecayField g → IsDecayField (f - g)

def DecayFieldDilate : Prop :=
  ∀ (μ : ℝ) (f : Space → Space), 0 < μ → IsDecayField f → IsDecayField (dilateField μ f)

def DilateCalculus : Prop :=
  ∀ (μ : ℝ) (f : Space → Space), ContDiff ℝ ∞ f → ∀ x : Space,
    fderiv ℝ (dilateField μ f) x = (Real.sqrt μ ^ 2) • fderiv ℝ f (Real.sqrt μ • x) ∧
    sumSecondPartialsAt (dilateField μ f) x = (Real.sqrt μ ^ 3) • sumSecondPartialsAt f (Real.sqrt μ • x) ∧
    advectionAt (dilateField μ f) x = (Real.sqrt μ ^ 3) • advectionAt f (Real.sqrt μ • x)

def GradientScale : Prop :=
  ∀ (c : ℝ) (g : Space → ℝ), ContDiff ℝ ∞ g → ∀ x : Space,
    gradientAt (fun y => g (c • y)) x = c • gradientAt g (c • x)

def SumSecondPartialsPairing : Prop :=
  ∀ f φ : Space → Space, ContDiff ℝ ∞ f → IsTestField φ →
    ∫ x, inner ℝ (sumSecondPartialsAt f x) (φ x) = -gradientPairing f φ

def GradientPairingZero : Prop :=
  ∀ (g : Space → ℝ) (φ : Space → Space), ContDiff ℝ ∞ g → IsTestField φ →
    ∫ x, inner ℝ (gradientAt g x) (φ x) = 0

end Breakdown
