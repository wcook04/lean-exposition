import Breakdown.Base.Realization

open scoped ContDiff ENNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown

instance factOneLeSixExponent : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩

structure IsSolutionOn (T : ℝ) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ) : Prop where
  smooth_velocity : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (Icc 0 T ×ˢ univ)
  smooth_pressure : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2) (Icc 0 T ×ˢ univ)
  momentum : ∀ t ∈ Ioo 0 T, ∀ x,
    deriv (fun τ => u τ x) t + advectionAt (u t) x = sumSecondPartialsAt (u t) x - gradientAt (p t) x
  incompressible : ∀ t ∈ Icc 0 T, ∀ x, divergenceAt (u t) x = 0

def EnergyBoundedOn (T : ℝ) (u : ℝ → Space → Space) : Prop :=
  ∃ A : ℝ, ∀ t ∈ Icc 0 T, ∫⁻ x, ENNReal.ofReal (‖u t x‖ ^ 2) ≤ ENNReal.ofReal A

def GradientBoundedOn (T : ℝ) (u : ℝ → Space → Space) : Prop :=
  ∃ B : ℝ, ∀ t ∈ Icc 0 T, ∀ x, ‖u t x‖ ≤ B ∧ ‖fderiv ℝ (u t) x‖ ≤ B

def HasBoundedEnergy (u : ℝ → Space → Space) : Prop :=
  ∃ C : ℝ, ∀ t ≥ 0, ∫⁻ x, ENNReal.ofReal (‖u t x‖ ^ 2) ≤ ENNReal.ofReal C

def NoBoundedSmoothSolution (ν : ℝ) (u₀ : Space → Space) : Prop :=
  ¬ ∃ (u : ℝ → Space → Space) (p : ℝ → Space → ℝ), IsSmoothSolution ν u₀ u p ∧ HasBoundedEnergy u

structure FieldReading {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (Rlz : Realization X) (vel : X →L[ℝ] Lp (α := Space) Space 6) : Prop where
  injective : ∀ x, (vel x : Space → Space) =ᵐ[volume] 0 → x = 0
  rot : ∀ R x, (vel (Rlz.rot R x) : Space → Space) =ᵐ[volume] pushForward R (vel x)
  dil : ∀ μ, 0 < μ → ∀ x, (vel (Rlz.F.D μ x) : Space → Space) =ᵐ[volume] dilateField μ (vel x)

def MildRegular {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (Rlz : Realization X) (vel : X →L[ℝ] Lp (α := Space) Space 6) : Prop :=
  ∀ φ, IsTestField φ → ∀ (u : ℝ → X) (T : ℝ), 0 < T → Rlz.F.IsMildOnIcc u 0 T → u 0 = Rlz.embed φ →
    ∃ (U : ℝ → Space → Space) (P : ℝ → Space → ℝ), IsSolutionOn T U P ∧ U 0 = φ ∧
      EnergyBoundedOn T U ∧ GradientBoundedOn T U ∧
      ∀ t ∈ Icc 0 T, (vel (u t) : Space → Space) =ᵐ[volume] U t

def radialCutoff (r : ℝ) (x : Space) : ℝ := Real.smoothTransition (2 - ‖x‖ / r)

end Breakdown
