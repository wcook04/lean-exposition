import Breakdown.CertTorus.KernelStatements
import Breakdown.Uniqueness.FundSolDefs

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

def tensorShift (F : ℝ → Space → Fin 3 → Fin 3 → ℝ) (s τ : ℝ) : Space → Fin 3 → Fin 3 → ℝ :=
  fun z => F (s - Real.log (1 + τ)) ((Real.sqrt (1 + τ))⁻¹ • z)

def profileOp (β : ℝ) (F : ℝ → Space → Fin 3 → Fin 3 → ℝ) (s : ℝ) (y : Space) : Space :=
  -∫ τ in Ioi (0 : ℝ), (1 + τ) ^ (-β) • kernelConv τ (tensorShift F s τ) y

def pairTensor (a b : ℝ → Space → Space) : ℝ → Space → Fin 3 → Fin 3 → ℝ :=
  fun s => tensorField (a s) (b s)

def directionalTensor (F : ℝ → Space → Fin 3 → Fin 3 → ℝ) (v : Space) :
    ℝ → Space → Fin 3 → Fin 3 → ℝ :=
  fun s z => fderiv ℝ (F s) z v

def IsBoundedMeasurableTensor (F : ℝ → Space → Fin 3 → Fin 3 → ℝ) : Prop :=
  Measurable (fun p : ℝ × Space => F p.1 p.2) ∧ ∃ C : ℝ, ∀ s z, ‖F s z‖ ≤ C

def kernelWeightIntegral (γ τ : ℝ) (y : Space) : ℝ :=
  ∫ z, ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ)

def farMajorant (γ τ R : ℝ) : ℝ :=
  (Real.sqrt τ)⁻¹ * min 1 ((Real.sqrt (1 + τ) / R) ^ γ)

def nearMajorant (γ τ R : ℝ) : ℝ :=
  R ^ 3 / (R + Real.sqrt τ) ^ 4 * min 1 ((Real.sqrt (1 + τ) / R) ^ min γ 3)

def pressureSource (W : ℝ → Space → Space) (s : ℝ) (y : Space) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    fderiv ℝ (W s) y (unitVector i) j * fderiv ℝ (W s) y (unitVector j) i

def divDivSource (f : Space → Fin 3 → Fin 3 → ℝ) (z : Space) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, iteratedFDeriv ℝ 2 (fun x => f x i j) z ![unitVector i, unitVector j]

def newtonGradientComp (g : Space → ℝ) (i : Fin 3) (y : Space) : ℝ :=
  ∫ z, FundSol.kernelGrad (y - z) i * g z

def ballCutoff (ρ : ℝ) (z : Space) : ℝ :=
  Real.smoothTransition (2 - ‖z‖ ^ 2 / ρ ^ 2)

def nearCutoff (y z : Space) : ℝ :=
  Real.smoothTransition (2 - 8 * ‖z - y‖ ^ 2 / (max 1 ‖y‖) ^ 2)

def KernelMassBound : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ y : Space,
    Integrable (fun z : Space => ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹) ∧
      ∫ z, ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ ≤ 5 * (Real.sqrt τ)⁻¹

def RadialWeightBound : Prop :=
  ∀ γ : ℝ, 0 ≤ γ → γ ≠ 3 → ∃ C : ℝ, ∀ a r : ℝ, 0 < a → 0 < r →
    ∫ z in Metric.ball (0 : Space) r, (1 + ‖z‖ / a) ^ (-γ) ≤ C * r ^ 3 * min 1 ((a / r) ^ min γ 3)

def InnerSplitBound : Prop :=
  ∀ γ : ℝ, 0 ≤ γ → γ ≠ 3 → ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → ∀ y : Space,
    Integrable (fun z : Space =>
      ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ)) ∧
    kernelWeightIntegral γ τ y ≤ C * (Real.sqrt τ)⁻¹ ∧
    (1 ≤ ‖y‖ → kernelWeightIntegral γ τ y ≤ C * (farMajorant γ τ ‖y‖ + nearMajorant γ τ ‖y‖))

def OuterFarBound : Prop :=
  ∀ n : ℕ, n ≤ 2 → ∀ γ : ℝ, 0 ≤ γ → γ ≠ (n : ℝ) + 1 → ∃ K : ℝ, ∀ R : ℝ, 1 ≤ R →
    IntegrableOn (fun τ => (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * farMajorant γ τ R) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * farMajorant γ τ R
      ≤ K * R ^ (-min γ ((n : ℝ) + 1))

def OuterNearBound : Prop :=
  ∀ n : ℕ, n ≤ 2 → ∀ γ : ℝ, 0 ≤ γ → ∃ K : ℝ, ∀ R : ℝ, 1 ≤ R →
    IntegrableOn (fun τ => (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * nearMajorant γ τ R) (Ioi 0) ∧
    ∫ τ in Ioi (0 : ℝ), (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * nearMajorant γ τ R
      ≤ K * R ^ (-min γ ((n : ℝ) + 1))

def SmallTimeIntegrable : Prop :=
  ∀ n : ℕ, IntegrableOn (fun τ : ℝ => (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * (Real.sqrt τ)⁻¹) (Ioi 0)

def OpWeightedBound : Prop :=
  LerayKernelBound → ∀ n : ℕ, n ≤ 2 → ∀ γ : ℝ, 0 ≤ γ → γ ≠ 3 → γ ≠ (n : ℝ) + 1 →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : ℝ → Space → Fin 3 → Fin 3 → ℝ) (A : ℝ), WeightedBound F γ A →
      WeightedBound (profileOp (1 + (n : ℝ) / 2) F) (min γ ((n : ℝ) + 1)) (K * A)

def OpLinear : Prop :=
  LerayKernelBound →
    (∀ β : ℝ, 1 ≤ β → ∀ F G : ℝ → Space → Fin 3 → Fin 3 → ℝ,
      IsBoundedMeasurableTensor F → IsBoundedMeasurableTensor G →
        ∀ s y, profileOp β (F + G) s y = profileOp β F s y + profileOp β G s y) ∧
    ∀ (β c : ℝ) (F : ℝ → Space → Fin 3 → Fin 3 → ℝ) (s : ℝ) (y : Space),
      profileOp β (c • F) s y = c • profileOp β F s y

def OpMeasurable : Prop :=
  ∀ (β : ℝ) (F : ℝ → Space → Fin 3 → Fin 3 → ℝ), Measurable (fun p : ℝ × Space => F p.1 p.2) →
    Measurable (fun p : ℝ × Space => profileOp β F p.1 p.2)

def TensorWeight : Prop :=
  ∀ (a b : ℝ → Space → Space) (γ γ' A B : ℝ), 0 ≤ γ → 0 ≤ γ' →
    WeightedBound a γ A → WeightedBound b γ' B → WeightedBound (pairTensor a b) (γ + γ') (A * B)

def NeumannDecay : Prop :=
  LerayKernelBound → ∀ W : ℝ → Space → Space, Measurable (fun p : ℝ × Space => W p.1 p.2) →
    (∃ C : ℝ, ∀ s y, ‖W s y‖ ≤ C) → TailVanishes W →
      (∀ s y, W s y = profileOp 1 (pairTensor W W) s y) → ∃ A : ℝ, WeightedBound W (3 / 4) A

def KernelConvDeriv : Prop :=
  LerayKernelBound → ∀ τ : ℝ, 0 < τ → ∀ (G : Space → Fin 3 → Fin 3 → ℝ) (A : ℝ), ContDiff ℝ 1 G →
    (∀ z, ‖G z‖ ≤ A) → (∀ z, ‖fderiv ℝ G z‖ ≤ A) → ∀ y,
      DifferentiableAt ℝ (kernelConv τ G) y ∧
        ∀ v, fderiv ℝ (kernelConv τ G) y v = kernelConv τ (fun z => fderiv ℝ G z v) y

def ProfileOpDeriv : Prop :=
  LerayKernelBound → ∀ β : ℝ, 1 ≤ β → ∀ (F : ℝ → Space → Fin 3 → Fin 3 → ℝ) (A : ℝ),
    ContDiff ℝ 1 (fun p : ℝ × Space => F p.1 p.2) → (∀ s z, ‖F s z‖ ≤ A) →
      (∀ s z, ‖fderiv ℝ (F s) z‖ ≤ A) → ∀ s y,
        DifferentiableAt ℝ (profileOp β F s) y ∧
          ∀ v, fderiv ℝ (profileOp β F s) y v = profileOp (β + 1 / 2) (directionalTensor F v) s y

def DerivRepresentation : Prop :=
  LerayKernelBound → ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space),
    IsRegularOrbitField W q P R → ∀ s y v,
      fderiv ℝ (W s) y v = profileOp (3 / 2) (directionalTensor (pairTensor W W) v) s y ∧
        ∀ w, iteratedFDeriv ℝ 2 (W s) y ![w, v] =
          profileOp 2 (directionalTensor (directionalTensor (pairTensor W W) v) w) s y

def FirstDerivBootstrap : Prop :=
  LerayKernelBound → ∀ W : ℝ → Space → Space, ContDiff ℝ ∞ (fun p : ℝ × Space => W p.1 p.2) →
    (∃ C : ℝ, UniformDerivBound W 2 C) → (∃ A : ℝ, WeightedBound W 1 A) →
      (∀ s y v, fderiv ℝ (W s) y v = profileOp (3 / 2) (directionalTensor (pairTensor W W) v) s y) →
        ∃ B : ℝ, WeightedBound (fun s y => fderiv ℝ (W s) y) 2 B

def SecondDerivBootstrap : Prop :=
  LerayKernelBound → ∀ W : ℝ → Space → Space, ContDiff ℝ ∞ (fun p : ℝ × Space => W p.1 p.2) →
    (∃ C : ℝ, UniformDerivBound W 2 C) → (∃ A : ℝ, WeightedBound W 1 A) →
      (∃ B : ℝ, WeightedBound (fun s y => fderiv ℝ (W s) y) 2 B) →
        (∀ s y v w, iteratedFDeriv ℝ 2 (W s) y ![w, v] =
          profileOp 2 (directionalTensor (directionalTensor (pairTensor W W) v) w) s y) →
          ∃ B : ℝ, WeightedBound (fun s y => iteratedFDeriv ℝ 2 (W s) y) 3 B

def PressureSumSecondPartials : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space),
    IsSmoothOrbitField W q P R → ∀ s y, FundSol.scalarSumSecondPartials (q s) y = -pressureSource W s y

def PressureSourceDivDiv : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space),
    IsSmoothOrbitField W q P R → ∀ s z, pressureSource W s z = divDivSource (pairTensor W W s) z

def PressureSourceBound : Prop :=
  ∀ W : ℝ → Space → Space, ContDiff ℝ ∞ (fun p : ℝ × Space => W p.1 p.2) →
    ∀ A : ℝ, WeightedBound (fun s y => fderiv ℝ (W s) y) 2 A →
      ∃ C : ℝ, ∀ s, ContDiff ℝ ∞ (pressureSource W s) ∧
        ∀ z, |pressureSource W s z| ≤ C / (1 + ‖z‖) ^ 4

def TensorDerivDecay : Prop :=
  ∀ W : ℝ → Space → Space, ContDiff ℝ ∞ (fun p : ℝ × Space => W p.1 p.2) →
    ∀ A₀ A₁ A₂ : ℝ, WeightedBound W 1 A₀ → WeightedBound (fun s y => fderiv ℝ (W s) y) 2 A₁ →
      WeightedBound (fun s y => iteratedFDeriv ℝ 2 (W s) y) 3 A₂ →
        ∃ A : ℝ, ∀ s, ContDiff ℝ 2 (pairTensor W W s) ∧
          ∀ m ≤ 2, ∀ z, ‖iteratedFDeriv ℝ m (pairTensor W W s) z‖ ≤ A / (1 + ‖z‖) ^ (2 + m)

def HarmonicMeanValue : Prop :=
  ∀ (g : Space → ℝ) (y : Space) (r : ℝ), 0 < r → ContDiff ℝ ∞ g →
    (∀ x ∈ Metric.ball y r, FundSol.scalarSumSecondPartials g x = 0) →
      ∀ ρ : ℝ, 0 < ρ → ρ < r → g y = ∫ z, FundSol.mollifier ρ (y - z) * g z

def HarmonicGradientBound : Prop :=
  ∃ C : ℝ, ∀ (g : Space → ℝ) (y : Space) (r : ℝ), 0 < r → ContDiff ℝ ∞ g →
    (∀ x ∈ Metric.ball y r, FundSol.scalarSumSecondPartials g x = 0) →
      ‖fderiv ℝ g y‖ ≤ C * r ^ (-(3 / 2 : ℝ)) *
        (∫ x in Metric.ball y r, ‖fderiv ℝ g x‖ ^ 2) ^ (1 / 2 : ℝ)

def TruncatedNewton : Prop :=
  ∀ (g : Space → ℝ) (A : ℝ), ContDiff ℝ ∞ g → (∀ z, |g z| ≤ A / (1 + ‖z‖) ^ 4) →
    (∃ C : ℝ, ∀ ρ : ℝ, 1 ≤ ρ → ∀ y,
      ‖fderiv ℝ (FundSol.potential (fun z => ballCutoff ρ z * g z)) y‖ ≤ C / (1 + ‖y‖) ^ 2) ∧
    ∀ (i : Fin 3) (y : Space),
      Tendsto (fun ρ : ℝ => fderiv ℝ (FundSol.potential (fun z => ballCutoff ρ z * g z)) y (unitVector i))
        atTop (𝓝 (newtonGradientComp g i y))

def PressureIdentification : Prop :=
  ∀ (q g : Space → ℝ) (A : ℝ), ContDiff ℝ ∞ q → ContDiff ℝ ∞ g →
    (∀ y, FundSol.scalarSumSecondPartials q y = -g y) → MemLp (fun y => fderiv ℝ q y) 2 volume →
      (∀ z, |g z| ≤ A / (1 + ‖z‖) ^ 4) →
        ∀ (i : Fin 3) (y : Space), fderiv ℝ q y (unitVector i) = -newtonGradientComp g i y

def NewtonNear : Prop :=
  ∃ C : ℝ, ∀ (g : Space → ℝ) (A : ℝ), Continuous g → (∀ z, |g z| ≤ A / (1 + ‖z‖) ^ 4) →
    ∀ (i : Fin 3) (y : Space),
      Integrable (fun z => FundSol.kernelGrad (y - z) i * (nearCutoff y z * g z)) ∧
        |∫ z, FundSol.kernelGrad (y - z) i * (nearCutoff y z * g z)| ≤ C * A / (1 + ‖y‖) ^ 3

def NewtonFar : Prop :=
  ∃ C : ℝ, ∀ (f : Space → Fin 3 → Fin 3 → ℝ) (A : ℝ), ContDiff ℝ 2 f →
    (∀ m ≤ 2, ∀ z, ‖iteratedFDeriv ℝ m f z‖ ≤ A / (1 + ‖z‖) ^ (2 + m)) →
      ∀ (i : Fin 3) (y : Space),
        Integrable (fun z => FundSol.kernelGrad (y - z) i * ((1 - nearCutoff y z) * divDivSource f z)) ∧
          |∫ z, FundSol.kernelGrad (y - z) i * ((1 - nearCutoff y z) * divDivSource f z)|
            ≤ C * A / (1 + ‖y‖) ^ 3

def farWeight (i : Fin 3) (y z : Space) : ℝ :=
  FundSol.kernelGrad (y - z) i * (1 - nearCutoff y z)

def NewtonFarIdentity : Prop :=
  ∀ (f : Space → Fin 3 → Fin 3 → ℝ) (A : ℝ), ContDiff ℝ 2 f →
    (∀ m ≤ 2, ∀ z, ‖iteratedFDeriv ℝ m f z‖ ≤ A / (1 + ‖z‖) ^ (2 + m)) →
      ∀ (i : Fin 3) (y : Space),
        Integrable (fun z => farWeight i y z * divDivSource f z) ∧
          ∫ z, farWeight i y z * divDivSource f z =
            ∫ z, ∑ a : Fin 3, ∑ b : Fin 3,
              iteratedFDeriv ℝ 2 (farWeight i y) z ![unitVector a, unitVector b] * f z a b

def NewtonFarEstimate : Prop :=
  ∃ C : ℝ, ∀ (f : Space → Fin 3 → Fin 3 → ℝ) (A : ℝ), Continuous f →
    (∀ z, ‖f z‖ ≤ A / (1 + ‖z‖) ^ 2) → ∀ (i : Fin 3) (y : Space),
      |∫ z, ∑ a : Fin 3, ∑ b : Fin 3,
          iteratedFDeriv ℝ 2 (farWeight i y) z ![unitVector a, unitVector b] * f z a b|
        ≤ C * A / (1 + ‖y‖) ^ 3

def ClassFormOfWeights : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ),
    (∃ A : ℝ, WeightedBound W 1 A) → (∃ A : ℝ, WeightedBound (fun s y => fderiv ℝ (W s) y) 2 A) →
      (∃ A : ℝ, WeightedBound (fun s y => iteratedFDeriv ℝ 2 (W s) y) 3 A) →
        (∃ A : ℝ, ∀ s y (i : Fin 3), |fderiv ℝ (q s) y (unitVector i)| ≤ A / (1 + ‖y‖) ^ 3) →
          ∃ C : ℝ, DecayBounds W q C

theorem profileBilin_eq_profileOp (a b : ℝ → Space → Space) (s : ℝ) (y : Space) :
    profileBilin a b s y = profileOp 1 (pairTensor a b) s y := by
  unfold profileBilin profileOp
  congr 2
  funext τ
  rw [Real.rpow_neg_one]
  rfl

end Breakdown.FarField
