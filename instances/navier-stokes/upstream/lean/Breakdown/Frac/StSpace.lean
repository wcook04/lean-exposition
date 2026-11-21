import Breakdown.Frac.StOperator
import Breakdown.Uniqueness.EnergyDefs

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

structure FracSolutionOn (α T : ℝ) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ) : Prop where
  smooth_velocity : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (Icc 0 T ×ˢ univ)
  smooth_pressure : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2) (Icc 0 T ×ˢ univ)
  momentum : ∀ t ∈ Ioo 0 T, ∀ x,
    deriv (fun τ => u τ x) t + advectionAt (u t) x + fractionalPowerAt α (u t) x = -gradientAt (p t) x
  incompressible : ∀ t ∈ Icc 0 T, ∀ x, divergenceAt (u t) x = 0

structure IsForcedSolutionOn (T : ℝ) (v : ℝ → Space → Space) (q : ℝ → Space → ℝ)
    (F : ℝ → Space → Space) : Prop where
  smooth_velocity : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (Icc 0 T ×ˢ univ)
  smooth_pressure : ContDiffOn ℝ ∞ (fun z : ℝ × Space => q z.1 z.2) (Icc 0 T ×ˢ univ)
  momentum : ∀ t ∈ Ioo 0 T, ∀ x,
    deriv (fun τ => v τ x) t + advectionAt (v t) x + F t x = -gradientAt (q t) x
  incompressible : ∀ t ∈ Icc 0 T, ∀ x, divergenceAt (v t) x = 0
  force_smooth : ∀ t ∈ Ioo 0 T, ContDiff ℝ ∞ (F t)
  force_div : ∀ t ∈ Ioo 0 T, ∀ x, divergenceAt (F t) x = 0
  force_weak : ∀ ϕ : Space → Space, ContDiff ℝ ∞ ϕ → HasCompactSupport ϕ →
    ContinuousOn (fun t => ∫ x, inner ℝ (F t x) (ϕ x)) (Icc 0 T)
  force_mollify : ∀ ϕ : Space → Space, ContDiff ℝ ∞ ϕ → HasCompactSupport ϕ → ∀ ε : ℝ, 0 < ε →
    ∃ ρ₀ : ℝ, ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ t ∈ Ioo 0 T, |∫ x, inner ℝ (F t x) (FundSol.mollify ρ ϕ x)| ≤ ε

def scalarSecondOrderRemainder (g : Space → ℝ) (x z : Space) : ℝ :=
  g (x + z) - g x - fderiv ℝ g x z - (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 g x ![z, z]

def scalarPowerAt (α : ℝ) (g : Space → ℝ) (x : Space) : ℝ :=
  (fractionalNormalizer α)⁻¹ * ∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) * scalarSecondOrderRemainder g x z

def fracDifferenceRHS (α r : ℝ) (u w : Space → Space) : ℝ :=
  -(∫ x, inner ℝ (w x) (fractionalPowerAt α (fun y => cutoffPow r y • w y) x))
    + (1 / 2) * (∫ x, ‖w x‖ ^ 2 * inner ℝ (u x + w x) (gradientAt (cutoffPow r) x))
    - (∫ x, cutoffPow r x * inner ℝ (w x) (fderiv ℝ u x (w x)))
    - (stressPairing w w (FundSol.potential (cutoffSource r w))
      + stressPairing u w (FundSol.potential (cutoffSource r w))
      + stressPairing w u (FundSol.potential (cutoffSource r w)))

def FracNoBoundedSolution (α : ℝ) (u₀ : Space → Space) : Prop :=
  ¬ ∃ (u : ℝ → Space → Space) (p : ℝ → Space → ℝ), IsFractionalSolution α 1 u₀ u p ∧
    ∃ C : ℝ, ∀ t ≥ 0, ∫⁻ x, ENNReal.ofReal (‖u t x‖ ^ 2) ≤ ENNReal.ofReal C

def FracRestrictStatement : Prop :=
  ∀ (α : ℝ) (u₀ : Space → Space) (u : ℝ → Space → Space) (p : ℝ → Space → ℝ),
    IsFractionalSolution α 1 u₀ u p → (∀ x, divergenceAt u₀ x = 0) → ∀ T : ℝ, FracSolutionOn α T u p

def FracScalingStatement : Prop :=
  ∀ α : ℝ, (∃ u₀ : Space → Space, ContDiff ℝ ∞ u₀ ∧ HasCompactSupport u₀ ∧
    (∀ x, divergenceAt u₀ x = 0) ∧ FracNoBoundedSolution α u₀) → FractionalBreakdownOnSpace α

def FracCompactDecayStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ ϕ : Space → Space, ContDiff ℝ ∞ ϕ → HasCompactSupport ϕ →
    Continuous (fractionalPowerAt α ϕ) ∧
    ∃ C : ℝ, ∀ x, ‖fractionalPowerAt α ϕ x‖ ≤ C * (1 + ‖x‖) ^ (-(3 + 2 * α))

def FracWeakSolenoidalStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ v : Space → Space, ContDiff ℝ ∞ v → MemLp v 2 volume →
    (∀ x, divergenceAt v x = 0) → ∀ ξ : Space → ℝ, ContDiff ℝ ∞ ξ → HasCompactSupport ξ →
    ∫ x, inner ℝ (fractionalPowerAt α v x) (gradientAt ξ x) = 0

def FracWeakContinuityStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ (T : ℝ) (v : ℝ → Space → Space),
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (Icc 0 T ×ˢ univ) → EnergyBoundedOn T v →
    ∀ ϕ : Space → Space, ContDiff ℝ ∞ ϕ → HasCompactSupport ϕ →
    ContinuousOn (fun t => ∫ x, inner ℝ (v t x) (fractionalPowerAt α ϕ x)) (Icc 0 T)

def FracMollifyPairingStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ ϕ : Space → Space, ContDiff ℝ ∞ ϕ → HasCompactSupport ϕ →
    ∀ A ε : ℝ, 0 < ε → ∃ ρ₀ : ℝ, ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ w : Space → Space, Continuous w →
      ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≤ ENNReal.ofReal A →
      |∫ x, inner ℝ (w x) (fractionalPowerAt α (FundSol.mollify ρ ϕ) x)| ≤ ε

def FracForcedStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ (T : ℝ) (v : ℝ → Space → Space) (q : ℝ → Space → ℝ),
    FracSolutionOn α T v q → EnergyBoundedOn T v →
    IsForcedSolutionOn T v q (fun t => fractionalPowerAt α (v t))

def ForcedScalarTraceSecondDerivStatement : Prop :=
  ∀ (T : ℝ) (v : ℝ → Space → Space) (q : ℝ → Space → ℝ) (F : ℝ → Space → Space),
    IsForcedSolutionOn T v q F → ∀ t ∈ Ioo 0 T, ∀ x,
    FundSol.scalarSumSecondPartials (q t) x = -∑ i, ∑ j, FundSol.secondPartial (fun y => v t y i * v t y j) i j x

def ForcedPressureMollifyStatement : Prop :=
  ∀ (T : ℝ) (v : ℝ → Space → Space) (q : ℝ → Space → ℝ) (F : ℝ → Space → Space),
    IsForcedSolutionOn T v q F → EnergyBoundedOn T v → ∀ t ∈ Ioo 0 T,
    ∀ ϕ : Space → Space, ContDiff ℝ ∞ ϕ → HasCompactSupport ϕ → ∀ ρ : ℝ, 0 < ρ →
    pressureDefect v q t (FundSol.mollify ρ ϕ) = pressureDefect v q t ϕ

def ForcedPressureContinuityStatement : Prop :=
  ∀ (T : ℝ) (v : ℝ → Space → Space) (q : ℝ → Space → ℝ) (F : ℝ → Space → Space),
    IsForcedSolutionOn T v q F → EnergyBoundedOn T v →
    ∀ ϕ : Space → Space, ContDiff ℝ ∞ ϕ → HasCompactSupport ϕ →
    ContinuousOn (fun t => pressureDefect v q t ϕ) (Icc 0 T)

def ForcedTimeIdentityStatement : Prop :=
  ∀ (T : ℝ) (v : ℝ → Space → Space) (q : ℝ → Space → ℝ) (F : ℝ → Space → Space),
    IsForcedSolutionOn T v q F → ∀ t ∈ Ioo 0 T,
    ∀ Φ : Space → Space, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
    (∫ x, inner ℝ (deriv (fun τ => v τ x) t) (Φ x)) + pressureDefect v q t Φ =
      -(∫ x, inner ℝ (F t x) (Φ x)) +
        (∫ x, ∑ i, ∑ j, v t x i * v t x j * fderiv ℝ Φ x (unitVector i) j) -
        stressPairing (v t) (v t) (FundSol.potential (divergenceAt Φ))

def ForcedPressureAverageStatement : Prop :=
  ∀ (T : ℝ) (v : ℝ → Space → Space) (q : ℝ → Space → ℝ) (F : ℝ → Space → Space),
    IsForcedSolutionOn T v q F → EnergyBoundedOn T v →
    ∀ ϕ : Space → Space, ContDiff ℝ ∞ ϕ → HasCompactSupport ϕ → ∀ t₁ t₂ : ℝ,
    0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
    Filter.Tendsto (fun ρ => ∫ t in t₁..t₂, pressureDefect v q t (FundSol.mollify ρ ϕ))
      Filter.atTop (nhds 0)

def ForcedPressureIdentityStatement : Prop :=
  ∀ (T : ℝ) (v : ℝ → Space → Space) (q : ℝ → Space → ℝ) (F : ℝ → Space → Space),
    IsForcedSolutionOn T v q F → EnergyBoundedOn T v → ∀ t ∈ Ioo 0 T,
    ∀ ϕ : Space → Space, ContDiff ℝ ∞ ϕ → HasCompactSupport ϕ → pressureDefect v q t ϕ = 0

def ForcedPressureDifferenceStatement : Prop :=
  ∀ (T : ℝ) (u v : ℝ → Space → Space) (p q : ℝ → Space → ℝ) (F G : ℝ → Space → Space),
    IsForcedSolutionOn T u p F → IsForcedSolutionOn T v q G → EnergyBoundedOn T u →
    EnergyBoundedOn T v → ∀ r : ℝ, 0 < r → ∀ t ∈ Ioo 0 T,
    (∫ x, inner ℝ (gradientAt (q t) x - gradientAt (p t) x) (cutoffPow r x • (v t x - u t x))) =
      stressPairing (v t - u t) (v t - u t) (FundSol.potential (cutoffSource r (v t - u t)))
      + stressPairing (u t) (v t - u t) (FundSol.potential (cutoffSource r (v t - u t)))
      + stressPairing (v t - u t) (u t) (FundSol.potential (cutoffSource r (v t - u t)))

def ForcedLocalEnergyStatement : Prop :=
  ∀ (T : ℝ) (u v : ℝ → Space → Space) (p q : ℝ → Space → ℝ) (F G : ℝ → Space → Space),
    IsForcedSolutionOn T u p F → IsForcedSolutionOn T v q G → ∀ r : ℝ, 0 < r →
    ContinuousOn (fun τ => cutoffEnergy r (v τ - u τ)) (Icc 0 T) ∧
    ∀ t ∈ Ioo 0 T, HasDerivAt (fun τ => cutoffEnergy r (v τ - u τ))
      (-(∫ x, cutoffPow r x * inner ℝ (v t x - u t x) (G t x - F t x))
        + (1 / 2) * (∫ x, ‖v t x - u t x‖ ^ 2 * inner ℝ (v t x) (gradientAt (cutoffPow r) x))
        - (∫ x, cutoffPow r x * inner ℝ (v t x - u t x) (fderiv ℝ (u t) x (v t x - u t x)))
        - (∫ x, inner ℝ (gradientAt (q t) x - gradientAt (p t) x)
            (cutoffPow r x • (v t x - u t x)))) t

def FracLocalizationStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ w : Space → Space, ContDiff ℝ ∞ w → MemLp w 2 volume →
    ∀ φ : Space → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    Integrable (fun z : Space × Space =>
      (φ z.1 - φ z.2) ^ 2 * ‖w z.1 - w z.2‖ ^ 2 * ‖z.1 - z.2‖ ^ (-(3 + 2 * α))) (volume.prod volume) ∧
    ∫ x, inner ℝ (w x) (fractionalPowerAt α (fun y => φ y ^ 2 • w y) x) =
      (∫ x, inner ℝ (φ x • w x) (fractionalPowerAt α (fun y => φ y • w y) x))
      + (1 / 2) * (∫ x, (scalarPowerAt α (fun y => φ y ^ 2) x - 2 * φ x * scalarPowerAt α φ x) *
          ‖w x‖ ^ 2)
      - (fractionalNormalizer α)⁻¹ / 4 * ∫ z : Space × Space,
          (φ z.1 - φ z.2) ^ 2 * ‖w z.1 - w z.2‖ ^ 2 * ‖z.1 - z.2‖ ^ (-(3 + 2 * α)) ∂(volume.prod volume)

def FracGradientBoundStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ W : Space → Space, ContDiff ℝ ∞ W → HasCompactSupport W →
    0 ≤ ∫ x, inner ℝ (W x) (fractionalPowerAt α W x) ∧
    (∫ x, ∑ i, ‖fderiv ℝ W x (unitVector i)‖ ^ 2) ≤
      (∫ x, ‖W x‖ ^ 2) + ∫ x, inner ℝ (W x) (fractionalPowerAt α W x)

def cutoffFracDissipation (α r : ℝ) (w : Space → Space) : ℝ :=
  ∫ x, inner ℝ (radialCutoff r x ^ 2 • w x) (fractionalPowerAt α (fun y => radialCutoff r y ^ 2 • w y) x)

def FracCutoffLowerBoundStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∃ r₀ C : ℝ, 1 ≤ r₀ ∧ ∀ w : Space → Space, ContDiff ℝ ∞ w →
    ∀ a : ℝ, 0 ≤ a → ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≤ ENNReal.ofReal (a ^ 2) → ∀ r : ℝ, r₀ ≤ r →
    (3 / 4) * cutoffFracDissipation α r w - C * a ^ 2 / r ^ 2 ≤
      ∫ x, inner ℝ (w x) (fractionalPowerAt α (fun y => cutoffPow r y • w y) x)

def FracSixthNormStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∃ S : ℝ, 0 ≤ S ∧ ∀ (A : ℝ) (w : Space → Space),
    IsFiniteEnergyField A w → ∀ r : ℝ, 1 ≤ r →
    cutoffSixthNorm r w ≤ S * (A + Real.sqrt (cutoffFracDissipation α r w))

def FracDifferenceStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∃ K r₀ : ℝ, 1 ≤ r₀ ∧ ∀ (A U₀ U₁ : ℝ) (u w : Space → Space),
    IsDifferenceData A U₀ U₁ u w → ∀ r : ℝ, r₀ ≤ r →
    fracDifferenceRHS α r u w ≤ 2 * U₁ * cutoffEnergy r w + K * (1 + U₀) * (A ^ 2 + A ^ 6) / r

def FracUniquenessStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (T : ℝ) (u v : ℝ → Space → Space) (p q : ℝ → Space → ℝ),
    FracSolutionOn α T u p → FracSolutionOn α T v q → EnergyBoundedOn T u → EnergyBoundedOn T v →
    GradientBoundedOn T u → u 0 = v 0 → ∀ t ∈ Icc 0 T, u t = v t

end Breakdown
