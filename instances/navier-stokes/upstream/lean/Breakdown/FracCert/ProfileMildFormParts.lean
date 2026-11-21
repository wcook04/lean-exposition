import Breakdown.FracCert.StMildProfile
import Breakdown.FracCert.WeakNiceDrift

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq

def orbitPairing (α a : ℝ) (x : X) (φ : Space → Space) (τ : ℝ) : ℝ :=
  ∫ y, inner ℝ ((velocity x : Space → Space) y)
    (heatField α (1 - Real.exp (-τ)) (simAdj α a (Real.exp τ) φ) y)

def orbitGenerator (α a : ℝ) (x : X) (φ : Space → Space) (τ : ℝ) : ℝ :=
  -(∫ y, inner ℝ ((velocity x : Space → Space) y)
      (driftAdjoint α a (heatField α (1 - Real.exp (-τ)) (simAdj α a (Real.exp τ) φ)) y)) -
    ∫ y, inner ℝ ((velocity x : Space → Space) y)
      (fractionalPowerAt α (heatField α (1 - Real.exp (-τ)) (simAdj α a (Real.exp τ) φ)) y)

def OrbitPairingDerivStatement : Prop :=
  ∀ α a : ℝ, 1 < α → α < 5 / 4 → ∀ (x : X) (φ : Space → Space), IsNiceField φ →
    ∀ τ : ℝ, 0 ≤ τ → HasDerivAt (orbitPairing α a x φ) (orbitGenerator α a x φ τ) τ

def OrbitGeneratorIntegrableStatement : Prop :=
  ∀ α a : ℝ, 1 < α → α < 5 / 4 → ∀ (x : X) (φ : Space → Space), IsNiceField φ →
    IntegrableOn (orbitGenerator α a x φ) (Ioi 0)

def OrbitPairingLimitStatement : Prop :=
  ∀ α a : ℝ, 1 < α → α < 5 / 4 → ∀ (x : X) (φ : Space → Space), IsNiceField φ →
    Tendsto (orbitPairing α a x φ) atTop (𝓝 0)


def orbitSymbol (α a : ℝ) (m : Space → CSpace) (τ : ℝ) (ξ : Space) : CSpace :=
  Real.exp (-((1 - Real.exp (-τ)) * (2 * π * ‖ξ‖) ^ (2 * α))) •
    rotC (axialRotation (-(a * τ)))
      ((Real.exp τ ^ (4 * (1 / (2 * α)) - 1) * (Real.exp τ ^ (1 / (2 * α)))⁻¹ ^ 3) •
        m ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ))

def symbolPairing (f n : Space → CSpace) : ℝ :=
  ∫ ξ, inner ℝ (f ξ) (((2 * π * ‖ξ‖)⁻¹ : ℝ) • n ξ)

def orbitSymbolGenerator (α a : ℝ) (f m : Space → CSpace) (τ : ℝ) : ℝ :=
  -symbolPairing f (Breakdown.FracInternal.NiceDrift.driftSym α a (orbitSymbol α a m τ)) -
    symbolPairing f (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • orbitSymbol α a m τ ξ)

def OrbitSymbolDerivStatement : Prop :=
  ∀ α a : ℝ, 1 < α → α < 5 / 4 → ∀ f : Space → CSpace, MemLp f 2 volume →
    ∀ m : Space → CSpace, IsNiceSymbol m → ∀ τ : ℝ, 0 ≤ τ →
      HasDerivAt (fun s => symbolPairing f (orbitSymbol α a m s)) (orbitSymbolGenerator α a f m τ) τ

def OrbitSymbolIntegrableStatement : Prop :=
  ∀ α a : ℝ, 1 < α → α < 5 / 4 → ∀ f : Space → CSpace, MemLp f 2 volume →
    ∀ m : Space → CSpace, IsNiceSymbol m → IntegrableOn (orbitSymbolGenerator α a f m) (Ioi 0)

def OrbitSymbolLimitStatement : Prop :=
  ∀ α a : ℝ, 1 < α → α < 5 / 4 → ∀ f : Space → CSpace, MemLp f 2 volume →
    ∀ m : Space → CSpace, IsNiceSymbol m →
      Tendsto (fun s => symbolPairing f (orbitSymbol α a m s)) atTop (𝓝 0)

def OrbitSymbolBoundStatement : Prop :=
  ∀ α a : ℝ, 1 < α → α < 5 / 4 → ∀ m : Space → CSpace, IsNiceSymbol m →
    ∃ B : ℝ → ℝ, IntegrableOn B (Ioi 0) ∧
      (∀ τ₀ : ℝ, 0 ≤ τ₀ → ∃ ε > 0, ∃ C : ℝ, ∀ s ∈ Metric.ball τ₀ ε, B s ≤ C) ∧
      ∀ s : ℝ, -1 < s → ∀ ξ : Space,
        ‖((2 * π * ‖ξ‖)⁻¹ : ℝ) • Breakdown.FracInternal.NiceDrift.driftSym α a (orbitSymbol α a m s) ξ‖ ≤
            B s * ((1 + ‖ξ‖) ^ 2)⁻¹ ∧
          ‖((2 * π * ‖ξ‖)⁻¹ : ℝ) • (((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • orbitSymbol α a m s ξ)‖ ≤
            B s * ((1 + ‖ξ‖) ^ 2)⁻¹ ∧
          ‖((2 * π * ‖ξ‖)⁻¹ : ℝ) • orbitSymbol α a m s ξ‖ ≤ B s * ((1 + ‖ξ‖) ^ 2)⁻¹

def OrbitScalarBoundStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ r R : ℝ, 0 < r → r ≤ R →
    ∃ B : ℝ → ℝ, IntegrableOn B (Ioi 0) ∧
      (∀ τ₀ : ℝ, 0 ≤ τ₀ → ∃ ε > 0, ∃ C : ℝ, ∀ s ∈ Metric.ball τ₀ ε, B s ≤ C) ∧
      ∀ s : ℝ, -1 < s → ∀ ρ : ℝ, r * Real.exp s ^ (1 / (2 * α)) ≤ ρ → ρ ≤ R * Real.exp s ^ (1 / (2 * α)) →
        (2 * π * ρ)⁻¹ * Real.exp (-((1 - Real.exp (-s)) * (2 * π * ρ) ^ (2 * α))) *
            (Real.exp s ^ (4 * (1 / (2 * α)) - 1) * (Real.exp s ^ (1 / (2 * α)))⁻¹ ^ 3) *
            (1 + 2 * (2 * π * ρ) ^ (2 * α)) * (1 + ρ) ^ 2 ≤ B s

end Breakdown.FracCert
