import Breakdown.FracCert.StFree
import Breakdown.FracCert.StWeak
import Breakdown.Held.Statements

open scoped ContDiff ENNReal
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace FracCertData

variable {k N : ℕ} (d : FracCertData k N)

def fullField (α : ℝ) (p : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space) (κ : Fin k → ℝ) (y : Space) : Space :=
  d.localField α p v G H κ y + d.splitField P H y

structure IsLinearState (α : ℝ) (p : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space) : Prop where
  second : IsSecondOrderField d.order v G H
  power : IsWeakFractionalPower α v P
  drift : MemLp (driftField α (d.rotationRate p) v G) 2 volume

structure IsHeldSolution (α : ℝ) (p : Fin k → ℝ) (u : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space) (κ : Fin k → ℝ) : Prop where
  state : d.IsLinearState α p u G H P
  equation : ∃ Q : Space → Space, IsGradientField Q ∧
    ∀ᵐ y ∂volume, d.fullField α p u G H P κ y + G y (u y) + d.defect α p y + Q y = 0
  pins : ∀ i, d.pins G i = 0

def heldMultiplier (p : Fin k → ℝ) (κ : Fin k → ℝ) : Fin k → ℝ := fun i => d.multiplier p i + κ i

end FracCertData

def AprioriBoundStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ p ∈ box d.radius, ∀ v G H P, d.IsLinearState α p v G H P → ∀ κ : Fin k → ℝ,
      d.size G H κ ≤ d.boundFn (projectedNorm (d.fullField α p v G H P κ))
        (Real.sqrt (d.rowsModGrad (d.fullField α p v G H P κ) ^ 2 + d.pinWeight * vecNorm (d.pins G) ^ 2)) 0

def LinearSolveStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ p ∈ box d.radius, ∀ F : Space → Space, MemLp F 2 volume → IsClassField d.order F →
    ∀ z : Fin k → ℝ, ∃ v G H P, ∃ κ : Fin k → ℝ, d.IsLinearState α p v G H P ∧
      (∃ Q : Space → Space, IsGradientField Q ∧ ∀ᵐ y ∂volume, d.fullField α p v G H P κ y = F y + Q y) ∧
      ∀ i, d.pins G i = z i

def HeldExistsStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ p ∈ box d.radius, ∃ u G H P, ∃ κ : Fin k → ℝ, d.IsHeldSolution α p u G H P κ ∧
      d.size G H κ ≤ d.heldRadius

def HeldUniqueStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ p ∈ box d.radius, ∀ u G H P κ u' G' H' P' κ', d.IsHeldSolution α p u G H P κ →
      d.IsHeldSolution α p u' G' H' P' κ' →
      (Real.sqrt (d.energy G H) + Real.sqrt (d.energy G' H')) * (d.rowConst * d.productConst) < 1 →
      (∀ᵐ y ∂volume, u y = u' y) ∧ κ = κ'

def HeldMultiplierContinuousStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∃ Φ : (Fin k → ℝ) → Fin k → ℝ, ContinuousOn Φ (box d.radius) ∧ ∀ p ∈ box d.radius,
      ∃ u G H P, d.IsHeldSolution α p u G H P (fun i => Φ p i - d.multiplier p i) ∧
        d.size G H (fun i => Φ p i - d.multiplier p i) ≤ d.heldRadius

def ActiveEnclosureStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ p ∈ d.testBox, ∀ u G H P κ, d.IsHeldSolution α p u G H P κ → d.size G H κ ≤ d.heldRadius →
      ∀ j ∈ d.activeSet, |(d.frameᵀ *ᵥ d.heldMultiplier p κ) j - d.slope j * p j| ≤ |d.slope j| * d.radius j

def StiffEnclosureStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ p ∈ d.testBox, ∀ u G H P κ, d.IsHeldSolution α p u G H P κ → d.size G H κ ≤ d.heldRadius →
      ∑ j ∈ d.activeSetᶜ, ((d.frameᵀ *ᵥ d.heldMultiplier p κ) j - d.slope j * p j) ^ 2 ≤ d.ellipsoidRadius ^ 2

def TestBoxSubsetStatement : Prop :=
  ∀ α : ℝ, ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d → d.testBox ⊆ box d.radius

def HeldZeroStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∃ p ∈ box d.radius, ∃ u G H P, ∃ κ : Fin k → ℝ, d.IsHeldSolution α p u G H P κ ∧
      d.size G H κ ≤ d.heldRadius ∧ d.heldMultiplier p κ = 0

def HeldNonzeroStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ p ∈ box d.radius, ∀ u G H P κ, d.IsHeldSolution α p u G H P κ → d.size G H κ ≤ d.heldRadius →
      ¬ (∀ᵐ y ∂volume, d.profile p y + u y = 0)

def HeldWeakProfileStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ p ∈ box d.radius, ∀ u G H P κ, d.IsHeldSolution α p u G H P κ → d.size G H κ ≤ d.heldRadius →
      d.heldMultiplier p κ = 0 → FracCert.WeakRotatingProfileExists α

def CertificateWeakProfileStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → FracCertificateHypothesis α → FracCert.WeakRotatingProfileExists α

end SteadyCert

end Breakdown
