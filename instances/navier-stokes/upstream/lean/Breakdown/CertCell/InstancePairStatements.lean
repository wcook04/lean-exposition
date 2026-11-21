import Breakdown.CertCell.InstanceStatements
import Breakdown.CertCell.CellCalculusStatements
import Breakdown.CertCell.StatementDefs

open scoped ENNReal ComplexOrder
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace InstancePair

open Instance

structure IsPairEntry {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (S : Fin k → Finset (ℤ × ℤ)) : Prop where
  actuator_labels : ∀ i, ∀ ι ∈ S i, ι ∈ R.pairLabels ∧ -ι ∈ R.pairLabels
  pin_labels : ∀ i K, ∀ ι ∈ (D.pinValues i).labels K, ι ∈ R.pairLabels ∧ -ι ∈ R.pairLabels
  actuator_profile : ∀ K i ι, ∀ p ∈ (D.mesh.box K).rect, ∀ a b,
    R.pairProfile K (.inl i) ι p a b = CellCalculus.gradAt D.azimuthOrder ι (gradField (D.cert.actuator i)) a b p
  pin_profile : ∀ K i ι, ∀ p ∈ (D.mesh.box K).rect, ∀ a b,
    R.pairProfile K (.inr i) ι p a b = CellCalculus.gradAt D.azimuthOrder ι (D.cert.pin i) a b p

def ActuatorSupportInCells {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) : Prop :=
  ∀ i σ y, D.cert.actuator i σ y ≠ 0 → ∃ K, (Real.sqrt (y 0 ^ 2 + y 1 ^ 2), |y 2|) ∈ (D.mesh.box K).rect

def PairSharesFromExactProfiles : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (S : Fin k → Finset (ℤ × ℤ)) (jmax : ℕ) (e : ℝ),
    Bridge.IsModeClass D.cert.symmetries D.azimuthOrder →
    IsActuatorInstance D S jmax → (∀ i, ActuatorShapeFacts D.azimuthOrder (S i) (D.cert.actuator i)) →
    ActuatorSupportInCells D → IsPinInstance D → IsPairEntry D R S → 0 ≤ e →
    ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
      ∀ κ ζ : Fin k → ℝ,
        ∑ K, CellCalculus.pairShare D K R.pairLabels (R.pairProfile K) κ ζ G
          ≤ (∑ i, κ i * multiplierRight (D.pieces q) v G H (D.cert.actuator i)
              + 2 * ∑ i, ζ i * pinValue (D.cert.pin i) G) / (4 * Real.pi) + e * ∑ i, κ i ^ 2

def PairSharesFromSurrogateProfiles : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (S : Fin k → Finset (ℤ × ℤ)) (jmax : ℕ) (ePair : Fin D.mesh.count → ℝ) (e : ℝ),
    Bridge.IsModeClass D.cert.symmetries D.azimuthOrder →
    IsActuatorInstance D S jmax → (∀ i, ActuatorShapeFacts D.azimuthOrder (S i) (D.cert.actuator i)) →
    ActuatorSupportInCells D → IsPinInstance D → IsPairSurrogate D R S ePair → ∑ K, ePair K ≤ e →
    ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
      ∀ κ ζ : Fin k → ℝ,
        ∑ K, CellCalculus.pairShare D K R.pairLabels (R.pairProfile K) κ ζ G
          ≤ (∑ i, κ i * multiplierRight (D.pieces q) v G H (D.cert.actuator i)
              + 2 * ∑ i, ζ i * pinValue (D.cert.pin i) G) / (4 * Real.pi) + e * ∑ i, κ i ^ 2
            + ∑ K, CellCalculus.pairStrainSlack D K (R.pairSlackLabels K) (R.pairSlackWeight K) G

def ActuatorPairingByParts : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (S : Fin k → Finset (ℤ × ℤ)) (jmax : ℕ),
    IsActuatorInstance D S jmax → (∀ i, ActuatorShapeFacts D.azimuthOrder (S i) (D.cert.actuator i)) →
    ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g → ∀ i,
      multiplierRight (D.pieces q) v G H (D.cert.actuator i) =
        ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, matInner (G σ y) (gradField (D.cert.actuator i) σ y)

def ActuatorGradientModes : Prop :=
  ∀ (m : ℕ) (S : Finset (ℤ × ℤ)) (b : ℝ → Space → Space), 0 < m → ActuatorShapeFacts m S b →
    ∀ ξ : ℤ × ℤ, (∀ ι ∈ S, labelHarmonic m ι ≠ ξ ∧ labelHarmonic m ι ≠ -ξ) →
      ∀ᵐ p : ℝ × ℝ, p ∈ halfPlane → modeGrad ξ (gradField b) 0 (planePoint p) = 0

def HalfPlanePairing : Prop :=
  ∀ (m : ℕ) (Γ : Set Symmetry) (P : ℝ) (labels : Finset (ℤ × ℤ)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (B : ℝ → Space → (Space →L[ℝ] Space)) (cells : Set (ℝ × ℝ)),
    Bridge.IsModeClass Γ m → IsPerturbation Γ P v G H g →
    AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume → IsTimePeriodic B →
    periodLIntegral (fun σ y => matSq (B σ y)) < ⊤ →
    (∀ᵐ z : ℝ × Space, ∀ u : Space, B z.1 (flipPoint z.2) u = flipPoint (B z.1 z.2 (flipPoint u))) →
    (∀ ξ : ℤ × ℤ, (∀ ι ∈ labels, labelHarmonic m ι ≠ ξ) →
      ∀ᵐ p : ℝ × ℝ, p ∈ halfPlane → modeGrad ξ B 0 (planePoint p) = 0) →
    (∀ σ y, B σ y ≠ 0 → (Real.sqrt (y 0 ^ 2 + y 1 ^ 2), |y 2|) ∈ cells) →
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, matInner (G σ y) (B σ y) =
        4 * Real.pi * ∑ ι ∈ labels, (∫ p in cells ∩ halfPlane, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
          CellCalculus.gradAt m ι G a b p * starRingEnd ℂ (CellCalculus.gradAt m ι B a b p)).re

end InstancePair

end CertCell

end Breakdown
