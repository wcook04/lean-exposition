import Breakdown.CellReduction.PotentialShape

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect

def AxisAdmissible (M : ℤ) (withSine : Bool) (S : PotScalar) : Prop :=
  (M ≠ 0 → withSine = false → 1 ≤ S.axisPower ∨ AxisCellsVanish S.amp) ∧
    (withSine = true → |M| ≠ 1 → 1 ≤ S.axisPower ∨ AxisCellsVanish S.amp)

def ScalarSmoothAwayFromOrigin : Prop :=
  ∀ (P : ShapeParams) (κ : FieldKey) (M : ℤ) (withSine : Bool) (S : PotScalar) (σ : ℝ),
    IsShapeParams P → IsJetClass 1 1 S.amp → AxisAdmissible M withSine S →
    (∀ y : Space, y ≠ 0 → ContDiffAt ℝ 1 (scalarValue P κ M withSine S σ) y) ∧
    ∀ r R : ℝ, 0 < r → ∃ L : NNReal,
      LipschitzOnWith L (fderiv ℝ (scalarValue P κ M withSine S σ)) {y : Space | r ≤ ‖y‖ ∧ ‖y‖ ≤ R}

def ScalarSmoothNearOrigin : Prop :=
  ∀ (P : ShapeParams) (κ : FieldKey) (M : ℤ) (withSine : Bool) (S : PotScalar) (σ : ℝ),
    IsShapeParams P → IsJetClass 1 1 S.amp → AxisAdmissible M withSine S →
    (∃ z ≤ S.amp.tAxis.depth, 2 ≤ S.lowOrder + z ∧ StartVanishOrder S.amp z) →
    ContDiffAt ℝ 1 (scalarValue P κ M withSine S σ) 0 ∧
    ∃ δ > (0 : ℝ), ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (scalarValue P κ M withSine S σ)) (Metric.closedBall 0 δ)

def ScalarDecayOrder (h : ℕ) : Prop :=
  ∀ (P : ShapeParams) (κ : FieldKey) (M : ℤ) (withSine : Bool) (S : PotScalar),
    IsShapeParams P → IsPotentialScalar 2 h S → AxisAdmissible M withSine S → ∃ C : ℝ,
    (∀ σ y, ‖scalarValue P κ M withSine S σ y‖ ≤ C / (1 + ‖y‖) ^ h ∧
      ‖fderiv ℝ (scalarValue P κ M withSine S σ) y‖ ≤ C / (1 + ‖y‖) ^ (h + 1)) ∧
    ∀ σ, ∀ᵐ y, ‖fderiv ℝ (fun x => fderiv ℝ (scalarValue P κ M withSine S σ) x) y‖ ≤ C / (1 + ‖y‖) ^ (h + 2)

structure IsPotentialPick (h : ℕ) (F : PotentialSeries) (pick : PotKeyData → PotComponent → PotScalar) : Prop where
  scalar : ∀ κ ∈ F.keys, ∀ c, IsPotentialScalar 2 h (pick (F.data κ) c)
  axis : ∀ κ ∈ F.keys, κ.label.1 ≠ 0 → ∀ c,
    1 ≤ (pick (F.data κ) c).axisPower ∨ AxisCellsVanish (pick (F.data κ) c).amp

theorem isPotentialPick_theta {F : PotentialSeries} (hF : IsPotentialSeries F) :
    IsPotentialPick 2 F PotKeyData.theta :=
  ⟨hF.theta_scalar, hF.theta_axis⟩

theorem isPotentialPick_phi {F : PotentialSeries} (hF : IsPotentialSeries F) :
    IsPotentialPick 1 F PotKeyData.phi :=
  ⟨hF.phi_scalar, hF.phi_axis⟩

theorem axisAdmissible_of_pick {h : ℕ} {F : PotentialSeries} {pick : PotKeyData → PotComponent → PotScalar}
    (hF : IsPotentialPick h F pick) (m : ℕ) {κ : FieldKey} (hκ : κ ∈ F.keys) (c : PotComponent) :
    AxisAdmissible (labelAzimuth m κ.label + c.shift) c.carriesSine (pick (F.data κ) c) := by
  by_cases h0 : κ.label.1 = 0
  · have hz : labelAzimuth m κ.label = 0 := by simp [labelAzimuth, h0]
    rw [hz, zero_add]
    cases c <;> refine ⟨fun hM hw => ?_, fun hw hM => ?_⟩ <;>
      simp_all [PotComponent.shift, PotComponent.carriesSine]
  · exact ⟨fun _ _ => hF.axis κ hκ h0 c, fun _ _ => hF.axis κ hκ h0 c⟩

end PotentialShape

end Breakdown
