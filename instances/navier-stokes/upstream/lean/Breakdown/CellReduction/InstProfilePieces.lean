import Breakdown.CellReduction.InstMovedParams
import Breakdown.CellReduction.InstAffineStructure

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown
namespace CellReduction
namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal

theorem pairField_eq (P : ShapeParams) (g : OriginProfile) (D : TimeFieldData) (s : ℝ) :
    affineField P g D (fun _ : Fin 2 => g) (fun _ => D) ![s, -s] = shapeInfoField (withOrigin P g) D := by
  funext σ y
  simp [affineField, Fin.sum_univ_two]

theorem pairRate_eq (a : ℝ) : phaseRate ![(1 : ℝ), -1] ![a / 2, -(a / 2)] = a := by
  simp [phaseRate, Fin.sum_univ_two]

theorem pairCoord_le {a A : ℝ} (ha : |a| ≤ A) (i : Fin 2) : |(![a / 2, -(a / 2)] : Fin 2 → ℝ) i| ≤ A / 2 := by
  fin_cases i
  · simp [abs_div]
    linarith
  · simp [abs_div]
    linarith

theorem phaseRate_abs_le {k : ℕ} (rate q : Fin k → ℝ) {M : ℝ} (hq : ∀ i, |q i| ≤ M) :
    |phaseRate rate q| ≤ (∑ i, |rate i|) * M := by
  unfold phaseRate
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hq i) (abs_nonneg _)

theorem movedPiece_flow (hdecay : MovedFieldUniformDecayHolds) {P : ShapeParams} {moving : ℝ → ℝ}
    (hP : IsShapeParams P) (hm : IsRadialPhase moving) {g : OriginProfile} {D : TimeFieldData}
    (hg : IsOriginProfile g) (hD : IsTimeFieldData D) (A : ℝ) :
    ∃ B : ℝ, ∀ B', B ≤ B' → ∀ a : ℝ, |a| ≤ A →
      AdjointDefect.IsFlowPiece (shapeInfoField (withOrigin (movedParams P moving a) g) D) B' := by
  obtain ⟨B, hB⟩ := hdecay P moving ![(1 : ℝ), -1] g D (fun _ => g) (fun _ => D) (A / 2) hP hm hg
    (fun _ => hg) hD (fun _ => hD)
  refine ⟨max B 0, fun B' hB' a ha => ?_⟩
  have hB'0 : 0 ≤ B' := (le_max_right B 0).trans hB'
  have hBB' : B ≤ B' := (le_max_left B 0).trans hB'
  have hPa : IsShapeParams (withOrigin (movedParams P moving a) g) :=
    withOrigin_valid (movedParamsValid_holds P moving a hP hm) hg
  obtain ⟨hs, hper, -, -⟩ := shapeParts_closed.field_smooth _ _ hPa hD
  refine ⟨hs, hper, shapeParts_closed.field_divergence _ _ hPa hD, fun σ y => ?_⟩
  obtain ⟨h1, h2, -⟩ := hB _ (pairCoord_le ha) σ y
  rw [pairRate_eq, pairField_eq] at h1 h2
  have q1 : 0 < 1 + ‖y‖ := by positivity
  have q1' : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have q2 : 1 + ‖y‖ ≤ (1 + ‖y‖) ^ 2 := by nlinarith
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · calc B / (1 + ‖y‖) ≤ B' / (1 + ‖y‖) := div_le_div_of_nonneg_right hBB' q1.le
      _ ≤ B' := div_le_self hB'0 q1'
  · calc B / (1 + ‖y‖) ^ 2 ≤ B' / (1 + ‖y‖) ^ 2 := div_le_div_of_nonneg_right hBB' (by positivity)
      _ ≤ B' / (1 + ‖y‖) := div_le_div_of_nonneg_left hB'0 q1 q2

end Internal

open _root_.Breakdown.CellReduction.Instantiation.Internal

theorem profilePiecesFlow_of (hstep : StepPhaseHolds) (hdecay : MovedFieldUniformDecayHolds) :
    ProfilePiecesFlowHolds := by
  intro k C nE nM D R M hR
  have hm : IsRadialPhase R.moving :=
    (hstep R.params.chartLength R.stepEdge R.step hR.params_valid.chartLength_pos hR.step_valid).1
  obtain ⟨B0, h0⟩ := movedPiece_flow hdecay hR.params_valid hm hR.centreOrigin_valid hR.centre_valid
    ((∑ i, |R.rate i|) * M)
  have hi := fun i => movedPiece_flow hdecay hR.params_valid hm (hR.tangentOrigin_valid i)
    (hR.tangent_valid i) ((∑ i, |R.rate i|) * M)
  choose Bi hBi using hi
  have hsum : 0 ≤ ∑ i, |Bi i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨|B0| + ∑ i, |Bi i|, fun q hq => ?_⟩
  have ha := phaseRate_abs_le R.rate q hq
  refine ⟨h0 _ ((le_abs_self B0).trans (le_add_of_nonneg_right hsum)) _ ha, fun i => ?_⟩
  refine hBi i _ ?_ _ ha
  calc Bi i ≤ |Bi i| := le_abs_self _
    _ ≤ ∑ j, |Bi j| := Finset.single_le_sum (f := fun j => |Bi j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ |B0| + ∑ j, |Bi j| := le_add_of_nonneg_left (abs_nonneg _)

end Instantiation
end CellReduction
end Breakdown
