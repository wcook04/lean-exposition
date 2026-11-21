import Breakdown.FracCell.RelStream
import Breakdown.FracCell.ModeRectIntegrable

open MeasureTheory

noncomputable section

namespace Breakdown.FracInternal.ModeStripIntegrable

open Set Real

theorem strip_sub (R z₁ z₂ : ℝ) :
    Icc (0 : ℝ) R ×ˢ Icc z₁ z₂ ⊆ Icc 0 R ×ˢ Icc (-(|z₁| + |z₂|)) (|z₁| + |z₂|) := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨h1, ?_, ?_⟩
  · linarith [neg_abs_le z₁, abs_nonneg z₂]
  · linarith [le_abs_self z₂, abs_nonneg z₁]

end Breakdown.FracInternal.ModeStripIntegrable

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis
open Set Real
open Breakdown.FracInternal.ModeRectIntegrable Breakdown.FracInternal.ModeHeightAxis
open Breakdown.FracInternal.ModeStripIntegrable
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal

theorem modeStripIntegrable : ModeStripIntegrableStatement := by
  intro m v G H hs n R z₁ z₂
  set Z : ℝ := |z₁| + |z₂| with hZ
  have hsub := strip_sub R z₁ z₂
  have hSm : MeasurableSet (Icc (0 : ℝ) R ×ˢ Icc z₁ z₂) := measurableSet_Icc.prod measurableSet_Icc
  constructor
  · intro a
    have hint := IntegrableOn.mono_set ((six_int R Z hs.velocity_six (velKernel m n a) (velKernel_cont m n a)
      (velKernel_bound m n a)).const_mul (1 / (2 * π) : ℂ)) hsub
    refine IntegrableOn.congr_fun hint (fun p _ => ?_) hSm
    rw [modeVec_eq]
  · intro a b
    set ρ : ℝ := 2 * |R| + |Z| + 1 with hρ
    have hρ0 : 0 < ρ := by positivity
    have hχ : IsTestScalar (radialCutoff ρ) := ⟨contDiff_radialCutoff hρ0, hasCompactSupport_radialCutoff hρ0⟩
    have hχ1 : ∀ y, |radialCutoff ρ y| ≤ 1 := fun y => by
      rw [abs_of_nonneg (radialCutoff_nonneg ρ y)]
      exact radialCutoff_le_one ρ y
    have h6 := op_six hs hχ hχ1
    have hint := IntegrableOn.mono_set ((six_int R Z h6 (gradKernel m n a b) (gradKernel_cont m n a b)
      (gradKernel_bound m n a b)).const_mul (1 / (2 * π) : ℂ)) hsub
    refine IntegrableOn.congr_fun hint (fun p hp => ?_) hSm
    rw [gradMode_eq]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    have hp' := hsub hp
    have hn : ‖cylPoint p.1 θ p.2‖ ≤ ρ := by
      refine (cylPoint_norm _ _ _).trans ?_
      have h1 : |p.1| ≤ |R| := by rw [abs_of_nonneg hp'.1.1]; exact hp'.1.2.trans (le_abs_self _)
      have h2 : |p.2| ≤ |Z| :=
        abs_le.2 ⟨by linarith [hp'.2.1, le_abs_self Z, neg_abs_le Z], hp'.2.2.trans (le_abs_self _)⟩
      rw [hρ]
      linarith
    simp only [radialCutoff_eq_one hρ0 hn, one_smul]

end Breakdown.CellCert.CellFormula
