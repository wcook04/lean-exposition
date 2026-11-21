import Breakdown.FracCell.SharpCircleSquare

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.SliceMeasurable

open SteadyCert Assembly
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.SharpCircleSquare.Internal

private theorem comp_aesm {E : Type*} [TopologicalSpace E] {μ : Measure ℝ} {Y : ℝ → E}
    (hY : AEStronglyMeasurable Y μ) (φ : ℝ → E → ℂ) (hφc : Continuous (fun w : ℝ × E => φ w.1 w.2)) :
    AEStronglyMeasurable (fun θ => φ θ (Y θ)) μ :=
  hφc.comp_aestronglyMeasurable (measurable_id.aestronglyMeasurable.prodMk hY)

theorem slice_aesm (K : CellBox) (hK : IsCellBox K) {G : Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable G volume) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∀ a b : Fin 3,
      AEStronglyMeasurable (fun θ => (frameMat θ (G (cylPoint p.1 θ p.2)) a b : ℂ)) (volume.restrict (Ioc (-π) π)) := by
  have hF : AEStronglyMeasurable (fun w : (ℝ × ℝ) × ℝ => G (cylArg w)) muU :=
    hG.comp_quasiMeasurePreserving qmp
  rw [muU_def] at hF
  have hslice := hF.prodMk_left
  filter_upwards [ae_mono (rect_le K hK) hslice] with p hp a b
  have h1 : AEStronglyMeasurable (fun θ => G (cylPoint p.1 θ p.2)) (volume.restrict (Ioo (-π) π)) := hp
  have h2 := comp_aesm h1 (fun θ M => (frameMat θ M a b : ℂ)) (Complex.continuous_ofReal.comp (frameMat_cont a b))
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := -π) (b := π))]
  exact h2

end Breakdown.CellCert.CellAnalysis.SliceMeasurable
