import Breakdown.FracCell.SharpYClassCrossSt
import Breakdown.FracCell.SharpModeExpansionRegular

open MeasureTheory Set

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.ClassCrossRegular.Internal

open SteadyCert Assembly SharpParts ModeExpansionParts
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal
open Breakdown.CellCert.CellAnalysis.SharpModeExpansionRegular.Internal

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

theorem cross_int (α : ℝ) (hc : IsFormData α c) (hK : IsCellBox K)
    (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (T : Set ℤ) (n n' : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * classCrossDensity c K S x T n n' p) K.rect := by
  classical
  by_cases hT : n' ∈ T
  · refine (wt_re K (cross_wt c K S x α hc hK hs n n')).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [classCrossDensity, if_pos hT, crossPair, lowSharpPair, sharpLowPair]
  · refine (integrableOn_zero (s := K.rect) (μ := volume)).congr (Filter.Eventually.of_forall fun p => ?_)
    simp [classCrossDensity, hT]

theorem loss_int {α : ℝ} {B : CellBases} {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k}
    (hd : IsCellData α c K S B Cl R) (n : ℤ) (i : Fin Cl.count) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * Cl.classLoss S.splitLength i p
      (K.lowStrainAt c.order n S.degHigh x.2.1 p) (K.lowVelocityAt c.order n S.degHigh x.1 p)) K.rect := by
  obtain ⟨hm1, hm2, -, -, C, hC⟩ := hd.class_regular i
  have hls : Continuous (fun p => K.lowStrainAt c.order n S.degHigh x.2.1 p) :=
    continuous_pi fun a => continuous_pi fun b => by
      simpa only [CellBox.lowStrainAt, CellBox.lowStrain] using
        proj_cont K S.degHigh S.degHigh (gradMode c.order n x.2.1 a b)
  have hlv : Continuous (fun p => K.lowVelocityAt c.order n S.degHigh x.1 p) :=
    continuous_pi fun a => by
      simpa only [CellBox.lowVelocityAt, CellBox.lowVelocity] using
        proj_cont K (S.degHigh - 1) (S.degHigh - 1) (fun p => modeVec c.order n x.1 p.1 p.2 a)
  have hc1 : Continuous (fun p : ℝ × ℝ => p.1 * curlSq (K.lowStrainAt c.order n S.degHigh x.2.1 p)) :=
    continuous_fst.mul (continuous_curlSq.comp hls)
  have hc2 : Continuous (fun p : ℝ × ℝ => p.1 * (S.splitLength * sumSq (K.lowStrainAt c.order n S.degHigh x.2.1 p)
      + vecSq (K.lowVelocityAt c.order n S.degHigh x.1 p) / S.splitLength)) :=
    continuous_fst.mul ((continuous_const.mul (continuous_sumSq.comp hls)).add
      ((continuous_vecSq.comp hlv).div_const _))
  have hb1 : ∀ᵐ p ∂(volume.restrict K.rect), ‖Cl.strainDev i p‖ ≤ C :=
    (ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => by
      rw [Real.norm_eq_abs]; exact (hC p hp).1)
  have hb2 : ∀ᵐ p ∂(volume.restrict K.rect), ‖Cl.gradDev i p‖ ≤ C :=
    (ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => by
      rw [Real.norm_eq_abs]; exact (hC p hp).2.1)
  have i1 : IntegrableOn (fun p : ℝ × ℝ => Cl.strainDev i p *
      (p.1 * curlSq (K.lowStrainAt c.order n S.degHigh x.2.1 p))) K.rect :=
    Integrable.bdd_mul (hc1.continuousOn.integrableOn_compact (rect_compact K)) hm1.aestronglyMeasurable hb1
  have i2 : IntegrableOn (fun p : ℝ × ℝ => Cl.gradDev i p *
      (p.1 * (S.splitLength * sumSq (K.lowStrainAt c.order n S.degHigh x.2.1 p)
        + vecSq (K.lowVelocityAt c.order n S.degHigh x.1 p) / S.splitLength))) K.rect :=
    Integrable.bdd_mul (hc2.continuousOn.integrableOn_compact (rect_compact K)) hm2.aestronglyMeasurable hb2
  refine (i1.add (i2.const_mul ((1 / 2) * Exterior.traceFreeConst))).congr
    (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.add_apply, CellClasses.classLoss]
  ring

end Breakdown.CellCert.CellAnalysis.ClassCrossRegular.Internal

namespace Breakdown.CellCert.CellAnalysis

open ClassCrossRegular.Internal

theorem classCrossRegular_holds : ClassCrossRegularStatement := by
  intro α _ _ k N c hc K S B Cl slots R hd _ x hx
  have hK := hd.box
  have hs : SteadyCert.IsSecondOrderField c.order x.1 x.2.1 x.2.2.1 := hx.1
  exact ⟨fun n _ n' => cross_int c K S x α hc hK hs _ n n', fun n _ i => loss_int c K S x hd n i⟩

end Breakdown.CellCert.CellAnalysis
