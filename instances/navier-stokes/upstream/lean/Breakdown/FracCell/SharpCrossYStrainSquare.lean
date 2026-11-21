import Breakdown.FracCell.SharpYSharpCross
import Breakdown.FracCell.SharpTargetSquare

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpTargetSquare.Internal

theorem yStrainSquare_holds : YStrainSquareStatement := by
  intro α _ _ k N c hform K S B Cl slots R hcell _ x _ ζ
  have hK := hcell.box
  obtain ⟨C0, hC0⟩ := hform.model_bounded
  have hsol : ∀ y ∈ K.solid, ‖c.modelStrain y‖ ≤ C0 ∧ ‖c.modelCurlGrad y‖ ≤ C0 := fun y hy =>
    ⟨(hC0 y (hcell.solid_in_region hy)).2.2.1, (hC0 y (hcell.solid_in_region hy)).2.2.2⟩
  obtain ⟨_, _, mS, mG⟩ := hform.model_measurable
  have hR : Bd K (fun p => ((CellScalars.rHat K p : ℝ) : ℂ)) := Bd_rHat hK
  have bS : ∀ β a b, Bd K (fun p => CellScalars.strainMode c β p a b) :=
    fun β a b => modeMat_bd hK mS _ _ a b (fun y hy => (hsol y hy).1)
  have bG : ∀ β a b, Bd K (fun p => CellScalars.curlGradMode c β p a b) :=
    fun β a b => modeMat_bd hK mG _ _ a b (fun y hy => (hsol y hy).2)
  have bLS : ∀ n' a b, Bd K (fun p => K.lowStrainAt c.order n' S.degHigh x.2.1 p a b) :=
    fun n' a b => Bd_proj _ _ _
  have bLV : ∀ n' a, Bd K (fun p => K.lowVelocityAt c.order n' S.degHigh x.1 p a) :=
    fun n' a => Bd_proj _ _ _
  have bL : ∀ n ∈ S.resolved, ∀ i j, Bd K (fun p => S.localMatrix n p i j) := by
    intro n hn i j
    obtain ⟨hm, C, hC⟩ := hcell.scalars.data_regular.1 n hn
    exact ⟨(hm i j).aestronglyMeasurable, C, fun p hp => hC p hp i j⟩
  have wA : ∀ i n a b, IsWeightedSquareOn K (fun p => modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b) :=
    fun i n a b => modeMat_W hK (memLp_of_entry (hform.modelActuatorGrad_data i).1
      (hform.modelActuatorGrad_data i).2.1) _ _ a b
  have wP : ∀ i n a b, IsWeightedSquareOn K (fun p => modeMat c.order n (c.modelPinField i) p.1 p.2 a b) :=
    fun i n a b => modeMat_W hK (memLp_of_entry (hform.modelPin_data i).1 (hform.modelPin_data i).2.1) _ _ a b
  refine ⟨fun n _ a b => ?_, fun n _ b => ?_⟩
  · exact yStrain_W hK c S _ _ _ _ n hR (fun n' a b => wave_bd (bS _) (bG _) (bLS n') (bLV n') a b)
      (fun hn => (split_bd (bL n hn) (bLS n) (bLV n)).1) (wA · n) (wP · n) a b
  · exact W_of_Bd hK (yVel_bd c S _ _ n hR (fun n' b => waveV_bd (bG _) (bLS n') b)
      (fun hn => (split_bd (bL n hn) (bLS n) (bLV n)).2) b)

end Breakdown.CellCert.CellAnalysis
