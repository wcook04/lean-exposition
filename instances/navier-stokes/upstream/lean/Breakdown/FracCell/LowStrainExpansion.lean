import Breakdown.FracCell.EnergyPair
import Breakdown.FracCell.LowEntry
import Breakdown.FracCell.EnergyHeightProj

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

private lemma weighted_mode_int (K : CellBox) (hK : IsCellBox K) (m : ℕ) (n : ℤ)
    {G : Space → (Space →L[ℝ] Space)} (hG1 : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) (a b : Fin 3) (t s : ℝ → ℝ) (ht : Continuous t)
    (hs : Continuous s) :
    IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * gradMode m n G a b p) K.rect := by
  have h := (LowEntry.Internal.gradMode_int K hK m n hG1 hG2 a b).mul_continuousOn
    (g' := fun p : ℝ × ℝ => ((t p.1 * s p.2 : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp ((ht.comp continuous_fst).mul (hs.comp continuous_snd))).continuousOn
    (isCompact_Icc.prod isCompact_Icc)
  refine h.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  push_cast
  ring

theorem lowStrainExpansion : LowStrainExpansionStatement := by
  intro α D _ _ k N c K B S modes Q q I v G H u h n a b p _
  have hF := weighted_mode_int K h.box c.order n h.field.measurable_gradient h.field.gradient_two a b
  have e := HeightProj.proj_eq_basis K B h.bases Q (gradMode c.order n G a b) hF
  unfold CellBox.lowStrain
  rw [e]

end Breakdown.CellCert.CellEnergy
