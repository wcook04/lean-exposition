import Breakdown.CertCell.BridgeTraceStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

open CellCert.CellFormula

namespace Internal

theorem restrict_prod_iterate {G : ℝ × ℝ → ℂ} {s₁ s₂ : Set ℝ} (hG : IntegrableOn G (s₁ ×ˢ s₂)) :
    ∫ p in s₁ ×ˢ s₂, G p = ∫ x in s₁, ∫ y in s₂, G (x, y) := by
  have hprod : (volume.restrict s₁).prod (volume.restrict s₂) = (volume : Measure (ℝ × ℝ)).restrict (s₁ ×ˢ s₂) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hG' : Integrable G ((volume.restrict s₁).prod (volume.restrict s₂)) := by
    rw [hprod]
    exact hG
  rw [← hprod]
  exact integral_prod G hG'

end Internal

theorem heightStripTrace : HeightStripTraceHolds := by
  intro c o lo hi wt F dF t _hco _hlh hwt ht hF hdF
  unfold heightStripMoment sideTrace
  have hK : IsCompact (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) := isCompact_Icc.prod isCompact_Icc
  have hB : ContinuousOn (fun p : ℝ × ℝ => ((((p.2 - o) / (c - o)) : ℝ) : ℂ))
      (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) := by
    apply Continuous.continuousOn
    fun_prop
  have h2 := hdF.continuousOn_mul hB hK
  have h1 := hF.const_mul ((((1 / (c - o)) : ℝ) : ℂ))
  have hG : IntegrableOn (fun p : ℝ × ℝ =>
      ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((wt p.1 * t p.1 : ℝ) : ℂ))
      (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) := by
    refine (IntegrableOn.add h1 h2).congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    simp only [Pi.add_apply]
    ring
  rw [Internal.restrict_prod_iterate hG, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
  simp only
  rw [integral_mul_const]
  ring

end SideTrace

end CertCell

end Breakdown
