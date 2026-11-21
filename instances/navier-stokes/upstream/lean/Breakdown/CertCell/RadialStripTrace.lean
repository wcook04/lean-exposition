import Breakdown.CertCell.BridgeTraceStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

open CellCert.CellFormula CellCert.CellAnalysis Bridge

theorem radialStripTrace : RadialStripTraceHolds := by
  intro c o lo hi F dF t _hco _hlohi _ht hF hdF
  set A : Set ℝ := Set.Icc (min c o) (max c o)
  set B : Set ℝ := Set.Icc lo hi
  set g : ℝ × ℝ → ℂ := fun p =>
    ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ)
    with hgdef
  have hgeq : g = fun p => (((1 / (c - o) : ℝ)) : ℂ) *
      (((t p.2 : ℝ) : ℂ) * F p + (((p.1 - o) * t p.2 : ℝ) : ℂ) * dF p) := by
    funext p
    simp only [hgdef]
    push_cast
    ring
  have hgint : Integrable g ((volume.restrict A).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, hgeq]
    exact (hF.add hdF).const_mul _
  have hslice : ∀ z, (∫ r in A, g (r, z)) = ((t z : ℝ) : ℂ) *
      ∫ r in A, ((((1 / (c - o)) : ℝ) : ℂ) * F (r, z) + (((r - o) / (c - o) : ℝ) : ℂ) * dF (r, z)) := by
    intro z
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
    simp only [hgdef]
    ring
  have hfub : (∫ p in A ×ˢ B, g p) = ∫ z in B, ∫ r in A, g (r, z) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integral_prod_symm g hgint
  unfold radialStripMoment sideTrace
  change edgeSign c o * (∫ p in A ×ˢ B, g p) = _
  rw [hfub, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [hslice]
  ring

end SideTrace

end CertCell

end Breakdown
