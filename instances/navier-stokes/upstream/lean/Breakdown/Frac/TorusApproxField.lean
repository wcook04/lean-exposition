import Breakdown.Frac.StTorusApprox
import Breakdown.Torus.ApproxField
import Breakdown.Torus.Cutoff

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

open ApproxField.Internal

theorem fracApproxFieldProperties_of (α : ℝ) (hS : FracSelfSimilarSolves α) (hH : HomotopyCurl) :
    FracApproxFieldProperties α := by
  intro a U P hR T hT
  obtain ⟨hSW, hSq, hSdiv⟩ := hS a U P hR T hT
  have hD : CutoffDivergenceFree := cutoffDivergenceFree hH
  have hslice : ∀ t < T, ContDiff ℝ ∞ (fracSelfSimilar α a U T t) := fun t ht =>
    hSW.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)
  refine ⟨?_, ?_, fun t ht x => ⟨?_, fun hx => ⟨?_, ?_⟩, fun hx => ?_⟩⟩
  · refine contDiffOn_of_clamped T (fracApproxField α a U T) fun ψ hψ hψT => ?_
    have hg : ContDiff ℝ ∞ (fun z : ℝ × Space => fracSelfSimilar α a U T (ψ z.1) z.2) :=
      hSW.comp_contDiff ((hψ.comp contDiff_fst).prodMk contDiff_snd)
        (fun z => ⟨hψT z.1, mem_univ _⟩)
    exact contDiff_cutoffField_family (fun z => fracSelfSimilar α a U T (ψ z.1) z.2) hg
  · have hP : ContDiffOn ℝ ∞
        (fun z : ℝ × Space => fracSelfSimilarPressure α a P T z.1 pressureAnchor)
        (Iio T ×ˢ univ) :=
      hSq.comp (contDiff_fst.prodMk contDiff_const).contDiffOn
        (fun z hz => ⟨hz.1, mem_univ _⟩)
    exact ((contDiff_centralCut.comp contDiff_snd).contDiffOn).mul (hSq.sub hP)
  · exact (hD centralCut center (fracSelfSimilar α a U T t) contDiff_centralCut (hslice t ht)
      (fun y => (hSdiv t ht y).1)).2 x
  · show centralCut x • fracSelfSimilar α a U T t x +
        cross (gradientAt centralCut x) (homotopyPotential center (fracSelfSimilar α a U T t) x) = 0
    rw [gradient_eq_zero_of_fderiv (fderiv_centralCut_outer hx), cross_zero_left,
      centralCut_outer hx]
    simp
  · show centralCut x * _ = 0
    rw [centralCut_outer hx]
    simp
  · show centralCut x • fracSelfSimilar α a U T t x +
        cross (gradientAt centralCut x) (homotopyPotential center (fracSelfSimilar α a U T t) x) = _
    rw [gradient_eq_zero_of_fderiv (fderiv_centralCut_inner hx), cross_zero_left,
      centralCut_inner hx]
    simp

end Breakdown.Periodic
