import Breakdown.FracCell.SegmentPairDefs
import Breakdown.FracCell.CornerIndependenceParts
import Breakdown.FracCell.ModeRadialPartsA
import Breakdown.FracCell.ModeStripIntegrable

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis
open Breakdown.FracInternal.CornerModes Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.ModeRadialPartsA.Internal

theorem modes_radial_pair_gradient {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (hx : IsAdmissible c x)
    (L : CellLayout) (hL : L.order = c.order) (n : ℤ) (a : Fin 3) :
    IsRadialWeakPair (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0) := by
  have hs : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := by rw [hL]; exact hx.1
  have hc : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
      gradKernel L.order n a 0 q.1 (q.2 (radialUnit q.1))) :=
    (gradKernel_cont L.order n a 0).comp
      (continuous_fst.prodMk (continuous_snd.clm_apply (radialUnit_cont.comp continuous_fst)))
  have hb : ∀ θ (M : Space →L[ℝ] Space →L[ℝ] Space), ‖gradKernel L.order n a 0 θ (M (radialUnit θ))‖ ≤ ‖M‖ := by
    intro θ M
    refine (gradKernel_bound L.order n a 0 θ _).trans ((M.le_opNorm _).trans ?_)
    simpa using mul_le_mul_of_nonneg_left (unit_norm θ 0) (norm_nonneg M)
  have he : ∀ p : ℝ × ℝ, L.secondModeOf n x a 0 0 p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in Set.Ioo (-Real.pi) Real.pi, gradKernel L.order n a 0 θ (x.2.2.1 (cylPoint p.1 θ p.2) (radialUnit θ)) :=
    fun p => third_eq L.order n x.2.2.1 a 0 p
  have hw : ∀ R Z : ℝ, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * L.secondModeOf n x a 0 0 p)
      (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z) := by
    intro R Z
    have h := weighted_int R Z (locH hs) (fun θ M => gradKernel L.order n a 0 θ (M (radialUnit θ))) hc hb
    have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * L.secondModeOf n x a 0 0 p) = fun p => (1 / (2 * Real.pi) : ℂ) *
        ((p.1 : ℂ) * ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          gradKernel L.order n a 0 θ (x.2.2.1 (cylPoint p.1 θ p.2) (radialUnit θ))) := by
      funext p
      rw [he]
      ring
    rw [e]
    exact h.const_mul _
  have hm : AEStronglyMeasurable (L.secondModeOf n x a 0 0)
      (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) := by
    have h := (kmeas (locH hs).aestronglyMeasurable
      (fun θ M => gradKernel L.order n a 0 θ (M (radialUnit θ))) hc).const_mul (1 / (2 * Real.pi) : ℂ)
    exact h.congr (Filter.Eventually.of_forall fun p => (he p).symm)
  refine ⟨fun R Z => ⟨?_, hw R Z⟩, fun δ R Z hδ => off_int δ R Z hδ (hw R Z) hm,
    fun ψ hψ hc hpos => weak_radial hs n a 0 ψ hψ hc hpos⟩
  exact (modeStripIntegrable L.order x.1 x.2.1 x.2.2.1 hs n R (-Z) Z).2 a 0

end Breakdown.CellCert.CellFormula
