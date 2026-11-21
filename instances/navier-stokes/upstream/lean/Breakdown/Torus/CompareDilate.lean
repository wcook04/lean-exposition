import Breakdown.Torus.CompareStatements
import Breakdown.Torus.ShellTorusBase

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace CompareDilate.Internal

theorem fderiv_dilate {f : Space → Space} (hf : Differentiable ℝ f) (r : ℝ) (y v : Space) :
    fderiv ℝ (fun z => r • f (r • z)) y v = (r * r) • fderiv ℝ f (r • y) v := by
  have h1 : HasFDerivAt (fun z : Space => r • z) (r • ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id y).const_smul r
  have h2 : HasFDerivAt (fun z => r • f (r • z)) _ y := ((hf (r • y)).hasFDerivAt.comp y h1).const_smul r
  rw [h2.fderiv]
  simp [smul_smul]

end CompareDilate.Internal

theorem transplantDilate : TransplantDilate := by
  intro μ c f hμ hc
  funext x
  simp only [transplantField, simCoord, dilateField]
  rw [Real.sqrt_mul hμ.le, smul_smul, smul_smul]
  have hm : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hcs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  congr 1
  · field_simp
  · congr 1
    congr 1
    field_simp

theorem dilateTest : DilateTest := by
  intro c f hc hf
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · exact (h1.comp (contDiff_const_smul _)).const_smul _
  · have hs : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
    have hk : HasCompactSupport (f ∘ (Homeomorph.smulOfNeZero (Real.sqrt c) hs)) :=
      h2.comp_homeomorph _
    exact hk.comp_left (g := fun v : Space => Real.sqrt c • v) (smul_zero _)
  · intro y
    have hd : Differentiable ℝ f := h1.differentiable (by simp)
    unfold divergenceAt
    have := h3 (Real.sqrt c • y)
    unfold divergenceAt at this
    have e : ∀ i : Fin 3, (fderiv ℝ (dilateField c f) y (unitVector i)) i =
        (Real.sqrt c * Real.sqrt c) * (fderiv ℝ f (Real.sqrt c • y) (unitVector i)) i := by
      intro i
      rw [show dilateField c f = fun z => Real.sqrt c • f (Real.sqrt c • z) from rfl,
        CompareDilate.Internal.fderiv_dilate hd]
      rfl
    simp only [e]
    rw [← Finset.mul_sum, this, mul_zero]

theorem advectShellBounds (hG : Freq.GradSixDecay) (hE : Freq.EmbedNorm) : AdvectShellBounds :=
  ⟨ShellTorus.Internal.advectShell_threeHalves hG hE, ShellTorus.Internal.advectShell_ae_zero⟩

end Breakdown.Periodic
