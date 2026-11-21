import Breakdown.FracCell.StrainFaceHeightNormal
import Breakdown.FracCell.ModeRadialWeakProof
import Breakdown.FracCell.ModeWeakIdentity

open scoped ContDiff
open MeasureTheory Set

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

private theorem axis_meas {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : AEStronglyMeasurable H volume) :
    AEStronglyMeasurable (fun y => H y axialUnit) volume :=
  (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) axialUnit).continuous.comp_aestronglyMeasurable hH

private theorem axis_sq {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : AEStronglyMeasurable H volume)
    (h2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) :
    Integrable (fun y => entrySq (H y axialUnit)) := by
  have hc : Continuous (fun M : Space →L[ℝ] Space => entrySq M) := by
    unfold entrySq
    fun_prop
  refine h2.mono' (hc.comp_aestronglyMeasurable (axis_meas hH)) (Filter.Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ entrySq (H y axialUnit) := by
    unfold entrySq
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  have e : entrySq (H y axialUnit) = ∑ j : Fin 3, ‖H y (unitVector 2) (unitVector j)‖ ^ 2 := rfl
  rw [e]
  exact Finset.single_le_sum (f := fun i => ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)
    (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ 2)

private theorem third_eq (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : Fin 3) :
    modeThird m n H a 0 2 = gradMode m n (fun y => H y axialUnit) a 0 := rfl

theorem radialMixedWeak_holds : RadialMixedWeakStatement := by
  intro K hK m v G H hs n a ψ hψ hψ1 hψ2 t ht
  set G' : Space → (Space →L[ℝ] Space) := fun y => H y axialUnit with hG'
  have hm' : AEStronglyMeasurable G' volume := axis_meas hs.measurable_second
  have hq' : Integrable (fun y => entrySq (G' y)) := axis_sq hs.measurable_second hs.second_two
  have hGl : LocallyIntegrable G' volume :=
    (ModeRadialWeakInternal.grad_memLp hm' hq').locallyIntegrable (by norm_num)
  have hF : ∀ R Z, IntegrableOn (gradMode m n G a 2) (Icc 0 R ×ˢ Icc (-Z) Z) :=
    fun R Z => modeHeightAxis m v G H hs n a R Z
  have hg : ∀ R Z, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m n H a 0 2 p)
      (Icc 0 R ×ˢ Icc (-Z) Z) := by
    intro R Z
    rw [third_eq]
    exact ModeRadialWeakInternal.grad_on hGl n a R Z
  have hW : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ p ∈ tsupport φ, 0 < p.1) →
      ∫ p, ((fderiv ℝ φ p (1, 0) : ℝ) : ℂ) * gradMode m n G a 2 p =
        -∫ p, (φ p : ℂ) * modeThird m n H a 0 2 p :=
    fun φ h1 h2 h3 => (modeWeakIdentity m v G H hs n a φ h1 h2 h3).2.2.1
  have h0 : 0 ≤ K.r₁ := hK.r_order.1
  have h12 : K.r₁ < K.r₂ := hK.r_order.2
  have hz0 : 0 ≤ K.z₁ := hK.z_order.1
  have hsub : K.rect ⊆ Icc 0 K.r₂ ×ˢ Icc (-K.z₂) K.z₂ := fun p hp =>
    ⟨⟨h0.trans hp.1.1, hp.1.2⟩, ⟨by linarith [hp.2.1, hp.2.2], hp.2.2⟩⟩
  have hFr : IntegrableOn (gradMode m n G a 2) K.rect := (hF K.r₂ K.z₂).mono_set hsub
  have hgr : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * modeThird m n H a 0 2 p) K.rect := by
    rw [third_eq]
    exact LowEntry.Internal.gradMode_int K hK m n hm' hq' a 0
  have hgm : AEStronglyMeasurable (modeThird m n H a 0 2) (volume.restrict K.rect) := by
    rw [third_eq]
    exact (ModeRadialWeakInternal.grad_meas hm' n a K.r₂ K.z₂).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hwpos : ∀ r, 0 < r → 0 < K.lineWeight r := by
    intro r hr
    simp only [CellBox.lineWeight]
    split_ifs <;> linarith
  have hwn : ∀ r ∈ Icc K.r₁ K.r₂, 0 ≤ K.lineWeight r := by
    intro r hr
    simp only [CellBox.lineWeight]
    split_ifs <;> linarith [hr.1]
  have hwl : ∀ r ∈ Icc K.r₁ K.r₂, r - K.r₁ ≤ (1 + (K.r₂ - K.r₁)) * K.lineWeight r := by
    intro r hr
    simp only [CellBox.lineWeight]
    split_ifs with h
    · rw [h, sub_zero]
      have : 0 ≤ r := h0.trans hr.1
      nlinarith
    · linarith [hr.2]
  exact ModeRadialWeakInternal.rect_psi hF hg hW h0 h12 (LowEntry.Internal.lineWeight_cont K) hwpos hwn hwl
    hFr hgr hgm hψ hψ1 hψ2 ht

end Breakdown.CellCert.CellFormula
