import Breakdown.Profile.StatementsPhysical

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private lemma slice_contDiff {W : ℝ → Space → Space}
    (h : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2)) (s : ℝ) : ContDiff ℝ ∞ (W s) :=
  h.comp (ContDiff.prodMk contDiff_const contDiff_id)

private lemma pressure_slice_contDiff {q : ℝ → Space → ℝ}
    (h : ContDiff ℝ ∞ (fun z : ℝ × Space => q z.1 z.2)) (s : ℝ) : ContDiff ℝ ∞ (q s) :=
  h.comp (ContDiff.prodMk contDiff_const contDiff_id)

private lemma integrable_inner_of_continuous {f φ : Space → Space} (hf : Continuous f)
    (hφ : IsTestField φ) : Integrable (fun x => inner ℝ (f x) (φ x)) := by
  refine (hf.inner hφ.1.continuous).integrable_of_hasCompactSupport ?_
  refine hφ.2.1.mono ?_
  intro x hx
  by_contra h0
  exact hx (by simp [Function.notMem_support.mp h0])

private lemma continuous_sumSecondPartialsAt {v : Space → Space} (hv : ContDiff ℝ ∞ v) :
    Continuous (sumSecondPartialsAt v) := by
  unfold sumSecondPartialsAt
  refine continuous_finsetSum _ (fun i _ => ?_)
  exact (continuous_eval_const _).comp
    (hv.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top))

private lemma continuous_advectionAt {v : Space → Space} (hv : ContDiff ℝ ∞ v) :
    Continuous (advectionAt v) := by
  unfold advectionAt
  exact (hv.continuous_fderiv (by simp)).clm_apply hv.continuous

private lemma continuous_gradientAt {p : Space → ℝ} (hp : ContDiff ℝ ∞ p) :
    Continuous (gradientAt p) := by
  unfold gradientAt
  refine continuous_finsetSum _ (fun i _ => ?_)
  exact ((hp.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const

theorem physicalWeak_holds (hpd : PhysicalPairingDeriv) (hssp : SumSecondPartialsPairing)
    (hzero : GradientPairingZero) : PhysicalWeak := by
  intro W q C h s₀ t ht φ hφ
  refine (hpd W q C h s₀ t ht φ hφ).congr_deriv ?_
  have hv : ContDiff ℝ ∞ (physicalField W s₀ t) := by
    unfold physicalField dilateField
    exact ((slice_contDiff h.smooth _).comp (contDiff_id.const_smul _)).const_smul _
  have hp : ContDiff ℝ ∞ (physicalPressure q s₀ t) := by
    unfold physicalPressure
    exact contDiff_const.mul
      ((pressure_slice_contDiff h.smooth_pressure _).comp (contDiff_id.const_smul _))
  have i1 := integrable_inner_of_continuous (continuous_sumSecondPartialsAt hv) hφ
  have i2 := integrable_inner_of_continuous (continuous_advectionAt hv) hφ
  have i3 := integrable_inner_of_continuous (continuous_gradientAt hp) hφ
  have e : (fun x => inner ℝ (sumSecondPartialsAt (physicalField W s₀ t) x
        - advectionAt (physicalField W s₀ t) x
        - gradientAt (physicalPressure q s₀ t) x) (φ x))
      = fun x => inner ℝ (sumSecondPartialsAt (physicalField W s₀ t) x) (φ x)
        - inner ℝ (advectionAt (physicalField W s₀ t) x) (φ x)
        - inner ℝ (gradientAt (physicalPressure q s₀ t) x) (φ x) := by
    funext x
    simp only [inner_sub_left]
  have hs := integral_sub (i1.sub i2) i3
  have hs2 := integral_sub i1 i2
  simp only [Pi.sub_apply] at hs hs2
  rw [e, hs, hs2, hssp _ φ hv hφ, hzero _ φ hp hφ]
  unfold advectionPairing
  ring

end Breakdown
