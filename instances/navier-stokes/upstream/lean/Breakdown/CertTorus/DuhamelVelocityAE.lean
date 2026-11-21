import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real Filter
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

open Freq

namespace Internal.DuhamelVelocity

theorem dilateField_congr_ae {μ : ℝ} (hμ : 0 < μ) {f g : Space → Space} (h : f =ᵐ[volume] g) :
    dilateField μ f =ᵐ[volume] dilateField μ g := by
  have hq : Measure.QuasiMeasurePreserving (fun y : Space => Real.sqrt μ • y) volume volume :=
    Measure.quasiMeasurePreserving_smul volume (Real.sqrt_pos.2 hμ).ne'
  filter_upwards [hq.ae_eq_comp h] with y hy
  simp only [dilateField, Function.comp_apply] at hy ⊢
  rw [hy]

theorem heatConv_congr_ae (τ : ℝ) {f g : Space → Space} (h : f =ᵐ[volume] g) :
    heatConv τ f = heatConv τ g := by
  funext y
  unfold heatConv
  exact integral_congr_ae (h.mono fun z hz => by simp only [hz])

theorem kernelConv_congr_ae (τ : ℝ) {a b : Space → Space} (h : a =ᵐ[volume] b) :
    kernelConv τ (tensorField a a) = kernelConv τ (tensorField b b) := by
  funext y
  unfold kernelConv
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact integral_congr_ae (h.mono fun z hz => by simp only [tensorField, hz])

theorem similarity_flow_eq (τ : ℝ) (x : X) :
    realization.F.S τ x = dilX (Real.exp (-τ)) (heatX (1 - Real.exp (-τ)) x) := rfl

theorem similarity_bilin_eq (τ : ℝ) (u v : X) :
    realization.F.Ks τ u v = dilX (Real.exp (-τ)) (bilinX (1 - Real.exp (-τ)) u v) := rfl

theorem duhamelIntegrand_measurable (lM : LerayKernelMeasurable) (W : ℝ → Space → Space)
    (hcont : Continuous (fun p : ℝ × Space => W p.1 p.2)) (s : ℝ) :
    Measurable (fun p : ℝ × Space => dilateField (Real.exp (-(s - p.1)))
      (fun x => -kernelConv (1 - Real.exp (-(s - p.1))) (tensorField (W p.1) (W p.1)) x) p.2) := by
  have hW : ∀ j : Fin 3, Measurable (fun q : (ℝ × Space) × Space => W q.1.1 q.2 j) := by
    intro j
    have h1 : Continuous (fun q : (ℝ × Space) × Space => W q.1.1 q.2) :=
      hcont.comp (continuous_fst.fst.prodMk continuous_snd)
    exact ((PiLp.continuous_apply 2 _ j).comp h1).measurable
  have hK : ∀ i j k : Fin 3, Measurable (fun q : (ℝ × Space) × Space =>
      lerayKernel i j k (1 - Real.exp (-(s - q.1.1)))
        (Real.sqrt (Real.exp (-(s - q.1.1))) • q.1.2 - q.2)) := by
    intro i j k
    refine (lM i j k).comp (Measurable.prodMk ?_ ?_)
    · fun_prop
    · fun_prop
  have hI : ∀ i : Fin 3, Measurable (fun p : ℝ × Space =>
      ∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k (1 - Real.exp (-(s - p.1)))
        (Real.sqrt (Real.exp (-(s - p.1))) • p.2 - z) * (W p.1 z j * W p.1 z k)) := by
    intro i
    have hf : Measurable (fun q : (ℝ × Space) × Space =>
        ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k (1 - Real.exp (-(s - q.1.1)))
          (Real.sqrt (Real.exp (-(s - q.1.1))) • q.1.2 - q.2) * (W q.1.1 q.2 j * W q.1.1 q.2 k)) := by
      refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
      exact (hK i j k).mul ((hW j).mul (hW k))
    exact hf.stronglyMeasurable.integral_prod_right'.measurable
  have hsq : Measurable (fun p : ℝ × Space => Real.sqrt (Real.exp (-(s - p.1)))) := by fun_prop
  simp only [dilateField, kernelConv, tensorField]
  refine hsq.smul (Measurable.neg ?_)
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (hI i).smul_const _

theorem one_sub_exp_pos {a b : ℝ} (h : a < b) : 0 < 1 - Real.exp (-(b - a)) := by
  have h1 := Real.exp_lt_exp.2 (show -(b - a) < 0 by linarith)
  rw [Real.exp_zero] at h1
  linarith

theorem heat_part_ae (hv : HeatVelocity) {w : ℝ → X} {W : ℝ → Space → Space} (hV : IsVelocityOf w W)
    {s' s : ℝ} (hss : s' < s) :
    (velocity (realization.F.S (s - s') (w s')) : Space → Space) =ᵐ[volume]
      dilateField (Real.exp (-(s - s'))) (heatConv (1 - Real.exp (-(s - s'))) (W s')) := by
  have hμ : 0 < Real.exp (-(s - s')) := Real.exp_pos _
  rw [similarity_flow_eq, ← heatConv_congr_ae _ (hV s')]
  exact (velocityCov_holds.2 _ hμ _).trans (dilateField_congr_ae hμ (hv _ (one_sub_exp_pos hss) (w s')))

theorem duhamel_part_ae (bk : BilinKernel) {w : ℝ → X} {W : ℝ → Space → Space} (hV : IsVelocityOf w W)
    {σ s : ℝ} (hσ : σ < s) :
    (velocity (realization.F.Ks (s - σ) (w σ) (w σ)) : Space → Space) =ᵐ[volume]
      fun y => dilateField (Real.exp (-(s - σ)))
        (fun x => -kernelConv (1 - Real.exp (-(s - σ))) (tensorField (W σ) (W σ)) x) y := by
  have hμσ : 0 < Real.exp (-(s - σ)) := Real.exp_pos _
  have e1 := velocityCov_holds.2 _ hμσ (bilinX (1 - Real.exp (-(s - σ))) (w σ) (w σ))
  have e2 := dilateField_congr_ae hμσ (bk _ (one_sub_exp_pos hσ) (w σ))
  have e3 := kernelConv_congr_ae (1 - Real.exp (-(s - σ))) (hV σ)
  rw [similarity_bilin_eq]
  refine e1.trans (e2.trans (Eventually.of_forall fun y => ?_))
  simp only [dilateField, e3]

end Internal.DuhamelVelocity

open Internal.DuhamelVelocity in
theorem duhamelVelocityAE_holds (hv : HeatVelocity) (bk : BilinKernel) (hI6 : IntervalIntegralL6)
    (lM : LerayKernelMeasurable) (_hsup : KernelConvSup) : DuhamelVelocityAE := by
  intro w P R W q hO hS hV s' s hss
  have hcont : Continuous (fun p : ℝ × Space => W p.1 p.2) := hS.smooth_field.continuous
  obtain ⟨hint, hflow⟩ := hO.flow s' s hss.le
  have hfi : IntervalIntegrable (fun σ => velocity (realization.F.Ks (s - σ) (w σ) (w σ))) volume s' s :=
    ⟨(velocity : X →L[ℝ] L6R).integrable_comp hint.1, (velocity : X →L[ℝ] L6R).integrable_comp hint.2⟩
  have hvel : velocity (w s) = velocity (realization.F.S (s - s') (w s')) +
      ∫ σ in s'..s, velocity (realization.F.Ks (s - σ) (w σ) (w σ)) := by
    rw [ContinuousLinearMap.intervalIntegral_comp_comm _ hint, ← map_add, ← hflow]
  have hDu := hI6 (fun σ => velocity (realization.F.Ks (s - σ) (w σ) (w σ))) s' s hss.le hfi
    (fun σ y => dilateField (Real.exp (-(s - σ)))
      (fun x => -kernelConv (1 - Real.exp (-(s - σ))) (tensorField (W σ) (W σ)) x) y)
    (duhamelIntegrand_measurable lM W hcont s) (fun σ hσ => duhamel_part_ae bk hV hσ.2)
  have hadd := Lp.coeFn_add (velocity (realization.F.S (s - s') (w s')))
    (∫ σ in s'..s, velocity (realization.F.Ks (s - σ) (w σ) (w σ)))
  rw [← hvel] at hadd
  filter_upwards [(hV s).symm, hadd, heat_part_ae hv hV hss, hDu] with y h1 h2 h3 h4
  rw [h1, h2, Pi.add_apply, h3, h4]
  rfl

end Breakdown.FarField
