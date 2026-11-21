import Breakdown.Defs

open MeasureTheory Set Metric

noncomputable section

namespace Breakdown.CertCell.AnnihilatorGradient.Internal

def radialPotential (F : Space → Space) (x : Space) : ℝ :=
  ∫ t in (0 : ℝ)..1, inner ℝ (F (t • x)) x

def radialDeriv (F : Space → Space) (x : Space) (t : ℝ) : Space →L[ℝ] ℝ :=
  t • ((innerSL ℝ x).comp (fderiv ℝ F (t • x))) + innerSL ℝ (F (t • x))

theorem hasFDerivAt_radial_integrand {F : Space → Space} (hF : ContDiff ℝ 1 F) (t : ℝ) (x : Space) :
    HasFDerivAt (fun y => inner ℝ (F (t • y)) y) (radialDeriv F x t) x := by
  have h1 : HasFDerivAt (fun y : Space => F (t • y))
      ((fderiv ℝ F (t • x)).comp (t • ContinuousLinearMap.id ℝ Space)) x :=
    ((hF.differentiable one_ne_zero) (t • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul t)
  have h2 := h1.inner ℝ (hasFDerivAt_id x)
  refine h2.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp [radialDeriv, fderivInnerCLM_apply, inner_smul_left]
  rw [real_inner_comm x]
  ring

theorem continuous_radialDeriv {F : Space → Space} (hF : ContDiff ℝ 1 F) (x : Space) :
    Continuous (radialDeriv F x) := by
  have hd : Continuous (fun t : ℝ => fderiv ℝ F (t • x)) :=
    (hF.continuous_fderiv one_ne_zero).comp (continuous_id.smul continuous_const)
  have hv : Continuous (fun t : ℝ => F (t • x)) := hF.continuous.comp (continuous_id.smul continuous_const)
  unfold radialDeriv
  exact (continuous_id.smul (continuous_const.clm_comp hd)).add ((innerSL ℝ).continuous.comp hv)

theorem hasFDerivAt_radialPotential {F : Space → Space} (hF : ContDiff ℝ 1 F)
    (hs : ∀ z v w, inner ℝ (fderiv ℝ F z v) w = inner ℝ (fderiv ℝ F z w) v) (x : Space) :
    HasFDerivAt (radialPotential F) (innerSL ℝ (F x)) x := by
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : Space) (‖x‖ + 1)).exists_bound_of_continuousOn
    hF.continuous.continuousOn
  obtain ⟨M1, hStrain⟩ := (isCompact_closedBall (0 : Space) (‖x‖ + 1)).exists_bound_of_continuousOn
    (hF.continuous_fderiv one_ne_zero).continuousOn
  have key : HasFDerivAt (radialPotential F) (∫ t in (0 : ℝ)..1, radialDeriv F x t) x := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (bound := fun _ => (‖x‖ + 1) * M1 + M0) (ball_mem_nhds x one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun y =>
        ((hF.continuous.comp (continuous_id.smul continuous_const)).inner continuous_const).aestronglyMeasurable
    · exact ((hF.continuous.comp (continuous_id.smul continuous_const)).inner continuous_const).intervalIntegrable _ _
    · exact (continuous_radialDeriv hF x).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t ht y hy => ?_
      have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa [uIoc_of_le zero_le_one] using ht
      have hy' : ‖y‖ ≤ ‖x‖ + 1 := by
        have := mem_ball_iff_norm.mp hy
        have h3 := norm_le_norm_add_norm_sub' y x
        linarith [norm_sub_rev y x]
      have hty : t • y ∈ closedBall (0 : Space) (‖x‖ + 1) := by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht'.1.le]
        nlinarith [ht'.1, ht'.2, norm_nonneg y]
      have hA := hM0 _ hty
      have hB := hStrain _ hty
      unfold radialDeriv
      calc ‖t • ((innerSL ℝ y).comp (fderiv ℝ F (t • y))) + innerSL ℝ (F (t • y))‖
          ≤ ‖t • ((innerSL ℝ y).comp (fderiv ℝ F (t • y)))‖ + ‖innerSL ℝ (F (t • y))‖ := norm_add_le _ _
        _ ≤ 1 * (‖y‖ * ‖fderiv ℝ F (t • y)‖) + ‖F (t • y)‖ := by
            gcongr
            · rw [norm_smul, Real.norm_of_nonneg ht'.1.le]
              gcongr
              · exact ht'.2
              · calc ‖(innerSL ℝ y).comp (fderiv ℝ F (t • y))‖ ≤ ‖innerSL ℝ y‖ * ‖fderiv ℝ F (t • y)‖ :=
                    ContinuousLinearMap.opNorm_comp_le _ _
                  _ = ‖y‖ * ‖fderiv ℝ F (t • y)‖ := by rw [innerSL_apply_norm]
            · rw [innerSL_apply_norm]
        _ ≤ (‖x‖ + 1) * M1 + M0 := by
            have hM1p : 0 ≤ M1 := (norm_nonneg _).trans hB
            nlinarith [norm_nonneg (fderiv ℝ F (t • y)), norm_nonneg y]
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t _ y _ => hasFDerivAt_radial_integrand hF t y
  refine key.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  rw [ContinuousLinearMap.intervalIntegral_apply ((continuous_radialDeriv hF x).intervalIntegrable _ _)]
  have hder : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s * inner ℝ (F (s • x)) v)
      (inner ℝ (F (t • x)) v + t * inner ℝ (fderiv ℝ F (t • x) x) v) t := by
    intro t
    have hc : HasDerivAt (fun s : ℝ => s • x) x t := by simpa using (hasDerivAt_id t).smul_const x
    have hF1 : HasDerivAt (fun s : ℝ => F (s • x)) (fderiv ℝ F (t • x) x) t :=
      ((hF.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t hc
    have hi : HasDerivAt (fun s : ℝ => inner ℝ (F (s • x)) v) (inner ℝ (fderiv ℝ F (t • x) x) v) t := by
      simpa using hF1.inner ℝ (hasDerivAt_const t v)
    have h := (hasDerivAt_id' t).mul hi
    rw [one_mul] at h
    exact h
  have hcont : Continuous (fun t : ℝ => inner ℝ (F (t • x)) v + t * inner ℝ (fderiv ℝ F (t • x) x) v) := by
    have hv : Continuous (fun t : ℝ => F (t • x)) := hF.continuous.comp (continuous_id.smul continuous_const)
    have hd : Continuous (fun t : ℝ => fderiv ℝ F (t • x)) :=
      (hF.continuous_fderiv one_ne_zero).comp (continuous_id.smul continuous_const)
    exact (hv.inner continuous_const).add (continuous_id.mul ((hd.clm_apply continuous_const).inner continuous_const))
  have hint : ∫ t in (0 : ℝ)..1, radialDeriv F x t v
      = ∫ t in (0 : ℝ)..1, (inner ℝ (F (t • x)) v + t * inner ℝ (fderiv ℝ F (t • x) x) v) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [radialDeriv, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
    rw [real_inner_comm (fderiv ℝ F (t • x) v) x, hs]
    ring
  rw [hint, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) (hcont.intervalIntegrable _ _)]
  simp

theorem continuous_radialPotential {F : Space → Space} (hF : ContDiff ℝ 1 F)
    (hs : ∀ z v w, inner ℝ (fderiv ℝ F z v) w = inner ℝ (fderiv ℝ F z w) v) :
    Continuous (radialPotential F) :=
  continuous_iff_continuousAt.2 fun y => (hasFDerivAt_radialPotential hF hs y).continuousAt

theorem radialPotential_shift {F : Space → Space} (hF : ContDiff ℝ 1 F)
    (hs : ∀ z v w, inner ℝ (fderiv ℝ F z v) w = inner ℝ (fderiv ℝ F z w) v) (a x : Space) :
    ∫ t in (0 : ℝ)..1, inner ℝ (F (a + t • (x - a))) (x - a) = radialPotential F x - radialPotential F a := by
  set G : Space → Space := fun y => F (a + y) with hGdef
  have hGd : ∀ y, HasFDerivAt G (fderiv ℝ F (a + y)) y := fun y => by
    have := ((hF.differentiable one_ne_zero) (a + y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_add a)
    exact this.congr_fderiv (ContinuousLinearMap.comp_id _)
  have hG : ContDiff ℝ 1 G := hF.comp (contDiff_const.add contDiff_id)
  have hGs : ∀ z v w, inner ℝ (fderiv ℝ G z v) w = inner ℝ (fderiv ℝ G z w) v := by
    intro z v w
    rw [(hGd z).fderiv]
    exact hs _ v w
  have hD : ∀ y, HasFDerivAt (fun y => radialPotential G (y - a) - radialPotential F y) (0 : Space →L[ℝ] ℝ) y := by
    intro y
    have h1 := (hasFDerivAt_radialPotential hG hGs (y - a)).comp y ((hasFDerivAt_id y).sub_const a)
    have h2 := hasFDerivAt_radialPotential hF hs y
    refine (h1.sub h2).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [G]
  have hconst := is_const_of_fderiv_eq_zero (fun y => (hD y).differentiableAt) (fun y => (hD y).fderiv) x a
  have h0 : radialPotential G 0 = 0 := by simp [radialPotential]
  simp only [sub_self, h0] at hconst
  have : radialPotential G (x - a) = ∫ t in (0 : ℝ)..1, inner ℝ (F (a + t • (x - a))) (x - a) := rfl
  linarith

def avgPotential (F : Space → Space) (x : Space) : ℝ :=
  ∫ z in closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1, inner ℝ (F (z.1 + z.2 • (x - z.1))) (x - z.1)

theorem avgPotential_eq {F : Space → Space} (hF : ContDiff ℝ 1 F)
    (hs : ∀ z v w, inner ℝ (fderiv ℝ F z v) w = inner ℝ (fderiv ℝ F z w) v) (x : Space) :
    avgPotential F x = volume.real (closedBall (0 : Space) 1) * radialPotential F x
      - ∫ a in closedBall (0 : Space) 1, radialPotential F a := by
  have hFc : Continuous F := hF.continuous
  have hcont : Continuous (fun z : Space × ℝ => inner ℝ (F (z.1 + z.2 • (x - z.1))) (x - z.1)) := by
    fun_prop
  have hint : IntegrableOn (fun z : Space × ℝ => inner ℝ (F (z.1 + z.2 • (x - z.1))) (x - z.1))
      (closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1) (volume.prod volume) :=
    (hcont.continuousOn.integrableOn_compact ((isCompact_closedBall _ _).prod isCompact_Icc)).mono_set
      (prod_mono le_rfl Ioc_subset_Icc_self)
  have hrad := continuous_radialPotential hF hs
  rw [avgPotential, Measure.volume_eq_prod, setIntegral_prod _ hint]
  have h1 : ∀ a, ∫ t in Ioc (0 : ℝ) 1, inner ℝ (F (a + t • (x - a))) (x - a)
      = radialPotential F x - radialPotential F a := by
    intro a
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact radialPotential_shift hF hs a x
  simp_rw [h1]
  rw [integral_sub (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
    (hrad.continuousOn.integrableOn_compact (isCompact_closedBall _ _)), setIntegral_const, smul_eq_mul]

theorem integrable_mul_of_support {f g : Space → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun x => f x * g x) :=
  (hf.mul hg).integrable_of_hasCompactSupport hgc.mul_left

theorem avgPotential_weak {F : Space → Space} (hF : ContDiff ℝ 1 F)
    (hs : ∀ z v w, inner ℝ (fderiv ℝ F z v) w = inner ℝ (fderiv ℝ F z w) v)
    {φ : Space → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (v : Space) :
    ∫ x, fderiv ℝ φ x v * avgPotential F x
      = -(volume.real (closedBall (0 : Space) 1) * ∫ x, φ x * inner ℝ (F x) v) := by
  have hd := hasFDerivAt_radialPotential hF hs
  have hrad := continuous_radialPotential hF hs
  have hφ' : Continuous (fun x => fderiv ℝ φ x v) := (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hφ'c : HasCompactSupport (fun x => fderiv ℝ φ x v) := hφc.fderiv_apply ℝ v
  have hfd : ∀ x, fderiv ℝ (radialPotential F) x v = inner ℝ (F x) v := fun x => by
    rw [(hd x).fderiv]
    simp
  have hFv : Continuous (fun x => inner ℝ (F x) v) := hF.continuous.inner continuous_const
  have ibp1 : ∫ x, radialPotential F x * fderiv ℝ φ x v = -∫ x, φ x * inner ℝ (F x) v := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := radialPotential F) (g := φ) (v := v)
      (μ := volume) (by simp_rw [hfd]; exact integrable_mul_of_support hFv hφ.continuous hφc)
      (integrable_mul_of_support hrad hφ' hφ'c) (integrable_mul_of_support hrad hφ.continuous hφc)
      (fun x _ => (hd x).differentiableAt) (fun x _ => hφ.differentiable one_ne_zero x)
    rw [h]
    simp_rw [hfd, mul_comm (inner ℝ _ _)]
  have ibp2 : ∫ x, fderiv ℝ φ x v = 0 := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := fun _ : Space => (1 : ℝ)) (g := φ) (v := v)
      (μ := volume) (by simp)
      (integrable_mul_of_support continuous_const hφ' hφ'c)
      (integrable_mul_of_support continuous_const hφ.continuous hφc)
      (fun x _ => differentiableAt_const _) (fun x _ => hφ.differentiable one_ne_zero x)
    simp at h
    exact h
  have he : (fun x => fderiv ℝ φ x v * avgPotential F x) = fun x =>
      volume.real (closedBall (0 : Space) 1) * (radialPotential F x * fderiv ℝ φ x v)
        - (∫ a in closedBall (0 : Space) 1, radialPotential F a) * fderiv ℝ φ x v := by
    funext x
    rw [avgPotential_eq hF hs x]
    ring
  rw [he, integral_sub ((integrable_mul_of_support hrad hφ' hφ'c).const_mul _)
    ((hφ'.integrable_of_hasCompactSupport hφ'c).const_mul _), integral_const_mul, integral_const_mul, ibp1, ibp2]
  ring

end Breakdown.CertCell.AnnihilatorGradient.Internal
