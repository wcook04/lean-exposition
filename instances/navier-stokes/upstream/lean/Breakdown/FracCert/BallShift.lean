import Breakdown.FracCert.ProductCompact
import Breakdown.Cert.SpaceModulus

open scoped ContDiff ENNReal Topology Convolution
open MeasureTheory Real Filter Set

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace BallShiftInternal

open Breakdown.Cert.Internal.SpaceModulus

theorem average_sq_le (p : Space → ℝ) (f : Space → Space) (hp0 : ∀ t, 0 ≤ p t)
    (hpi : Integrable p) (hp1 : ∫ t, p t = 1) :
    ENNReal.ofReal (‖∫ t, p t • f t‖ ^ 2) ≤ ∫⁻ t, ENNReal.ofReal (p t * ‖f t‖ ^ 2) := by
  by_cases hi : Integrable (fun t => p t • f t)
  · set D := ∫ t, p t • f t with hD
    set g : Space → ℝ := fun t => 2 * inner ℝ D (p t • f t) - p t * ‖D‖ ^ 2 with hg
    have hgi1 : Integrable (fun t => 2 * inner ℝ D (p t • f t)) := (hi.const_inner D).const_mul 2
    have hgi : Integrable g := hgi1.sub (hpi.mul_const _)
    have hgint : ∫ t, g t = ‖D‖ ^ 2 := by
      rw [integral_sub hgi1 (hpi.mul_const _), integral_const_mul, integral_inner hi, ← hD,
        integral_mul_const, hp1, real_inner_self_eq_norm_sq]
      ring
    have hpt : ∀ t, g t ≤ p t * ‖f t‖ ^ 2 := by
      intro t
      simp only [hg, inner_smul_right]
      have h1 := real_inner_le_norm D (f t)
      have h2 := hp0 t
      nlinarith [mul_le_mul_of_nonneg_left (two_mul_le_add_sq ‖D‖ ‖f t‖) h2,
        mul_le_mul_of_nonneg_left h1 h2]
    calc ENNReal.ofReal (‖D‖ ^ 2) = ENNReal.ofReal (∫ t, g t) := by rw [hgint]
      _ ≤ ENNReal.ofReal (∫ t, max (g t) 0) :=
          ENNReal.ofReal_le_ofReal (integral_mono hgi hgi.pos_part fun t => le_max_left _ _)
      _ = ∫⁻ t, ENNReal.ofReal (max (g t) 0) :=
          ofReal_integral_eq_lintegral_ofReal hgi.pos_part (ae_of_all _ fun t => le_max_right _ _)
      _ ≤ ∫⁻ t, ENNReal.ofReal (p t * ‖f t‖ ^ 2) :=
          lintegral_mono fun t => ENNReal.ofReal_le_ofReal
            (max_le (hpt t) (mul_nonneg (hp0 t) (sq_nonneg _)))
  · rw [integral_undef hi]
    simp

theorem sum_three_le (f : Fin 3 → Space → ℝ≥0∞) :
    ∑ i : Fin 3, ∫⁻ t, f i t ≤ ∫⁻ t, ∑ i : Fin 3, f i t := by
  simp only [Fin.sum_univ_three]
  exact (add_le_add (le_lintegral_add _ _) le_rfl).trans (le_lintegral_add _ _)


theorem deriv_eq (u : Space → Space) (K : Space → (Space →L[ℝ] Space)) (R : ℝ)
    (hwk : IsWeakGradientOf u K) (ρ : Space → ℝ) (hρc : ContDiff ℝ ∞ ρ) (hρs : HasCompactSupport ρ)
    (hρt : tsupport ρ ⊆ Metric.ball (0 : Space) 1)
    (hw : LocallyIntegrable ((Metric.ball (0 : Space) (R + 2)).indicator u) volume)
    (x : Space) (hx : ‖x‖ ≤ R + 1) (j : Fin 3) :
    fderiv ℝ ((Metric.ball (0 : Space) (R + 2)).indicator u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] ρ) x
      (unitVector j) = ∫ t, ρ (x - t) • K t (unitVector j) := by
  set w := (Metric.ball (0 : Space) (R + 2)).indicator u with hw_def
  set L : Space →L[ℝ] ℝ →L[ℝ] Space := (ContinuousLinearMap.lsmul ℝ ℝ).flip with hL
  have hd := hρs.hasFDerivAt_convolution_right L hw (hρc.of_le (by simp)) x
  rw [hd.fderiv, convolution_precompR_apply L hw (hρs.fderiv (𝕜 := ℝ)) (hρc.continuous_fderiv (by simp)) x
    (unitVector j), convolution_def]
  have hψc : ContDiff ℝ ∞ (fun s => ρ (x - s)) := hρc.comp (contDiff_const.sub contDiff_id)
  have hψs : HasCompactSupport (fun s => ρ (x - s)) := hρs.comp_homeomorph (Homeomorph.subLeft x)
  have hψd : ∀ t, fderiv ℝ (fun s => ρ (x - s)) t (unitVector j) = -fderiv ℝ ρ (x - t) (unitVector j) := by
    intro t
    have h1 : HasFDerivAt (fun s => ρ (x - s))
        ((fderiv ℝ ρ (x - t)).comp (-(ContinuousLinearMap.id ℝ Space))) t :=
      ((hρc.differentiable (by simp)) (x - t)).hasFDerivAt.comp t ((hasFDerivAt_id t).const_sub x)
    rw [h1.fderiv]
    simp
  have hid := hwk (fun s => ρ (x - s)) ⟨hψc, hψs⟩ j
  have hpt : ∀ t, L (w t) (fderiv ℝ ρ (x - t) (unitVector j)) =
      -(fderiv ℝ (fun s => ρ (x - s)) t (unitVector j) • u t) := by
    intro t
    rw [hψd t, neg_smul, neg_neg]
    simp only [hL, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply]
    by_cases ht : t ∈ Metric.ball (0 : Space) (R + 2)
    · rw [hw_def, indicator_of_mem ht]
    · have hz : fderiv ℝ ρ (x - t) = 0 := by
        have hn : x - t ∉ tsupport ρ := by
          intro hm
          have h1 := hρt hm
          rw [Metric.mem_ball, dist_zero_right] at h1
          rw [Metric.mem_ball, dist_zero_right, not_lt] at ht
          have h2 : ‖t‖ ≤ ‖x - t‖ + ‖x‖ := by
            have := norm_sub_le x (x - t)
            rw [sub_sub_cancel] at this
            linarith [norm_sub_rev x t]
          linarith
        exact Function.notMem_support.mp (fun hm => hn (support_fderiv_subset ℝ hm))
      rw [hz]
      simp
  simp_rw [hpt, integral_neg, hid, neg_neg]

theorem grad_sq_le (u : Space → Space) (K : Space → (Space →L[ℝ] Space)) (R : ℝ)
    (hwk : IsWeakGradientOf u K) (ρ : Space → ℝ) (hρc : ContDiff ℝ ∞ ρ) (hρs : HasCompactSupport ρ)
    (hρt : tsupport ρ ⊆ Metric.ball (0 : Space) 1) (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : ∫ z, ρ z = 1)
    (hw : LocallyIntegrable ((Metric.ball (0 : Space) (R + 2)).indicator u) volume)
    (x : Space) (hx : ‖x‖ ≤ R + 1) :
    ∑ j : Fin 3, ENNReal.ofReal (‖fderiv ℝ ((Metric.ball (0 : Space) (R + 2)).indicator u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] ρ) x
      (unitVector j)‖ ^ 2) ≤ ∫⁻ t, ENNReal.ofReal (ρ (x - t) * entrySq (K t)) := by
  have hpi : Integrable (fun t => ρ (x - t)) :=
    (hρc.continuous.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (hρs.comp_homeomorph (Homeomorph.subLeft x))
  have hp1 : ∫ t, ρ (x - t) = 1 := by rw [integral_sub_left_eq_self, hρ1]
  calc ∑ j : Fin 3, ENNReal.ofReal (‖fderiv ℝ ((Metric.ball (0 : Space) (R + 2)).indicator u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] ρ) x
      (unitVector j)‖ ^ 2)
      ≤ ∑ j : Fin 3, ∫⁻ t, ENNReal.ofReal (ρ (x - t) * ‖K t (unitVector j)‖ ^ 2) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [deriv_eq u K R hwk ρ hρc hρs hρt hw x hx j]
        exact average_sq_le _ _ (fun t => hρ0 _) hpi hp1
    _ ≤ ∫⁻ t, ∑ j : Fin 3, ENNReal.ofReal (ρ (x - t) * ‖K t (unitVector j)‖ ^ 2) :=
        sum_three_le _
    _ = ∫⁻ t, ENNReal.ofReal (ρ (x - t) * entrySq (K t)) := by
        congr 1
        funext t
        rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hρ0 _) (sq_nonneg _)),
          ← Finset.mul_sum]
        rfl

theorem smooth_ball_le (u : Space → Space) (K : Space → (Space →L[ℝ] Space)) (R : ℝ)
    (hwk : IsWeakGradientOf u K) (ρ : Space → ℝ) (hρc : ContDiff ℝ ∞ ρ) (hρs : HasCompactSupport ρ)
    (hρt : tsupport ρ ⊆ Metric.ball (0 : Space) 1) (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : ∫ z, ρ z = 1)
    (hw : LocallyIntegrable ((Metric.ball (0 : Space) (R + 2)).indicator u) volume)
    (E : Space → ℝ) (hEm : Measurable E) (hEe : ∀ᵐ t, entrySq (K t) = E t)
    (h : Space) (hh : ‖h‖ ≤ 1) :
    ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖((Metric.ball (0 : Space) (R + 2)).indicator u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] ρ) (y + h) -
        ((Metric.ball (0 : Space) (R + 2)).indicator u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] ρ) y‖ ^ 2) ≤
      ENNReal.ofReal (‖h‖ ^ 2) * ∫⁻ t, ENNReal.ofReal (E t) := by
  set φ := (Metric.ball (0 : Space) (R + 2)).indicator u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] ρ
    with hφ
  have hφc : ContDiff ℝ ∞ φ := hρs.contDiff_convolution_right _ hw hρc
  have hρi : Integrable ρ := hρc.continuous.integrable_of_hasCompactSupport hρs
  set c : ℝ≥0∞ := ENNReal.ofReal (‖h‖ ^ 2) with hc
  set M : Space → ℝ≥0∞ := fun x => ∫⁻ t, ENNReal.ofReal (ρ (x - t) * E t) with hM
  have hFm : Measurable (fun p : Space × Space => ENNReal.ofReal (ρ (p.1 - p.2) * E p.2)) :=
    ENNReal.measurable_ofReal.comp
      ((hρc.continuous.measurable.comp (measurable_fst.sub measurable_snd)).mul
        (hEm.comp measurable_snd))
  have hMm : Measurable M := hFm.lintegral_prod_right'
  have hgrad : ∀ x : Space, ‖x‖ ≤ R + 1 → ENNReal.ofReal (‖fderiv ℝ φ x h‖ ^ 2) ≤ c * M x := by
    intro x hx
    have h1 := grad_sq_le u K R hwk ρ hρc hρs hρt hρ0 hρ1 hw x hx
    have h2 : ∫⁻ t, ENNReal.ofReal (ρ (x - t) * entrySq (K t)) = M x :=
      lintegral_congr_ae (hEe.mono fun t ht => by dsimp only; rw [ht])
    rw [h2] at h1
    calc ENNReal.ofReal (‖fderiv ℝ φ x h‖ ^ 2)
        ≤ ENNReal.ofReal (‖h‖ ^ 2 * ∑ i : Fin 3, ‖fderiv ℝ φ x (unitVector i)‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (norm_apply_sq_le _ _)
      _ = c * ∑ i : Fin 3, ENNReal.ofReal (‖fderiv ℝ φ x (unitVector i)‖ ^ 2) := by
          rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
      _ ≤ c * M x := by gcongr
  have hpt : ∀ y ∈ Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖φ (y + h) - φ y‖ ^ 2) ≤
      ∫⁻ t in Ioc (0 : ℝ) 1, c * M (y + t • h) := by
    intro y hy
    have hD : Continuous (fderiv ℝ φ) := hφc.continuous_fderiv (by simp)
    have hcy : Continuous (fun t : ℝ => fderiv ℝ φ (y + t • h) h) :=
      (hD.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
    have h1 := norm_intervalIntegral_sq_le hcy
    rw [← sub_eq_intervalIntegral hφc y h, intervalIntegral.integral_of_le zero_le_one] at h1
    calc ENNReal.ofReal (‖φ (y + h) - φ y‖ ^ 2)
        ≤ ENNReal.ofReal (∫ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (y + t • h) h‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal h1
      _ = ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (‖fderiv ℝ φ (y + t • h) h‖ ^ 2) :=
          ofReal_integral_eq_lintegral_ofReal (hcy.norm.pow 2).integrableOn_Ioc
            (ae_of_all _ fun t => sq_nonneg _)
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, c * M (y + t • h) := by
          refine setLIntegral_mono' measurableSet_Ioc fun t ht => hgrad _ ?_
          rw [Metric.mem_closedBall, dist_zero_right] at hy
          have ht1 : t * ‖h‖ ≤ 1 := by nlinarith [ht.1, ht.2, norm_nonneg h]
          calc ‖y + t • h‖ ≤ ‖y‖ + ‖t • h‖ := norm_add_le _ _
            _ = ‖y‖ + t * ‖h‖ := by rw [norm_smul, Real.norm_of_nonneg ht.1.le]
            _ ≤ R + 1 := by linarith
  have hMint : ∫⁻ x, M x = ∫⁻ t, ENNReal.ofReal (E t) := by
    rw [hM]
    simp only
    rw [lintegral_lintegral_swap hFm.aemeasurable]
    congr 1
    funext t
    calc ∫⁻ x, ENNReal.ofReal (ρ (x - t) * E t)
        = ∫⁻ x, ENNReal.ofReal (ρ (x - t)) * ENNReal.ofReal (E t) := by
          congr 1
          funext x
          rw [ENNReal.ofReal_mul (hρ0 _)]
      _ = (∫⁻ x, ENNReal.ofReal (ρ (x - t))) * ENNReal.ofReal (E t) :=
          lintegral_mul_const _
            (ENNReal.measurable_ofReal.comp (hρc.continuous.measurable.comp (measurable_id.sub_const t)))
      _ = ENNReal.ofReal (E t) := by
          rw [lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (ρ x)) t,
            ← ofReal_integral_eq_lintegral_ofReal hρi (ae_of_all _ hρ0), hρ1, ENNReal.ofReal_one,
            one_mul]
  have hGm : AEMeasurable (Function.uncurry fun (y : Space) (t : ℝ) => c * M (y + t • h))
      ((volume : Measure Space).prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
    (measurable_const.mul (hMm.comp (measurable_fst.add (measurable_snd.smul_const h)))).aemeasurable
  calc ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖φ (y + h) - φ y‖ ^ 2)
      ≤ ∫⁻ y in Metric.closedBall (0 : Space) R, ∫⁻ t in Ioc (0 : ℝ) 1, c * M (y + t • h) :=
        setLIntegral_mono' Metric.isClosed_closedBall.measurableSet hpt
    _ ≤ ∫⁻ y, ∫⁻ t in Ioc (0 : ℝ) 1, c * M (y + t • h) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y, c * M (y + t • h) := lintegral_lintegral_swap hGm
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y, c * M y := by
        congr 1
        funext t
        exact lintegral_add_right_eq_self (fun y => c * M y) (t • h)
    _ = ∫⁻ y, c * M y := by
        rw [setLIntegral_const, Real.volume_Ioc]
        simp
    _ = c * ∫⁻ y, M y := lintegral_const_mul _ hMm
    _ = c * ∫⁻ t, ENNReal.ofReal (E t) := by rw [hMint]

end BallShiftInternal

open BallShiftInternal in
theorem ballShift : BallShiftStatement := by
  intro u K R hum hwk hui hKi h hh
  set V := Metric.ball (0 : Space) (R + 2) with hV
  have hmem : MemLp u 2 (volume.restrict V) :=
    (memLp_two_iff_integrable_sq_norm hum.restrict).2 hui
  have : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : IntegrableOn u V := hmem.integrable one_le_two
  have hw : LocallyIntegrable (V.indicator u) volume :=
    ((integrable_indicator_iff measurableSet_ball).2 hint).locallyIntegrable
  set E : Space → ℝ := hKi.1.mk _ with hE
  have hEm : Measurable E := hKi.1.stronglyMeasurable_mk.measurable
  have hEe : ∀ᵐ t, entrySq (K t) = E t := hKi.1.ae_eq_mk
  let b : ℕ → ContDiffBump (0 : Space) := fun n =>
    ⟨1 / ((n : ℝ) + 1) / 4, 1 / ((n : ℝ) + 1) / 2, by positivity, by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith⟩
  have hrout : ∀ n, (b n).rOut < 1 := by
    intro n
    show 1 / ((n : ℝ) + 1) / 2 < 1
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  have hlim0 : Tendsto (fun n => (b n).rOut) atTop (𝓝 0) := by
    show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) / 2) atTop (𝓝 0)
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2 : ℝ)
    rw [zero_div] at h0
    exact h0
  have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    (φ := b) (l := atTop) (K := 2) hlim0 (Eventually.of_forall fun n => by
      show 1 / ((n : ℝ) + 1) / 2 ≤ 2 * (1 / ((n : ℝ) + 1) / 4)
      linarith) hw
  set L : Space →L[ℝ] ℝ →L[ℝ] Space := (ContinuousLinearMap.lsmul ℝ ℝ).flip with hL
  set φ : ℕ → Space → Space := fun n => V.indicator u ⋆[L, volume] (b n).normed volume with hφ
  have hae : ∀ᵐ y, Tendsto (fun n => φ n y) atTop (𝓝 (V.indicator u y)) := by
    filter_upwards [hconv] with y hy
    refine hy.congr fun n => ?_
    rw [hφ, hL]
    simp only
    rw [convolution_flip]
  have hB := (measurePreserving_add_right (volume : Measure Space) h).quasiMeasurePreserving.ae hae
  have hρc : ∀ n, ContDiff ℝ ∞ ((b n).normed volume) := fun n => (b n).contDiff_normed
  have hρt : ∀ n, tsupport ((b n).normed volume) ⊆ Metric.ball (0 : Space) 1 := fun n => by
    rw [ContDiffBump.tsupport_normed_eq]
    exact Metric.closedBall_subset_ball (hrout n)
  have hbound : ∀ n, ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖φ n (y + h) - φ n y‖ ^ 2) ≤
        ENNReal.ofReal (‖h‖ ^ 2) * ∫⁻ t, ENNReal.ofReal (E t) := fun n =>
    smooth_ball_le u K R hwk ((b n).normed volume) (hρc n) (b n).hasCompactSupport_normed (hρt n)
      (b n).nonneg_normed (b n).integral_normed hw E hEm hEe h hh
  have hφc : ∀ n, Continuous (φ n) := fun n =>
    ((b n).hasCompactSupport_normed.contDiff_convolution_right L hw (hρc n)).continuous
  have hlim : ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) R)),
      Tendsto (fun n => ENNReal.ofReal (‖φ n (y + h) - φ n y‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (‖u (y + h) - u y‖ ^ 2))) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_of_ae hB,
      ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with y h1 h2 hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    have e1 : V.indicator u y = u y := by
      refine indicator_of_mem ?_ _
      rw [hV, Metric.mem_ball, dist_zero_right]
      linarith
    have e2 : V.indicator u (y + h) = u (y + h) := by
      refine indicator_of_mem ?_ _
      rw [hV, Metric.mem_ball, dist_zero_right]
      linarith [norm_add_le y h]
    rw [e1] at h1
    rw [e2] at h2
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((h2.sub h1).norm.pow 2)
  have hmeas : ∀ n, AEMeasurable (fun y => ENNReal.ofReal (‖φ n (y + h) - φ n y‖ ^ 2))
      (volume.restrict (Metric.closedBall (0 : Space) R)) := fun n =>
    (ENNReal.continuous_ofReal.comp
      ((((hφc n).comp (continuous_id.add continuous_const)).sub (hφc n)).norm.pow 2)).measurable.aemeasurable
  have hEint : ∫⁻ t, ENNReal.ofReal (E t) = ENNReal.ofReal (∫ y, entrySq (K y)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hKi (ae_of_all _ fun y =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact lintegral_congr_ae (hEe.mono fun t ht => by dsimp only; rw [ht])
  calc ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖u (y + h) - u y‖ ^ 2)
      = ∫⁻ y in Metric.closedBall (0 : Space) R,
          liminf (fun n => ENNReal.ofReal (‖φ n (y + h) - φ n y‖ ^ 2)) atTop :=
        lintegral_congr_ae (hlim.mono fun y hy => hy.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ y in Metric.closedBall (0 : Space) R,
          ENNReal.ofReal (‖φ n (y + h) - φ n y‖ ^ 2)) atTop := lintegral_liminf_le' hmeas
    _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal (‖h‖ ^ 2) * ∫⁻ t, ENNReal.ofReal (E t)) atTop :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = ENNReal.ofReal (‖h‖ ^ 2) * ∫⁻ t, ENNReal.ofReal (E t) := liminf_const _
    _ = ENNReal.ofReal (‖h‖ ^ 2 * ∫ y, entrySq (K y)) := by
        rw [hEint, ENNReal.ofReal_mul (sq_nonneg _)]

end SteadyCert

end Breakdown
