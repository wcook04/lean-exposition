import Breakdown.Cert.CoerciveSmoothApproxKernel
import Breakdown.Cert.TranslationCriterion

open scoped ContDiff ENNReal Topology Convolution
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothApprox

theorem sq_lintegral_mul_le_prod {X : Type*} [MeasurableSpace X] {μ : Measure X} {A B : X → ℝ≥0∞}
    (hA : AEMeasurable A μ) (hB : AEMeasurable B μ) :
    (∫⁻ x, A x * B x ∂μ) ^ 2 ≤ (∫⁻ x, A x ∂μ) * ∫⁻ x, A x * B x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun x => A x ^ (1 / 2 : ℝ)) (g := fun x => A x ^ (1 / 2 : ℝ) * B x) (hA.pow_const _)
    ((hA.pow_const _).mul hB)
  have e1 : ∀ x, A x ^ (1 / 2 : ℝ) * (A x ^ (1 / 2 : ℝ) * B x) = A x * B x := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ x, (A x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = A x := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  have e3 : ∀ x, (A x ^ (1 / 2 : ℝ) * B x) ^ (2 : ℝ) = A x * B x ^ 2 := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2, ENNReal.rpow_two]
  simp only [Pi.mul_apply, e1, e2, e3] at h
  calc (∫⁻ x, A x * B x ∂μ) ^ 2
      ≤ ((∫⁻ x, A x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, A x * B x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ x, A x ∂μ) * ∫⁻ x, A x * B x ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

theorem period_convolution_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ × Space → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) {w : ℝ → Space → E}
    (hw : AEStronglyMeasurable (joint w) volume) (hper : IsTimePeriodic w) :
    periodLIntegral (fun σ y => ‖∫ t, φ t • joint w ((σ, y) - t)‖ ^ 2) ≤
      (∫⁻ t, ‖φ t‖ₑ) ^ 2 * periodLIntegral (fun σ y => ‖w σ y‖ ^ 2) := by
  have hH := volume_prod_invariantClass
  set F : ℝ × Space → ℝ≥0∞ := fun z => ENNReal.ofReal (‖joint w z‖ ^ 2) with hFdef
  have hF : AEMeasurable F volume := (hw.norm.aemeasurable.pow_const 2).ennreal_ofReal
  have hC : (∫⁻ t, ‖φ t‖ₑ) ≠ ⊤ := (hφ.integrable_of_hasCompactSupport hφc).2.ne
  have hpt : ∀ x : ℝ × Space, ENNReal.ofReal (‖∫ t, φ t • joint w (x - t)‖ ^ 2) ≤
      (∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ‖φ t‖ₑ * F (x - t) := by
    intro x
    have h1 : ‖∫ t, φ t • joint w (x - t)‖ₑ ≤ ∫⁻ t, ‖φ t‖ₑ * ‖joint w (x - t)‖ₑ :=
      (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (by simp only [enorm_smul]))
    have hm : AEMeasurable (fun t => ‖joint w (x - t)‖ₑ) volume :=
      hw.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x)
    calc ENNReal.ofReal (‖∫ t, φ t • joint w (x - t)‖ ^ 2) = ‖∫ t, φ t • joint w (x - t)‖ₑ ^ 2 := by
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ ≤ (∫⁻ t, ‖φ t‖ₑ * ‖joint w (x - t)‖ₑ) ^ 2 := by gcongr
      _ ≤ (∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ‖φ t‖ₑ * ‖joint w (x - t)‖ₑ ^ 2 :=
          sq_lintegral_mul_le_prod hφ.enorm.aemeasurable hm
      _ = (∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ‖φ t‖ₑ * F (x - t) := by
          simp only [hFdef, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hac : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) ≪ volume := by
    rw [Measure.volume_eq_prod (α := ℝ) (β := Space)]
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod
      Measure.AbsolutelyContinuous.rfl
  have hK0 : AEMeasurable (fun p : (ℝ × Space) × (ℝ × Space) => ‖φ p.2‖ₑ * F (p.1 - p.2))
      (volume.prod volume) :=
    (hφ.enorm.measurable.comp measurable_snd).aemeasurable.mul
      (hF.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  have hK : AEMeasurable (fun p : (ℝ × Space) × (ℝ × Space) => ‖φ p.2‖ₑ * F (p.1 - p.2))
      (((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)).prod volume) := hK0.mono_ac (hac.prod Measure.AbsolutelyContinuous.rfl)
  have hshift : ∀ t : ℝ × Space, ∫⁻ x, F (x - t) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) = periodLIntegral (fun σ y => ‖w σ y‖ ^ 2) := by
    intro t
    have hm : AEMeasurable (fun x => F (x - t)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
      (hF.comp_quasiMeasurePreserving (measurePreserving_sub_right (volume : Measure (ℝ × Space)) t).quasiMeasurePreserving).mono_ac
        hac
    refine (lintegral_prod _ hm).trans ?_
    unfold periodLIntegral
    have e1 : ∀ σ : ℝ, ∫⁻ y, F ((σ, y) - t) = ∫⁻ y, ENNReal.ofReal (‖w (σ + -t.1) y‖ ^ 2) := by
      intro σ
      have := lintegral_sub_right_eq_self (μ := (volume : Measure Space)) (fun y => ENNReal.ofReal (‖w (σ - t.1) y‖ ^ 2)) t.2
      simpa [hFdef, joint, sub_eq_add_neg] using this
    simp_rw [e1]
    exact Breakdown.Cert.Internal.TranslationCriterion.lintegral_Icc_add
      (fun σ => ∫⁻ y, ENNReal.ofReal (‖w σ y‖ ^ 2)) (fun σ => by simp only [hper σ]) (-t.1)
  calc periodLIntegral (fun σ y => ‖∫ t, φ t • joint w ((σ, y) - t)‖ ^ 2)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ‖φ t‖ₑ * F ((σ, y) - t) :=
        lintegral_mono fun σ => lintegral_mono fun y => hpt (σ, y)
    _ = (∫⁻ t, ‖φ t‖ₑ) * ∫⁻ x, (∫⁻ t, ‖φ t‖ₑ * F (x - t)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
        simp_rw [lintegral_const_mul' _ _ hC]
        congr 1
        exact (lintegral_prod _ hK.lintegral_prod_right').symm
    _ = (∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ∫⁻ x, ‖φ t‖ₑ * F (x - t) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
        congr 1
        exact lintegral_lintegral_swap (f := fun x t => ‖φ t‖ₑ * F (x - t)) hK
    _ = (∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ‖φ t‖ₑ * periodLIntegral (fun σ y => ‖w σ y‖ ^ 2) := by
        congr 1
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top, hshift]
    _ = (∫⁻ t, ‖φ t‖ₑ) ^ 2 * periodLIntegral (fun σ y => ‖w σ y‖ ^ 2) := by
        rw [lintegral_mul_const _ hφ.enorm.measurable, sq, mul_assoc]

theorem period_convolution_weighted_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ × Space → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) {w : ℝ → Space → E}
    (hw : AEStronglyMeasurable (joint w) volume) (hper : IsTimePeriodic w)
    {wt : Space → ℝ} (hwtm : Measurable wt) {c : ℝ} (hc : 0 ≤ c)
    (hwtc : ∀ t : ℝ × Space, φ t ≠ 0 → ∀ y, wt y ≤ c * wt (y - t.2)) :
    periodLIntegral (fun σ y => ‖∫ t, φ t • joint w ((σ, y) - t)‖ ^ 2 * wt y) ≤
      ENNReal.ofReal c * (∫⁻ t, ‖φ t‖ₑ) ^ 2 * periodLIntegral (fun σ y => ‖w σ y‖ ^ 2 * wt y) := by
  have hH := volume_prod_invariantClass
  set F : ℝ × Space → ℝ≥0∞ := fun z => ENNReal.ofReal (‖joint w z‖ ^ 2 * wt z.2) with hFdef
  have hF : AEMeasurable F volume :=
    ((hw.norm.aemeasurable.pow_const 2).mul (hwtm.comp measurable_snd).aemeasurable).ennreal_ofReal
  have hC : (∫⁻ t, ‖φ t‖ₑ) ≠ ⊤ := (hφ.integrable_of_hasCompactSupport hφc).2.ne
  have hpt : ∀ x : ℝ × Space, ENNReal.ofReal (‖∫ t, φ t • joint w (x - t)‖ ^ 2 * wt x.2) ≤
      ENNReal.ofReal c * ((∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ‖φ t‖ₑ * F (x - t)) := by
    intro x
    have h1 : ‖∫ t, φ t • joint w (x - t)‖ₑ ≤ ∫⁻ t, ‖φ t‖ₑ * ‖joint w (x - t)‖ₑ :=
      (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (by simp only [enorm_smul]))
    have hm : AEMeasurable (fun t => ‖joint w (x - t)‖ₑ) volume :=
      hw.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x)
    have hpw : ∀ t, ‖φ t‖ₑ * (‖joint w (x - t)‖ₑ ^ 2 * ENNReal.ofReal (wt x.2)) ≤
        ENNReal.ofReal c * (‖φ t‖ₑ * F (x - t)) := by
      intro t
      by_cases h0 : φ t = 0
      · simp [h0]
      · have hb := hwtc t h0 x.2
        have e : F (x - t) = ‖joint w (x - t)‖ₑ ^ 2 * ENNReal.ofReal (wt (x.2 - t.2)) := by
          simp only [hFdef, Prod.snd_sub]
          rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
        rw [e]
        calc ‖φ t‖ₑ * (‖joint w (x - t)‖ₑ ^ 2 * ENNReal.ofReal (wt x.2))
            ≤ ‖φ t‖ₑ * (‖joint w (x - t)‖ₑ ^ 2 * ENNReal.ofReal (c * wt (x.2 - t.2))) := by
              gcongr
          _ = ENNReal.ofReal c * (‖φ t‖ₑ * (‖joint w (x - t)‖ₑ ^ 2 *
                ENNReal.ofReal (wt (x.2 - t.2)))) := by
              rw [ENNReal.ofReal_mul hc]
              ring
    calc ENNReal.ofReal (‖∫ t, φ t • joint w (x - t)‖ ^ 2 * wt x.2)
        = ‖∫ t, φ t • joint w (x - t)‖ₑ ^ 2 * ENNReal.ofReal (wt x.2) := by
          rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ ≤ (∫⁻ t, ‖φ t‖ₑ * ‖joint w (x - t)‖ₑ) ^ 2 * ENNReal.ofReal (wt x.2) := by gcongr
      _ ≤ ((∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ‖φ t‖ₑ * ‖joint w (x - t)‖ₑ ^ 2) * ENNReal.ofReal (wt x.2) := by
          gcongr
          exact sq_lintegral_mul_le_prod hφ.enorm.aemeasurable hm
      _ = (∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ‖φ t‖ₑ * (‖joint w (x - t)‖ₑ ^ 2 * ENNReal.ofReal (wt x.2)) := by
          rw [mul_assoc, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          simp only [mul_assoc]
      _ ≤ (∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ENNReal.ofReal c * (‖φ t‖ₑ * F (x - t)) := by
          exact mul_le_mul (le_refl _) (lintegral_mono hpw) zero_le zero_le
      _ = ENNReal.ofReal c * ((∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ‖φ t‖ₑ * F (x - t)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          ring
  have hac : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) ≪ volume := by
    rw [Measure.volume_eq_prod (α := ℝ) (β := Space)]
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod
      Measure.AbsolutelyContinuous.rfl
  have hK0 : AEMeasurable (fun p : (ℝ × Space) × (ℝ × Space) => ‖φ p.2‖ₑ * F (p.1 - p.2))
      (volume.prod volume) :=
    (hφ.enorm.measurable.comp measurable_snd).aemeasurable.mul
      (hF.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  have hK : AEMeasurable (fun p : (ℝ × Space) × (ℝ × Space) => ‖φ p.2‖ₑ * F (p.1 - p.2))
      (((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)).prod volume) := hK0.mono_ac (hac.prod Measure.AbsolutelyContinuous.rfl)
  have hshift : ∀ t : ℝ × Space, ∫⁻ x, F (x - t) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) =
      periodLIntegral (fun σ y => ‖w σ y‖ ^ 2 * wt y) := by
    intro t
    have hm : AEMeasurable (fun x => F (x - t)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
      (hF.comp_quasiMeasurePreserving (measurePreserving_sub_right (volume : Measure (ℝ × Space))
        t).quasiMeasurePreserving).mono_ac hac
    refine (lintegral_prod _ hm).trans ?_
    unfold periodLIntegral
    have e1 : ∀ σ : ℝ, ∫⁻ y, F ((σ, y) - t) =
        ∫⁻ y, ENNReal.ofReal (‖w (σ + -t.1) y‖ ^ 2 * wt y) := by
      intro σ
      have := lintegral_sub_right_eq_self (μ := (volume : Measure Space))
        (fun y => ENNReal.ofReal (‖w (σ - t.1) y‖ ^ 2 * wt y)) t.2
      simpa [hFdef, joint, sub_eq_add_neg] using this
    simp_rw [e1]
    exact Breakdown.Cert.Internal.TranslationCriterion.lintegral_Icc_add
      (fun σ => ∫⁻ y, ENNReal.ofReal (‖w σ y‖ ^ 2 * wt y)) (fun σ => by simp only [hper σ]) (-t.1)
  calc periodLIntegral (fun σ y => ‖∫ t, φ t • joint w ((σ, y) - t)‖ ^ 2 * wt y)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          ENNReal.ofReal c * ((∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ‖φ t‖ₑ * F ((σ, y) - t)) :=
        lintegral_mono fun σ => lintegral_mono fun y => hpt (σ, y)
    _ = ENNReal.ofReal c * ((∫⁻ t, ‖φ t‖ₑ) * ∫⁻ x, (∫⁻ t, ‖φ t‖ₑ * F (x - t)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ hC]
        congr 2
        exact (lintegral_prod _ hK.lintegral_prod_right').symm
    _ = ENNReal.ofReal c * ((∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ∫⁻ x, ‖φ t‖ₑ * F (x - t) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) := by
        congr 2
        exact lintegral_lintegral_swap (f := fun x t => ‖φ t‖ₑ * F (x - t)) hK
    _ = ENNReal.ofReal c * ((∫⁻ t, ‖φ t‖ₑ) *
          ∫⁻ t, ‖φ t‖ₑ * periodLIntegral (fun σ y => ‖w σ y‖ ^ 2 * wt y)) := by
        congr 2
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top, hshift]
    _ = ENNReal.ofReal c * (∫⁻ t, ‖φ t‖ₑ) ^ 2 * periodLIntegral (fun σ y => ‖w σ y‖ ^ 2 * wt y) := by
        rw [lintegral_mul_const _ hφ.enorm.measurable, sq]
        ring

end Internal.SmoothApprox

end Coercive

end Breakdown
