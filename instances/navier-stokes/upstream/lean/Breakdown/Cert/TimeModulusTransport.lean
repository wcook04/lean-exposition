import Mathlib
import Breakdown.Cert.JointRepresentative
import Breakdown.Cert.PeriodIntegral
import Breakdown.Cert.Basic
import Breakdown.Cert.TimeModulusRepresentation

open scoped ENNReal
open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.Cert

namespace Internal.TimeModulus


private theorem exists_measurable_periodic {F : ℝ → Space → ℝ≥0∞}
    (hF : AEMeasurable (fun z : ℝ × Space => F z.1 z.2)) (hper : IsTimePeriodic F) :
    ∃ F' : ℝ → Space → ℝ≥0∞, Measurable (fun z : ℝ × Space => F' z.1 z.2) ∧ IsTimePeriodic F' ∧
      ∀ᵐ z : ℝ × Space, F z.1 z.2 = F' z.1 z.2 := by
  obtain ⟨Fh, hFh, hm⟩ := aestronglyMeasurable_lift_of_periodic F hper hF.aestronglyMeasurable
  refine ⟨fun s y => hm.mk _ ((s : AddCircle (1 : ℝ)), y), ?_, ?_, ?_⟩
  · exact hm.stronglyMeasurable_mk.measurable.comp
      (((PeriodIntegralInternal.measurePreserving_mk_int 0).measurable.comp measurable_fst).prodMk measurable_snd)
  · intro σ y
    simp only [AddCircle.coe_add_period]
  · have he : ∀ᵐ w ∂((volume : Measure (AddCircle (1 : ℝ))).prod (volume : Measure Space)),
        Fh w.1 w.2 = hm.mk _ w := by
      rw [← Measure.volume_eq_prod]
      exact hm.ae_eq_mk
    have key : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure Space)),
        F z.1 z.2 = hm.mk _ ((z.1 : AddCircle (1 : ℝ)), z.2) := by
      rw [← Measure.restrict_univ (μ := (volume : Measure ℝ).prod (volume : Measure Space)),
        ← univ_prod_univ, ← iUnion_Ioc_intCast, iUnion_prod_const, ae_restrict_iUnion_iff]
      intro n
      rw [← Measure.prod_restrict, Measure.restrict_univ]
      have hmp := (PeriodIntegralInternal.measurePreserving_mk_int n).prod
        (MeasurePreserving.id (volume : Measure Space))
      filter_upwards [hmp.quasiMeasurePreserving.ae he] with z hz
      simp only [Prod.map_fst, Prod.map_snd, id_eq, hFh] at hz
      exact hz
    exact key

private theorem lintegral_Icc_circle (g : AddCircle (1 : ℝ) → ℝ≥0∞) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, g (σ : AddCircle (1 : ℝ)) = ∫⁻ t, g t := by
  have h := AddCircle.lintegral_preimage 1 0 g
  rw [zero_add] at h
  rw [← h, Measure.restrict_congr_set Ioc_ae_eq_Icc]

private theorem periodic_lintegral_shift {Φ : ℝ → ℝ≥0∞} (hΦ : Function.Periodic Φ 1) (t : ℝ) :
    ∫⁻ σ in Icc (0 : ℝ) 1, Φ (σ + t) = ∫⁻ σ in Icc (0 : ℝ) 1, Φ σ := by
  have h1 : ∀ σ : ℝ, Φ (σ + t) = hΦ.lift ((σ : AddCircle (1 : ℝ)) + (t : AddCircle (1 : ℝ))) := by
    intro σ
    rw [← AddCircle.coe_add, Function.Periodic.lift_coe]
  have h2 : ∀ σ : ℝ, Φ σ = hΦ.lift (σ : AddCircle (1 : ℝ)) := fun σ => (Function.Periodic.lift_coe hΦ σ).symm
  simp_rw [h1, h2]
  rw [lintegral_Icc_circle (fun x => hΦ.lift (x + (t : AddCircle (1 : ℝ)))),
    lintegral_Icc_circle (fun x => hΦ.lift x),
    lintegral_add_right_eq_self (fun x => hΦ.lift x) (t : AddCircle (1 : ℝ))]

private theorem shift_lintegral_of_measurable {F : ℝ → Space → ℝ≥0∞}
    (hF : Measurable (fun z : ℝ × Space => F z.1 z.2)) (hper : IsTimePeriodic F) (S : Set Space)
    (δ : ℝ) :
    ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in S, ∫⁻ t in Ioc (0 : ℝ) δ, F (σ + t) y =
      ENNReal.ofReal δ * ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in S, F σ y := by
  have hm3 : Measurable (fun w : (ℝ × ℝ) × Space => F (w.1.1 + w.1.2) w.2) :=
    hF.comp ((measurable_fst.fst.add measurable_fst.snd).prodMk measurable_snd)
  have e1 : ∀ σ : ℝ, ∫⁻ y in S, ∫⁻ t in Ioc (0 : ℝ) δ, F (σ + t) y =
      ∫⁻ t in Ioc (0 : ℝ) δ, ∫⁻ y in S, F (σ + t) y := by
    intro σ
    refine lintegral_lintegral_swap ?_
    have : Measurable (fun w : Space × ℝ => F (σ + w.2) w.1) :=
      hF.comp ((measurable_const.add measurable_snd).prodMk measurable_fst)
    exact this.aemeasurable
  simp_rw [e1]
  have hΦ : Measurable (fun p : ℝ × ℝ => ∫⁻ y in S, F (p.1 + p.2) y) :=
    hm3.lintegral_prod_right'
  rw [lintegral_lintegral_swap hΦ.aemeasurable]
  have hper' : Function.Periodic (fun s : ℝ => ∫⁻ y in S, F s y) 1 := by
    intro s
    simp only [hper s]
  have e2 : ∀ t : ℝ, ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in S, F (σ + t) y =
      ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in S, F σ y :=
    fun t => periodic_lintegral_shift hper' t
  simp_rw [e2]
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, mul_comm]

private theorem ae_shift_eq {F F' : ℝ → Space → ℝ≥0∞} (h : ∀ᵐ z : ℝ × Space, F z.1 z.2 = F' z.1 z.2) :
    ∀ᵐ y : Space, ∀ σ : ℝ, ∀ᵐ t : ℝ, F (σ + t) y = F' (σ + t) y := by
  have hs : ∀ᵐ w ∂((volume : Measure Space).prod (volume : Measure ℝ)), F w.2 w.1 = F' w.2 w.1 := by
    have := (Measure.measurePreserving_swap (μ := (volume : Measure Space))
      (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae (p := fun z : ℝ × Space => F z.1 z.2 = F' z.1 z.2)
      (by rw [← Measure.volume_eq_prod]; exact h)
    exact this
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with y hy σ
  exact (measurePreserving_add_left (volume : Measure ℝ) σ).quasiMeasurePreserving.ae
    (p := fun s => F s y = F' s y) hy

private theorem shift_period_lintegral_le {F : ℝ → Space → ℝ≥0∞}
    (hF : AEMeasurable (fun z : ℝ × Space => F z.1 z.2)) (hper : IsTimePeriodic F) (S : Set Space)
    (δ : ℝ) :
    ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in S, ∫⁻ t in Ioc (0 : ℝ) δ, F (σ + t) y ≤
      ENNReal.ofReal δ * ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in S, F σ y := by
  obtain ⟨F', hF'm, hF'p, hae⟩ := exists_measurable_periodic hF hper
  have hL : ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in S, ∫⁻ t in Ioc (0 : ℝ) δ, F (σ + t) y =
      ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in S, ∫⁻ t in Ioc (0 : ℝ) δ, F' (σ + t) y := by
    refine lintegral_congr fun σ => ?_
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [ae_shift_eq hae] with y hy
    exact lintegral_congr_ae (ae_restrict_of_ae (hy σ))
  have hR : ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in S, F σ y = ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in S, F' σ y := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    have h2 := Measure.ae_ae_of_ae_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space))
      (p := fun z : ℝ × Space => F z.1 z.2 = F' z.1 z.2) hae
    filter_upwards [h2] with σ hσ
    exact lintegral_congr_ae (ae_restrict_of_ae hσ)
  rw [hL, hR]
  exact (shift_lintegral_of_measurable hF'm hF'p S δ).le

private theorem sq_norm_intervalIntegral_le (f : ℝ → Space) {δ : ℝ} (hδ : 0 ≤ δ) :
    ENNReal.ofReal (‖∫ t in (0 : ℝ)..δ, f t‖ ^ 2) ≤
      ENNReal.ofReal δ * ∫⁻ t in Ioc (0 : ℝ) δ, ENNReal.ofReal (‖f t‖ ^ 2) := by
  rw [intervalIntegral.integral_of_le hδ]
  by_cases hm : AEStronglyMeasurable f (volume.restrict (Ioc (0 : ℝ) δ))
  · have h1 : ‖∫ t in Ioc (0 : ℝ) δ, f t‖ₑ ≤ eLpNorm f 1 (volume.restrict (Ioc (0 : ℝ) δ)) := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact enorm_integral_le_lintegral_enorm _
    have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hm
    have h3 : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
    rw [h3] at h2
    calc ENNReal.ofReal (‖∫ t in Ioc (0 : ℝ) δ, f t‖ ^ 2)
        = ‖∫ t in Ioc (0 : ℝ) δ, f t‖ₑ ^ 2 := by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ ≤ (eLpNorm f 2 (volume.restrict (Ioc (0 : ℝ) δ)) *
            (volume.restrict (Ioc (0 : ℝ) δ)) Set.univ ^ (1 / 2 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (h1.trans h2) 2
      _ = eLpNorm f 2 (volume.restrict (Ioc (0 : ℝ) δ)) ^ 2 * (volume.restrict (Ioc (0 : ℝ) δ)) Set.univ := by
          rw [mul_pow, ← ENNReal.rpow_natCast ((volume.restrict (Ioc (0 : ℝ) δ)) Set.univ ^ (1 / 2 : ℝ)),
            ← ENNReal.rpow_mul]
          norm_num
      _ = ENNReal.ofReal δ * ∫⁻ t in Ioc (0 : ℝ) δ, ENNReal.ofReal (‖f t‖ ^ 2) := by
          rw [JointRepresentativeInternal.sq_eLpNorm_two, Measure.restrict_apply_univ, Real.volume_Ioc,
            sub_zero, mul_comm]
          congr 1
          refine lintegral_congr fun t => ?_
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  · rw [integral_undef fun hi => hm hi.aestronglyMeasurable]
    simp

private theorem norm_apply_sq_le (L : Space →L[ℝ] Space) (y : Space) : ‖L y‖ ^ 2 ≤ matSq L * ‖y‖ ^ 2 := by
  have hy : y = ∑ i : Fin 3, y i • unitVector i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr y]
    simp [unitVector, EuclideanSpace.basisFun_apply]
  have hLy : L y = ∑ i : Fin 3, y i • L (unitVector i) := by
    conv_lhs => rw [hy]
    simp [map_sum, map_smul]
  have h1 : ‖L y‖ ≤ ∑ i : Fin 3, |y i| * ‖L (unitVector i)‖ := by
    rw [hLy]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
  have h2 : (∑ i : Fin 3, |y i| * ‖L (unitVector i)‖) ^ 2 ≤
      (∑ i : Fin 3, |y i| ^ 2) * ∑ i : Fin 3, ‖L (unitVector i)‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ‖y‖ ^ 2 = ∑ i : Fin 3, |y i| ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp
  have h0 : 0 ≤ ∑ i : Fin 3, |y i| * ‖L (unitVector i)‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  calc ‖L y‖ ^ 2 ≤ (∑ i : Fin 3, |y i| * ‖L (unitVector i)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
    _ = matSq L * ‖y‖ ^ 2 := by rw [h3, mul_comm]; rfl

private theorem matSq_nonneg' (L : Space →L[ℝ] Space) : 0 ≤ matSq L :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem continuous_matSq' : Continuous matSq :=
  continuous_finsetSum _ fun i _ =>
    ((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.norm.pow 2)

private theorem three_sq_le (x w c : ℝ) : (x + w + c) ^ 2 ≤ 3 * (x ^ 2 + w ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (x - w), sq_nonneg (w - c), sq_nonneg (x - c)]

private theorem rate_sq_le {P b R : ℝ} (hP : 0 < P) (hPb : P ≤ b) (a w c : Space) {F : ℝ} (hF : 0 ≤ F)
    (hc : ‖c‖ ^ 2 ≤ F * R ^ 2) :
    ‖P • (a - (1 / 2 : ℝ) • w - (1 / 2 : ℝ) • c)‖ ^ 2 ≤
      3 * b ^ 2 * (1 + R ^ 2) * (‖a‖ ^ 2 + ‖w‖ ^ 2 + F) := by
  have n1 : ‖a - (1 / 2 : ℝ) • w - (1 / 2 : ℝ) • c‖ ≤ ‖a‖ + (1 / 2) * ‖w‖ + (1 / 2) * ‖c‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul ((1 / 2 : ℝ)) c, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := norm_sub_le a ((1 / 2 : ℝ) • w)
    rw [norm_smul ((1 / 2 : ℝ)) w, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    linarith
  have n2 : ‖a - (1 / 2 : ℝ) • w - (1 / 2 : ℝ) • c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖w‖ ^ 2 + F * R ^ 2) := by
    refine (pow_le_pow_left₀ (norm_nonneg _) n1 2).trans ?_
    refine (three_sq_le _ _ _).trans ?_
    have hw := sq_nonneg ‖w‖
    nlinarith
  have n3 : 3 * (‖a‖ ^ 2 + ‖w‖ ^ 2 + F * R ^ 2) ≤ 3 * (1 + R ^ 2) * (‖a‖ ^ 2 + ‖w‖ ^ 2 + F) := by
    have ha := sq_nonneg ‖a‖
    have hw := sq_nonneg ‖w‖
    have hR := sq_nonneg R
    nlinarith [mul_nonneg hR (add_nonneg ha hw)]
  have hPP : P ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hP.le hPb 2
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hq : 0 ≤ 3 * (1 + R ^ 2) * (‖a‖ ^ 2 + ‖w‖ ^ 2 + F) := by positivity
  calc P ^ 2 * ‖a - (1 / 2 : ℝ) • w - (1 / 2 : ℝ) • c‖ ^ 2
      ≤ P ^ 2 * (3 * (1 + R ^ 2) * (‖a‖ ^ 2 + ‖w‖ ^ 2 + F)) :=
        mul_le_mul_of_nonneg_left (n2.trans n3) (sq_nonneg P)
    _ ≤ b ^ 2 * (3 * (1 + R ^ 2) * (‖a‖ ^ 2 + ‖w‖ ^ 2 + F)) := mul_le_mul_of_nonneg_right hPP hq
    _ = _ := by ring

private theorem iter_eq_prod {F : ℝ × Space → ℝ≥0∞} (hF : AEMeasurable F) (I : Set ℝ) (S : Set Space) :
    ∫⁻ σ in I, ∫⁻ y in S, F (σ, y) = ∫⁻ z in I ×ˢ S, F z := by
  have h' : AEMeasurable F ((volume.restrict I).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact (lintegral_prod F h').symm


private theorem ball_energy_le {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) volume) (R M : ℝ)
    (hgb : periodLIntegral (fun σ y => ‖g σ y‖ ^ 2) ≤ ENNReal.ofReal (M ^ 2))
    (hGb : periodLIntegral (fun σ y => matSq (G σ y)) ≤ ENNReal.ofReal (M ^ 2))
    (hvb : periodBallLIntegral R (fun σ y => ‖v σ y‖ ^ 2) ≤ ENNReal.ofReal (M ^ 2)) :
    ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
        ENNReal.ofReal (‖g σ y‖ ^ 2 + ‖v σ y‖ ^ 2 + matSq (G σ y)) ≤
      ENNReal.ofReal (M ^ 2) + ENNReal.ofReal (M ^ 2) + ENNReal.ofReal (M ^ 2) := by
  have ma : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖g z.1 z.2‖ ^ 2)) volume :=
    (hg.norm.pow 2).aemeasurable.ennreal_ofReal
  have mb : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖v z.1 z.2‖ ^ 2)) volume :=
    (hv.norm.pow 2).aemeasurable.ennreal_ofReal
  have mc : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (matSq (G z.1 z.2))) volume :=
    (continuous_matSq'.comp_aestronglyMeasurable hG).aemeasurable.ennreal_ofReal
  have hsplit : ∀ σ y, ENNReal.ofReal (‖g σ y‖ ^ 2 + ‖v σ y‖ ^ 2 + matSq (G σ y)) =
      ENNReal.ofReal (‖g σ y‖ ^ 2) + ENNReal.ofReal (‖v σ y‖ ^ 2) + ENNReal.ofReal (matSq (G σ y)) := by
    intro σ y
    rw [ENNReal.ofReal_add (by positivity) (matSq_nonneg' _), ENNReal.ofReal_add (by positivity) (by positivity)]
  simp_rw [hsplit]
  have e := iter_eq_prod (F := fun z : ℝ × Space => ENNReal.ofReal (‖g z.1 z.2‖ ^ 2) +
    ENNReal.ofReal (‖v z.1 z.2‖ ^ 2) + ENNReal.ofReal (matSq (G z.1 z.2))) ((ma.add mb).add mc)
    (Icc (0 : ℝ) 1) (Metric.closedBall (0 : Space) R)
  simp only at e
  have mab : AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (‖g z.1 z.2‖ ^ 2) + ENNReal.ofReal (‖v z.1 z.2‖ ^ 2)) volume := ma.add mb
  rw [e, lintegral_add_left' mab.restrict, lintegral_add_left' ma.restrict,
    ← iter_eq_prod ma, ← iter_eq_prod mb, ← iter_eq_prod mc]
  simp only
  refine add_le_add (add_le_add ?_ hvb) ?_
  · exact le_trans (lintegral_mono fun σ => setLIntegral_le_lintegral _ _) hgb
  · exact le_trans (lintegral_mono fun σ => setLIntegral_le_lintegral _ _) hGb

private theorem final_algebra {b R M δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ * (3 * b ^ 2 * (1 + R ^ 2)) * (δ * (3 * M ^ 2)) ≤ 9 * b ^ 2 * (1 + R ^ 2) * δ * M ^ 2 := by
  have hδδ : δ * δ ≤ δ := by nlinarith
  have hq : 0 ≤ 9 * b ^ 2 * (1 + R ^ 2) * M ^ 2 := by positivity
  calc δ * (3 * b ^ 2 * (1 + R ^ 2)) * (δ * (3 * M ^ 2)) = (9 * b ^ 2 * (1 + R ^ 2) * M ^ 2) * (δ * δ) := by ring
    _ ≤ (9 * b ^ 2 * (1 + R ^ 2) * M ^ 2) * δ := mul_le_mul_of_nonneg_left hδδ hq
    _ = _ := by ring

theorem transport_shift_bound (b R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P, 0 < P → P ≤ b → ∀ (v : VelField) (G : GradField) (H : SecondField)
      (g : ℝ → Space → Space), IsPerturbation ∅ P v G H g → ∀ M : ℝ, 0 ≤ M →
      periodLIntegral (fun σ y => ‖g σ y‖ ^ 2) ≤ ENNReal.ofReal (M ^ 2) →
      periodLIntegral (fun σ y => matSq (G σ y)) ≤ ENNReal.ofReal (M ^ 2) →
      periodBallLIntegral R (fun σ y => ‖v σ y‖ ^ 2) ≤ ENNReal.ofReal (M ^ 2) →
      ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
        periodBallLIntegral R (fun σ y => ‖v (σ + δ) y - v σ y‖ ^ 2) ≤
          ENNReal.ofReal (C * δ * M ^ 2) := by
  refine ⟨9 * b ^ 2 * (1 + R ^ 2), by positivity, ?_⟩
  intro P hP hPb v G H g hv M _hM hgb hGb hvb δ hδ
  have hδ0 : 0 ≤ δ := hδ.1.le
  have hK : 0 ≤ 3 * b ^ 2 * (1 + R ^ 2) := by positivity
  have hrep := transport_representation hP hv (lt_of_le_of_lt hvb ENNReal.ofReal_lt_top) δ
  have hpt : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) R)),
        ENNReal.ofReal (‖v (σ + δ) y - v σ y‖ ^ 2) ≤ ENNReal.ofReal δ *
          ∫⁻ t in Ioc (0 : ℝ) δ, ENNReal.ofReal (3 * b ^ 2 * (1 + R ^ 2)) *
            ENNReal.ofReal (‖g (σ + t) y‖ ^ 2 + ‖v (σ + t) y‖ ^ 2 + matSq (G (σ + t) y)) := by
    have h2 := Measure.ae_ae_of_ae_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space))
      (p := fun z : ℝ × Space => z.2 ∈ Metric.closedBall (0 : Space) R →
        v (z.1 + δ) z.2 - v z.1 z.2 = ∫ t in (0 : ℝ)..δ, transportRate P v G g (z.1 + t) z.2) hrep
    refine ae_restrict_of_ae (h2.mono fun σ hσ => ?_)
    refine (ae_restrict_iff' Metric.isClosed_closedBall.measurableSet).2 (hσ.mono fun y hy hyB => ?_)
    rw [hy hyB]
    refine (sq_norm_intervalIntegral_le _ hδ0).trans (mul_le_mul_of_nonneg_left (lintegral_mono fun t => ?_) (by positivity))
    rw [← ENNReal.ofReal_mul hK]
    refine ENNReal.ofReal_le_ofReal ?_
    have hyR : ‖y‖ ≤ R := mem_closedBall_zero_iff.1 hyB
    have hc : ‖G (σ + t) y y‖ ^ 2 ≤ matSq (G (σ + t) y) * R ^ 2 :=
      (norm_apply_sq_le _ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hyR 2)
        (matSq_nonneg' _))
    exact rate_sq_le hP hPb _ _ _ (matSq_nonneg' _) hc
  have hEm : AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (‖g z.1 z.2‖ ^ 2 + ‖v z.1 z.2‖ ^ 2 + matSq (G z.1 z.2))) volume :=
    (((hv.measurable_derivative.norm.pow 2).add (hv.measurable_velocity.norm.pow 2)).add
      (continuous_matSq'.comp_aestronglyMeasurable hv.measurable_gradient)).aemeasurable.ennreal_ofReal
  have hEp : IsTimePeriodic (fun s y =>
      ENNReal.ofReal (‖g s y‖ ^ 2 + ‖v s y‖ ^ 2 + matSq (G s y))) := by
    intro σ y
    simp only [hv.periodic_derivative σ y, hv.periodic_velocity σ y, hv.periodic_gradient σ y]
  have hB := shift_period_lintegral_le hEm hEp (Metric.closedBall (0 : Space) R) δ
  have hE := ball_energy_le hv.measurable_velocity hv.measurable_gradient hv.measurable_derivative R M
    hgb hGb hvb
  unfold periodBallLIntegral
  calc ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
        ENNReal.ofReal (‖v (σ + δ) y - v σ y‖ ^ 2)
      ≤ ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal δ *
          ∫⁻ t in Ioc (0 : ℝ) δ, ENNReal.ofReal (3 * b ^ 2 * (1 + R ^ 2)) *
            ENNReal.ofReal (‖g (σ + t) y‖ ^ 2 + ‖v (σ + t) y‖ ^ 2 + matSq (G (σ + t) y)) :=
        lintegral_mono_ae (hpt.mono fun σ hσ => lintegral_mono_ae hσ)
    _ = ENNReal.ofReal δ * ENNReal.ofReal (3 * b ^ 2 * (1 + R ^ 2)) *
          ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R, ∫⁻ t in Ioc (0 : ℝ) δ,
            ENNReal.ofReal (‖g (σ + t) y‖ ^ 2 + ‖v (σ + t) y‖ ^ 2 + matSq (G (σ + t) y)) := by
        simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        ring
    _ ≤ ENNReal.ofReal δ * ENNReal.ofReal (3 * b ^ 2 * (1 + R ^ 2)) *
          (ENNReal.ofReal δ * (ENNReal.ofReal (M ^ 2) + ENNReal.ofReal (M ^ 2) + ENNReal.ofReal (M ^ 2))) :=
        mul_le_mul_of_nonneg_left (hB.trans (mul_le_mul_of_nonneg_left hE (by positivity))) (by positivity)
    _ = ENNReal.ofReal (δ * (3 * b ^ 2 * (1 + R ^ 2)) * (δ * (3 * M ^ 2))) := by
        rw [← ENNReal.ofReal_add (sq_nonneg M) (sq_nonneg M),
          ← ENNReal.ofReal_add (by positivity) (sq_nonneg M), ← ENNReal.ofReal_mul hδ0,
          ← ENNReal.ofReal_mul hδ0, ← ENNReal.ofReal_mul (mul_nonneg hδ0 hK)]
        ring_nf
    _ ≤ ENNReal.ofReal (9 * b ^ 2 * (1 + R ^ 2) * δ * M ^ 2) :=
        ENNReal.ofReal_le_ofReal (final_algebra hδ0 hδ.2)

end Internal.TimeModulus

end Breakdown.Cert
