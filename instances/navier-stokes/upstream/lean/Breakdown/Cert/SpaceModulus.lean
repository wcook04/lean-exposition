import Breakdown.Cert.Nodes
import Breakdown.Cert.ReadingEnergy
import Breakdown.Cert.PeriodIntegral
import Breakdown.FreqTr.Realization

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.SpaceModulus

open Internal.SliceFields Internal.ReadingEnergy

theorem norm_apply_sq_le (L : Space →L[ℝ] Space) (h : Space) :
    ‖L h‖ ^ 2 ≤ ‖h‖ ^ 2 * ∑ i : Fin 3, ‖L (unitVector i)‖ ^ 2 := by
  have hh : h = ∑ i : Fin 3, h i • unitVector i := by
    ext j
    simp [unitVector, Pi.single_apply]
  have h1 : ‖L h‖ ≤ ∑ i : Fin 3, |h i| * ‖L (unitVector i)‖ := by
    conv_lhs => rw [hh]
    rw [map_sum]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, norm_smul, Real.norm_eq_abs]
  have h2 : (∑ i : Fin 3, |h i| * ‖L (unitVector i)‖) ^ 2 ≤
      (∑ i : Fin 3, |h i| ^ 2) * ∑ i : Fin 3, ‖L (unitVector i)‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ‖h‖ ^ 2 = ∑ i : Fin 3, |h i| ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs]
  rw [h3]
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem norm_intervalIntegral_sq_le {g : ℝ → Space} (hg : Continuous g) :
    ‖∫ t in (0 : ℝ)..1, g t‖ ^ 2 ≤ ∫ t in (0 : ℝ)..1, ‖g t‖ ^ 2 := by
  set D := ∫ t in (0 : ℝ)..1, g t with hD
  have hi : IntervalIntegrable g volume 0 1 := hg.intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume 0 1 :=
    (hg.norm.pow 2).intervalIntegrable 0 1
  have e1 : ‖D‖ ^ 2 = ∫ t in (0 : ℝ)..1, innerSL ℝ D (g t) := by
    rw [ContinuousLinearMap.intervalIntegral_comp_comm _ hi, ← hD, innerSL_apply_apply,
      real_inner_self_eq_norm_sq]
  have e2 : ∫ t in (0 : ℝ)..1, innerSL ℝ D (g t) ≤
      ∫ t in (0 : ℝ)..1, (‖D‖ ^ 2 / 2 + ‖g t‖ ^ 2 / 2) := by
    refine intervalIntegral.integral_mono_on zero_le_one
      ((continuous_const.inner hg).intervalIntegrable 0 1)
      ((continuous_const.add ((hg.norm.pow 2).div_const 2)).intervalIntegrable 0 1) fun t _ => ?_
    rw [innerSL_apply_apply]
    have := real_inner_le_norm D (g t)
    nlinarith [two_mul_le_add_sq ‖D‖ ‖g t‖]
  have e3 : ∫ t in (0 : ℝ)..1, (‖D‖ ^ 2 / 2 + ‖g t‖ ^ 2 / 2) =
      ‖D‖ ^ 2 / 2 + (∫ t in (0 : ℝ)..1, ‖g t‖ ^ 2) / 2 := by
    rw [intervalIntegral.integral_add intervalIntegrable_const (hi2.div_const 2),
      intervalIntegral.integral_const, intervalIntegral.integral_div]
    simp
  linarith

theorem sub_eq_intervalIntegral {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (y h : Space) :
    φ (y + h) - φ y = ∫ t in (0 : ℝ)..1, fderiv ℝ φ (y + t • h) h := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hc : Continuous (fun t : ℝ => fderiv ℝ φ (y + t • h) h) :=
    ((hφ.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => φ (y + t • h))]
  · simp
  · intro t _
    have := ((hd (y + t • h)).hasFDerivAt).comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const h).const_add y)
    simpa [Function.comp_def] using this
  · exact hc.intervalIntegrable 0 1

theorem lintegral_translate_sub_le {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ) (h : Space) :
    ∫⁻ y, ENNReal.ofReal (‖φ (y + h) - φ y‖ ^ 2) ≤
      ENNReal.ofReal (‖h‖ ^ 2 * ∫ y, ∑ i : Fin 3, ‖fderiv ℝ φ y (unitVector i)‖ ^ 2) := by
  have hD : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  set k : Space → ℝ := fun y => ∑ i : Fin 3, ‖fderiv ℝ φ y (unitVector i)‖ ^ 2 with hk_def
  have hk : Continuous k :=
    continuous_finsetSum _ fun i _ => (hD.clm_apply continuous_const).norm.pow 2
  have hks : HasCompactSupport k := by
    have := (hs.fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : Space →L[ℝ] Space => ∑ i : Fin 3, ‖L (unitVector i)‖ ^ 2) (by simp)
    exact this
  have hki : Integrable k := hk.integrable_of_hasCompactSupport hks
  set F : Space → ℝ → ℝ := fun y t => ‖fderiv ℝ φ (y + t • h) h‖ ^ 2 with hF_def
  have hFc : Continuous (Function.uncurry F) :=
    ((hD.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply
      continuous_const).norm.pow 2
  have hpt : ∀ y, ENNReal.ofReal (‖φ (y + h) - φ y‖ ^ 2) ≤
      ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (F y t) := by
    intro y
    have hcy : Continuous (fun t : ℝ => fderiv ℝ φ (y + t • h) h) :=
      (hD.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const
    have h1 := norm_intervalIntegral_sq_le hcy
    rw [← sub_eq_intervalIntegral hφ y h, intervalIntegral.integral_of_le zero_le_one] at h1
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · exact ENNReal.ofReal_le_ofReal h1
    · exact (hcy.norm.pow 2).integrableOn_Ioc
    · exact ae_of_all _ fun t => sq_nonneg _
  calc ∫⁻ y, ENNReal.ofReal (‖φ (y + h) - φ y‖ ^ 2)
      ≤ ∫⁻ y, ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (F y t) := lintegral_mono hpt
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (F y t) :=
        lintegral_lintegral_swap (ENNReal.continuous_ofReal.comp hFc).measurable.aemeasurable
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ φ y h‖ ^ 2) := by
        congr 1
        funext t
        exact lintegral_add_right_eq_self (fun y => ENNReal.ofReal (‖fderiv ℝ φ y h‖ ^ 2)) (t • h)
    _ = ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ φ y h‖ ^ 2) := by
        rw [setLIntegral_const, Real.volume_Ioc]
        simp
    _ ≤ ∫⁻ y, ENNReal.ofReal (‖h‖ ^ 2 * k y) :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (norm_apply_sq_le _ _)
    _ = ENNReal.ofReal (‖h‖ ^ 2 * ∫ y, k y) := by
        rw [← integral_const_mul]
        exact (ofReal_integral_eq_lintegral_ofReal (hki.const_mul _)
          (ae_of_all _ fun y => mul_nonneg (sq_nonneg _)
            (Finset.sum_nonneg fun i _ => sq_nonneg _))).symm

theorem exists_test_seq (x : X) : ∃ φ : ℕ → Space → Space, (∀ n, IsTestField (φ n)) ∧
    Tendsto (fun n => embedX (φ n)) atTop (𝓝 x) ∧
    ∀ᵐ y, Tendsto (fun n => φ n y) atTop (𝓝 ((velocity x : Space → Space) y)) := by
  have hmem : x ∈ closure (testSpan : Set X) := by
    rw [testDense_holds.2.closure_eq]
    exact mem_univ x
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
  choose φ hφ hφe using fun n => testSpan_holds (s n) (hs n)
  have hlim' : Tendsto (fun n => embedX (φ n)) atTop (𝓝 x) :=
    hlim.congr fun n => (hφe n).symm
  have hv : Tendsto (fun n => velocity (embedX (φ n))) atTop (𝓝 (velocity x)) :=
    (velocity.continuous.tendsto x).comp hlim'
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  refine ⟨fun i => φ (ns i), fun i => hφ _, hlim'.comp hns.tendsto_atTop, ?_⟩
  have hdec : ∀ n, (velocity (embedX (φ n)) : Space → Space) =ᵐ[volume] φ n := fun n =>
    velocityDecay_holds (φ n) (Internal.VelocityExists.isDecayField_of_isTestField (hφ n))
  filter_upwards [ae_all_iff.2 hdec, hae] with y h1 h2
  exact h2.congr fun i => h1 (ns i)

theorem lintegral_translate_le_of_tendsto {f : Space → Space} {φ : ℕ → Space → Space}
    (hc : ∀ n, Continuous (φ n)) (hae : ∀ᵐ y, Tendsto (fun n => φ n y) atTop (𝓝 (f y)))
    (h : Space) (b : ℕ → ℝ≥0∞) (b₀ : ℝ≥0∞)
    (hb : ∀ n, ∫⁻ y, ENNReal.ofReal (‖φ n (y + h) - φ n y‖ ^ 2) ≤ b n)
    (hbt : Tendsto b atTop (𝓝 b₀)) :
    ∫⁻ y, ENNReal.ofReal (‖f (y + h) - f y‖ ^ 2) ≤ b₀ := by
  have hB := (measurePreserving_add_right (volume : Measure Space) h).quasiMeasurePreserving.ae hae
  have hlimit : ∀ᵐ y, Tendsto (fun n => ENNReal.ofReal (‖φ n (y + h) - φ n y‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (‖f (y + h) - f y‖ ^ 2))) := by
    filter_upwards [hae, hB] with y h1 h2
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((h2.sub h1).norm.pow 2)
  have hmeas : ∀ n, AEMeasurable (fun y => ENNReal.ofReal (‖φ n (y + h) - φ n y‖ ^ 2)) volume :=
    fun n => (ENNReal.continuous_ofReal.comp
      ((((hc n).comp (continuous_id.add continuous_const)).sub (hc n)).norm.pow 2)).measurable.aemeasurable
  calc ∫⁻ y, ENNReal.ofReal (‖f (y + h) - f y‖ ^ 2)
      = ∫⁻ y, liminf (fun n => ENNReal.ofReal (‖φ n (y + h) - φ n y‖ ^ 2)) atTop :=
        lintegral_congr_ae (hlimit.mono fun y hy => hy.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ y, ENNReal.ofReal (‖φ n (y + h) - φ n y‖ ^ 2)) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ liminf b atTop := liminf_le_liminf (Eventually.of_forall hb)
    _ = b₀ := hbt.liminf_eq

theorem lintegral_velocity_translate_sub_le (x : X) (h : Space) :
    ∫⁻ y, ENNReal.ofReal (‖(velocity x : Space → Space) (y + h) - (velocity x : Space → Space) y‖ ^ 2) ≤
      ENNReal.ofReal (‖h‖ ^ 2 * ‖x‖ ^ 2) := by
  obtain ⟨φ, hφ, hlim, hae⟩ := exists_test_seq x
  refine lintegral_translate_le_of_tendsto (fun n => (hφ n).1.continuous) hae h
    (fun n => ENNReal.ofReal (‖h‖ ^ 2 * ‖embedX (φ n)‖ ^ 2)) _ (fun n => ?_)
    ((ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_const_nhds.mul (((continuous_norm.tendsto x).comp hlim).pow 2)))
  rw [embedNormLinear_holds.1 _ (Internal.VelocityExists.isDecayField_of_isTestField (hφ n))]
  exact lintegral_translate_sub_le (hφ n).1 (hφ n).2.1 h

theorem slice_bound (R : ℝ) {F : Space → Space} (z : X)
    (hF : F =ᵐ[volume] (velocity z : Space → Space)) (h : Space) :
    ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖F (y + h) - F y‖ ^ 2) ≤
      ENNReal.ofReal (‖h‖ ^ 2 * ‖z‖ ^ 2) := by
  have hT := (measurePreserving_add_right (volume : Measure Space) h).quasiMeasurePreserving.ae hF
  refine (setLIntegral_le_lintegral _ _).trans ?_
  refine (lintegral_congr_ae ?_).trans_le (lintegral_velocity_translate_sub_le z h)
  filter_upwards [hF, hT] with y h1 h2
  rw [h1, h2]

theorem periodBallNorm_le {F : ℝ → Space → Space} (R : ℝ) (c : TimeCircle → ℝ)
    (hc : Integrable c) (hc0 : ∀ t, 0 ≤ c t) (a : ℝ) (ha : 0 ≤ a) (hca : ∫ t, c t = a ^ 2)
    (hb : ∀ᵐ σ : ℝ, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖F σ y‖ ^ 2) ≤
      ENNReal.ofReal (c σ)) :
    periodBallNorm R F ≤ a := by
  have h1 : periodBallLIntegral R (fun σ y => ‖F σ y‖ ^ 2) ≤ ENNReal.ofReal (a ^ 2) := by
    unfold periodBallLIntegral
    calc ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
          ENNReal.ofReal (‖F σ y‖ ^ 2)
        ≤ ∫⁻ σ in Icc (0 : ℝ) 1, ENNReal.ofReal (c σ) := lintegral_mono_ae (ae_restrict_of_ae hb)
      _ = ∫⁻ t, ENNReal.ofReal (c t) :=
          lintegral_Icc_coe (fun t => ENNReal.ofReal (c t)) hc.aemeasurable.ennreal_ofReal
      _ = ENNReal.ofReal (a ^ 2) := by
          rw [← hca, ofReal_integral_eq_lintegral_ofReal hc (ae_of_all _ hc0)]
  unfold periodBallNorm
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_ofReal (sq_nonneg a)] at h2
  calc Real.sqrt _ ≤ Real.sqrt (a ^ 2) := Real.sqrt_le_sqrt h2
    _ = a := Real.sqrt_sq ha

theorem isReadingOf_readingOf (h : ReadingExistsHolds) (u : XX) :
    IsReadingOf u (readingOf u).1 (readingOf u).2.1 (readingOf u).2.2 := by
  obtain ⟨v, G, H, hr, -⟩ := h u
  have hex : ∃ r : VelField × GradField × SecondField, IsReadingOf u r.1 r.2.1 r.2.2 :=
    ⟨(v, G, H), hr⟩
  unfold readingOf
  rw [dif_pos hex]
  exact hex.choose_spec

theorem norm_derivX_sq_le (j : Fin 3) (k : X) : ‖derivX j k‖ ^ 2 ≤ ‖k‖ ^ 2 := by
  rw [← sum_norm_derivX_sq k]
  exact Finset.single_le_sum (f := fun i => ‖derivX i k‖ ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ j)

theorem integral_scaled_gradSq (u : XX) (s : Space) :
    ∫ t, ‖s‖ ^ 2 * ‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2 = (‖s‖ * ‖gradCLM u‖) ^ 2 :=
  calc _ = ‖s‖ ^ 2 * ∫ t, ‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2 := integral_const_mul _ _
    _ = ‖s‖ ^ 2 * ‖gradCLM u‖ ^ 2 := congrArg (‖s‖ ^ 2 * ·) (norm_sq_gradCLM u).symm
    _ = _ := (mul_pow _ _ _).symm

theorem integral_scaled_secondSq (u : XX) (s : Space) :
    ∫ t, ‖s‖ ^ 2 * ‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2 = (‖s‖ * ‖secondCLM u‖) ^ 2 :=
  calc _ = ‖s‖ ^ 2 * ∫ t, ‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2 := integral_const_mul _ _
    _ = ‖s‖ ^ 2 * ‖secondCLM u‖ ^ 2 := congrArg (‖s‖ ^ 2 * ·) (norm_sq_secondCLM u).symm
    _ = _ := (mul_pow _ _ _).symm

theorem velocity_part (R : ℝ) (u : XX) (s : Space) (r : VelField × GradField × SecondField)
    (hr : IsReadingOf u r.1 r.2.1 r.2.2) :
    periodBallNorm R (fun σ y => r.1 σ (y + s) - r.1 σ y) ≤ ‖s‖ * ‖gradCLM u‖ := by
  refine periodBallNorm_le (F := fun σ y => r.1 σ (y + s) - r.1 σ y) R
    (fun t => ‖s‖ ^ 2 * ‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2)
    ((integrable_gradSq u).const_mul _) (fun t => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (‖s‖ * ‖gradCLM u‖)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_ ?_
  · exact integral_scaled_gradSq u s
  · filter_upwards [hr.velocity_eq] with σ hσ
    exact slice_bound R _ hσ s

theorem column_eq (h2 : GraphClosedHolds) (u : XX) (r : VelField × GradField × SecondField)
    (hr : IsReadingOf u r.1 r.2.1 r.2.2) (j : Fin 3) :
    ∀ᵐ σ : ℝ, gradColumn r.2.1 j σ =ᵐ[volume]
      (velocity (derivX j (secondPart ((u : TimeCircle → XBar) (σ : TimeCircle)))) :
        Space → Space) := by
  filter_upwards [hr.velocity_eq, hr.weak_gradient] with σ hσ hg
  have hcol := column_ae h2 ((u : TimeCircle → XBar) (σ : TimeCircle)) hσ hg j
  have hinv := velocityInverts_holds _ _
    (halfSsp_derivX j (h2 ((u : TimeCircle → XBar) (σ : TimeCircle))))
  have hp := partialX_eq j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))
  filter_upwards [hcol, hinv] with y h1 h3
  refine h1.trans (Eq.trans ?_ h3.symm)
  rw [hp]

theorem column_part (R : ℝ) (h2 : GraphClosedHolds) (u : XX) (s : Space)
    (r : VelField × GradField × SecondField)
    (hr : IsReadingOf u r.1 r.2.1 r.2.2) (j : Fin 3) :
    periodBallNorm R (fun σ y => gradColumn r.2.1 j σ (y + s) - gradColumn r.2.1 j σ y) ≤
      ‖s‖ * ‖secondCLM u‖ := by
  refine periodBallNorm_le
    (F := fun σ y => gradColumn r.2.1 j σ (y + s) - gradColumn r.2.1 j σ y) R
    (fun t => ‖s‖ ^ 2 * ‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2)
    ((integrable_secondSq u).const_mul _) (fun t => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (‖s‖ * ‖secondCLM u‖)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_ ?_
  · exact integral_scaled_secondSq u s
  · filter_upwards [column_eq h2 u r hr j] with σ hF
    refine (slice_bound R _ hF s).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (norm_derivX_sq_le j _) (sq_nonneg _)

end Internal.SpaceModulus

open Internal.SpaceModulus Internal.SliceFields Internal.ReadingEnergy

theorem spaceModulusHolds_of (h : ReadingExistsHolds) (h2 : GraphClosedHolds) :
    SpaceModulusHolds := fun R _ u s =>
  ⟨velocity_part R u s (readingOf u) (isReadingOf_readingOf h u),
    fun j => column_part R h2 u s (readingOf u) (isReadingOf_readingOf h u) j⟩

end Breakdown.Cert
