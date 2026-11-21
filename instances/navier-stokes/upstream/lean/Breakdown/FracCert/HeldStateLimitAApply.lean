import Breakdown.FracCert.HeldStateLimitAWeak
import Breakdown.FracCert.LinearStateClosed
import Breakdown.FracCert.ActiveEnclosure

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace ApplyPairingInternal

theorem abs_pair_le {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    |∫ y, inner ℝ (f y) (g y)| ≤ Real.sqrt (∫ y, ‖f y‖ ^ 2) * Real.sqrt (∫ y, ‖g y‖ ^ 2) := by
  rw [WeakPairingInternal.pair_eq_inner hf hg, ← WeakPairingInternal.norm_toLp_sq hf,
    ← WeakPairingInternal.norm_toLp_sq hg, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact abs_real_inner_le_norm _ _

theorem unit_norm : ‖unitVector 0‖ = 1 := by
  simp [unitVector]

theorem apply_meas {A : Space → (Space →L[ℝ] Space)} (hA : AEStronglyMeasurable A volume) {b : Space → Space}
    (hb : AEStronglyMeasurable b volume) : AEStronglyMeasurable (fun y => A y (b y)) volume :=
  Continuous.comp_aestronglyMeasurable₂ (g := fun (L : Space →L[ℝ] Space) (x : Space) => L x)
    (continuous_fst.clm_apply continuous_snd) hA hb

theorem apply_norm_le (A : Space →L[ℝ] Space) (x : Space) : ‖A x‖ ≤ Real.sqrt (entrySq A) * ‖x‖ := by
  have h := LinearStateClosedInternal.clm_sq_le A x
  have h0 : 0 ≤ entrySq A := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [← Real.sqrt_sq (norm_nonneg (A x)), ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul h0]
  exact Real.sqrt_le_sqrt h

theorem small_bound {A : Space → (Space →L[ℝ] Space)} (hAm : AEStronglyMeasurable A volume)
    (hAi : Integrable (fun y => entrySq (A y))) {b : Space → Space} (hbm : AEStronglyMeasurable b volume)
    {ψ : Space → Space} (hψc : Continuous ψ) {M r : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y, ‖ψ y‖ ≤ M)
    (hz : ∀ y, y ∉ Metric.ball (0 : Space) r → ψ y = 0)
    (hbi : IntegrableOn (fun y => ‖b y‖ ^ 2) (Metric.ball (0 : Space) r) volume) :
    Integrable (fun y => inner ℝ (A y (b y)) (ψ y)) ∧
    |∫ y, inner ℝ (A y (b y)) (ψ y)| ≤
      Real.sqrt (∫ y, entrySq (A y)) * (M * Real.sqrt (∫ y in Metric.ball (0 : Space) r, ‖b y‖ ^ 2)) := by
  set e := unitVector 0
  have he := unit_norm
  have hes : ∀ y, 0 ≤ entrySq (A y) := fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
  set F : Space → Space := fun y => Real.sqrt (entrySq (A y)) • e with hF
  set Gb : Space → Space := fun y => (‖b y‖ * ‖ψ y‖) • e with hGb
  have hFm : AEStronglyMeasurable F volume :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hAi.aestronglyMeasurable).smul_const e
  have hGm : AEStronglyMeasurable Gb volume :=
    (hbm.norm.mul hψc.aestronglyMeasurable.norm).smul_const e
  have hFn : ∀ y, ‖F y‖ ^ 2 = entrySq (A y) := by
    intro y
    rw [hF]
    simp only
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hes y)]
  have hGn : ∀ y, ‖Gb y‖ ^ 2 ≤ M ^ 2 * (Metric.ball (0 : Space) r).indicator (fun y => ‖b y‖ ^ 2) y := by
    intro y
    rw [hGb]
    simp only
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg (by positivity)]
    by_cases hy : y ∈ Metric.ball (0 : Space) r
    · rw [Set.indicator_of_mem hy]
      have := hM y
      have h1 : ‖ψ y‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      nlinarith [sq_nonneg ‖b y‖]
    · rw [hz y hy, norm_zero, mul_zero, Set.indicator_of_notMem hy]
      simp
  have hind : Integrable ((Metric.ball (0 : Space) r).indicator (fun y => ‖b y‖ ^ 2)) volume :=
    hbi.integrable_indicator measurableSet_ball
  have hF2 : MemLp F 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hFm]
    exact hAi.congr (Eventually.of_forall fun y => (hFn y).symm)
  have hG2 : MemLp Gb 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hGm]
    refine (hind.const_mul (M ^ 2)).mono' (hGm.norm.pow 2) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hGn y
  have hpw : ∀ y, |inner ℝ (A y (b y)) (ψ y)| ≤ inner ℝ (F y) (Gb y) := by
    intro y
    rw [hF, hGb]
    simp only
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
    calc |inner ℝ (A y (b y)) (ψ y)| ≤ ‖A y (b y)‖ * ‖ψ y‖ := abs_real_inner_le_norm _ _
      _ ≤ Real.sqrt (entrySq (A y)) * ‖b y‖ * ‖ψ y‖ :=
          mul_le_mul_of_nonneg_right (apply_norm_le _ _) (norm_nonneg _)
      _ = _ := by ring
  have hFG := ActiveEnclosureInternal.pair_integrable hF2 hG2
  have hmeas : AEStronglyMeasurable (fun y => inner ℝ (A y (b y)) (ψ y)) volume :=
    (apply_meas hAm hbm).inner hψc.aestronglyMeasurable
  have hint : Integrable (fun y => inner ℝ (A y (b y)) (ψ y)) volume :=
    hFG.mono' hmeas (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hpw y)
  refine ⟨hint, ?_⟩
  have e1 : ∫ y, ‖F y‖ ^ 2 = ∫ y, entrySq (A y) := integral_congr_ae (Eventually.of_forall hFn)
  have e2 : ∫ y, ‖Gb y‖ ^ 2 ≤ M ^ 2 * ∫ y in Metric.ball (0 : Space) r, ‖b y‖ ^ 2 := by
    calc ∫ y, ‖Gb y‖ ^ 2 ≤ ∫ y, M ^ 2 * (Metric.ball (0 : Space) r).indicator (fun y => ‖b y‖ ^ 2) y :=
          integral_mono (hG2.integrable_norm_pow (p := 2) (by norm_num)) (hind.const_mul _) hGn
      _ = M ^ 2 * ∫ y, (Metric.ball (0 : Space) r).indicator (fun y => ‖b y‖ ^ 2) y := integral_const_mul _ _
      _ = M ^ 2 * ∫ y in Metric.ball (0 : Space) r, ‖b y‖ ^ 2 := by rw [integral_indicator measurableSet_ball]
  have e3 : Real.sqrt (∫ y, ‖Gb y‖ ^ 2) ≤ M * Real.sqrt (∫ y in Metric.ball (0 : Space) r, ‖b y‖ ^ 2) := by
    calc Real.sqrt (∫ y, ‖Gb y‖ ^ 2) ≤ Real.sqrt (M ^ 2 * ∫ y in Metric.ball (0 : Space) r, ‖b y‖ ^ 2) :=
          Real.sqrt_le_sqrt e2
      _ = M * Real.sqrt (∫ y in Metric.ball (0 : Space) r, ‖b y‖ ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0]
  calc |∫ y, inner ℝ (A y (b y)) (ψ y)| ≤ ∫ y, |inner ℝ (A y (b y)) (ψ y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y, inner ℝ (F y) (Gb y) := integral_mono hint.abs hFG hpw
    _ ≤ |∫ y, inner ℝ (F y) (Gb y)| := le_abs_self _
    _ ≤ Real.sqrt (∫ y, ‖F y‖ ^ 2) * Real.sqrt (∫ y, ‖Gb y‖ ^ 2) := abs_pair_le hF2 hG2
    _ ≤ _ := by rw [e1]; exact mul_le_mul_of_nonneg_left e3 (Real.sqrt_nonneg _)

theorem unit_inner (x : Space) (i : Fin 3) : inner ℝ x (unitVector i) = x i := by
  simp [unitVector, EuclideanSpace.inner_single_right]

theorem sub_sq_le (x z : Space) : ‖x - z‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖z‖ ^ 2 := by
  have h := norm_sub_le x z
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖x‖ - ‖z‖)]

theorem frame_meas {a₀ ψ : Space → Space} (ha : AEStronglyMeasurable a₀ volume) (hψ : Continuous ψ) :
    AEStronglyMeasurable (fun y => ContinuousLinearMap.smulRightL ℝ Space Space (innerSL ℝ (a₀ y)) (ψ y)) volume :=
  Continuous.comp_aestronglyMeasurable₂
    (g := fun (x v : Space) => ContinuousLinearMap.smulRightL ℝ Space Space (innerSL ℝ x) v)
    (((ContinuousLinearMap.smulRightL ℝ Space Space).continuous.comp
      ((innerSL ℝ).continuous.comp continuous_fst)).clm_apply continuous_snd) ha hψ.aestronglyMeasurable

theorem frame_apply (x v w : Space) :
    ContinuousLinearMap.smulRightL ℝ Space Space (innerSL ℝ x) v w = inner ℝ x w • v := rfl

theorem frame_entry (B : Space →L[ℝ] Space) (x v : Space) :
    entryInner B (ContinuousLinearMap.smulRightL ℝ Space Space (innerSL ℝ x) v) = inner ℝ (B x) v := by
  simp only [entryInner, frame_apply]
  rw [ActiveEnclosureInternal.apply_expand B x, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right, unit_inner]

theorem frame_sq (x v : Space) :
    entrySq (ContinuousLinearMap.smulRightL ℝ Space Space (innerSL ℝ x) v) ≤ 3 * (‖x‖ ^ 2 * ‖v‖ ^ 2) := by
  simp only [entrySq, frame_apply, unit_inner, norm_smul, Real.norm_eq_abs, Fin.sum_univ_three]
  have h : ∀ i : Fin 3, (|x i| * ‖v‖) ^ 2 ≤ ‖x‖ ^ 2 * ‖v‖ ^ 2 := by
    intro i
    have hi : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hi 2) (sq_nonneg _)
  linarith [h 0, h 1, h 2]

theorem apply_pairing_limit {A : ℕ → Space → (Space →L[ℝ] Space)} {A₀ : Space → (Space →L[ℝ] Space)}
    {a : ℕ → Space → Space} {a₀ : Space → Space} {K : ℝ}
    (hAm : ∀ n, AEStronglyMeasurable (A n) volume) (hAi : ∀ n, Integrable (fun y => entrySq (A n y)))
    (hAK : ∀ n, ∫ y, entrySq (A n y) ≤ K)
    (hAw : ∀ E : Space → (Space →L[ℝ] Space), AEStronglyMeasurable E volume →
      Integrable (fun y => entrySq (E y)) →
      Tendsto (fun n => ∫ y, entryInner (A n y) (E y)) atTop (nhds (∫ y, entryInner (A₀ y) (E y))))
    (ham : ∀ n, AEStronglyMeasurable (a n) volume) (ha₀m : AEStronglyMeasurable a₀ volume)
    (hai : ∀ n r, IntegrableOn (fun y => ‖a n y‖ ^ 2) (Metric.ball (0 : Space) r) volume)
    (ha₀i : ∀ r, IntegrableOn (fun y => ‖a₀ y‖ ^ 2) (Metric.ball (0 : Space) r) volume)
    (hloc : ∀ r, Tendsto (fun n => ∫ y in Metric.ball (0 : Space) r, ‖a n y - a₀ y‖ ^ 2) atTop (nhds 0))
    {ψ : Space → Space} (hψ : IsTestVectorField ψ) :
    Tendsto (fun n => ∫ y, inner ℝ (A n y (a n y)) (ψ y)) atTop
      (nhds (∫ y, inner ℝ (A₀ y (a₀ y)) (ψ y))) := by
  have hψc : Continuous ψ := hψ.1.continuous
  obtain ⟨M₁, hM₁⟩ := hψc.bounded_above_of_compact_support hψ.2
  have hM : ∀ y, ‖ψ y‖ ≤ max M₁ 0 := fun y => (hM₁ y).trans (le_max_left _ _)
  have hM0 : 0 ≤ max M₁ 0 := le_max_right _ _
  obtain ⟨r, hr⟩ := hψ.2.isCompact.isBounded.subset_ball (0 : Space)
  have hz : ∀ y, y ∉ Metric.ball (0 : Space) r → ψ y = 0 :=
    fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hr h))
  have hbi : ∀ n, IntegrableOn (fun y => ‖a n y - a₀ y‖ ^ 2) (Metric.ball (0 : Space) r) volume := by
    intro n
    refine (((hai n r).const_mul 2).add ((ha₀i r).const_mul 2)).mono'
      ((((ham n).sub ha₀m).norm.pow 2).restrict) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact sub_sq_le _ _
  have hs := fun n => small_bound (hAm n) (hAi n) (b := fun y => a n y - a₀ y) ((ham n).sub ha₀m) hψc hM0
    hM hz (hbi n)
  have hw := fun n => small_bound (hAm n) (hAi n) ha₀m hψc hM0 hM hz (ha₀i r)
  set E₀ : Space → (Space →L[ℝ] Space) :=
    fun y => ContinuousLinearMap.smulRightL ℝ Space Space (innerSL ℝ (a₀ y)) (ψ y) with hE₀
  have hE₀m : AEStronglyMeasurable E₀ volume := frame_meas ha₀m hψc
  have hE₀i : Integrable (fun y => entrySq (E₀ y)) volume := by
    have hind : Integrable ((Metric.ball (0 : Space) r).indicator (fun y => ‖a₀ y‖ ^ 2)) volume :=
      (ha₀i r).integrable_indicator measurableSet_ball
    refine (hind.const_mul (3 * max M₁ 0 ^ 2)).mono'
      (Continuous.comp_aestronglyMeasurable (g := entrySq) (by unfold entrySq; fun_prop) hE₀m)
      (Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ entrySq (E₀ y) := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [Real.norm_of_nonneg h0]
    refine (frame_sq (a₀ y) (ψ y)).trans ?_
    by_cases hy : y ∈ Metric.ball (0 : Space) r
    · rw [Set.indicator_of_mem hy]
      have h1 : ‖ψ y‖ ^ 2 ≤ max M₁ 0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM y) 2
      nlinarith [sq_nonneg ‖a₀ y‖]
    · rw [hz y hy, Set.indicator_of_notMem hy]
      simp
  have hweak : Tendsto (fun n => ∫ y, inner ℝ (A n y (a₀ y)) (ψ y)) atTop
      (nhds (∫ y, inner ℝ (A₀ y (a₀ y)) (ψ y))) := by
    have h := hAw E₀ hE₀m hE₀i
    simp only [hE₀, frame_entry] at h
    exact h
  have hsmall : Tendsto (fun n => ∫ y, inner ℝ (A n y (a n y - a₀ y)) (ψ y)) atTop (nhds 0) := by
    refine squeeze_zero_norm (fun n => ?_) (a := fun n => Real.sqrt K *
      (max M₁ 0 * Real.sqrt (∫ y in Metric.ball (0 : Space) r, ‖a n y - a₀ y‖ ^ 2))) ?_
    · rw [Real.norm_eq_abs]
      refine (hs n).2.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hAK n)) ?_)
      exact mul_nonneg hM0 (Real.sqrt_nonneg _)
    · have h := ((hloc r).sqrt.const_mul (max M₁ 0)).const_mul (Real.sqrt K)
      simpa using h
  have e : ∀ n, ∫ y, inner ℝ (A n y (a n y)) (ψ y) =
      (∫ y, inner ℝ (A n y (a n y - a₀ y)) (ψ y)) + ∫ y, inner ℝ (A n y (a₀ y)) (ψ y) := by
    intro n
    rw [← integral_add (hs n).1 (hw n).1]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [map_sub, inner_sub_left]
    ring
  simpa [e] using hsmall.add hweak

end ApplyPairingInternal

end SteadyCert

end Breakdown
