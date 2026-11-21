import Breakdown.FracCell.StExterior
import Mathlib.MeasureTheory.Constructions.HaarToSphere

open MeasureTheory Set

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Exterior

open SteadyCert

namespace RaySmoothInternal

lemma polar (F : Space → ENNReal) (hF : Measurable F) :
    ∫⁻ y, F y = ∫⁻ p : Metric.sphere (0 : Space) 1,
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * F (r • (p : Space)))
        ∂(volume : Measure Space).toSphere := by
  have hdim : Module.finrank ℝ Space - 1 = 2 := by simp
  have hmp := (volume : Measure Space).measurePreserving_homeomorphUnitSphereProd
  rw [hdim] at hmp
  have h1 : ∫⁻ y, F y = ∫⁻ y in ({0}ᶜ : Set Space), F y := by
    rw [restrict_compl_singleton]
  rw [h1, ← lintegral_subtype_comap (measurableSet_singleton _).compl]
  set h := homeomorphUnitSphereProd Space with hh
  have h3 : ∫⁻ a : ({0}ᶜ : Set Space), F a ∂(volume.comap Subtype.val) =
      ∫⁻ a : ({0}ᶜ : Set Space), (fun p => F (h.symm p : Space)) (h a)
        ∂(volume.comap Subtype.val) := by
    congr 1
    funext a
    simp only [Homeomorph.symm_apply_apply]
  rw [h3, hmp.lintegral_comp_emb h.measurableEmbedding (fun p => F (h.symm p : Space))]
  rw [lintegral_prod _ ?_]
  · refine lintegral_congr fun p => ?_
    rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ ?_ ?_]
    · rw [← lintegral_subtype_comap measurableSet_Ioi
        (fun r => ENNReal.ofReal (r ^ 2) * F (r • (p : Space)))]
      rfl
    · fun_prop
    · exact hF.comp ((continuous_subtype_val.comp h.symm.continuous).comp
        (Continuous.prodMk continuous_const continuous_id)).measurable
  · exact (hF.comp (continuous_subtype_val.comp h.symm.continuous).measurable).aemeasurable

lemma apply_sq_le (G : Space →L[ℝ] Space) (e : Space) (he : ‖e‖ = 1) :
    ‖G e‖ ^ 2 ≤ entrySq G := by
  have hrep : e = ∑ j : Fin 3, e j • unitVector j := by
    ext i
    simp [unitVector, Finset.sum_apply, Pi.single_apply]
  have h1 : ‖G e‖ ≤ ∑ j : Fin 3, |e j| * ‖G (unitVector j)‖ := by
    conv_lhs => rw [hrep]
    rw [map_sum]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, norm_smul, Real.norm_eq_abs]
  have h2 : (∑ j : Fin 3, |e j| * ‖G (unitVector j)‖) ^ 2 ≤
      (∑ j : Fin 3, |e j| ^ 2) * ∑ j : Fin 3, ‖G (unitVector j)‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ∑ j : Fin 3, |e j| ^ 2 = 1 := by
    have := EuclideanSpace.norm_sq_eq e
    rw [he] at this
    simpa [Real.norm_eq_abs] using this.symm
  rw [h3, one_mul] at h2
  calc ‖G e‖ ^ 2 ≤ (∑ j : Fin 3, |e j| * ‖G (unitVector j)‖) ^ 2 := by
        gcongr
    _ ≤ _ := h2


lemma ion {X : Type*} [Zero X] (f : ℝ → ℝ) (hf : Continuous f) (G : ℝ → X)
    (hG : HasCompactSupport G) (h0 : ∀ r, G r = 0 → f r = 0) (a : ℝ) :
    IntegrableOn f (Ioi a) := by
  have hcs : HasCompactSupport f := hG.mono fun r hr hGr => hr (h0 r hGr)
  exact (hf.integrable_of_hasCompactSupport hcs).integrableOn

lemma sq_sum (x : Space) : ‖x‖ ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

lemma ray_real (hline : RayLineStatement) (u : Space → Space) (hu : ContDiff ℝ 1 u)
    (hs : HasCompactSupport u) (e : Space) (he : ‖e‖ = 1) (a : ℝ) (ha : 0 < a) :
    (∫ r in Ioi a, ‖u (r • e)‖ ^ 2) ≤ 4 * ∫ r in Ioi a, r ^ 2 * entrySq (fderiv ℝ u (r • e)) := by
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  have hemb : Topology.IsClosedEmbedding (fun r : ℝ => r • e) := isClosedEmbedding_smul_left he0
  have hcs : HasCompactSupport (fun r : ℝ => u (r • e)) := hs.comp_isClosedEmbedding hemb
  have hcont : Continuous (fun r : ℝ => u (r • e)) :=
    hu.continuous.comp (continuous_id.smul continuous_const)
  have hdc : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv one_ne_zero
  have hdcont : Continuous (fun r : ℝ => fderiv ℝ u (r • e)) :=
    hdc.comp (continuous_id.smul continuous_const)
  have hdcs : HasCompactSupport (fun r : ℝ => fderiv ℝ u (r • e)) :=
    (hs.fderiv (𝕜 := ℝ)).comp_isClosedEmbedding hemb
  set g : Fin 3 → ℝ → ℝ := fun i r => u (r • e) i with hg
  have hgd : ∀ i r, HasDerivAt (g i) (fderiv ℝ u (r • e) e i) r := by
    intro i r
    have h1 : HasDerivAt (fun r : ℝ => r • e) e r := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) r).smul_const e
    have h2 := ((hu.differentiable one_ne_zero) (r • e)).hasFDerivAt.comp_hasDerivAt r h1
    have h3 := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt r h2
    exact h3
  have hgc : ∀ i, ContDiff ℝ 1 (g i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp (hu.comp (contDiff_id.smul contDiff_const))
  have hgs : ∀ i, HasCompactSupport (g i) := fun i =>
    hcs.mono fun r hr h0 => hr (by simp [g, h0])
  have hint1 : ∀ i, IntegrableOn (fun r => g i r ^ 2) (Ioi a) := fun i =>
    ion _ ((hgc i).continuous.pow 2) _ hcs (fun r h0 => by simp [g, h0]) a
  have hint2 : ∀ i, IntegrableOn (fun r => r ^ 2 * deriv (g i) r ^ 2) (Ioi a) := by
    intro i
    have hfe : (fun r => r ^ 2 * deriv (g i) r ^ 2) =
        fun r => r ^ 2 * (fderiv ℝ u (r • e) e i) ^ 2 := by
      funext r
      rw [(hgd i r).deriv]
    rw [hfe]
    refine ion _ ?_ _ hdcs (fun r h0 => by simp [h0]) a
    fun_prop
  have hint3 : IntegrableOn (fun r => r ^ 2 * ‖fderiv ℝ u (r • e) e‖ ^ 2) (Ioi a) :=
    ion _ (by fun_prop) _ hdcs (fun r h0 => by simp [h0]) a
  have hint4 : IntegrableOn (fun r => r ^ 2 * entrySq (fderiv ℝ u (r • e))) (Ioi a) :=
    ion _ (by unfold entrySq; fun_prop) _ hdcs (fun r h0 => by simp [h0, entrySq]) a
  calc (∫ r in Ioi a, ‖u (r • e)‖ ^ 2) = ∑ i : Fin 3, ∫ r in Ioi a, g i r ^ 2 := by
        rw [← integral_finsetSum _ (fun i _ => hint1 i)]
        simp_rw [sq_sum, hg]
    _ ≤ ∑ i : Fin 3, 4 * ∫ r in Ioi a, r ^ 2 * deriv (g i) r ^ 2 :=
        Finset.sum_le_sum fun i _ => hline a (g i) ha (hgc i) (hgs i)
    _ = 4 * ∫ r in Ioi a, r ^ 2 * ‖fderiv ℝ u (r • e) e‖ ^ 2 := by
        rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => hint2 i)]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
        simp only
        rw [sq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [(hgd i r).deriv]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (setIntegral_mono hint3 hint4 fun r => ?_) (by norm_num)
        exact mul_le_mul_of_nonneg_left (apply_sq_le _ _ he) (sq_nonneg r)

lemma ray_ennreal (hline : RayLineStatement) (R : Space → ℝ) (hRpos : ∀ y, 0 < R y)
    (hhom : ∀ (t : ℝ) (y : Space), 0 < t → R (t • y) = R y)
    (u : Space → Space) (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u) (e : Space)
    (he : ‖e‖ = 1) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) *
        (rayRegion R).indicator (fun y => ENNReal.ofReal (‖u y‖ ^ 2 / ‖y‖ ^ 2)) (r • e)
      ≤ 4 * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) *
        (rayRegion R).indicator (fun y => ENNReal.ofReal (entrySq (fderiv ℝ u y))) (r • e) := by
  set a := R e with ha_def
  have ha : 0 < a := hRpos e
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  have hemb : Topology.IsClosedEmbedding (fun r : ℝ => r • e) := isClosedEmbedding_smul_left he0
  have hcs : HasCompactSupport (fun r : ℝ => u (r • e)) := hs.comp_isClosedEmbedding hemb
  have hdc : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv one_ne_zero
  have hdcont : Continuous (fun r : ℝ => fderiv ℝ u (r • e)) :=
    hdc.comp (continuous_id.smul continuous_const)
  have hcont : Continuous (fun r : ℝ => u (r • e)) :=
    hu.continuous.comp (continuous_id.smul continuous_const)
  have hdcs : HasCompactSupport (fun r : ℝ => fderiv ℝ u (r • e)) :=
    (hs.fderiv (𝕜 := ℝ)).comp_isClosedEmbedding hemb
  have hi1 : IntegrableOn (fun r : ℝ => ‖u (r • e)‖ ^ 2) (Ioi a) :=
    ion _ (by fun_prop) _ hcs (fun r h0 => by simp [h0]) a
  have hi2 : IntegrableOn (fun r : ℝ => r ^ 2 * entrySq (fderiv ℝ u (r • e))) (Ioi a) :=
    ion _ (by unfold entrySq; fun_prop) _ hdcs (fun r h0 => by simp [h0, entrySq]) a
  have hmem : ∀ r : ℝ, 0 < r → (r • e ∈ rayRegion R ↔ a < r) := by
    intro r hr
    simp only [rayRegion, mem_ofPred_eq, hhom r e hr, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      he, mul_one, ha_def]
  have hset : ∀ f : ℝ → ENNReal, ∫⁻ r in Ioi a, f r = ∫⁻ r in Ioi (0 : ℝ), (Ioi a).indicator f r := by
    intro f
    rw [setLIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_left ha.le]
  have hL : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) *
        (rayRegion R).indicator (fun y => ENNReal.ofReal (‖u y‖ ^ 2 / ‖y‖ ^ 2)) (r • e)
      = ∫⁻ r in Ioi a, ENNReal.ofReal (‖u (r • e)‖ ^ 2) := by
    rw [hset]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 < r := hr
    by_cases h : a < r
    · have hin : r • e ∈ rayRegion R := (hmem r hr0).2 h
      rw [indicator_of_mem hin, indicator_of_mem (show r ∈ Ioi a from h)]
      rw [← ENNReal.ofReal_mul (sq_nonneg r), norm_smul, Real.norm_eq_abs, abs_of_pos hr0, he,
        mul_one]
      congr 1
      field_simp
    · have hout : r • e ∉ rayRegion R := fun hh => h ((hmem r hr0).1 hh)
      rw [indicator_of_notMem hout, indicator_of_notMem (show r ∉ Ioi a from h), mul_zero]
  have hR : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) *
        (rayRegion R).indicator (fun y => ENNReal.ofReal (entrySq (fderiv ℝ u y))) (r • e)
      = ∫⁻ r in Ioi a, ENNReal.ofReal (r ^ 2 * entrySq (fderiv ℝ u (r • e))) := by
    rw [hset]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 < r := hr
    by_cases h : a < r
    · have hin : r • e ∈ rayRegion R := (hmem r hr0).2 h
      rw [indicator_of_mem hin, indicator_of_mem (show r ∈ Ioi a from h),
        ← ENNReal.ofReal_mul (sq_nonneg r)]
    · have hout : r • e ∉ rayRegion R := fun hh => h ((hmem r hr0).1 hh)
      rw [indicator_of_notMem hout, indicator_of_notMem (show r ∉ Ioi a from h), mul_zero]
  rw [hL, hR, ← ofReal_integral_eq_lintegral_ofReal hi1
      (Filter.Eventually.of_forall fun r => by positivity),
    ← ofReal_integral_eq_lintegral_ofReal hi2
      (Filter.Eventually.of_forall fun r => mul_nonneg (sq_nonneg r) (by
        unfold entrySq
        exact Finset.sum_nonneg fun i _ => sq_nonneg _))]
  calc ENNReal.ofReal (∫ r in Ioi a, ‖u (r • e)‖ ^ 2)
      ≤ ENNReal.ofReal (4 * ∫ r in Ioi a, r ^ 2 * entrySq (fderiv ℝ u (r • e))) :=
        ENNReal.ofReal_le_ofReal (ray_real hline u hu hs e he a ha)
    _ = _ := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        simp

lemma main_one (hline : RayLineStatement) (R : Space → ℝ) (R₀ : ℝ) (hRm : Measurable R)
    (h0 : 0 < R₀) (hb : ∀ y, R₀ ≤ R y) (hhom : ∀ (t : ℝ) (y : Space), 0 < t → R (t • y) = R y)
    (u : Space → Space) (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u) :
    (∫ y in rayRegion R, ‖u y‖ ^ 2 / ‖y‖ ^ 2) ≤ 4 * ∫ y in rayRegion R, entrySq (fderiv ℝ u y) := by
  have hRpos : ∀ y, 0 < R y := fun y => h0.trans_le (hb y)
  have hS : MeasurableSet (rayRegion R) := measurableSet_lt hRm continuous_norm.measurable
  have hdc : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv one_ne_zero
  have hEc : Continuous (fun y => entrySq (fderiv ℝ u y)) := by
    unfold entrySq
    fun_prop
  have hEi : Integrable (fun y => entrySq (fderiv ℝ u y)) :=
    hEc.integrable_of_hasCompactSupport
      ((hs.fderiv (𝕜 := ℝ)).mono fun y hy h0 => hy (by simp [h0, entrySq]))
  have hf1 : Measurable (fun y : Space => ‖u y‖ ^ 2 / ‖y‖ ^ 2) :=
    (hu.continuous.norm.pow 2).measurable.div (continuous_norm.pow 2).measurable
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => by positivity)
      hf1.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => by
      unfold entrySq
      exact Finset.sum_nonneg fun i _ => sq_nonneg _) hEc.aestronglyMeasurable]
  have hB : (∫⁻ y in rayRegion R, ENNReal.ofReal (entrySq (fderiv ℝ u y))) ≠ ⊤ :=
    (hEi.integrableOn (s := rayRegion R)).lintegral_lt_top.ne
  have hAB : (∫⁻ y in rayRegion R, ENNReal.ofReal (‖u y‖ ^ 2 / ‖y‖ ^ 2)) ≤
      4 * ∫⁻ y in rayRegion R, ENNReal.ofReal (entrySq (fderiv ℝ u y)) := by
    rw [← lintegral_indicator hS, ← lintegral_indicator hS,
      polar _ (hf1.ennreal_ofReal.indicator hS), polar _ (hEc.measurable.ennreal_ofReal.indicator hS),
      ← lintegral_const_mul' (4 : ENNReal) _ (by simp)]
    exact lintegral_mono fun q =>
      ray_ennreal hline R hRpos hhom u hu hs (q : Space) (mem_sphere_zero_iff_norm.mp q.2)
  calc (∫⁻ y in rayRegion R, ENNReal.ofReal (‖u y‖ ^ 2 / ‖y‖ ^ 2)).toReal
      ≤ (4 * ∫⁻ y in rayRegion R, ENNReal.ofReal (entrySq (fderiv ℝ u y))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hB) hAB
    _ = _ := by simp [ENNReal.toReal_mul]

end RaySmoothInternal

open RaySmoothInternal in
theorem raySmooth_of (h1 : RayLineStatement) : RaySmoothStatement := by
  intro R R₀ R₁ hRm h0 hb hhom u hu hs
  exact main_one h1 R R₀ hRm h0 (fun y => (hb y).1) hhom u (hu.of_le (by simp)) hs

end Exterior

end CellCert

end Breakdown
