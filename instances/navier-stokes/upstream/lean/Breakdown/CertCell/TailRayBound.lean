import Breakdown.CertCell.TailStatements
import Breakdown.FracCell.RaySmooth
import Breakdown.FracCell.RayLine
import Breakdown.FracCell.ReductionAdjointMollifySecondApprox
import Breakdown.FracCell.ReductionAdjointFrameMirrorLeaves

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal Convolution

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

open SteadyCert

def IsRayExterior (S : Set Space) : Prop :=
  MeasurableSet S ∧ ∀ e : Space, ‖e‖ = 1 →
    (∀ t : ℝ, 0 < t → t • e ∉ S) ∨ ∃ a : ℝ, 0 < a ∧ ∀ t : ℝ, 0 < t → (t • e ∈ S ↔ a < t)

def radialApply (A : Space →L[ℝ] Space) (y : Space) : Space := A (‖y‖⁻¹ • y)

def RadialRayStatement : Prop :=
  ∀ S : Set Space, IsRayExterior S →
    ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)), MemLp v 6 volume →
      AEStronglyMeasurable G volume → Integrable (fun y => entrySq (G y)) → IsWeakGradient v G →
      ∫⁻ y in S, ENNReal.ofReal (‖v y‖ ^ 2 / ‖y‖ ^ 2)
        ≤ 4 * ∫⁻ y in S, ENNReal.ofReal (‖radialApply (G y) y‖ ^ 2)

namespace RadialRayInternal

open CellCert.Exterior CellCert.Exterior.RaySmoothInternal

private theorem line_sum (u : Space → Space) (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    (e : Space) (he : e ≠ 0) (a : ℝ) (ha : 0 < a) :
    ∫ r in Ioi a, ‖u (r • e)‖ ^ 2 ≤ 4 * ∫ r in Ioi a, r ^ 2 * ‖fderiv ℝ u (r • e) e‖ ^ 2 := by
  have hemb : Topology.IsClosedEmbedding (fun r : ℝ => r • e) := isClosedEmbedding_smul_left he
  have hline : HasCompactSupport (fun r : ℝ => u (r • e)) := hs.comp_isClosedEmbedding hemb
  have hdline : HasCompactSupport (fun r : ℝ => fderiv ℝ u (r • e)) :=
    (hs.fderiv (𝕜 := ℝ)).comp_isClosedEmbedding hemb
  have hsm : Continuous (fun r : ℝ => r • e) := continuous_id.smul continuous_const
  have hDc : Continuous (fun r : ℝ => fderiv ℝ u (r • e)) :=
    (hu.continuous_fderiv one_ne_zero).comp hsm
  have hcomp : ∀ i : Fin 3, ContDiff ℝ 1 (fun r : ℝ => u (r • e) i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp (hu.comp (contDiff_id.smul contDiff_const))
  have hsupp : ∀ i : Fin 3, HasCompactSupport (fun r : ℝ => u (r • e) i) := fun i =>
    hline.mono fun r hr h0 => hr (by simp [h0])
  have hder : ∀ (i : Fin 3) (r : ℝ),
      HasDerivAt (fun r : ℝ => u (r • e) i) (fderiv ℝ u (r • e) e i) r := by
    intro i r
    have h1 : HasDerivAt (fun r : ℝ => r • e) e r := by
      simpa using (hasDerivAt_id r).smul_const e
    exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt r
      (((hu.differentiable one_ne_zero) (r • e)).hasFDerivAt.comp_hasDerivAt r h1)
  have hi1 : ∀ i : Fin 3, IntegrableOn (fun r : ℝ => u (r • e) i ^ 2) (Ioi a) := fun i =>
    ion _ ((hcomp i).continuous.pow 2) _ hline (fun r h0 => by simp [h0]) a
  have hi2 : ∀ i : Fin 3, IntegrableOn (fun r : ℝ => r ^ 2 * (fderiv ℝ u (r • e) e i) ^ 2) (Ioi a) :=
    fun i => ion _ (by fun_prop) _ hdline (fun r h0 => by simp [h0]) a
  calc ∫ r in Ioi a, ‖u (r • e)‖ ^ 2 = ∑ i : Fin 3, ∫ r in Ioi a, u (r • e) i ^ 2 := by
        rw [← integral_finsetSum _ fun i _ => hi1 i]
        simp_rw [sq_sum]
    _ ≤ ∑ i : Fin 3, 4 * ∫ r in Ioi a, r ^ 2 * deriv (fun r : ℝ => u (r • e) i) r ^ 2 :=
        Finset.sum_le_sum fun i _ => rayLine a _ ha (hcomp i) (hsupp i)
    _ = 4 * ∫ r in Ioi a, r ^ 2 * ‖fderiv ℝ u (r • e) e‖ ^ 2 := by
        rw [← Finset.mul_sum, ← integral_finsetSum _ fun i _ => ?_]
        · congr 1
          refine integral_congr_ae (Eventually.of_forall fun r => ?_)
          simp only [(hder _ r).deriv]
          rw [sq_sum, Finset.mul_sum]
        · simp only [(hder i _).deriv]
          exact hi2 i

private theorem ray_cut (F : Space → ℝ≥0∞) (S : Set Space) (e : Space) (a : ℝ) (ha : 0 < a)
    (hmem : ∀ t : ℝ, 0 < t → (t • e ∈ S ↔ a < t)) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * S.indicator F (r • e)
      = ∫⁻ r in Ioi a, ENNReal.ofReal (r ^ 2) * F (r • e) := by
  have hpt : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * S.indicator F (r • e)
      = (Ioi a).indicator (fun r => ENNReal.ofReal (r ^ 2) * F (r • e)) r := by
    intro r hr
    by_cases h : a < r
    · rw [indicator_of_mem ((hmem r hr).2 h), indicator_of_mem (show r ∈ Ioi a from h)]
    · rw [indicator_of_notMem (fun hh => h ((hmem r hr).1 hh)),
        indicator_of_notMem (show r ∉ Ioi a from h), mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, setLIntegral_indicator measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_left ha.le]

private theorem dir_bound (S : Set Space) (hS : IsRayExterior S) (u : Space → Space)
    (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u) (e : Space) (he : ‖e‖ = 1) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) *
        S.indicator (fun y => ENNReal.ofReal (‖u y‖ ^ 2 / ‖y‖ ^ 2)) (r • e)
      ≤ 4 * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) *
        S.indicator (fun y => ENNReal.ofReal (‖radialApply (fderiv ℝ u y) y‖ ^ 2)) (r • e) := by
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  rcases hS.2 e he with hmiss | ⟨a, ha, hmem⟩
  · have hz : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) *
        S.indicator (fun y => ENNReal.ofReal (‖u y‖ ^ 2 / ‖y‖ ^ 2)) (r • e) = 0 := fun r hr => by
      rw [indicator_of_notMem (hmiss r hr), mul_zero]
    rw [setLIntegral_congr_fun measurableSet_Ioi hz]
    simp
  · rw [ray_cut _ S e a ha hmem, ray_cut _ S e a ha hmem]
    have hn : ∀ r ∈ Ioi a, ‖r • e‖ = r := fun r hr => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (ha.trans hr), he, mul_one]
    have h1 : ∀ r ∈ Ioi a, ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (‖u (r • e)‖ ^ 2 / ‖r • e‖ ^ 2)
        = ENNReal.ofReal (‖u (r • e)‖ ^ 2) := fun r hr => by
      have hr0 : 0 < r := ha.trans hr
      rw [← ENNReal.ofReal_mul (sq_nonneg r), hn r hr]
      congr 1
      field_simp
    have h2 : ∀ r ∈ Ioi a, ENNReal.ofReal (r ^ 2) *
        ENNReal.ofReal (‖radialApply (fderiv ℝ u (r • e)) (r • e)‖ ^ 2)
        = ENNReal.ofReal (r ^ 2 * ‖fderiv ℝ u (r • e) e‖ ^ 2) := fun r hr => by
      have hr0 : 0 < r := ha.trans hr
      rw [← ENNReal.ofReal_mul (sq_nonneg r), radialApply, hn r hr, smul_smul,
        inv_mul_cancel₀ hr0.ne', one_smul]
    have hline : HasCompactSupport (fun r : ℝ => u (r • e)) :=
      hs.comp_isClosedEmbedding (isClosedEmbedding_smul_left he0)
    have hdline : HasCompactSupport (fun r : ℝ => fderiv ℝ u (r • e)) :=
      (hs.fderiv (𝕜 := ℝ)).comp_isClosedEmbedding (isClosedEmbedding_smul_left he0)
    have hsm : Continuous (fun r : ℝ => r • e) := continuous_id.smul continuous_const
    have hDc : Continuous (fun r : ℝ => fderiv ℝ u (r • e)) :=
      (hu.continuous_fderiv one_ne_zero).comp hsm
    have hi1 : IntegrableOn (fun r : ℝ => ‖u (r • e)‖ ^ 2) (Ioi a) :=
      ion _ ((hu.continuous.comp hsm).norm.pow 2) _ hline (fun r h0 => by simp [h0]) a
    have hi2 : IntegrableOn (fun r : ℝ => r ^ 2 * ‖fderiv ℝ u (r • e) e‖ ^ 2) (Ioi a) :=
      ion _ (by fun_prop) _ hdline (fun r h0 => by simp [h0]) a
    rw [setLIntegral_congr_fun measurableSet_Ioi h1, setLIntegral_congr_fun measurableSet_Ioi h2,
      ← ofReal_integral_eq_lintegral_ofReal hi1 (Eventually.of_forall fun r => by positivity),
      ← ofReal_integral_eq_lintegral_ofReal hi2 (Eventually.of_forall fun r => by positivity)]
    calc ENNReal.ofReal (∫ r in Ioi a, ‖u (r • e)‖ ^ 2)
        ≤ ENNReal.ofReal (4 * ∫ r in Ioi a, r ^ 2 * ‖fderiv ℝ u (r • e) e‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (line_sum u hu hs e he0 a ha)
      _ = _ := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          simp

private theorem slope_measurable {A : Space → (Space →L[ℝ] Space)} (hA : Measurable A) :
    Measurable (fun y : Space => ENNReal.ofReal (‖radialApply (A y) y‖ ^ 2)) := by
  have hb : Measurable (fun y : Space => ‖y‖⁻¹ • y) := measurable_norm.inv.smul measurable_id
  have h := isBoundedBilinearMap_apply.continuous.measurable.comp (hA.prodMk hb)
  exact (h.norm.pow_const 2).ennreal_ofReal

private theorem compact_bound (S : Set Space) (hS : IsRayExterior S) (u : Space → Space)
    (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u) :
    ∫⁻ y in S, ENNReal.ofReal (‖u y‖ ^ 2 / ‖y‖ ^ 2)
      ≤ 4 * ∫⁻ y in S, ENNReal.ofReal (‖radialApply (fderiv ℝ u y) y‖ ^ 2) := by
  have hm1 : Measurable (fun y : Space => ENNReal.ofReal (‖u y‖ ^ 2 / ‖y‖ ^ 2)) :=
    ((hu.continuous.norm.pow 2).measurable.div (continuous_norm.pow 2).measurable).ennreal_ofReal
  have hm2 := slope_measurable (hu.continuous_fderiv one_ne_zero).measurable
  rw [← lintegral_indicator hS.1, ← lintegral_indicator hS.1, polar _ (hm1.indicator hS.1),
    polar _ (hm2.indicator hS.1), ← lintegral_const_mul' 4 _ (by simp)]
  exact lintegral_mono fun q => dir_bound S hS u hu hs q (mem_sphere_zero_iff_norm.mp q.2)

private theorem sq_le_split (b c : Space) {θ : ℝ} (hθ : 0 < θ) :
    ‖b + c‖ ^ 2 ≤ (1 + θ) * ‖b‖ ^ 2 + (1 + θ⁻¹) * ‖c‖ ^ 2 := by
  have h1 : ‖b + c‖ ^ 2 ≤ (‖b‖ + ‖c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le b c) 2
  have h2 : 0 ≤ θ⁻¹ * (θ * ‖b‖ - ‖c‖) ^ 2 := by positivity
  have h3 : θ⁻¹ * (θ * ‖b‖ - ‖c‖) ^ 2 = θ * ‖b‖ ^ 2 - 2 * ‖b‖ * ‖c‖ + θ⁻¹ * ‖c‖ ^ 2 := by
    field_simp
    ring
  nlinarith

private theorem entrySq_nonneg' (A : Space →L[ℝ] Space) : 0 ≤ entrySq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem slope_diff_le (A B : Space →L[ℝ] Space) (y : Space) :
    ‖radialApply A y - radialApply B y‖ ^ 2 ≤ entrySq (A - B) := by
  by_cases hy : y = 0
  · subst hy
    simp only [radialApply, smul_zero, map_zero, sub_zero, norm_zero]
    rw [zero_pow two_ne_zero]
    exact entrySq_nonneg' _
  · have he : ‖‖y‖⁻¹ • y‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)]
    have h := apply_sq_le (A - B) _ he
    rw [radialApply, radialApply, ← sub_apply]
    exact h

private theorem slope_aesm {G : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume) :
    AEStronglyMeasurable (fun y : Space => radialApply (G y) y) volume := by
  have hb : Measurable (fun y : Space => ‖y‖⁻¹ • y) := measurable_norm.inv.smul measurable_id
  exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
    (hG.prodMk hb.aestronglyMeasurable)

private theorem transfer {S : Set Space} (u : ℕ → Space → Space)
    (D : ℕ → Space → (Space →L[ℝ] Space)) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (hu : ∀ n, AEStronglyMeasurable (u n) volume) (hG : AEStronglyMeasurable G volume)
    (hlim : ∀ᵐ y, Tendsto (fun n => u n y) atTop (𝓝 (v y)))
    (hD : Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (entrySq (D n y - G y))) atTop (𝓝 0))
    (hineq : ∀ᶠ n in atTop, ∫⁻ y in S, ENNReal.ofReal (‖u n y‖ ^ 2 / ‖y‖ ^ 2)
      ≤ 4 * ∫⁻ y in S, ENNReal.ofReal (‖radialApply (D n y) y‖ ^ 2)) :
    ∫⁻ y in S, ENNReal.ofReal (‖v y‖ ^ 2 / ‖y‖ ^ 2)
      ≤ 4 * ∫⁻ y in S, ENNReal.ofReal (‖radialApply (G y) y‖ ^ 2) := by
  set X := ∫⁻ y in S, ENNReal.ofReal (‖radialApply (G y) y‖ ^ 2) with hX
  set ε : ℕ → ℝ≥0∞ := fun n => ∫⁻ y, ENNReal.ofReal (entrySq (D n y - G y)) with hε
  have hfat : ∫⁻ y in S, ENNReal.ofReal (‖v y‖ ^ 2 / ‖y‖ ^ 2) ≤
      liminf (fun n => ∫⁻ y in S, ENNReal.ofReal (‖u n y‖ ^ 2 / ‖y‖ ^ 2)) atTop := by
    calc ∫⁻ y in S, ENNReal.ofReal (‖v y‖ ^ 2 / ‖y‖ ^ 2)
        = ∫⁻ y in S, liminf (fun n => ENNReal.ofReal (‖u n y‖ ^ 2 / ‖y‖ ^ 2)) atTop := by
          refine lintegral_congr_ae (ae_restrict_of_ae ?_)
          filter_upwards [hlim] with y hy
          exact ((ENNReal.tendsto_ofReal (((hy.norm).pow 2).div_const _)).liminf_eq).symm
      _ ≤ _ := lintegral_liminf_le' fun n => by
          have h1 : AEMeasurable (fun y => ‖u n y‖ ^ 2) volume := ((hu n).norm.pow 2).aemeasurable
          have h2 : Measurable (fun y : Space => ‖y‖ ^ 2) := measurable_norm.pow_const 2
          exact (h1.div h2.aemeasurable).ennreal_ofReal.restrict
  have hGs : AEMeasurable (fun y => ENNReal.ofReal (‖radialApply (G y) y‖ ^ 2)) volume :=
    (((slope_aesm hG).norm.pow 2).aemeasurable).ennreal_ofReal
  have hbound : ∀ θ : ℝ, 0 < θ →
      ∫⁻ y in S, ENNReal.ofReal (‖v y‖ ^ 2 / ‖y‖ ^ 2) ≤ 4 * (ENNReal.ofReal (1 + θ) * X) := by
    intro θ hθ
    have hpt : ∀ n y, ENNReal.ofReal (‖radialApply (D n y) y‖ ^ 2) ≤
        ENNReal.ofReal (1 + θ) * ENNReal.ofReal (‖radialApply (G y) y‖ ^ 2)
          + ENNReal.ofReal (1 + θ⁻¹) * ENNReal.ofReal (entrySq (D n y - G y)) := by
      intro n y
      have h2 := sq_le_split (radialApply (G y) y) (radialApply (D n y) y - radialApply (G y) y) hθ
      rw [add_sub_cancel] at h2
      have h3 := slope_diff_le (D n y) (G y) y
      rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by positivity) (entrySq_nonneg' _))]
      refine ENNReal.ofReal_le_ofReal (h2.trans ?_)
      gcongr
    have hn : ∀ n, ∫⁻ y in S, ENNReal.ofReal (‖radialApply (D n y) y‖ ^ 2) ≤
        ENNReal.ofReal (1 + θ) * X + ENNReal.ofReal (1 + θ⁻¹) * ε n := by
      intro n
      calc ∫⁻ y in S, ENNReal.ofReal (‖radialApply (D n y) y‖ ^ 2)
          ≤ ∫⁻ y in S, (ENNReal.ofReal (1 + θ) * ENNReal.ofReal (‖radialApply (G y) y‖ ^ 2)
              + ENNReal.ofReal (1 + θ⁻¹) * ENNReal.ofReal (entrySq (D n y - G y))) :=
            lintegral_mono (hpt n)
        _ = ENNReal.ofReal (1 + θ) * X +
              ENNReal.ofReal (1 + θ⁻¹) * ∫⁻ y in S, ENNReal.ofReal (entrySq (D n y - G y)) := by
            rw [lintegral_add_left' (hGs.const_mul _).restrict,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (1 + θ) * X + ENNReal.ofReal (1 + θ⁻¹) * ε n := by
            gcongr
            exact setLIntegral_le_lintegral _ _
    have hlim2 : Tendsto (fun n => 4 * (ENNReal.ofReal (1 + θ) * X + ENNReal.ofReal (1 + θ⁻¹) * ε n))
        atTop (𝓝 (4 * (ENNReal.ofReal (1 + θ) * X))) := by
      have h1 : Tendsto (fun n => ENNReal.ofReal (1 + θ⁻¹) * ε n) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul hD (Or.inr ENNReal.ofReal_ne_top)
      have h2 := (tendsto_const_nhds (x := ENNReal.ofReal (1 + θ) * X)).add h1
      rw [add_zero] at h2
      exact ENNReal.Tendsto.const_mul h2 (Or.inr (by norm_num))
    calc ∫⁻ y in S, ENNReal.ofReal (‖v y‖ ^ 2 / ‖y‖ ^ 2)
        ≤ liminf (fun n => ∫⁻ y in S, ENNReal.ofReal (‖u n y‖ ^ 2 / ‖y‖ ^ 2)) atTop := hfat
      _ ≤ liminf (fun n => 4 * (ENNReal.ofReal (1 + θ) * X + ENNReal.ofReal (1 + θ⁻¹) * ε n)) atTop := by
          refine liminf_le_liminf ?_
          filter_upwards [hineq] with n hn'
          exact hn'.trans (by gcongr; exact hn n)
      _ = _ := hlim2.liminf_eq
  by_cases hXt : X = ⊤
  · rw [hXt]
    simp
  · have h1 : Tendsto (fun m : ℕ => ENNReal.ofReal (1 + 1 / ((m : ℝ) + 1))) atTop
        (𝓝 (ENNReal.ofReal (1 + 0))) :=
      ENNReal.tendsto_ofReal (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat)
    have ht := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const h1 (Or.inr hXt))
      (Or.inr (by norm_num : (4 : ℝ≥0∞) ≠ ⊤))
    rw [add_zero, ENNReal.ofReal_one, one_mul] at ht
    exact ge_of_tendsto ht (Eventually.of_forall fun m => hbound _ (by positivity))

private theorem smooth_bound (S : Set Space) (hS : IsRayExterior S) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) (h6 : MemLp w 6 volume) (hE : Integrable (fun y => entrySq (fderiv ℝ w y))) :
    ∫⁻ y in S, ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2)
      ≤ 4 * ∫⁻ y in S, ENNReal.ofReal (‖radialApply (fderiv ℝ w y) y‖ ^ 2) := by
  have hc := FracInternal.FrameMirrorLeaves.cutoffGradient w hw h6 hE
  have hR : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  refine transfer (fun n z => radialCutoff ((n : ℝ) + 1) z • w z)
    (fun n y => fderiv ℝ (fun z => radialCutoff ((n : ℝ) + 1) z • w z) y) w (fun y => fderiv ℝ w y)
    (fun n => ((contDiff_radialCutoff (hpos n)).continuous.smul hw.continuous).aestronglyMeasurable)
    (hw.continuous_fderiv (by simp)).aestronglyMeasurable ?_ (hc.comp hR) ?_
  · refine ae_of_all _ fun y => tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    rw [radialCutoff_eq_one (hpos n) (by linarith), one_smul]
  · exact Eventually.of_forall fun n => compact_bound S hS _
      (((contDiff_radialCutoff (hpos n)).smul hw).of_le (by simp))
      (hasCompactSupport_radialCutoff (hpos n)).smul_right

end RadialRayInternal

open RadialRayInternal CellCert.Reduction.MollifySecondApproxInternal in
theorem radialRay : RadialRayStatement := by
  intro S hS v G h6 hGm hE hw
  have hloc : LocallyIntegrable v volume := hw.1
  have hwo : IsWeakGradientOf v G := fun φ hφ j => by
    rw [hw.2.2 φ hφ j, neg_neg]
  have hGc : ∀ j : Fin 3, AEStronglyMeasurable (fun y => G y (unitVector j)) volume := fun j =>
    hGm.apply_continuousLinearMap _
  have hGi : ∀ j : Fin 3, Integrable (fun y => ‖G y (unitVector j)‖ ^ 2) := fun j =>
    hE.mono' ((hGc j).norm.pow 2) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j))
  have hGl : ∀ j : Fin 3, LocallyIntegrable (fun y => G y (unitVector j)) volume := fun j =>
    ((memLp_two_iff_integrable_sq_norm (hGc j)).2 (hGi j)).locallyIntegrable (by norm_num)
  set w : ℕ → Space → Space := fun n =>
    (kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v with hwdef
  have hder : ∀ n y (j : Fin 3), fderiv ℝ (w n) y (unitVector j) =
      ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun z => G z (unitVector j)) y := fun n y j =>
    mollify_fderiv_apply' _ v G hloc hwo y j
  have hwc : ∀ n, ContDiff ℝ ∞ (w n) := fun n =>
    (kernelBump n).hasCompactSupport_normed.contDiff_convolution_left _ (kernelBump n).contDiff_normed hloc
  have h6' : MemLp v ((6 : ℕ) : ℝ≥0∞) volume := by exact_mod_cast h6
  have hI6 : Integrable (fun z => ‖v z‖ ^ 6) := h6'.integrable_norm_pow (by norm_num)
  have hw6 : ∀ n, MemLp (w n) 6 volume := by
    intro n
    have hm : AEStronglyMeasurable (w n) volume := (hwc n).continuous.aestronglyMeasurable
    have hi : Integrable (fun y => ‖w n y‖ ^ 6) :=
      ((kernelBump n).integrable_normed.integrable_convolution _ hI6).mono' (hm.norm.pow 6)
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact normPow_conv_le (kernelBump n) v 6 (by norm_num) hI6 y)
    refine (integrable_norm_rpow_iff hm (by norm_num) (by norm_num)).1 ?_
    simpa using hi
  have hwE : ∀ n, Integrable (fun y => entrySq (fderiv ℝ (w n) y)) := by
    intro n
    simp only [entrySq, hder]
    exact integrable_finsetSum _ fun j _ => (conv_sq_integral_le _ _ (hGl j) (hGi j)).1
  have hcol : ∀ j : Fin 3, Tendsto (fun n => ∫⁻ y, ENNReal.ofReal
      (‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun z => G z (unitVector j)) y - G y (unitVector j)‖ ^ 2)) atTop (𝓝 0) := by
    intro j
    have h := ENNReal.tendsto_ofReal (conv_sq_tendsto _ (hGc j) (hGi j))
    rw [ENNReal.ofReal_zero] at h
    refine h.congr fun n => ?_
    exact ofReal_integral_eq_lintegral_ofReal (diff_sq_integrable _ _ (hGc j) (hGi j))
      (Eventually.of_forall fun y => by positivity)
  have hD : Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - G y))) atTop (𝓝 0) := by
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => hcol j
    simp only [Finset.sum_const_zero] at hsum
    refine hsum.congr fun n => ?_
    rw [← lintegral_finsetSum']
    · refine lintegral_congr fun y => ?_
      rw [entrySq, ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sub_apply, hder]
    · intro j _
      have hc : Continuous ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun z => G z (unitVector j)) :=
        ((kernelBump n).hasCompactSupport_normed.contDiff_convolution_left _ (kernelBump n).contDiff_normed
          (hGl j) (n := 0)).continuous
      exact (((hc.aestronglyMeasurable.sub (hGc j)).norm.pow 2).aemeasurable).ennreal_ofReal
  refine transfer w (fun n y => fderiv ℝ (w n) y) v G
    (fun n => (hwc n).continuous.aestronglyMeasurable) hGm ?_ hD
    (Eventually.of_forall fun n => smooth_bound S hS (w n) (hwc n) (hw6 n) (hwE n))
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (φ := kernelBump) (K := 2)
    kernelBump_rOut (Eventually.of_forall fun n => le_of_eq (by
      show 1 / ((n : ℝ) + 1) = 2 * (1 / (2 * ((n : ℝ) + 1)))
      field_simp)) hloc

end TailBand

end CertCell

end Breakdown
