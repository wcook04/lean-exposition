import Breakdown.FracCert.StFree
import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff ENNReal NNReal
open MeasureTheory Filter Topology
open scoped Convolution

noncomputable section

namespace Breakdown

namespace FracInternal

open SteadyCert

private theorem weight_fderiv_apply {δ : ℝ} (hδ : 0 < δ) (j : Fin 3) (y : Space) :
    fderiv ℝ (fun z : Space => z j * (‖z‖ ^ 2 + δ)⁻¹) y (unitVector j) =
      (‖y‖ ^ 2 + δ)⁻¹ - 2 * y j ^ 2 * ((‖y‖ ^ 2 + δ) ^ 2)⁻¹ := by
  have hne : ‖y‖ ^ 2 + δ ≠ 0 := by positivity
  have h1 : HasFDerivAt (fun z : Space => z j) (EuclideanSpace.proj j : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun z : Space => ‖z‖ ^ 2 + δ) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt.add_const δ
  have h3 : HasFDerivAt (fun z : Space => (‖z‖ ^ 2 + δ)⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-((‖y‖ ^ 2 + δ) ^ 2)⁻¹)).comp
        (2 • innerSL ℝ y)) y :=
    (hasFDerivAt_inv hne).comp y h2
  have h4 := h1.fun_mul h3
  rw [h4.fderiv]
  simp [unitVector, EuclideanSpace.inner_single_right]
  ring

private theorem normSq_fderiv_apply {u : Space → Space} (hu : Differentiable ℝ u) (y e : Space) :
    fderiv ℝ (fun z => ‖u z‖ ^ 2) y e = 2 * inner ℝ (u y) (fderiv ℝ u y e) := by
  rw [((hu y).hasFDerivAt.norm_sq).fderiv]
  simp

private theorem contDiff_weight {δ : ℝ} (hδ : 0 < δ) (j : Fin 3) :
    ContDiff ℝ ∞ (fun z : Space => z j * (‖z‖ ^ 2 + δ)⁻¹) :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.mul
    (((contDiff_norm_sq ℝ).add contDiff_const).inv fun z => by positivity)

private theorem sum_sq_coord (y : Space) : ∑ j : Fin 3, y j ^ 2 = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp

private theorem integrable_mul_of_support {a b : Space → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hs : HasCompactSupport a) : Integrable (fun x => a x * b x) :=
  (ha.mul hb).integrable_of_hasCompactSupport hs.mul_right

private theorem neg_partial_le {u : Space → Space} (hud : Differentiable ℝ u) {δ : ℝ} (hδ : 0 < δ) (y : Space)
    (j : Fin 3) :
    -(fderiv ℝ (fun z => ‖u z‖ ^ 2) y (unitVector j) * (y j * (‖y‖ ^ 2 + δ)⁻¹)) ≤
      ‖u y‖ ^ 2 * y j ^ 2 * ((‖y‖ ^ 2 + δ)⁻¹) ^ 2 / 2 + 2 * ‖fderiv ℝ u y (unitVector j)‖ ^ 2 := by
  rw [normSq_fderiv_apply hud]
  have hin := abs_real_inner_le_norm (u y) (fderiv ℝ u y (unitVector j))
  set p := inner ℝ (u y) (fderiv ℝ u y (unitVector j))
  set q := ‖u y‖
  set c := ‖fderiv ℝ u y (unitVector j)‖
  set t := (‖y‖ ^ 2 + δ)⁻¹
  set s := y j
  have ht : 0 ≤ t := by positivity
  have hq : 0 ≤ q := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have h1 : -(2 * p * (s * t)) ≤ 2 * |p| * |s| * t := by
    have := neg_abs_le (2 * p * (s * t))
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ht, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
    linarith
  have h2 : 2 * |p| * |s| * t ≤ 2 * (q * |s| * t) * c := by
    have : |p| * (|s| * t) ≤ q * c * (|s| * t) :=
      mul_le_mul_of_nonneg_right hin (mul_nonneg (abs_nonneg _) ht)
    nlinarith
  have h3 : 2 * (q * |s| * t) * c ≤ (q * |s| * t) ^ 2 / 2 + 2 * c ^ 2 := by
    nlinarith [sq_nonneg (q * |s| * t - 2 * c)]
  have h4 : (q * |s| * t) ^ 2 = q ^ 2 * s ^ 2 * t ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
  linarith

private theorem weight_sum_ge {δ : ℝ} (hδ : 0 < δ) (y : Space) :
    (‖y‖ ^ 2 + δ)⁻¹ ≤ ∑ j : Fin 3, fderiv ℝ (fun z : Space => z j * (‖z‖ ^ 2 + δ)⁻¹) y (unitVector j) := by
  rw [Finset.sum_congr rfl (fun j _ => weight_fderiv_apply hδ j y), Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, sum_sq_coord]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hR : 0 < ‖y‖ ^ 2 + δ := by positivity
  have hsR : ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + δ := by linarith
  have h : ‖y‖ ^ 2 * ((‖y‖ ^ 2 + δ) ^ 2)⁻¹ ≤ (‖y‖ ^ 2 + δ)⁻¹ := by
    rw [pow_two (‖y‖ ^ 2 + δ), mul_inv, ← mul_assoc]
    refine mul_le_of_le_one_left (inv_nonneg.2 hR.le) ?_
    rw [← div_eq_mul_inv]
    exact div_le_one_of_le₀ hsR hR.le
  push_cast
  linarith

private theorem sq_weight_le {δ : ℝ} (hδ : 0 < δ) (y : Space) :
    ‖y‖ ^ 2 * ((‖y‖ ^ 2 + δ)⁻¹) ^ 2 ≤ (‖y‖ ^ 2 + δ)⁻¹ := by
  have hR : 0 < ‖y‖ ^ 2 + δ := by positivity
  have hsR : ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + δ := by linarith
  rw [pow_two ((‖y‖ ^ 2 + δ)⁻¹), ← mul_assoc]
  refine mul_le_of_le_one_left (inv_nonneg.2 hR.le) ?_
  rw [← div_eq_mul_inv]
  exact div_le_one_of_le₀ hsR hR.le

private theorem regularizedInverseSquare_le (u : Space → Space) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (δ : ℝ) (hδ : 0 < δ) :
    ∫ y, ‖u y‖ ^ 2 / (‖y‖ ^ 2 + δ) ≤ 4 * ∫ y, entrySq (fderiv ℝ u y) := by
  set w : Space → ℝ := fun y => ‖u y‖ ^ 2 with hw
  set g : Fin 3 → Space → ℝ := fun j z => z j * (‖z‖ ^ 2 + δ)⁻¹ with hg
  set E : Space → ℝ := fun y => entrySq (fderiv ℝ u y) with hE
  have hud : Differentiable ℝ u := hu.differentiable (by simp)
  have hwc : ContDiff ℝ ∞ w := hu.norm_sq ℝ
  have hwd : Differentiable ℝ w := hwc.differentiable (by simp)
  have hws : HasCompactSupport w := hc.mono fun y hy h0 => hy (by simp [hw, h0])
  have hgc : ∀ j, ContDiff ℝ ∞ (g j) := fun j => contDiff_weight hδ j
  have hgd : ∀ j, Differentiable ℝ (g j) := fun j => (hgc j).differentiable (by simp)
  have hrc : Continuous (fun y : Space => (‖y‖ ^ 2 + δ)⁻¹) :=
    ((continuous_norm.pow 2).add continuous_const).inv₀ fun y => (add_pos_of_nonneg_of_pos (sq_nonneg ‖y‖) hδ).ne'
  have hdw : ∀ j, Continuous (fun y => fderiv ℝ w y (unitVector j)) := fun j =>
    (hwc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdws : ∀ j, HasCompactSupport (fun y => fderiv ℝ w y (unitVector j)) := fun j =>
    (hws.fderiv (𝕜 := ℝ)).mono fun y hy h0 => hy (by simp [h0])
  have hdg : ∀ j, Continuous (fun y => fderiv ℝ (g j) y (unitVector j)) := fun j =>
    ((hgc j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hEc : Continuous E := by
    simp only [hE, entrySq]
    exact continuous_finsetSum _ fun i _ =>
      (((hu.continuous_fderiv (by simp)).clm_apply continuous_const).norm).pow 2
  have hEs : HasCompactSupport E :=
    (hc.fderiv (𝕜 := ℝ)).mono fun y hy h0 => hy (by simp [hE, entrySq, h0])
  have hEi : Integrable E := hEc.integrable_of_hasCompactSupport hEs
  have hAi : Integrable (fun y => w y * (‖y‖ ^ 2 + δ)⁻¹) :=
    integrable_mul_of_support hwc.continuous hrc hws
  have hIi : ∀ j, Integrable (fun y => w y * fderiv ℝ (g j) y (unitVector j)) := fun j =>
    integrable_mul_of_support hwc.continuous (hdg j) hws
  have hJi : ∀ j, Integrable (fun y => fderiv ℝ w y (unitVector j) * g j y) := fun j =>
    integrable_mul_of_support (hdw j) (hgc j).continuous (hdws j)
  have ibp : ∀ j, ∫ y, w y * fderiv ℝ (g j) y (unitVector j) =
      -∫ y, fderiv ℝ w y (unitVector j) * g j y := fun j =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hJi j) (hIi j)
      (integrable_mul_of_support hwc.continuous (hgc j).continuous hws)
      (fun x _ => hwd x) (fun x _ => hgd j x)
  have hpt1 : ∀ y, w y * (‖y‖ ^ 2 + δ)⁻¹ ≤ ∑ j : Fin 3, w y * fderiv ℝ (g j) y (unitVector j) := by
    intro y
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (weight_sum_ge hδ y) (by positivity)
  have hpt2 : ∀ y, ∑ j : Fin 3, -(fderiv ℝ w y (unitVector j) * g j y) ≤
      w y * (‖y‖ ^ 2 + δ)⁻¹ / 2 + 2 * E y := by
    intro y
    have hs := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => neg_partial_le hud hδ y j
    refine hs.trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_mul, ← Finset.mul_sum,
      sum_sq_coord]
    have h := sq_weight_le hδ y
    have hq : 0 ≤ ‖u y‖ ^ 2 := by positivity
    have : ‖u y‖ ^ 2 * (‖y‖ ^ 2 * ((‖y‖ ^ 2 + δ)⁻¹) ^ 2) ≤ ‖u y‖ ^ 2 * (‖y‖ ^ 2 + δ)⁻¹ :=
      mul_le_mul_of_nonneg_left h hq
    simp only [hw, hE, entrySq]
    nlinarith
  have hsumI : Integrable (fun y => ∑ j : Fin 3, w y * fderiv ℝ (g j) y (unitVector j)) :=
    integrable_finsetSum _ fun j _ => hIi j
  have hsumJ : Integrable (fun y => ∑ j : Fin 3, -(fderiv ℝ w y (unitVector j) * g j y)) :=
    integrable_finsetSum _ fun j _ => (hJi j).neg
  have key : ∫ y, w y * (‖y‖ ^ 2 + δ)⁻¹ ≤
      (∫ y, w y * (‖y‖ ^ 2 + δ)⁻¹) / 2 + 2 * ∫ y, E y := by
    calc ∫ y, w y * (‖y‖ ^ 2 + δ)⁻¹
        ≤ ∫ y, ∑ j : Fin 3, w y * fderiv ℝ (g j) y (unitVector j) := integral_mono hAi hsumI hpt1
      _ = ∑ j : Fin 3, ∫ y, w y * fderiv ℝ (g j) y (unitVector j) :=
          integral_finsetSum _ fun j _ => hIi j
      _ = ∑ j : Fin 3, ∫ y, -(fderiv ℝ w y (unitVector j) * g j y) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ibp j, integral_neg]
      _ = ∫ y, ∑ j : Fin 3, -(fderiv ℝ w y (unitVector j) * g j y) :=
          (integral_finsetSum _ fun j _ => (hJi j).neg).symm
      _ ≤ ∫ y, (w y * (‖y‖ ^ 2 + δ)⁻¹ / 2 + 2 * E y) :=
          integral_mono hsumJ ((hAi.div_const 2).add (hEi.const_mul 2)) hpt2
      _ = (∫ y, w y * (‖y‖ ^ 2 + δ)⁻¹) / 2 + 2 * ∫ y, E y := by
          rw [integral_add (hAi.div_const 2) (hEi.const_mul 2), integral_div, integral_const_mul]
  have hgoal : ∫ y, ‖u y‖ ^ 2 / (‖y‖ ^ 2 + δ) = ∫ y, w y * (‖y‖ ^ 2 + δ)⁻¹ := by
    simp only [hw, div_eq_mul_inv]
  rw [hgoal]
  show _ ≤ 4 * ∫ y, E y
  linarith



private theorem fderiv_radialCutoff_ne {R : ℝ} (hR : 0 < R) {y : Space} (h : fderiv ℝ (radialCutoff R) y ≠ 0) :
    R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R := by
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    apply h
    have he : radialCutoff R =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (show y ∈ Metric.ball (0 : Space) R by simpa using hlt)]
        with z hz
      exact radialCutoff_eq_one hR (le_of_lt (by simpa using hz))
    rw [he.fderiv_eq]
    simp
  · by_contra hlt
    rw [not_le] at hlt
    apply h
    have hopen : IsOpen {z : Space | 2 * R < ‖z‖} := isOpen_lt continuous_const continuous_norm
    have he : radialCutoff R =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hlt] with z hz
      exact radialCutoff_eq_zero hR (le_of_lt hz)
    rw [he.fderiv_eq]
    simp

private theorem sq_le_six_add {a M : ℝ} (hM : 0 < M) : a ^ 2 ≤ a ^ 6 / M ^ 2 + M := by
  rcases le_or_gt (a ^ 2) M with h | h
  · have : 0 ≤ a ^ 6 / M ^ 2 := by positivity
    linarith
  · have h1 : M ^ 2 ≤ (a ^ 2) ^ 2 := pow_le_pow_left₀ hM.le h.le 2
    have h2 : a ^ 2 * M ^ 2 ≤ a ^ 6 := by
      have : a ^ 6 = a ^ 2 * (a ^ 2) ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : a ^ 2 ≤ a ^ 6 / M ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      exact h2
    linarith

private theorem cutoffTail (w : Space → Space) (hw : Continuous w) (h6 : MemLp w 6 volume) :
    Tendsto (fun R : ℝ => ∫ y, ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := norm_fderiv_radialCutoff_le
  have h6' : MemLp w ((6 : ℕ) : ℝ≥0∞) volume := by exact_mod_cast h6
  have hI : Integrable (fun y => ‖w y‖ ^ 6) := h6'.integrable_norm_pow (by norm_num)
  set tail : ℝ → ℝ := fun R => ∫ y, {z : Space | R ≤ ‖z‖}.indicator (fun z => ‖w z‖ ^ 6) y with htail
  have hmeasS : ∀ R : ℝ, MeasurableSet {z : Space | R ≤ ‖z‖} := fun R =>
    measurableSet_le measurable_const measurable_norm
  have htl : Tendsto tail atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
      (F := fun R : ℝ => {z : Space | R ≤ ‖z‖}.indicator (fun z => ‖w z‖ ^ 6)) (f := fun _ => (0 : ℝ))
      (fun y => ‖w y‖ ^ 6)
      (Eventually.of_forall fun R => hI.aestronglyMeasurable.indicator (hmeasS R))
      (Eventually.of_forall fun R => ae_of_all _ fun y => by
        refine (norm_indicator_le_norm_self _ _).trans ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)])
      hI
      (ae_of_all _ fun y => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop ‖y‖] with R hR
        have : y ∉ {z : Space | R ≤ ‖z‖} := by simpa using hR
        rw [Set.indicator_of_notMem this])
    simpa using this
  set V : ℝ := (volume : Measure Space).real (Metric.ball 0 1) with hV
  have hvol : ∀ R : ℝ, 0 < R → (volume : Measure Space).real (Metric.closedBall 0 (2 * R)) = (2 * R) ^ 3 * V := by
    intro R hR
    rw [measureReal_def, Measure.addHaar_closedBall volume 0 (by positivity), finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hV, measureReal_def]
  have hVpos : 0 ≤ V := measureReal_nonneg
  have hc0 : 0 ≤ c := by
    have := (norm_nonneg _).trans (hc 1 one_pos 0)
    simpa using this
  have hbound : ∀ κ : ℝ, 0 < κ → ∀ R : ℝ, 0 < R →
      ∫ y, ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2 ≤ c ^ 2 * tail R / κ ^ 2 + 8 * c ^ 2 * V * κ := by
    intro κ hκ R hR
    set M : ℝ := κ / R with hM
    have hM0 : 0 < M := by positivity
    have hcc : ContDiff ℝ ∞ (radialCutoff R) := contDiff_radialCutoff hR
    have hT : Integrable (fun y => ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2) := by
      refine Continuous.integrable_of_hasCompactSupport
        (((hcc.continuous_fderiv (by simp)).norm.pow 2).mul (hw.norm.pow 2)) ?_
      exact ((hasCompactSupport_radialCutoff hR).fderiv (𝕜 := ℝ)).mono fun y hy h0 => hy (by simp [h0])
    have hI1 : Integrable ({z : Space | R ≤ ‖z‖}.indicator (fun z => ‖w z‖ ^ 6)) :=
      hI.indicator (hmeasS R)
    have hI2 : Integrable ((Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => M)) :=
      (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
        (integrableOn_const (measure_closedBall_lt_top).ne)
    have hpt : ∀ y, ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2 ≤
        (c / R) ^ 2 * ({z : Space | R ≤ ‖z‖}.indicator (fun z => ‖w z‖ ^ 6) y / M ^ 2 +
          (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => M) y) := by
      intro y
      by_cases h0 : fderiv ℝ (radialCutoff R) y = 0
      · rw [h0, norm_zero]
        have h1 : 0 ≤ {z : Space | R ≤ ‖z‖}.indicator (fun z => ‖w z‖ ^ 6) y :=
          Set.indicator_nonneg (fun _ _ => by positivity) _
        have h2 : 0 ≤ (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => M) y :=
          Set.indicator_nonneg (fun _ _ => hM0.le) _
        have : 0 ≤ (c / R) ^ 2 * ({z : Space | R ≤ ‖z‖}.indicator (fun z => ‖w z‖ ^ 6) y / M ^ 2 +
          (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => M) y) := by positivity
        simpa using this
      · obtain ⟨hy1, hy2⟩ := fderiv_radialCutoff_ne hR h0
        have hm1 : y ∈ {z : Space | R ≤ ‖z‖} := hy1
        have hm2 : y ∈ Metric.closedBall (0 : Space) (2 * R) := by simpa using hy2
        rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2]
        have hd : ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 ≤ (c / R) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hc R hR y) 2
        have hs : ‖w y‖ ^ 2 ≤ ‖w y‖ ^ 6 / M ^ 2 + M := sq_le_six_add hM0
        exact mul_le_mul hd hs (by positivity) (by positivity)
    have hmono : ∫ y, ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2 ≤
        ∫ y, (c / R) ^ 2 * ({z : Space | R ≤ ‖z‖}.indicator (fun z => ‖w z‖ ^ 6) y / M ^ 2 +
          (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => M) y) :=
      integral_mono hT ((hI1.div_const (M ^ 2)).add hI2 |>.const_mul ((c / R) ^ 2)) hpt
    rw [integral_const_mul, integral_add (hI1.div_const (M ^ 2)) hI2, integral_div,
      integral_indicator_const _ Metric.isClosed_closedBall.measurableSet, hvol R hR, smul_eq_mul] at hmono
    refine hmono.trans_eq ?_
    simp only [htail, hM]
    field_simp
    ring
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun R => lt_of_lt_of_le ha ?_, fun ε hε => ?_⟩
  · exact integral_nonneg fun y => by positivity
  · set κ : ℝ := ε / (16 * (c ^ 2 * V + 1)) with hκ
    have hκ0 : 0 < κ := by positivity
    have hκs : 8 * c ^ 2 * V * κ < ε / 2 := by
      rw [hκ]
      have hpos : 0 < 16 * (c ^ 2 * V + 1) := by positivity
      rw [show 8 * c ^ 2 * V * (ε / (16 * (c ^ 2 * V + 1))) = ε * (8 * (c ^ 2 * V)) / (16 * (c ^ 2 * V + 1)) by ring,
        div_lt_iff₀ hpos]
      nlinarith [mul_nonneg hc0 hc0, mul_nonneg (mul_nonneg hc0 hc0) hVpos]
    have hev : ∀ᶠ R in atTop, c ^ 2 * tail R / κ ^ 2 < ε / 2 := by
      have : Tendsto (fun R => c ^ 2 * tail R / κ ^ 2) atTop (𝓝 (c ^ 2 * 0 / κ ^ 2)) :=
        (htl.const_mul (c ^ 2)).div_const (κ ^ 2)
      rw [mul_zero, zero_div] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    filter_upwards [hev, eventually_gt_atTop 0] with R hR hR0
    have := hbound κ hκ0 R hR0
    linarith

private theorem sq_add_le_weighted {x y θ : ℝ} (hθ : 0 < θ) :
    (x + y) ^ 2 ≤ (1 + θ) * x ^ 2 + (1 + θ⁻¹) * y ^ 2 := by
  have e : θ⁻¹ * (θ * x - y) ^ 2 = θ * x ^ 2 - 2 * x * y + θ⁻¹ * y ^ 2 := by
    field_simp
    ring
  have h := mul_nonneg (inv_nonneg.2 hθ.le) (sq_nonneg (θ * x - y))
  nlinarith

private theorem entrySq_cutoff_le {w : Space → Space} (hw : ContDiff ℝ ∞ w) {R : ℝ} (hR : 0 < R) {θ : ℝ}
    (hθ : 0 < θ) (y : Space) :
    entrySq (fderiv ℝ (fun z => radialCutoff R z • w z) y) ≤
      (1 + θ) * entrySq (fderiv ℝ w y) +
        3 * (1 + θ⁻¹) * (‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2) := by
  have hcd : DifferentiableAt ℝ (radialCutoff R) y :=
    ((contDiff_radialCutoff hR).differentiable (by simp)) y
  have hwd : DifferentiableAt ℝ w y := (hw.differentiable (by simp)) y
  rw [show (fun z => radialCutoff R z • w z) = radialCutoff R • w from rfl, fderiv_smul hcd hwd]
  simp only [entrySq]
  have key : ∀ i : Fin 3, ‖(radialCutoff R y • fderiv ℝ w y +
      (fderiv ℝ (radialCutoff R) y).smulRight (w y)) (unitVector i)‖ ^ 2 ≤
      (1 + θ) * ‖fderiv ℝ w y (unitVector i)‖ ^ 2 +
        (1 + θ⁻¹) * (‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2) := by
    intro i
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    have h0 := radialCutoff_nonneg R y
    have h1 := radialCutoff_le_one R y
    have hu : ‖unitVector i‖ = 1 := by simp [unitVector]
    have ha : ‖radialCutoff R y • fderiv ℝ w y (unitVector i)‖ ≤ ‖fderiv ℝ w y (unitVector i)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
      exact mul_le_of_le_one_left (norm_nonneg _) h1
    have hb : ‖fderiv ℝ (radialCutoff R) y (unitVector i) • w y‖ ≤
        ‖fderiv ℝ (radialCutoff R) y‖ * ‖w y‖ := by
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      simpa [hu] using (fderiv ℝ (radialCutoff R) y).le_opNorm (unitVector i)
    have ht := norm_add_le (radialCutoff R y • fderiv ℝ w y (unitVector i))
      (fderiv ℝ (radialCutoff R) y (unitVector i) • w y)
    have hs : ‖radialCutoff R y • fderiv ℝ w y (unitVector i) +
        fderiv ℝ (radialCutoff R) y (unitVector i) • w y‖ ^ 2 ≤
        (‖fderiv ℝ w y (unitVector i)‖ + ‖fderiv ℝ (radialCutoff R) y‖ * ‖w y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (ht.trans (add_le_add ha hb)) 2
    refine hs.trans ((sq_add_le_weighted hθ).trans_eq ?_)
    ring
  refine (Finset.sum_le_sum fun i _ => key i).trans_eq ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp
  ring

private theorem cutoffEnergy (w : Space → Space) (hw : ContDiff ℝ ∞ w) (h6 : MemLp w 6 volume)
    (hE : Integrable (fun y => entrySq (fderiv ℝ w y))) (η : ℝ) (hη : 0 < η) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R, R₀ ≤ R →
      ∫ y, entrySq (fderiv ℝ (fun z => radialCutoff R z • w z) y) ≤ (∫ y, entrySq (fderiv ℝ w y)) + η := by
  set B := ∫ y, entrySq (fderiv ℝ w y) with hB
  have hB0 : 0 ≤ B := integral_nonneg fun y => Finset.sum_nonneg fun _ _ => by positivity
  set θ := η / (2 * (B + 1)) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθB : θ * B ≤ η / 2 := by
    rw [hθ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have ht := cutoffTail w hw.continuous h6
  have hev : ∀ᶠ R in atTop, 3 * (1 + θ⁻¹) * ∫ y, ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2 < η / 2 := by
    have := (ht.const_mul (3 * (1 + θ⁻¹)))
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 hev
  refine ⟨max R₁ 1, by positivity, fun R hR => ?_⟩
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hcc : ContDiff ℝ ∞ (radialCutoff R) := contDiff_radialCutoff hRpos
  have hT : Integrable (fun y => ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2) := by
    refine Continuous.integrable_of_hasCompactSupport
      (((hcc.continuous_fderiv (by simp)).norm.pow 2).mul (hw.continuous.norm.pow 2)) ?_
    exact ((hasCompactSupport_radialCutoff hRpos).fderiv (𝕜 := ℝ)).mono fun y hy h0 => hy (by simp [h0])
  have hpc : ContDiff ℝ ∞ (fun z => radialCutoff R z • w z) := hcc.smul hw
  have hps : HasCompactSupport (fun z => radialCutoff R z • w z) :=
    (hasCompactSupport_radialCutoff hRpos).smul_right
  have hL : Integrable (fun y => entrySq (fderiv ℝ (fun z => radialCutoff R z • w z) y)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · simp only [entrySq]
      exact continuous_finsetSum _ fun i _ =>
        (((hpc.continuous_fderiv (by simp)).clm_apply continuous_const).norm).pow 2
    · exact (hps.fderiv (𝕜 := ℝ)).mono fun y hy h0 => hy (by simp [entrySq, h0])
  have hmono : ∫ y, entrySq (fderiv ℝ (fun z => radialCutoff R z • w z) y) ≤
      ∫ y, ((1 + θ) * entrySq (fderiv ℝ w y) +
        3 * (1 + θ⁻¹) * (‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2)) := integral_mono hL ((hE.const_mul (1 + θ)).add (hT.const_mul (3 * (1 + θ⁻¹))))
    (fun y => entrySq_cutoff_le hw hRpos hθ0 y)
  rw [integral_add (hE.const_mul (1 + θ)) (hT.const_mul (3 * (1 + θ⁻¹))), integral_const_mul,
    integral_const_mul] at hmono
  have h2 := hR₁ R (le_trans (le_max_left _ _) hR)
  have : (1 + θ) * B = B + θ * B := by ring
  linarith


private theorem normPow_convolution_le (φ : ContDiffBump (0 : Space)) (f : Space → Space)
    (k : ℕ) (hk : 1 ≤ k) (hI : Integrable (fun z => ‖f z‖ ^ k))
    (y : Space) :
    ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y‖ ^ k ≤
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ‖f z‖ ^ k) y := by
  set ρ : Space → ℝ := φ.normed volume with hρ
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => φ.nonneg_normed t
  have hρc : Continuous ρ := φ.continuous_normed
  set d : Space → ℝ≥0 := fun t => (ρ t).toNNReal with hd
  have hdm : Measurable d := hρc.measurable.real_toNNReal
  set μ : Measure Space := volume.withDensity (fun t => (d t : ℝ≥0∞)) with hμ
  have hprob : IsProbabilityMeasure μ := by
    constructor
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have h1 : ∫⁻ t, ENNReal.ofReal (ρ t) = ENNReal.ofReal (∫ t, ρ t) :=
      (ofReal_integral_eq_lintegral_ofReal φ.integrable_normed (ae_of_all _ hρ0)).symm
    have h2 : ∫ t, ρ t = 1 := φ.integral_normed
    rw [h2, ENNReal.ofReal_one] at h1
    exact h1
  have hint : ∀ g : Space → Space, ∫ t, g t ∂μ = ∫ t, ρ t • g t := by
    intro g
    rw [hμ, integral_withDensity_eq_integral_smul hdm]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [hd, NNReal.smul_def, Real.coe_toNNReal _ (hρ0 t)]
  have hintR : ∀ g : Space → ℝ, ∫ t, g t ∂μ = ∫ t, ρ t • g t := by
    intro g
    rw [hμ, integral_withDensity_eq_integral_smul hdm]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [hd, NNReal.smul_def, Real.coe_toNNReal _ (hρ0 t)]
  have hL : (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y = ∫ t, f (y - t) ∂μ := by
    rw [convolution_def, hint]
    rfl
  have hR : (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ‖f z‖ ^ k) y =
      ∫ t, ‖f (y - t)‖ ^ k ∂μ := by
    rw [convolution_def, hintR]
    rfl
  rw [hL, hR]
  by_cases hfi : Integrable (fun t => f (y - t)) μ
  · obtain ⟨C, hC⟩ := hρc.bounded_above_of_compact_support φ.hasCompactSupport_normed
    have hIt : Integrable (fun t => ‖f (y - t)‖ ^ k) := hI.comp_sub_left y
    have hgi : Integrable (fun t => ‖f (y - t)‖ ^ k) μ := by
      rw [hμ, integrable_withDensity_iff_integrable_smul hdm]
      refine (hIt.const_mul C).mono' ?_ (ae_of_all _ fun t => ?_)
      · exact (hdm.coe_nnreal_real.aestronglyMeasurable).smul hIt.aestronglyMeasurable
      · simp only [hd, NNReal.smul_def, Real.coe_toNNReal _ (hρ0 t), smul_eq_mul, norm_mul,
          Real.norm_eq_abs, abs_of_nonneg (hρ0 t), abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖f (y - t)‖ ^ k)]
        have h1 : ρ t ≤ C := by simpa [Real.norm_eq_abs, abs_of_nonneg (hρ0 t)] using hC t
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hconv : ConvexOn ℝ Set.univ (fun x : Space => ‖x‖ ^ k) :=
      (convexOn_norm convex_univ).pow (fun x _ => norm_nonneg x) k
    exact hconv.map_integral_le ((continuous_norm.pow k).continuousOn) isClosed_univ
      (ae_of_all _ fun _ => Set.mem_univ _) hfi hgi
  · rw [integral_undef hfi, norm_zero, zero_pow (by omega)]
    exact integral_nonneg fun t => by positivity


private theorem mollify_fderiv_apply (φ : ContDiffBump (0 : Space)) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (h6 : MemLp v 6 volume) (hw : IsWeakGradientOf v G) (y : Space) (j : Fin 3) :
    fderiv ℝ (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y (unitVector j) =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => G z (unitVector j)) y := by
  have hloc : LocallyIntegrable v volume := h6.locallyIntegrable (by norm_num)
  have hcf : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  have hcd : ContDiff ℝ ∞ (φ.normed volume) := φ.contDiff_normed
  have hd1 : ContDiff ℝ 1 (φ.normed volume) := hcd.of_le (by simp)
  have hder := hcf.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hd1 hloc y
  rw [hder.fderiv]
  have hex := (hcf.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).precompL Space)
    (hcd.continuous_fderiv (by simp)) hloc y
  rw [convolution_eq_swap, ContinuousLinearMap.integral_apply hex.integrable_swap, convolution_eq_swap]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  set ψ : Space → ℝ := fun s => φ.normed volume (y - s) with hψ
  have hψt : IsTestScalar ψ := by
    refine ⟨hcd.comp (contDiff_const.sub contDiff_id), ?_⟩
    exact hcf.comp_homeomorph (Homeomorph.subLeft y)
  have hψd : ∀ s, fderiv ℝ ψ s (unitVector j) = -fderiv ℝ (φ.normed volume) (y - s) (unitVector j) := by
    intro s
    have h1 : HasFDerivAt (φ.normed volume) (fderiv ℝ (φ.normed volume) (y - s)) (y - s) :=
      ((hcd.differentiable (by simp)) (y - s)).hasFDerivAt
    have h2 : HasFDerivAt ψ ((fderiv ℝ (φ.normed volume) (y - s)).comp (-ContinuousLinearMap.id ℝ Space)) s :=
      h1.comp s ((hasFDerivAt_id s).const_sub y)
    rw [h2.fderiv]
    simp
  have hwj := hw ψ hψt j
  simp only [hψd, neg_smul, integral_neg] at hwj
  exact neg_injective hwj

private theorem smoothApprox (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (h6 : MemLp v 6 volume) (hG : Integrable (fun y => entrySq (G y)))
    (hGm : ∀ j : Fin 3, AEStronglyMeasurable (fun y => G y (unitVector j)) volume)
    (hw : IsWeakGradientOf v G) :
    ∃ w : ℕ → Space → Space, (∀ n, ContDiff ℝ ∞ (w n)) ∧ (∀ n, MemLp (w n) 6 volume) ∧
      (∀ n, Integrable (fun y => entrySq (fderiv ℝ (w n) y))) ∧
      (∀ n, ∫ y, entrySq (fderiv ℝ (w n) y) ≤ ∫ y, entrySq (G y)) ∧
      ∀ᵐ y ∂volume, Tendsto (fun n => w n y) atTop (𝓝 (v y)) := by
  have hloc : LocallyIntegrable v volume := h6.locallyIntegrable (by norm_num)
  have hGc : ∀ j : Fin 3, Integrable (fun z => ‖G z (unitVector j)‖ ^ 2) := fun j =>
    hG.mono' ((hGm j).norm.pow 2) (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simp only [entrySq]
      exact Finset.single_le_sum (f := fun i => ‖G z (unitVector i)‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j))
  have h6' : MemLp v ((6 : ℕ) : ℝ≥0∞) volume := by exact_mod_cast h6
  have hI6 : Integrable (fun z => ‖v z‖ ^ 6) := h6'.integrable_norm_pow (by norm_num)
  let φ : ℕ → ContDiffBump (0 : Space) := fun n =>
    ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_div_iff₀ (by positivity) this]
      linarith⟩
  have hρi : ∀ n, Integrable ((φ n).normed volume) := fun n => (φ n).integrable_normed
  have hwc : ∀ n, ContDiff ℝ ∞ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) :=
    fun n => ((φ n).hasCompactSupport_normed).contDiff_convolution_left _ (φ n).contDiff_normed hloc
  have hEpt : ∀ n y, entrySq (fderiv ℝ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y) ≤
      ∑ j : Fin 3, ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun z => ‖G z (unitVector j)‖ ^ 2) y := by
    intro n y
    simp only [entrySq, mollify_fderiv_apply (φ n) v G h6 hw y]
    exact Finset.sum_le_sum fun j _ =>
      normPow_convolution_le (φ n) _ 2 (by norm_num) (hGc j) y
  have hSi : ∀ n, Integrable (fun y => ∑ j : Fin 3, ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      fun z => ‖G z (unitVector j)‖ ^ 2) y) := fun n =>
    integrable_finsetSum _ fun j _ => (hρi n).integrable_convolution _ (hGc j)
  have hEc : ∀ n, Continuous (fun y =>
      entrySq (fderiv ℝ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y)) := by
    intro n
    simp only [entrySq]
    exact continuous_finsetSum _ fun i _ =>
      ((((hwc n).continuous_fderiv (by simp)).clm_apply continuous_const).norm).pow 2
  have hEi : ∀ n, Integrable (fun y =>
      entrySq (fderiv ℝ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y)) := fun n =>
    (hSi n).mono' (hEc n).aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
      exact hEpt n y)
  refine ⟨fun n => (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v, hwc, fun n => ?_,
    hEi, fun n => ?_, ?_⟩
  · have hm : AEStronglyMeasurable ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) volume :=
      (hwc n).continuous.aestronglyMeasurable
    have hi : Integrable (fun y => ‖((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y‖ ^ 6) :=
      ((hρi n).integrable_convolution _ hI6).mono' (hm.norm.pow 6) (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact normPow_convolution_le (φ n) v 6 (by norm_num) hI6 y)
    refine (integrable_norm_rpow_iff hm (by norm_num) (by norm_num)).1 ?_
    simpa using hi
  · refine (integral_mono (hEi n) (hSi n) (hEpt n)).trans_eq ?_
    rw [integral_finsetSum _ fun j _ => (hρi n).integrable_convolution _ (hGc j)]
    simp only [entrySq]
    rw [integral_finsetSum _ fun j _ => hGc j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hρi n) (hGc j)]
    simp [ContDiffBump.integral_normed]
  · refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (φ := φ) (K := 2) ?_ ?_ hloc
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · refine Eventually.of_forall fun n => le_of_eq ?_
      show 1 / ((n : ℝ) + 1) = 2 * (1 / (2 * ((n : ℝ) + 1)))
      field_simp


private theorem testScalar_cutoff (n : ℕ) : IsTestScalar (radialCutoff ((n : ℝ) + 1)) :=
  ⟨contDiff_radialCutoff (by positivity), hasCompactSupport_radialCutoff (by positivity)⟩

private theorem exists_test_not_measurable {g : Space → Space} (hn : ¬ AEStronglyMeasurable g volume) :
    ∃ φ : Space → ℝ, IsTestScalar φ ∧ ¬ AEStronglyMeasurable (fun y => φ y • g y) volume := by
  by_contra hall
  push Not at hall
  apply hn
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun n : ℕ => fun y => radialCutoff ((n : ℝ) + 1) y • g y)
    (fun n => hall _ (testScalar_cutoff n)) (ae_of_all _ fun y => ?_)
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have h1 : ‖y‖ ≤ (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simp [radialCutoff_eq_one (by positivity : (0 : ℝ) < (n : ℝ) + 1) h1]

private theorem partial_zero_of_not_measurable {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    (hloc : LocallyIntegrable v volume) (hw : IsWeakGradientOf v G) (j : Fin 3)
    (hn : ¬ AEStronglyMeasurable (fun y => G y (unitVector j)) volume) (φ : Space → ℝ) (hφ : IsTestScalar φ) :
    ∫ y, fderiv ℝ φ y (unitVector j) • v y = 0 := by
  have hzero : ∀ ψ : Space → ℝ, IsTestScalar ψ →
      ¬ AEStronglyMeasurable (fun y => ψ y • G y (unitVector j)) volume →
      ∫ y, fderiv ℝ ψ y (unitVector j) • v y = 0 := by
    intro ψ hψ hnm
    rw [hw ψ hψ j, integral_undef (fun h => hnm h.1), neg_zero]
  have hint : ∀ ψ : Space → ℝ, IsTestScalar ψ → Integrable (fun y => fderiv ℝ ψ y (unitVector j) • v y) :=
    fun ψ hψ => hloc.integrable_smul_left_of_hasCompactSupport
      ((hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hψ.2.fderiv (𝕜 := ℝ)).mono fun y hy h0 => hy (by simp [h0]))
  by_cases hm : AEStronglyMeasurable (fun y => φ y • G y (unitVector j)) volume
  · obtain ⟨φ₀, hφ₀, hn₀⟩ := exists_test_not_measurable hn
    have hs : IsTestScalar (fun y => φ y + φ₀ y) := ⟨hφ.1.add hφ₀.1, hφ.2.add hφ₀.2⟩
    have hsn : ¬ AEStronglyMeasurable (fun y => (φ y + φ₀ y) • G y (unitVector j)) volume := by
      intro h
      apply hn₀
      refine (h.sub hm).congr (ae_of_all _ fun y => ?_)
      simp only [add_smul, Pi.sub_apply]
      abel
    have h1 := hzero _ hs hsn
    have h2 := hzero _ hφ₀ hn₀
    have hd : ∀ y, fderiv ℝ (fun y => φ y + φ₀ y) y (unitVector j) =
        fderiv ℝ φ y (unitVector j) + fderiv ℝ φ₀ y (unitVector j) := by
      intro y
      show fderiv ℝ (φ + φ₀) y (unitVector j) = _
      rw [fderiv_add ((hφ.1.differentiable (by simp)) y) ((hφ₀.1.differentiable (by simp)) y)]
      rfl
    simp only [hd, add_smul] at h1
    rw [integral_add (hint φ hφ) (hint φ₀ hφ₀), h2, add_zero] at h1
    exact h1
  · exact hzero φ hφ hm

private theorem measurableGradient_exists (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (h6 : MemLp v 6 volume) (hw : IsWeakGradientOf v G) :
    ∃ G' : Space → (Space →L[ℝ] Space),
      (∀ j : Fin 3, AEStronglyMeasurable (fun y => G' y (unitVector j)) volume) ∧
      (∀ y, entrySq (G' y) ≤ entrySq (G y)) ∧ IsWeakGradientOf v G' := by
  classical
  have hloc : LocallyIntegrable v volume := h6.locallyIntegrable (by norm_num)
  set c : Fin 3 → Space → Space := fun j y =>
    if AEStronglyMeasurable (fun y => G y (unitVector j)) volume then G y (unitVector j) else 0 with hc
  set G' : Space → (Space →L[ℝ] Space) := fun y =>
    ∑ i : Fin 3, (EuclideanSpace.proj i : Space →L[ℝ] ℝ).smulRight (c i y) with hG'
  have hcol : ∀ y j, G' y (unitVector j) = c j y := by
    intro y j
    simp [hG', unitVector]
  refine ⟨G', fun j => ?_, fun y => ?_, fun φ hφ j => ?_⟩
  · simp only [hcol]
    by_cases h : AEStronglyMeasurable (fun y => G y (unitVector j)) volume
    · simp only [hc, h, if_true]
    · simp [hc, h, aestronglyMeasurable_const]
  · simp only [entrySq, hcol]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases h : AEStronglyMeasurable (fun y => G y (unitVector j)) volume
    · simp [hc, h]
    · calc ‖c j y‖ ^ 2 = 0 := by simp [hc, h]
        _ ≤ _ := by positivity
  · simp only [hcol]
    by_cases h : AEStronglyMeasurable (fun y => G y (unitVector j)) volume
    · simpa [hc, h] using hw φ hφ j
    · simp only [hc, h, if_false, smul_zero, integral_zero, neg_zero]
      exact partial_zero_of_not_measurable hloc hw j h φ hφ

private theorem smoothCompactApprox (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (h6 : MemLp v 6 volume) (hG : Integrable (fun y => entrySq (G y)))
    (hGm : ∀ j : Fin 3, AEStronglyMeasurable (fun y => G y (unitVector j)) volume)
    (hw : IsWeakGradientOf v G) :
    ∃ u : ℕ → Space → Space, (∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n)) ∧
      (∀ᵐ y ∂volume, Tendsto (fun n => u n y) atTop (𝓝 (v y))) ∧
      ∀ n, ∫ y, entrySq (fderiv ℝ (u n) y) ≤ (∫ y, entrySq (G y)) + 1 / ((n : ℝ) + 1) := by
  obtain ⟨w, hwc, hw6, hwE, hwle, hwlim⟩ := smoothApprox v G h6 hG hGm hw
  have hcut := fun n => cutoffEnergy (w n) (hwc n) (hw6 n) (hwE n) (1 / ((n : ℝ) + 1)) (by positivity)
  choose R₀ hR₀ hR₀le using hcut
  set R : ℕ → ℝ := fun n => max (R₀ n) ((n : ℝ) + 1) with hR
  have hRpos : ∀ n, 0 < R n := fun n => lt_of_lt_of_le (hR₀ n) (le_max_left _ _)
  refine ⟨fun n z => radialCutoff (R n) z • w n z, fun n => ⟨?_, ?_⟩, ?_, fun n => ?_⟩
  · exact (contDiff_radialCutoff (hRpos n)).smul (hwc n)
  · exact (hasCompactSupport_radialCutoff (hRpos n)).smul_right
  · filter_upwards [hwlim] with y hy
    refine hy.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 : ‖y‖ ≤ R n := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      exact le_trans hN (le_trans (by linarith) (le_max_right _ _))
    simp [radialCutoff_eq_one (hRpos n) h1]
  · exact (hR₀le n (R n) (le_max_left _ _)).trans (add_le_add (hwle n) le_rfl)

end FracInternal

namespace SteadyCert

private theorem entrySq_nonneg' (A : Space →L[ℝ] Space) : 0 ≤ entrySq A :=
  Finset.sum_nonneg fun _ _ => by positivity

private theorem inverseSquare_of_approx (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (hv : AEStronglyMeasurable v volume) (u : ℕ → Space → Space)
    (hu : ∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n))
    (hlim : ∀ᵐ y ∂volume, Tendsto (fun n => u n y) atTop (𝓝 (v y)))
    (hE : ∀ n, ∫ y, entrySq (fderiv ℝ (u n) y) ≤ (∫ y, entrySq (G y)) + 1 / ((n : ℝ) + 1)) :
    Integrable (fun y => ‖v y‖ ^ 2 / ‖y‖ ^ 2) ∧ ∫ y, ‖v y‖ ^ 2 / ‖y‖ ^ 2 ≤ 4 * ∫ y, entrySq (G y) := by
  set A := ∫ y, entrySq (G y) with hA
  have hA0 : 0 ≤ A := integral_nonneg fun y => entrySq_nonneg' _
  set d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hd
  have hd0 : ∀ n, 0 < d n := fun n => by simp only [hd]; positivity
  have hdlim : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set f : ℕ → Space → ℝ := fun n y => ‖u n y‖ ^ 2 / (‖y‖ ^ 2 + d n) with hf
  have hfc : ∀ n, Continuous (f n) := by
    intro n
    have hc : Continuous (u n) := (hu n).1.continuous
    refine (hc.norm.pow 2).div (continuous_norm.pow 2 |>.add continuous_const) fun y => ?_
    have := hd0 n
    positivity
  have hfs : ∀ n, HasCompactSupport (f n) := by
    intro n
    refine (hu n).2.mono fun y hy => ?_
    intro h0
    apply hy
    simp only [hf, h0, norm_zero]
    ring
  have hfi : ∀ n, Integrable (f n) := fun n => (hfc n).integrable_of_hasCompactSupport (hfs n)
  have hfn : ∀ n y, 0 ≤ f n y := fun n y => by
    have := hd0 n
    simp only [hf]
    positivity
  have hbound : ∀ n, ∫ y, f n y ≤ 4 * (A + d n) := fun n => by
    have h1 := FracInternal.regularizedInverseSquare_le (u n) (hu n).1 (hu n).2 (d n) (hd0 n)
    have h2 : ∫ y, entrySq (fderiv ℝ (u n) y) ≤ A + d n := by simpa only [hA, hd] using hE n
    exact h1.trans (by linarith)
  have h0 : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
    have : (volume : Measure Space) {(0 : Space)} = 0 := measure_singleton 0
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with y hy
    simpa using hy
  have hpt : ∀ᵐ y ∂volume, Tendsto (fun n => f n y) atTop (𝓝 (‖v y‖ ^ 2 / ‖y‖ ^ 2)) := by
    filter_upwards [hlim, h0] with y hy hy0
    have hnum : Tendsto (fun n => ‖u n y‖ ^ 2) atTop (𝓝 (‖v y‖ ^ 2)) := (hy.norm).pow 2
    have hden : Tendsto (fun n => ‖y‖ ^ 2 + d n) atTop (𝓝 (‖y‖ ^ 2 + 0)) := tendsto_const_nhds.add hdlim
    rw [add_zero] at hden
    exact hnum.div hden (by positivity)
  have hgm : AEStronglyMeasurable (fun y => ‖v y‖ ^ 2 / ‖y‖ ^ 2) volume :=
    (hv.norm.pow 2).mul ((continuous_norm.pow 2).measurable.inv.aestronglyMeasurable)
  have hg0 : 0 ≤ᵐ[volume] fun y => ‖v y‖ ^ 2 / ‖y‖ ^ 2 := ae_of_all _ fun y => by positivity
  have hlimB : Tendsto (fun n => 4 * (A + d n)) atTop (𝓝 (4 * A)) := by
    have := (tendsto_const_nhds (x := A)).add hdlim
    rw [add_zero] at this
    exact this.const_mul 4
  have hfat : ∫⁻ y, ENNReal.ofReal (‖v y‖ ^ 2 / ‖y‖ ^ 2) ≤ ENNReal.ofReal (4 * A) := by
    calc ∫⁻ y, ENNReal.ofReal (‖v y‖ ^ 2 / ‖y‖ ^ 2)
        = ∫⁻ y, liminf (fun n => ENNReal.ofReal (f n y)) atTop := by
          refine lintegral_congr_ae ?_
          filter_upwards [hpt] with y hy
          exact ((ENNReal.tendsto_ofReal hy).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ y, ENNReal.ofReal (f n y)) atTop :=
          lintegral_liminf_le' fun n => ((hfc n).measurable.ennreal_ofReal).aemeasurable
      _ ≤ liminf (fun n => ENNReal.ofReal (4 * (A + d n))) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hfi n) (ae_of_all _ (hfn n))]
          exact ENNReal.ofReal_le_ofReal (hbound n)
      _ = ENNReal.ofReal (4 * A) := (ENNReal.tendsto_ofReal hlimB).liminf_eq
  have hint : Integrable (fun y => ‖v y‖ ^ 2 / ‖y‖ ^ 2) :=
    ⟨hgm, (hasFiniteIntegral_iff_ofReal hg0).2 (lt_of_le_of_lt hfat ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hg0 hgm]
  calc (∫⁻ y, ENNReal.ofReal (‖v y‖ ^ 2 / ‖y‖ ^ 2)).toReal ≤ (ENNReal.ofReal (4 * A)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hfat
    _ = 4 * A := ENNReal.toReal_ofReal (by positivity)

theorem inverseSquareBound : InverseSquareBoundStatement := by
  intro v G hv h6 hG hw
  obtain ⟨G', hG'm, hle, hw'⟩ := FracInternal.measurableGradient_exists v G h6 hw
  have hm : AEStronglyMeasurable (fun y => entrySq (G' y)) volume := by
    simp only [entrySq]
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hG'm i).norm.pow 2
  have hG'i : Integrable (fun y => entrySq (G' y)) :=
    hG.mono' hm (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (entrySq_nonneg' _)]
      exact hle y)
  obtain ⟨u, hu, hlim, hE⟩ := FracInternal.smoothCompactApprox v G' h6 hG'i hG'm hw'
  obtain ⟨hi, hle2⟩ := inverseSquare_of_approx v G' hv u hu hlim hE
  exact ⟨hi, hle2.trans (mul_le_mul_of_nonneg_left (integral_mono hG'i hG hle) (by norm_num))⟩

end SteadyCert

end Breakdown
