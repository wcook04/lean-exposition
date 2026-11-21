import Breakdown.FracCell.ReductionAdjointDefs
import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace PuncturedWeakInternal

theorem inner_gradient (q : Space → ℝ) (y : Space) (j : Fin 3) :
    inner ℝ (gradientAt q y) (unitVector j) = fderiv ℝ q y (unitVector j) := by
  simp [gradientAt, unitVector, EuclideanSpace.inner_single_right, Fin.sum_univ_three]
  fin_cases j <;> simp

theorem annulus_parts {q : Space → ℝ} {ε R : ℝ} {K : NNReal}
    (hK : LipschitzOnWith K q {y : Space | ε ≤ ‖y‖ ∧ ‖y‖ ≤ R})
    {ψ : Space → ℝ} (hψs : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ {y : Space | ε < ‖y‖ ∧ ‖y‖ < R}) (u : Space) :
    ∫ y, fderiv ℝ ψ y u * q y = -∫ y, ψ y * fderiv ℝ q y u := by
  set U : Set Space := {y : Space | ε < ‖y‖ ∧ ‖y‖ < R} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hUA : U ⊆ {y : Space | ε ≤ ‖y‖ ∧ ‖y‖ ≤ R} := fun y hy => ⟨hy.1.le, hy.2.le⟩
  obtain ⟨g, hgL, hgEq⟩ := hK.extend_real
  obtain ⟨Kψ, hψL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψc hψs (by simp)
  have hψd : Differentiable ℝ ψ := hψs.differentiable (by simp)
  have hψz : ∀ y, y ∉ U → ψ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport fun h => hy (hψU h)
  have hψdz : ∀ y, y ∉ U → fderiv ℝ ψ y = 0 := fun y hy => by
    by_contra h
    exact hy (hψU (support_fderiv_subset ℝ h))
  have key := hgL.integral_lineDeriv_mul_eq (μ := (volume : Measure Space)) hψL hψc u
  have h1 : (fun y => lineDeriv ℝ g y u * ψ y) =ᵐ[volume] fun y => ψ y * fderiv ℝ q y u := by
    filter_upwards [hgL.ae_differentiableAt (μ := (volume : Measure Space))] with y hy
    by_cases hyU : y ∈ U
    · have hev : q =ᶠ[nhds y] g := by
        filter_upwards [hUo.mem_nhds hyU] with z hz
        exact hgEq (hUA hz)
      have hq : HasFDerivAt q (fderiv ℝ g y) y := hy.hasFDerivAt.congr_of_eventuallyEq hev
      rw [hy.lineDeriv_eq_fderiv, hq.fderiv]
      ring
    · simp [hψz y hyU]
  have h2 : ∀ y, lineDeriv ℝ ψ y (-u) * g y = -(fderiv ℝ ψ y u * q y) := by
    intro y
    rw [(hψd y).lineDeriv_eq_fderiv, map_neg]
    by_cases hyU : y ∈ U
    · rw [← hgEq (hUA hyU)]
      ring
    · simp [hψdz y hyU]
  rw [integral_congr_ae h1] at key
  simp only [h2, integral_neg] at key
  rw [key, neg_neg]


theorem invNorm_ball (R : ℝ) : IntegrableOn (fun y : Space => ‖y‖⁻¹) (Metric.ball 0 R) volume := by
  have h := (integrableOn_fun_norm_addHaar (E := Space) volume (f := fun r : ℝ => r⁻¹) (r := R)).2 ?_
  · exact h
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  refine IntegrableOn.congr_fun ((continuous_id.integrableOn_Icc (a := 0) (b := R)).mono_set Set.Ioo_subset_Icc_self)
    (fun y hy => ?_) measurableSet_Ioo
  have : y ≠ 0 := hy.1.ne'
  simp only [id]
  field_simp

theorem inv_bound_integrable {F : Space → ℝ} (hF : AEStronglyMeasurable F volume) {R B : ℝ}
    (hb : ∀ᵐ y ∂volume, |F y| ≤ (Metric.ball (0 : Space) R).indicator (fun y => B * ‖y‖⁻¹) y) :
    Integrable F volume := by
  have hI : Integrable ((Metric.ball (0 : Space) R).indicator (fun y => B * ‖y‖⁻¹)) volume :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2 ((invNorm_ball R).const_mul B)
  exact hI.mono' hF (by filter_upwards [hb] with y hy; rwa [Real.norm_eq_abs])

theorem ball_volume (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.closedBall (0 : Space) r)).toReal = r ^ 3 * (volume (Metric.ball (0 : Space) 1)).toReal := by
  rw [Measure.addHaar_closedBall _ _ hr, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]

theorem small_integral {F : Space → ℝ} {r K : ℝ} (hr : 0 ≤ r) (hF : ∀ y, r < ‖y‖ → F y = 0)
    (hb : ∀ y, |F y| ≤ K) :
    |∫ y, F y| ≤ K * (r ^ 3 * (volume (Metric.ball (0 : Space) 1)).toReal) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.closedBall (0 : Space) r) (fun y hy => by
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    exact hF y hy), ← ball_volume r hr, ← Real.norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top (fun y _ => by rw [Real.norm_eq_abs]; exact hb y)

theorem weak_of_punctured {q : Space → ℝ} {M C : ℝ} (hm : AEStronglyMeasurable q volume)
    (hb : ∀ y, |q y| ≤ M)
    (hslope : ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, ∃ K : NNReal, LipschitzOnWith K q {y : Space | ε ≤ ‖y‖ ∧ ‖y‖ ≤ R})
    (hg : ∀ᵐ y ∂volume, ‖fderiv ℝ q y‖ ≤ C * ‖y‖⁻¹) :
    Reduction.IsWeakScalarGradientOf q (fun y => gradientAt q y) := by
  intro φ hφ j
  obtain ⟨hφs, hφc⟩ := hφ
  simp only [inner_gradient]
  set u := unitVector j with hu
  have hun : ‖u‖ = 1 := by simp [hu, unitVector]
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_ball (0 : Space)
  have hφz : ∀ y, y ∉ Metric.ball (0 : Space) R → φ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hR h)
  have hφd : Differentiable ℝ φ := hφs.differentiable (by simp)
  have hφdc : Continuous (fun y => fderiv ℝ φ y u) := (hφs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφdcs : HasCompactSupport (fun y => fderiv ℝ φ y u) :=
    (hφc.fderiv (𝕜 := ℝ)).mono' fun y hy => by
      by_contra h
      exact hy (by simp [image_eq_zero_of_notMem_tsupport h])
  obtain ⟨Bφ, hBφ⟩ := hφs.continuous.bounded_above_of_compact_support hφc
  obtain ⟨Bd, hBd⟩ := hφdc.bounded_above_of_compact_support hφdcs
  obtain ⟨c, hc⟩ := norm_fderiv_radialCutoff_le
  have hqD : Measurable (fun y => fderiv ℝ q y u) := measurable_fderiv_apply_const ℝ q u
  have hDq : ∀ᵐ y ∂volume, |fderiv ℝ q y u| ≤ |C| * ‖y‖⁻¹ := by
    filter_upwards [hg] with y hy
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ q y u‖ ≤ ‖fderiv ℝ q y‖ * ‖u‖ := (fderiv ℝ q y).le_opNorm u
      _ ≤ C * ‖y‖⁻¹ := by rw [hun, mul_one]; exact hy
      _ ≤ |C| * ‖y‖⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.2 (norm_nonneg y))
  have hweight : ∀ {F : Space → ℝ}, AEStronglyMeasurable F volume → (∀ y, |F y| ≤ |φ y| * |fderiv ℝ q y u|) →
      Integrable F volume := by
    intro F hF hFb
    refine inv_bound_integrable (R := R) (B := |Bφ| * |C|) hF ?_
    filter_upwards [hDq] with y hy
    by_cases hyR : y ∈ Metric.ball (0 : Space) R
    · rw [Set.indicator_of_mem hyR]
      calc |F y| ≤ |φ y| * |fderiv ℝ q y u| := hFb y
        _ ≤ |Bφ| * (|C| * ‖y‖⁻¹) := mul_le_mul ((Real.norm_eq_abs _ ▸ hBφ y).trans (le_abs_self _)) hy
            (abs_nonneg _) (abs_nonneg _)
        _ = |Bφ| * |C| * ‖y‖⁻¹ := by ring
    · rw [Set.indicator_of_notMem hyR]
      have := hFb y
      rw [hφz y hyR, abs_zero, zero_mul] at this
      exact this
  have hbI : Integrable ((Metric.ball (0 : Space) R).indicator (fun y => |Bφ| * |C| * ‖y‖⁻¹)) volume :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2 ((invNorm_ball R).const_mul _)
  have hdom : ∀ᵐ y ∂volume, |φ y| * |fderiv ℝ q y u| ≤
      (Metric.ball (0 : Space) R).indicator (fun y => |Bφ| * |C| * ‖y‖⁻¹) y := by
    filter_upwards [hDq] with y hy
    by_cases hyR : y ∈ Metric.ball (0 : Space) R
    · rw [Set.indicator_of_mem hyR]
      calc |φ y| * |fderiv ℝ q y u| ≤ |Bφ| * (|C| * ‖y‖⁻¹) := mul_le_mul ((Real.norm_eq_abs _ ▸ hBφ y).trans (le_abs_self _)) hy
            (abs_nonneg _) (abs_nonneg _)
        _ = |Bφ| * |C| * ‖y‖⁻¹ := by ring
    · rw [Set.indicator_of_notMem hyR, hφz y hyR, abs_zero, zero_mul]
  have hweight : ∀ {F : Space → ℝ}, AEStronglyMeasurable F volume → (∀ y, |F y| ≤ |φ y| * |fderiv ℝ q y u|) →
      Integrable F volume := by
    intro F hF hFb
    refine hbI.mono' hF ?_
    filter_upwards [hdom] with y hy
    rw [Real.norm_eq_abs]
    exact (hFb y).trans hy
  have hqb : ∀ y, |q y| ≤ |M| := fun y => (hb y).trans (le_abs_self M)
  have hcc : ∀ {g : Space → ℝ}, Continuous g → HasCompactSupport g → Integrable (fun y => g y * q y) volume := by
    intro g hg hgc
    have hI := hg.integrable_of_hasCompactSupport (μ := (volume : Measure Space)) hgc
    refine (hI.norm.mul_const |M|).mono' (hg.aestronglyMeasurable.mul hm) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hqb y) (abs_nonneg _)
  set r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hr
  have hr0 : ∀ n, 0 < r n := fun n => by simp only [hr]; positivity
  have hr1 : ∀ n, r n ≤ 1 := fun n => by
    simp only [hr]
    rw [div_le_one (by positivity)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set χ : ℕ → Space → ℝ := fun n => radialCutoff (r n) with hχ
  have hχs : ∀ n, ContDiff ℝ ∞ (χ n) := fun n => contDiff_radialCutoff (hr0 n)
  have hχd : ∀ n, Differentiable ℝ (χ n) := fun n => (hχs n).differentiable (by simp)
  have hχ1 : ∀ n y, ‖y‖ ≤ r n → χ n y = 1 := fun n y hy => radialCutoff_eq_one (hr0 n) hy
  have hχ0 : ∀ n y, 2 * r n < ‖y‖ → χ n y = 0 := fun n y hy => radialCutoff_eq_zero (hr0 n) hy.le
  have hχd0 : ∀ n y, 2 * r n < ‖y‖ → fderiv ℝ (χ n) y = 0 := by
    intro n y hy
    have hev : χ n =ᶠ[nhds y] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
      exact hχ0 n z hz
    rw [hev.fderiv_eq]
    simp
  have hχb0 : ∀ n y, 0 ≤ χ n y := fun n y => radialCutoff_nonneg _ _
  have hχb1 : ∀ n y, χ n y ≤ 1 := fun n y => radialCutoff_le_one _ _
  have hχdb : ∀ n y, |fderiv ℝ (χ n) y u| ≤ |c| / r n := by
    intro n y
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (χ n) y u‖ ≤ ‖fderiv ℝ (χ n) y‖ * ‖u‖ := (fderiv ℝ (χ n) y).le_opNorm u
      _ ≤ c / r n := by rw [hun, mul_one]; exact hc (r n) (hr0 n) y
      _ ≤ |c| / r n := div_le_div_of_nonneg_right (le_abs_self c) (hr0 n).le
  have hstep : ∀ n, (∫ y, fderiv ℝ φ y u * q y) + ∫ y, φ y * fderiv ℝ q y u =
      (∫ y, (fderiv ℝ φ y u * χ n y + φ y * fderiv ℝ (χ n) y u) * q y) +
        ∫ y, φ y * χ n y * fderiv ℝ q y u := by
    intro n
    set ψ : Space → ℝ := fun y => φ y * (1 - χ n y) with hψ
    have hψs : ContDiff ℝ ∞ ψ := hφs.mul (contDiff_const.sub (hχs n))
    have hψc : HasCompactSupport ψ := hφc.mul_right
    have hψd : ∀ y, fderiv ℝ ψ y u = fderiv ℝ φ y u * (1 - χ n y) - φ y * fderiv ℝ (χ n) y u := by
      intro y
      have h : HasFDerivAt ψ (φ y • (0 - fderiv ℝ (χ n) y) + (1 - χ n y) • fderiv ℝ φ y) y :=
        (hφd y).hasFDerivAt.mul ((hasFDerivAt_const (1 : ℝ) y).sub ((hχd n) y).hasFDerivAt)
      rw [h.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.zero_apply, smul_eq_mul]
      ring
    have hψU : tsupport ψ ⊆ {y : Space | r n / 2 < ‖y‖ ∧ ‖y‖ < R} := by
      have hcl : IsClosed ({y : Space | r n ≤ ‖y‖} ∩ tsupport φ) :=
        (isClosed_le continuous_const continuous_norm).inter (isClosed_tsupport φ)
      have hsub : Function.support ψ ⊆ {y : Space | r n ≤ ‖y‖} ∩ tsupport φ := by
        intro y hy
        refine ⟨?_, subset_tsupport φ (fun h => hy (by simp [hψ, h]))⟩
        by_contra h
        exact hy (by simp [hψ, hχ1 n y (not_le.1 h).le])
      intro y hy
      have h := hcl.closure_subset_iff.2 hsub hy
      have h2 := hR h.2
      rw [mem_ball_zero_iff] at h2
      have h1 : r n ≤ ‖y‖ := h.1
      exact ⟨by linarith [hr0 n], h2⟩
    obtain ⟨K, hK⟩ := hslope (r n / 2) (by linarith [hr0 n]) R
    have hparts := annulus_parts hK hψs hψc hψU u
    have hψdc : Continuous (fun y => fderiv ℝ ψ y u) := (hψs.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψdcs : HasCompactSupport (fun y => fderiv ℝ ψ y u) :=
      (hψc.fderiv (𝕜 := ℝ)).mono' fun y hy => by
        by_contra h
        exact hy (by simp [image_eq_zero_of_notMem_tsupport h])
    have iPD := hcc hψdc hψdcs
    have hE1c : Continuous (fun y => fderiv ℝ φ y u * χ n y + φ y * fderiv ℝ (χ n) y u) :=
      (hφdc.mul (hχs n).continuous).add (hφs.continuous.mul
        (((hχs n).continuous_fderiv (by simp)).clm_apply continuous_const))
    have hE1csupp : HasCompactSupport (fun y => fderiv ℝ φ y u * χ n y + φ y * fderiv ℝ (χ n) y u) :=
      (hφdcs.mul_right (f' := χ n)).add (hφc.mul_right (f' := fun y => fderiv ℝ (χ n) y u))
    have iE1 := hcc hE1c hE1csupp
    have hqm : AEStronglyMeasurable (fun y => fderiv ℝ q y u) volume := hqD.aestronglyMeasurable
    have iPsi : Integrable (fun y => ψ y * fderiv ℝ q y u) volume := by
      refine hweight (hψs.continuous.aestronglyMeasurable.mul hqm) fun y => ?_
      rw [abs_mul, abs_mul]
      have : |1 - χ n y| ≤ 1 := abs_le.2 ⟨by linarith [hχb1 n y, hχb0 n y], by linarith [hχb0 n y]⟩
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) this) (abs_nonneg _)
    have iE2 : Integrable (fun y => φ y * χ n y * fderiv ℝ q y u) volume := by
      refine hweight ((hφs.continuous.mul (hχs n).continuous).aestronglyMeasurable.mul hqm) fun y => ?_
      rw [abs_mul, abs_mul]
      have : |χ n y| ≤ 1 := abs_le.2 ⟨by linarith [hχb0 n y], hχb1 n y⟩
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) this) (abs_nonneg _)
    have eA : (∫ y, fderiv ℝ φ y u * q y) = (∫ y, fderiv ℝ ψ y u * q y) +
        ∫ y, (fderiv ℝ φ y u * χ n y + φ y * fderiv ℝ (χ n) y u) * q y := by
      rw [← integral_add iPD iE1]
      congr 1
      funext y
      rw [hψd]
      ring
    have eB : (∫ y, φ y * fderiv ℝ q y u) = (∫ y, ψ y * fderiv ℝ q y u) +
        ∫ y, φ y * χ n y * fderiv ℝ q y u := by
      rw [← integral_add iPsi iE2]
      congr 1
      funext y
      simp only [hψ]
      ring
    rw [eA, eB, hparts]
    ring
  set V : ℝ := (volume (Metric.ball (0 : Space) 1)).toReal with hV
  have hVpos : 0 ≤ V := ENNReal.toReal_nonneg
  have hrt : Filter.Tendsto r Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h12 : Filter.Tendsto (fun n => ∫ y, (fderiv ℝ φ y u * χ n y + φ y * fderiv ℝ (χ n) y u) * q y)
      Filter.atTop (nhds 0) := by
    set K0 : ℝ := 8 * V * |M| * (|Bd| + |Bφ| * |c|) with hK0
    refine squeeze_zero_norm (a := fun n => K0 * r n) (fun n => ?_) (by simpa using hrt.const_mul K0)
    have hb2 := small_integral (F := fun y => (fderiv ℝ φ y u * χ n y + φ y * fderiv ℝ (χ n) y u) * q y)
      (r := 2 * r n) (K := (|Bd| + |Bφ| * (|c| / r n)) * |M|) (by linarith [hr0 n])
      (fun y hy => by simp [hχ0 n y hy, hχd0 n y hy]) (fun y => by
        rw [abs_mul]
        refine mul_le_mul ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (hqb y) (abs_nonneg _) (by positivity)
        · rw [abs_mul]
          have : |χ n y| ≤ 1 := abs_le.2 ⟨by linarith [hχb0 n y], hχb1 n y⟩
          calc |fderiv ℝ φ y u| * |χ n y| ≤ |Bd| * 1 :=
                mul_le_mul ((Real.norm_eq_abs _ ▸ hBd y).trans (le_abs_self _)) this (abs_nonneg _) (abs_nonneg _)
            _ = |Bd| := mul_one _
        · rw [abs_mul]
          exact mul_le_mul ((Real.norm_eq_abs _ ▸ hBφ y).trans (le_abs_self _)) (hχdb n y) (abs_nonneg _)
            (abs_nonneg _))
    rw [Real.norm_eq_abs]
    refine hb2.trans ?_
    have hr := hr0 n
    have hr' := hr1 n
    have e : (|Bd| + |Bφ| * (|c| / r n)) * |M| * ((2 * r n) ^ 3 * V) =
        8 * V * |M| * (|Bd| * r n ^ 3 + |Bφ| * |c| * r n ^ 2) := by
      field_simp
      ring
    rw [e, hK0]
    have h3 : r n ^ 3 ≤ r n := by nlinarith [pow_le_one₀ hr.le hr' (n := 2)]
    have h2 : r n ^ 2 ≤ r n := by nlinarith
    have hA : 0 ≤ 8 * V * |M| := by positivity
    calc 8 * V * |M| * (|Bd| * r n ^ 3 + |Bφ| * |c| * r n ^ 2)
        ≤ 8 * V * |M| * (|Bd| * r n + |Bφ| * |c| * r n) := by gcongr
      _ = 8 * V * |M| * (|Bd| + |Bφ| * |c|) * r n := by ring
  have h3 : Filter.Tendsto (fun n => ∫ y, φ y * χ n y * fderiv ℝ q y u) Filter.atTop (nhds 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (F := fun n y => φ y * χ n y * fderiv ℝ q y u) (f := fun _ => (0 : ℝ))
      ((Metric.ball (0 : Space) R).indicator (fun y => |Bφ| * |C| * ‖y‖⁻¹))
      (fun n => (hφs.continuous.mul (hχs n).continuous).aestronglyMeasurable.mul hqD.aestronglyMeasurable) hbI
      (fun n => by
        filter_upwards [hdom] with y hy
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have : |χ n y| ≤ 1 := abs_le.2 ⟨by linarith [hχb0 n y], hχb1 n y⟩
        exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) this) (abs_nonneg _)).trans hy)
      (by
        filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : Space))] with y hy
        have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
        have ht : Filter.Tendsto (fun n => 2 * r n) Filter.atTop (nhds 0) := by simpa using hrt.const_mul 2
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [ht.eventually (gt_mem_nhds hy0)] with n hn
        simp [hχ0 n y hn])
    simpa using h
  have hlim := h12.add h3
  rw [add_zero] at hlim
  have hconst : (fun n => (∫ y, (fderiv ℝ φ y u * χ n y + φ y * fderiv ℝ (χ n) y u) * q y) +
      ∫ y, φ y * χ n y * fderiv ℝ q y u) = fun _ => (∫ y, fderiv ℝ φ y u * q y) + ∫ y, φ y * fderiv ℝ q y u :=
    funext fun n => (hstep n).symm
  rw [hconst] at hlim
  have h0 := tendsto_nhds_unique tendsto_const_nhds hlim
  linarith

end PuncturedWeakInternal

end CellCert

end Breakdown
