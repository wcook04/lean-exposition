import Breakdown.Cert.CoerciveEnergyIdentityTools

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEnergyIdentityInternal

open EnergyIdentityInternal

def baseBump : ContDiffBump (0 : Space) := ⟨1, 2, by norm_num, by norm_num⟩

def scaleMap (R : ℝ) : Space →L[ℝ] Space := R⁻¹ • ContinuousLinearMap.id ℝ Space

def cutoff (R : ℝ) (y : Space) : ℝ := baseBump (scaleMap R y)

def radiusSeq (n : ℕ) : ℝ := (n : ℝ) + 1

theorem scaleMap_apply (R : ℝ) (y : Space) : scaleMap R y = R⁻¹ • y := rfl

theorem radiusSeq_one_le (n : ℕ) : 1 ≤ radiusSeq n := by
  simp only [radiusSeq]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem radiusSeq_pos (n : ℕ) : 0 < radiusSeq n := by
  linarith [radiusSeq_one_le n]

theorem cutoff_contDiff (R : ℝ) : ContDiff ℝ ∞ (cutoff R) :=
  baseBump.contDiff.comp (scaleMap R).contDiff

theorem cutoff_nonneg (R : ℝ) (y : Space) : 0 ≤ cutoff R y := baseBump.nonneg

theorem cutoff_le_one (R : ℝ) (y : Space) : cutoff R y ≤ 1 := baseBump.le_one

theorem norm_scaleMap {R : ℝ} (hR : 0 < R) (y : Space) : ‖scaleMap R y‖ = R⁻¹ * ‖y‖ := by
  rw [scaleMap_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]

theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {y : Space} (hy : ‖y‖ ≤ R) : cutoff R y = 1 := by
  apply baseBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_scaleMap hR]
  change R⁻¹ * ‖y‖ ≤ 1
  rw [inv_mul_le_iff₀ hR]
  linarith

theorem cutoff_support {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutoff R) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * R))
  intro y hy
  apply baseBump.zero_of_le_dist
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
  rw [dist_zero_right, norm_scaleMap hR]
  change 2 ≤ R⁻¹ * ‖y‖
  rw [le_inv_mul_iff₀ hR]
  linarith

theorem cutoff_fderiv (R : ℝ) (y w : Space) :
    fderiv ℝ (cutoff R) y w = fderiv ℝ baseBump (scaleMap R y) (R⁻¹ • w) := by
  have hb : DifferentiableAt ℝ (⇑baseBump) (scaleMap R y) :=
    (baseBump.contDiff (n := 1)).differentiable (by norm_num) _
  have e : cutoff R = (⇑baseBump) ∘ (scaleMap R) := rfl
  rw [e, fderiv_comp y hb (scaleMap R).differentiableAt, ContinuousLinearMap.fderiv]
  rfl

theorem bump_deriv_bound : ∃ C, 0 ≤ C ∧ ∀ z : Space, ‖fderiv ℝ baseBump z‖ * (1 + ‖z‖) ≤ C := by
  have h0 : HasCompactSupport (fun z : Space => ‖fderiv ℝ baseBump z‖) :=
    (baseBump.hasCompactSupport.fderiv (𝕜 := ℝ)).norm
  have hc : HasCompactSupport (fun z : Space => ‖fderiv ℝ baseBump z‖ * (1 + ‖z‖)) := by
    have := h0.mul_right (f' := fun z : Space => 1 + ‖z‖)
    exact this
  have hcont : Continuous (fun z : Space => ‖fderiv ℝ baseBump z‖ * (1 + ‖z‖)) :=
    ((baseBump.contDiff (n := 1)).continuous_fderiv (by norm_num)).norm.mul
      (continuous_const.add continuous_norm)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hc
  refine ⟨C, le_trans (norm_nonneg _) (hC 0), fun z => le_trans (le_abs_self _) ?_⟩
  have := hC z
  rwa [Real.norm_eq_abs] at this

theorem cutoff_fderiv_bound {C : ℝ} (hC : ∀ z : Space, ‖fderiv ℝ baseBump z‖ * (1 + ‖z‖) ≤ C)
    {R : ℝ} (hR : 1 ≤ R) (y w : Space) : |fderiv ℝ (cutoff R) y w| ≤ C * ‖w‖ / (1 + ‖y‖) := by
  rw [cutoff_fderiv]
  have hR0 : 0 < R := by linarith
  have hzn := norm_scaleMap hR0 y
  have h1 : |fderiv ℝ baseBump (scaleMap R y) (R⁻¹ • w)|
      ≤ ‖fderiv ℝ baseBump (scaleMap R y)‖ * (R⁻¹ * ‖w‖) := by
    have := (fderiv ℝ baseBump (scaleMap R y)).le_opNorm (R⁻¹ • w)
    rw [Real.norm_eq_abs, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR0] at this
    exact this
  refine h1.trans ?_
  rw [le_div_iff₀ (by positivity)]
  have hA := norm_nonneg (fderiv ℝ baseBump (scaleMap R y))
  have hCz := hC (scaleMap R y)
  rw [hzn] at hCz
  have hinv : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hinv0 : 0 < R⁻¹ := inv_pos.mpr hR0
  have hw := norm_nonneg w
  have hy := norm_nonneg y
  have hlin : R⁻¹ * (1 + ‖y‖) ≤ 1 + R⁻¹ * ‖y‖ := by nlinarith
  have key : ‖fderiv ℝ baseBump (scaleMap R y)‖ * (R⁻¹ * (1 + ‖y‖)) ≤ C :=
    (mul_le_mul_of_nonneg_left hlin hA).trans hCz
  have k2 := mul_le_mul_of_nonneg_right key hw
  have e : ‖fderiv ℝ baseBump (scaleMap R y)‖ * (R⁻¹ * ‖w‖) * (1 + ‖y‖)
      = ‖fderiv ℝ baseBump (scaleMap R y)‖ * (R⁻¹ * (1 + ‖y‖)) * ‖w‖ := by ring
  rw [e]
  exact k2

theorem cutoff_eventually_one (y : Space) : ∀ᶠ n : ℕ in atTop, cutoff (radiusSeq n) y = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
  filter_upwards [eventually_ge_atTop N] with n hn
  apply cutoff_eq_one (radiusSeq_pos n)
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  simp only [radiusSeq]
  linarith

theorem cutoff_fderiv_eventually_zero (y : Space) :
    ∀ᶠ n : ℕ in atTop, fderiv ℝ (cutoff (radiusSeq n)) y = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have hyl : ‖y‖ < radiusSeq n := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    simp only [radiusSeq]
    linarith
  have he : cutoff (radiusSeq n) =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hyl)] with x hx
    exact cutoff_eq_one (radiusSeq_pos n) (le_of_lt (mem_ball_zero_iff.mp hx))
  rw [he.fderiv_eq]
  exact fderiv_const_apply _

theorem clm_apply_expand (L : Space →L[ℝ] ℝ) (u : Space) :
    L u = ∑ k : Fin 3, u k * L (unitVector k) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr u]
  simp [unitVector, map_sum, map_smul]

theorem div_smul (c : Space → ℝ) (a : Space → Space) (y : Space) (hc : DifferentiableAt ℝ c y)
    (ha : DifferentiableAt ℝ a y) :
    divergenceAt (fun x => c x • a x) y = c y * divergenceAt a y + fderiv ℝ c y (a y) := by
  simp only [divergenceAt]
  rw [show (fun x => c x • a x) = c • a from rfl, fderiv_smul hc ha]
  rw [clm_apply_expand (fderiv ℝ c y) (a y), Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp
  ring

theorem div_continuous (a : Space → Space) (ha : ContDiff ℝ 1 a) :
    Continuous (fun y => divergenceAt a y) := by
  unfold divergenceAt
  refine continuous_finsetSum _ (fun i _ => ?_)
  exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp
    ((ha.continuous_fderiv (by norm_num)).clm_apply continuous_const)

theorem compact_div_ibp (b : Space → Space) (g : Space → ℝ) (hb : ContDiff ℝ 1 b) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport b) :
    ∫ y, fderiv ℝ g y (b y) = -∫ y, divergenceAt b y * g y := by
  have hbk : ∀ k : Fin 3, ContDiff ℝ 1 (fun y => b y k) := fun k =>
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hb
  have hck : ∀ k : Fin 3, HasCompactSupport (fun y => b y k) := fun k => by
    have := hc.comp_left (g := fun u : Space => u k) (by simp)
    exact this
  have e1 : ∀ y, fderiv ℝ g y (b y) = ∑ k : Fin 3, b y k * fderiv ℝ g y (unitVector k) :=
    fun y => clm_apply_expand _ _
  have hdb : Differentiable ℝ b := hb.differentiable (by norm_num)
  have e2 : ∀ y, divergenceAt b y * g y =
      ∑ k : Fin 3, fderiv ℝ (fun x => b x k) y (unitVector k) * g y := by
    intro y
    simp only [divergenceAt, Finset.sum_mul, fderiv_component b (hdb y)]
  simp_rw [e1, e2]
  have cg' : ∀ k : Fin 3, Continuous fun y => fderiv ℝ g y (unitVector k) := fun k =>
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have cb' : ∀ k : Fin 3, Continuous fun y => fderiv ℝ (fun x => b x k) y (unitVector k) := fun k =>
    ((hbk k).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have i1 : ∀ k : Fin 3, Integrable (fun y => b y k * fderiv ℝ g y (unitVector k)) := fun k =>
    (((hbk k).continuous).mul (cg' k)).integrable_of_hasCompactSupport (hck k).mul_right
  have i2 : ∀ k : Fin 3, Integrable (fun y => fderiv ℝ (fun x => b x k) y (unitVector k) * g y) :=
    fun k => ((cb' k).mul hg.continuous).integrable_of_hasCompactSupport
      (((hck k).fderiv_apply (𝕜 := ℝ) _).mul_right)
  rw [integral_finsetSum _ (fun k _ => i1 k), integral_finsetSum _ (fun k _ => i2 k),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact ibp _ _ k (hbk k) hg (hck k)

theorem weighted_ibp (a : Space → Space) (g : Space → ℝ) (ha : ContDiff ℝ 1 a) (hg : ContDiff ℝ 1 g)
    (h1 : Integrable (fun y => fderiv ℝ g y (a y)))
    (h2 : Integrable (fun y => divergenceAt a y * g y))
    (h3 : Integrable (fun y => ‖a y‖ * |g y| / (1 + ‖y‖))) :
    ∫ y, fderiv ℝ g y (a y) = -∫ y, divergenceAt a y * g y := by
  obtain ⟨C, hC0, hC⟩ := bump_deriv_bound
  have hda : Differentiable ℝ a := ha.differentiable (by norm_num)
  have cc : ∀ R, ContDiff ℝ 1 (cutoff R) := fun R => (cutoff_contDiff R).of_le (by simp)
  have cga : Continuous (fun y => fderiv ℝ g y (a y)) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply ha.continuous
  have step : ∀ n, ∫ y, cutoff (radiusSeq n) y * fderiv ℝ g y (a y) =
      -∫ y, (cutoff (radiusSeq n) y * divergenceAt a y * g y
        + fderiv ℝ (cutoff (radiusSeq n)) y (a y) * g y) := by
    intro n
    have hb : ContDiff ℝ 1 (fun y => cutoff (radiusSeq n) y • a y) := (cc _).smul ha
    have hcs : HasCompactSupport (fun y => cutoff (radiusSeq n) y • a y) := by
      have := (cutoff_support (radiusSeq_pos n)).smul_right (f' := a)
      exact this
    have e := compact_div_ibp _ g hb hg hcs
    have e1 : ∀ y, fderiv ℝ g y (cutoff (radiusSeq n) y • a y)
        = cutoff (radiusSeq n) y * fderiv ℝ g y (a y) := fun y => by
      rw [map_smul, smul_eq_mul]
    have e2 : ∀ y, divergenceAt (fun x => cutoff (radiusSeq n) x • a x) y * g y =
        cutoff (radiusSeq n) y * divergenceAt a y * g y
          + fderiv ℝ (cutoff (radiusSeq n)) y (a y) * g y := fun y => by
      rw [div_smul _ _ y ((cc _).differentiable (by norm_num) y) (hda y)]
      ring
    simp_rw [e1, e2] at e
    exact e
  have lim1 : Tendsto (fun n => ∫ y, cutoff (radiusSeq n) y * fderiv ℝ g y (a y)) atTop
      (𝓝 (∫ y, fderiv ℝ g y (a y))) := by
    refine tendsto_integral_of_dominated_convergence
      (F := fun n y => cutoff (radiusSeq n) y * fderiv ℝ g y (a y))
      (fun y => ‖fderiv ℝ g y (a y)‖) (fun n => ?_) h1.norm (fun n => ?_) ?_
    · exact ((cutoff_contDiff _).continuous.mul cga).aestronglyMeasurable
    · refine Eventually.of_forall (fun y => ?_)
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)
    · refine Eventually.of_forall (fun y => ?_)
      apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_eventually_one y] with n hn
      rw [hn, one_mul]
  have lim2 : Tendsto (fun n => ∫ y, (cutoff (radiusSeq n) y * divergenceAt a y * g y
        + fderiv ℝ (cutoff (radiusSeq n)) y (a y) * g y)) atTop
      (𝓝 (∫ y, divergenceAt a y * g y)) := by
    refine tendsto_integral_of_dominated_convergence
      (F := fun n y => cutoff (radiusSeq n) y * divergenceAt a y * g y
        + fderiv ℝ (cutoff (radiusSeq n)) y (a y) * g y)
      (fun y => ‖divergenceAt a y * g y‖ + C * (‖a y‖ * |g y| / (1 + ‖y‖)))
      (fun n => ?_) (h2.norm.add (h3.const_mul C)) (fun n => ?_) ?_
    · refine (Continuous.add ?_ ?_).aestronglyMeasurable
      · exact ((cutoff_contDiff _).continuous.mul (div_continuous a ha)).mul hg.continuous
      · exact (((cutoff_contDiff _).continuous_fderiv (by simp)).clm_apply ha.continuous).mul
          hg.continuous
    · refine Eventually.of_forall (fun y => ?_)
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [mul_assoc, norm_mul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)
      · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        have hb := cutoff_fderiv_bound hC (radiusSeq_one_le n) y (a y)
        calc |fderiv ℝ (cutoff (radiusSeq n)) y (a y)| * |g y|
            ≤ C * ‖a y‖ / (1 + ‖y‖) * |g y| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
          _ = C * (‖a y‖ * |g y| / (1 + ‖y‖)) := by ring
    · refine Eventually.of_forall (fun y => ?_)
      apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_eventually_one y, cutoff_fderiv_eventually_zero y] with n hn hn'
      rw [hn, hn']
      simp
  have lim2' : Tendsto (fun n => ∫ y, cutoff (radiusSeq n) y * fderiv ℝ g y (a y)) atTop
      (𝓝 (-∫ y, divergenceAt a y * g y)) := by
    simp_rw [step]
    exact lim2.neg
  exact tendsto_nhds_unique lim1 lim2'

end SmoothEnergyIdentityInternal

end Coercive

end Breakdown
