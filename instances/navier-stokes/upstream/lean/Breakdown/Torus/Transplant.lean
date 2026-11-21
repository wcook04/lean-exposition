import Breakdown.Torus.StatementsShell
import Breakdown.Torus.FreqTrSeries
import Breakdown.Torus.CoefCalculus
import Breakdown.Torus.Basic

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace Transplant.Internal

def profile (μ : ℝ) (g : Space → Space) (y : Space) : Space :=
  (Real.sqrt μ)⁻¹ • g ((Real.sqrt μ)⁻¹ • (y - center))

theorem center_apply (j : Fin 3) : center j = 1 / 2 := by
  simp [center, unitVector, Pi.single_apply]

theorem unitVector_apply (i j : Fin 3) : unitVector i j = if j = i then 1 else 0 := by
  simp [unitVector]

theorem wrap_apply (x : Space) (j : Fin 3) : wrap x j = x j - round (x j - 1 / 2) := by
  simp [wrap, unitVector, Pi.single_apply, center_apply]

theorem freq_apply' (n : Lattice) (j : Fin 3) : (freq n) j = (n j : ℝ) := by
  simp [freq, unitVector, Pi.single_apply]

theorem int_eq_of_abs_lt {d e : ℤ} (h : |(d : ℝ) - e| < 1) : d = e := by
  have h' : |d - e| < 1 := by exact_mod_cast h
  have := abs_lt.mp h'
  omega

theorem abs_apply_le (v : Space) (j : Fin 3) : |v j| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v j
  rwa [Real.norm_eq_abs] at this

variable {μ b : ℝ} {g : Space → Space}

theorem coord_near_tsupport (hμ : IsShellScale μ b) (hsupp : tsupport g ⊆ Metric.closedBall 0 b)
    {v : Space} (hv : (Real.sqrt μ)⁻¹ • (v - center) ∈ tsupport g) (j : Fin 3) :
    |v j - 1 / 2| ≤ 1 / 8 := by
  obtain ⟨h0, -, -, hb⟩ := hμ
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.mpr h0
  have hm := hsupp hv
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos hs, inv_mul_le_iff₀ hs] at hm
  have := abs_apply_le (v - center) j
  rw [PiLp.sub_apply, center_apply] at this
  linarith

theorem coord_near (hμ : IsShellScale μ b) (hsupp : tsupport g ⊆ Metric.closedBall 0 b) {v : Space}
    (hv : profile μ g v ≠ 0) (j : Fin 3) : |v j - 1 / 2| ≤ 1 / 8 :=
  coord_near_tsupport hμ hsupp (subset_tsupport g fun h => hv (by simp [profile, h])) j

theorem transplant_eq (hμ : IsShellScale μ b) (hsupp : tsupport g ⊆ Metric.closedBall 0 b) (y : Space)
    (n : Lattice) (hn : ∀ j, |y j - n j - 1 / 2| < 7 / 8) :
    transplantField μ g y = profile μ g (y - freq n) := by
  change profile μ g (wrap y) = _
  have hw : (∀ j, round (y j - 1 / 2) = n j) → wrap y = y - freq n := by
    intro h
    ext j
    rw [wrap_apply, PiLp.sub_apply, freq_apply', h j]
  by_cases h1 : profile μ g (wrap y) = 0
  · by_cases h2 : profile μ g (y - freq n) = 0
    · rw [h1, h2]
    · rw [hw fun j => ?_]
      have a1 := coord_near hμ hsupp h2 j
      have a2 := abs_sub_round (y j - 1 / 2)
      rw [PiLp.sub_apply, freq_apply'] at a1
      refine int_eq_of_abs_lt ?_
      rw [abs_le] at a1 a2
      rw [abs_lt]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  · rw [hw fun j => ?_]
    have a1 := coord_near hμ hsupp h1 j
    have a2 := hn j
    rw [wrap_apply] at a1
    refine int_eq_of_abs_lt ?_
    rw [abs_le] at a1
    rw [abs_lt] at a2 ⊢
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]


theorem contDiff_profile (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (profile μ g) :=
  (hg.comp ((contDiff_id.sub contDiff_const).const_smul _)).const_smul _

theorem hasFDerivAt_profile (hg : Differentiable ℝ g) (y : Space) :
    HasFDerivAt (profile μ g) ((Real.sqrt μ)⁻¹ • ((fderiv ℝ g ((Real.sqrt μ)⁻¹ • (y - center))).comp
      ((Real.sqrt μ)⁻¹ • ContinuousLinearMap.id ℝ Space))) y := by
  have h1 : HasFDerivAt (fun y : Space => (Real.sqrt μ)⁻¹ • (y - center))
      ((Real.sqrt μ)⁻¹ • ContinuousLinearMap.id ℝ Space) y :=
    ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const center).const_smul ((Real.sqrt μ)⁻¹ : ℝ)
  exact ((hg _).hasFDerivAt.comp y h1).const_smul ((Real.sqrt μ)⁻¹ : ℝ)

theorem fderiv_profile_apply (hg : Differentiable ℝ g) (y v : Space) :
    fderiv ℝ (profile μ g) y v =
      ((Real.sqrt μ)⁻¹ * (Real.sqrt μ)⁻¹) • fderiv ℝ g ((Real.sqrt μ)⁻¹ • (y - center)) v := by
  rw [(hasFDerivAt_profile hg y).fderiv]
  simp [smul_smul]

theorem divergence_profile (hg : Differentiable ℝ g) (hdiv : ∀ x, divergenceAt g x = 0) (y : Space) :
    ∑ i : Fin 3, (fderiv ℝ (profile μ g) y (unitVector i)) i = 0 := by
  have h := hdiv ((Real.sqrt μ)⁻¹ • (y - center))
  simp only [divergenceAt] at h
  simp only [fderiv_profile_apply hg, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, h, mul_zero]

theorem transplant_eventually (hμ : IsShellScale μ b) (hsupp : tsupport g ⊆ Metric.closedBall 0 b)
    (x : Space) :
    transplantField μ g =ᶠ[𝓝 x] fun y => profile μ g (y - freq (fun j => round (x j - 1 / 2))) := by
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 4)] with y hy
  refine transplant_eq hμ hsupp y _ fun j => ?_
  have h1 := abs_apply_le (y - x) j
  rw [PiLp.sub_apply] at h1
  have h2 := abs_sub_round (x j - 1 / 2)
  rw [Metric.mem_ball, dist_eq_norm] at hy
  rw [abs_le] at h1 h2
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem wrap_add_unitVector (x : Space) (i : Fin 3) : wrap (x + unitVector i) = wrap x := by
  ext j
  rw [wrap_apply, wrap_apply, PiLp.add_apply, unitVector_apply]
  split_ifs with h
  · rw [show x j + 1 - 1 / 2 = (x j - 1 / 2) + 1 by ring, round_add_one]
    push_cast
    ring
  · simp

end Transplant.Internal

open Transplant.Internal

theorem transplantSmooth : TransplantSmooth := by
  intro g μ b hg hdiv hμ hsupp
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact contDiff_iff_contDiffAt.mpr fun x =>
      ((contDiff_profile hg).comp (contDiff_id.sub contDiff_const)).contDiffAt.congr_of_eventuallyEq
        (transplant_eventually hμ hsupp x)
  · intro i x
    show profile μ g (wrap (x + unitVector i)) = profile μ g (wrap x)
    rw [wrap_add_unitVector]
  · intro x
    have e := (transplant_eventually hμ hsupp x).fderiv_eq (𝕜 := ℝ)
    simp only [divergenceAt, e, fderiv_comp_sub (f := profile μ g)]
    exact divergence_profile hgd hdiv _
  · intro x hx
    rw [transplant_eq hμ hsupp x 0 fun j => ?_]
    · simp [profile, freq]
    · have h1 := abs_apply_le (x - center) j
      rw [PiLp.sub_apply, center_apply] at h1
      rw [dist_eq_norm] at hx
      simp only [Pi.zero_apply, Int.cast_zero, sub_zero]
      linarith

namespace Transplant.Internal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {μ b : ℝ} {g : Space → Space}

theorem hasSum_sq_freqTrCoef {G : Space → Space} (hG : Continuous G) (hp : IsPeriodic G) :
    HasSum (fun k => ‖freqTrCoef G k‖ ^ 2) (∫ x in cell, ‖G x‖ ^ 2) := by
  let h := fun j => FreqTrSeries.Internal.compMap hG hp j
  have hj : ∀ j, HasSum (fun k => ‖(freqTrCoef G k).ofLp j‖ ^ 2) (∫ t, ‖h j t‖ ^ 2) := by
    intro j
    have hs := UnitAddTorus.hasSum_sq_mFourierCoeff ((h j).toLp 2 volume ℂ)
    simp only [UnitAddTorus.mFourierCoeff_toLp, h, FreqTrSeries.Internal.mFreqTrCoeff_compMap] at hs
    have hae := ContinuousMap.coeFn_toLp (p := 2) (μ := (volume : Measure (UnitAddTorus (Fin 3))))
      (𝕜 := ℂ) (h j)
    have e := integral_congr_ae (hae.fun_comp fun z : ℂ => ‖z‖ ^ 2)
    simp only [Function.comp_def] at e
    rwa [e] at hs
  have hsum := hasSum_sum (s := Finset.univ) fun j _ => hj j
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun t => ‖h j t‖ ^ 2) := fun j _ =>
    ((h j).continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_finsetSum _ hint] at hsum
  have hG' : Continuous fun x => ‖G x‖ ^ 2 • unitVector 0 := (hG.norm.pow 2).smul continuous_const
  have hp' : IsPeriodic fun x => ‖G x‖ ^ 2 • unitVector 0 := fun i x => by simp only [hp i x]
  have key := FreqTrSeries.Internal.mFreqTrCoeff_compMap hG' hp' 0 0
  rw [UnitAddTorus.mFourierCoeff, FreqTrSeries.Internal.freqTrCoef_apply hG'] at key
  simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_smul] at key
  have e1 : ∀ t, FreqTrSeries.Internal.compMap hG' hp' 0 t = ((∑ i, ‖h i t‖ ^ 2 : ℝ) : ℂ) := by
    intro t
    simp only [h, FreqTrSeries.Internal.compMap, ContinuousMap.coe_mk, FreqTrSeries.Internal.compFun]
    simp [EuclideanSpace.norm_sq_eq, unitVector, Complex.norm_real, sq_abs]
  have e2 : ∀ x, character 0 x * (((‖G x‖ ^ 2 • unitVector 0 : Space)).ofLp 0 : ℂ) =
      ((‖G x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    simp [character, freq, unitVector]
  have k2 : ((∫ t, ∑ i, ‖h i t‖ ^ 2 : ℝ) : ℂ) = ((∫ x in cell, ‖G x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    simpa only [e1, e2] using key
  rw [Complex.ofReal_injective k2] at hsum
  convert hsum using 1
  funext k
  exact EuclideanSpace.norm_sq_eq _


theorem norm_freq_sq' (k : Lattice) : ‖freq k‖ ^ 2 = ∑ i, ((k i : ℤ) : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [freq_apply', sq_abs]

theorem hasSum_weight {F : Space → Space} (hF : ContDiff ℝ ∞ F) (hp : IsPeriodic F) :
    HasSum (fun k => weight k * ‖freqTrCoef F k‖ ^ 2)
      ((∫ x in cell, ‖F x‖ ^ 2) + ∑ i : Fin 3, ∫ x in cell, ‖fderiv ℝ F x (unitVector i)‖ ^ 2) := by
  have h0 := hasSum_sq_freqTrCoef hF.continuous hp
  have hi : ∀ i : Fin 3, HasSum (fun k => ‖freqTrCoef (fun x => fderiv ℝ F x (unitVector i)) k‖ ^ 2)
      (∫ x in cell, ‖fderiv ℝ F x (unitVector i)‖ ^ 2) := fun i =>
    hasSum_sq_freqTrCoef (FreqTrSeries.Internal.contDiff_partialD i hF).continuous
      (FreqTrSeries.Internal.isPeriodic_partialD i hp)
  convert h0.add (hasSum_sum fun i _ => hi i) using 1
  funext k
  have hd : ∀ i : Fin 3, ‖freqTrCoef (fun x => fderiv ℝ F x (unitVector i)) k‖ ^ 2 =
      4 * π ^ 2 * ((k i : ℤ) : ℝ) ^ 2 * ‖freqTrCoef F k‖ ^ 2 := by
    intro i
    rw [coefDeriv F (FreqTrSeries.Internal.contDiff_one hF) hp i k, norm_smul, mul_pow]
    congr 1
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs,
      abs_of_pos pi_pos, mul_one, mul_pow, sq_abs]
    norm_num
  simp only [hd, weight, norm_freq_sq', Fin.sum_univ_three]
  ring

theorem norm_toV_sq {F : Space → Space} (hF : ContDiff ℝ ∞ F) (hp : IsPeriodic F)
    (hdiv : ∀ x, divergenceAt F x = 0) :
    ‖toV F‖ ^ 2 = (∫ x in cell, ‖F x‖ ^ 2) + ∑ i : Fin 3, ∫ x in cell, ‖fderiv ℝ F x (unitVector i)‖ ^ 2 := by
  rw [norm_sq_eq_tsum]
  simp only [(freqTrSeriesSpec coefDeriv F hF hp hdiv).1]
  exact (hasSum_weight hF hp).tsum_eq

theorem integral_rescale (f : Space → ℝ) :
    ∫ x, f ((Real.sqrt μ)⁻¹ • (x - center)) = Real.sqrt μ ^ 3 * ∫ y, f y := by
  have e := integral_sub_right_eq_self (μ := (volume : Measure Space))
    (fun x => f ((Real.sqrt μ)⁻¹ • x)) center
  rw [e, Measure.integral_comp_inv_smul_of_nonneg volume f (Real.sqrt_nonneg μ),
    finrank_euclideanSpace_fin, smul_eq_mul]

theorem coord_far {x : Space} (hx : x ∉ cell) : ∃ j, 1 / 2 < |x j - 1 / 2| := by
  simp only [cell, Set.mem_ofPred_eq, not_forall, Set.mem_Icc, not_and_or, not_le] at hx
  obtain ⟨j, hj⟩ := hx
  refine ⟨j, ?_⟩
  rcases hj with hj | hj
  · rw [abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos (by linarith)]
    linarith

theorem profile_off (hμ : IsShellScale μ b) (hsupp : tsupport g ⊆ Metric.closedBall 0 b) {x : Space}
    (hx : x ∉ cell) : profile μ g x = 0 := by
  by_contra h
  obtain ⟨j, hj⟩ := coord_far hx
  linarith [coord_near hμ hsupp h j]

theorem fderiv_profile_off (hμ : IsShellScale μ b) (hsupp : tsupport g ⊆ Metric.closedBall 0 b)
    (hgd : Differentiable ℝ g) {x : Space} (hx : x ∉ cell) (v : Space) :
    fderiv ℝ (profile μ g) x v = 0 := by
  rw [fderiv_profile_apply hgd]
  have h0 : fderiv ℝ g ((Real.sqrt μ)⁻¹ • (x - center)) = 0 := by
    by_contra h
    have hm := support_fderiv_subset ℝ (f := g) (Function.mem_support.mpr h)
    obtain ⟨j, hj⟩ := coord_far hx
    linarith [coord_near_tsupport hμ hsupp hm j]
  simp [h0]

theorem freq_zero : freq 0 = 0 := by simp [freq]

theorem eventually_cell (hμ : IsShellScale μ b) (hsupp : tsupport g ⊆ Metric.closedBall 0 b)
    {x : Space} (hx : x ∈ cell) : transplantField μ g =ᶠ[𝓝 x] profile μ g := by
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 4)] with y hy
  rw [transplant_eq hμ hsupp y 0 fun j => ?_, freq_zero, sub_zero]
  have h1 := abs_apply_le (y - x) j
  rw [PiLp.sub_apply] at h1
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have h2 := hx j
  rw [abs_le] at h1
  simp only [Pi.zero_apply, Int.cast_zero, sub_zero]
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem measurableSet_cell : MeasurableSet cell :=
  FreqTrSeries.Internal.isCompact_cell.isClosed.measurableSet

theorem integral_value (hμ : IsShellScale μ b) (hsupp : tsupport g ⊆ Metric.closedBall 0 b) :
    ∫ x in cell, ‖transplantField μ g x‖ ^ 2 =
      ((Real.sqrt μ)⁻¹) ^ 2 * (Real.sqrt μ ^ 3 * ∫ y, ‖g y‖ ^ 2) := by
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ.1
  rw [setIntegral_congr_fun measurableSet_cell fun x hx => by
      rw [(eventually_cell hμ hsupp hx).self_of_nhds],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [profile_off hμ hsupp hx]; simp,
    ← integral_rescale (μ := μ) (fun y => ‖g y‖ ^ 2), ← integral_const_mul]
  congr 1
  funext x
  rw [profile, norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, abs_of_pos hs]

theorem integral_deriv (hμ : IsShellScale μ b) (hsupp : tsupport g ⊆ Metric.closedBall 0 b)
    (hg : ContDiff ℝ ∞ g) (hF : ContDiff ℝ ∞ (transplantField μ g)) :
    ∑ i : Fin 3, ∫ x in cell, ‖fderiv ℝ (transplantField μ g) x (unitVector i)‖ ^ 2 =
      ((Real.sqrt μ)⁻¹ * (Real.sqrt μ)⁻¹) ^ 2 *
        (Real.sqrt μ ^ 3 * ∫ y, ∑ i : Fin 3, ‖fderiv ℝ g y (unitVector i)‖ ^ 2) := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun x => ‖fderiv ℝ (transplantField μ g) x (unitVector i)‖ ^ 2) (volume.restrict cell) :=
    fun i _ => ((FreqTrSeries.Internal.contDiff_partialD i hF).continuous.norm.pow 2).continuousOn.integrableOn_compact
      FreqTrSeries.Internal.isCompact_cell
  rw [← integral_finsetSum _ hint,
    setIntegral_congr_fun
      (g := fun x => ∑ i : Fin 3, ‖fderiv ℝ (profile μ g) x (unitVector i)‖ ^ 2) measurableSet_cell
      fun x hx => by simp only [(eventually_cell hμ hsupp hx).fderiv_eq],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [fderiv_profile_off hμ hsupp hgd hx],
    ← integral_rescale (μ := μ) (fun y => ∑ i : Fin 3, ‖fderiv ℝ g y (unitVector i)‖ ^ 2),
    ← integral_const_mul]
  congr 1
  funext x
  simp only [fderiv_profile_apply hgd, norm_smul, mul_pow, Finset.mul_sum, Real.norm_eq_abs, sq_abs]

end Transplant.Internal

open Transplant.Internal in
theorem transplantNorm (hS : TransplantSmooth) : TransplantNorm := by
  intro g μ b hg hdiv hμ hsupp
  obtain ⟨hF, hp, hFdiv, -⟩ := hS g μ b hg hdiv hμ hsupp
  have h0 := hμ.1
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.mpr h0
  have hq : (μ ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt μ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, Real.sqrt_eq_rpow]
    norm_num
  have hμs : μ = Real.sqrt μ ^ 2 := (Real.sq_sqrt h0.le).symm
  rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0.le _), hq,
    norm_toV_sq hF hp hFdiv, integral_value hμ hsupp, integral_deriv hμ hsupp hg hF]
  set s := Real.sqrt μ
  rw [hμs]
  field_simp
  ring

end Breakdown.Periodic
