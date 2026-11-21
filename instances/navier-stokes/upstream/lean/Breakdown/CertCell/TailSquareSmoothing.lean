import Breakdown.CertCell.Defs
import Breakdown.Cert.CoerciveRotation

open scoped ENNReal ContDiff Convolution
open MeasureTheory Filter Topology ContinuousLinearMap

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

namespace SquareInternal

def profile : ContDiffBump (0 : ℝ) := ⟨1, 4, one_pos, by norm_num⟩

def roundBump (y : Space) : ℝ := profile (‖y‖ ^ 2)

theorem roundBump_contDiff : ContDiff ℝ ∞ roundBump :=
  profile.contDiff.comp (contDiff_norm_sq ℝ)

theorem roundBump_nonneg (y : Space) : 0 ≤ roundBump y := profile.nonneg

theorem roundBump_le_one (y : Space) : roundBump y ≤ 1 := profile.le_one

theorem roundBump_eq_one {y : Space} (hy : ‖y‖ ≤ 1) : roundBump y = 1 := by
  apply profile.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)]
  show ‖y‖ ^ 2 ≤ 1
  nlinarith [norm_nonneg y]

theorem roundBump_eq_zero {y : Space} (hy : 2 ≤ ‖y‖) : roundBump y = 0 := by
  apply profile.zero_of_le_dist
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)]
  show (4 : ℝ) ≤ ‖y‖ ^ 2
  nlinarith

theorem roundBump_hasCompactSupport : HasCompactSupport roundBump :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) 2) fun y hy =>
    roundBump_eq_zero (le_of_lt (not_le.1 (by simpa using hy)))

def scaledBump (s : ℝ) (y : Space) : ℝ := roundBump (s⁻¹ • y)

theorem scaledBump_contDiff (s : ℝ) : ContDiff ℝ ∞ (scaledBump s) :=
  roundBump_contDiff.comp (contDiff_id.const_smul s⁻¹)

theorem scaledBump_isometry (s : ℝ) (A : Space ≃ₗᵢ[ℝ] Space) (y : Space) :
    scaledBump s (A y) = scaledBump s y := by
  simp only [scaledBump, roundBump, ← map_smul, LinearIsometryEquiv.norm_map]

theorem scaledBump_eq_one {s : ℝ} (hs : 0 < s) {y : Space} (hy : ‖y‖ ≤ s) :
    scaledBump s y = 1 := by
  apply roundBump_eq_one
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, inv_mul_le_iff₀ hs]
  linarith

theorem scaledBump_eq_zero {s : ℝ} (hs : 0 < s) {y : Space} (hy : 2 * s ≤ ‖y‖) :
    scaledBump s y = 0 := by
  apply roundBump_eq_zero
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, le_inv_mul_iff₀ hs]
  linarith

theorem scaledBump_hasCompactSupport {s : ℝ} (hs : 0 < s) : HasCompactSupport (scaledBump s) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * s)) fun y hy =>
    scaledBump_eq_zero hs (le_of_lt (not_le.1 (by simpa using hy)))

def bumpMass : ℝ := ∫ y, roundBump y

theorem bumpMass_pos : 0 < bumpMass :=
  roundBump_contDiff.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    roundBump_hasCompactSupport roundBump_nonneg (x := 0) (by rw [roundBump_eq_one (by simp)]; norm_num)

def roundKernel (s : ℝ) (y : Space) : ℝ := scaledBump s y / (s ^ 3 * bumpMass)

theorem roundKernel_contDiff (s : ℝ) : ContDiff ℝ ∞ (roundKernel s) :=
  (scaledBump_contDiff s).div_const _

theorem roundKernel_nonneg {s : ℝ} (hs : 0 < s) (y : Space) : 0 ≤ roundKernel s y :=
  div_nonneg (roundBump_nonneg _) (by have := bumpMass_pos; positivity)

theorem roundKernel_hasCompactSupport {s : ℝ} (hs : 0 < s) : HasCompactSupport (roundKernel s) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * s)) fun y hy => by
    simp [roundKernel, scaledBump_eq_zero hs (le_of_lt (not_le.1 (by simpa using hy)))]

theorem roundKernel_isometry (s : ℝ) (A : Space ≃ₗᵢ[ℝ] Space) (y : Space) :
    roundKernel s (A y) = roundKernel s y := by
  simp only [roundKernel, scaledBump_isometry]

theorem roundKernel_integral {s : ℝ} (hs : 0 < s) : ∫ y, roundKernel s y = 1 := by
  have h := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (volume : Measure Space) roundBump hs.le
  rw [finrank_euclideanSpace_fin] at h
  simp only [roundKernel, scaledBump, integral_div, h, smul_eq_mul, bumpMass]
  have := bumpMass_pos
  unfold bumpMass at this
  field_simp

theorem roundKernel_le {s : ℝ} (hs : 0 < s) (y : Space) :
    roundKernel s y ≤ 1 / (s ^ 3 * bumpMass) :=
  div_le_div_of_nonneg_right (roundBump_le_one _) (by have := bumpMass_pos; positivity)

theorem norm_lt_of_roundKernel_ne {s : ℝ} (hs : 0 < s) {y : Space} (hy : roundKernel s y ≠ 0) :
    ‖y‖ < 2 * s := by
  by_contra h
  exact hy (by simp [roundKernel, scaledBump_eq_zero hs (not_lt.1 h)])

theorem ae_tendsto_roundKernel {w : Space → Space} (hw : LocallyIntegrable w) :
    ∀ᵐ x, Tendsto (fun n : ℕ => (roundKernel (1 / ((n : ℝ) + 1)) ⋆[lsmul ℝ ℝ, volume] w) x)
      atTop (𝓝 (w x)) := by
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure Space)).ae_tendsto_average_norm_sub hw]
    with x₀ h₀
  simp only [convolution_eq_swap, lsmul_apply]
  have hr : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 : ℝ)
    rwa [mul_zero] at this
  have := (h₀.comp (Besicovitch.tendsto_filterAt volume x₀)).comp hr
  have hV : 0 < volume.real (Metric.ball (0 : Space) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hM := bumpMass_pos
  apply tendsto_integral_smul_of_tendsto_average_norm_sub
    (8 * volume.real (Metric.ball (0 : Space) 1) / bumpMass) this
  · exact Eventually.of_forall fun n => hw.integrableOn_isCompact (isCompact_closedBall _ _)
  · refine tendsto_const_nhds.congr fun n => ?_
    rw [integral_sub_left_eq_self (fun y => roundKernel (1 / ((n : ℝ) + 1)) y) volume x₀,
      roundKernel_integral (by positivity)]
  · refine Eventually.of_forall fun n y hy => ?_
    have h := norm_lt_of_roundKernel_ne (by positivity) hy
    dsimp only
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
    exact h.le
  · refine Eventually.of_forall fun n y => ?_
    have hs : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    dsimp only
    rw [abs_of_nonneg (roundKernel_nonneg hs _),
      Measure.addHaar_real_closedBall _ _ (by positivity), finrank_euclideanSpace_fin]
    refine (roundKernel_le hs _).trans (le_of_eq ?_)
    field_simp
    ring

theorem matSq_nonneg' (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem continuous_matSq' : Continuous matSq := by
  unfold matSq
  fun_prop

theorem sq_norm_average_le {ρ : Space → ℝ} (hρ : ∀ t, 0 ≤ ρ t) (hρi : Integrable ρ)
    (hρ1 : ∫ t, ρ t = 1) {v : Space → Space} (hv : Integrable (fun t => ρ t • v t))
    (hv2 : Integrable (fun t => ρ t * ‖v t‖ ^ 2)) :
    ‖∫ t, ρ t • v t‖ ^ 2 ≤ ∫ t, ρ t * ‖v t‖ ^ 2 := by
  obtain ⟨A, hA⟩ : ∃ A, ∫ t, ρ t • v t = A := ⟨_, rfl⟩
  rw [hA]
  have hpt : ∀ t, 2 * inner ℝ A (ρ t • v t) - ρ t * ‖A‖ ^ 2 ≤ ρ t * ‖v t‖ ^ 2 := by
    intro t
    have h0 : 0 ≤ ρ t * ‖v t - A‖ ^ 2 := mul_nonneg (hρ t) (sq_nonneg _)
    rw [norm_sub_sq_real] at h0
    rw [inner_smul_right, real_inner_comm]
    nlinarith
  have hi1 : Integrable (fun t => 2 * inner ℝ A (ρ t • v t)) := (hv.const_inner A).const_mul 2
  have hi : Integrable (fun t => 2 * inner ℝ A (ρ t • v t) - ρ t * ‖A‖ ^ 2) :=
    hi1.sub (hρi.mul_const _)
  calc ‖A‖ ^ 2 = ∫ t, (2 * inner ℝ A (ρ t • v t) - ρ t * ‖A‖ ^ 2) := by
        rw [integral_sub hi1 (hρi.mul_const _), integral_const_mul, integral_inner hv, hA,
          integral_mul_const, hρ1, real_inner_self_eq_norm_sq]
        ring
    _ ≤ ∫ t, ρ t * ‖v t‖ ^ 2 := integral_mono hi hv2 hpt

theorem sixth_le_tangent' {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) :
    a ^ 6 + 6 * a ^ 5 * (r - a) ≤ r ^ 6 := by
  have h1 : r ^ 6 - (a ^ 6 + 6 * a ^ 5 * (r - a)) =
      (r - a) ^ 2 * (r ^ 4 + 2 * r ^ 3 * a + 3 * r ^ 2 * a ^ 2 + 4 * r * a ^ 3 + 5 * a ^ 4) := by
    ring
  have h2 : 0 ≤ (r - a) ^ 2 *
      (r ^ 4 + 2 * r ^ 3 * a + 3 * r ^ 2 * a ^ 2 + 4 * r * a ^ 3 + 5 * a ^ 4) := by
    positivity
  linarith

theorem sixth_norm_average_le {ρ : Space → ℝ} (hρ : ∀ t, 0 ≤ ρ t) (hρi : Integrable ρ)
    (hρ1 : ∫ t, ρ t = 1) {v : Space → Space} (hv : Integrable (fun t => ρ t • v t))
    (hv6 : Integrable (fun t => ρ t * ‖v t‖ ^ 6)) :
    ‖∫ t, ρ t • v t‖ ^ 6 ≤ ∫ t, ρ t * ‖v t‖ ^ 6 := by
  have hnorm : ∀ t, ‖ρ t • v t‖ = ρ t * ‖v t‖ := fun t => by
    rw [norm_smul, Real.norm_of_nonneg (hρ t)]
  have hn : Integrable (fun t => ρ t * ‖v t‖) := hv.norm.congr (Eventually.of_forall hnorm)
  obtain ⟨a, ha_def⟩ : ∃ a, ∫ t, ρ t * ‖v t‖ = a := ⟨_, rfl⟩
  have ha : 0 ≤ a := ha_def ▸ integral_nonneg fun t => mul_nonneg (hρ t) (norm_nonneg _)
  have hA : ‖∫ t, ρ t • v t‖ ≤ a := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp_rw [hnorm]
    exact ha_def
  have hpt : ∀ t, a ^ 6 * ρ t + 6 * a ^ 5 * (ρ t * ‖v t‖) - 6 * a ^ 6 * ρ t ≤
      ρ t * ‖v t‖ ^ 6 := by
    intro t
    have := mul_le_mul_of_nonneg_left (sixth_le_tangent' (norm_nonneg (v t)) ha) (hρ t)
    nlinarith
  have hi1 : Integrable (fun t => a ^ 6 * ρ t + 6 * a ^ 5 * (ρ t * ‖v t‖)) :=
    (hρi.const_mul _).add (hn.const_mul _)
  have hi : Integrable (fun t => a ^ 6 * ρ t + 6 * a ^ 5 * (ρ t * ‖v t‖) - 6 * a ^ 6 * ρ t) :=
    hi1.sub (hρi.const_mul _)
  have hint : ∫ t, (a ^ 6 * ρ t + 6 * a ^ 5 * (ρ t * ‖v t‖) - 6 * a ^ 6 * ρ t) = a ^ 6 := by
    rw [integral_sub hi1 (hρi.const_mul _), integral_add (hρi.const_mul _) (hn.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul, hρ1, ha_def]
    ring
  calc ‖∫ t, ρ t • v t‖ ^ 6 ≤ a ^ 6 := pow_le_pow_left₀ (norm_nonneg _) hA 6
    _ = _ := hint.symm
    _ ≤ _ := integral_mono hi hv6 hpt

theorem fderiv_smoothing_column {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρs : HasCompactSupport ρ)
    {w : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hw : IsWeakGradient w G) (x : Space)
    (i : Fin 3) :
    fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, volume] w) x (unitVector i) =
      ∫ t, ρ t • G (x - t) (unitVector i) := by
  have hc1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hd := hρs.hasFDerivAt_convolution_left (lsmul ℝ ℝ) hc1 hw.1 x
  have hex : ConvolutionExistsAt (fderiv ℝ ρ) w x (precompL Space (lsmul ℝ ℝ)) volume :=
    (hρs.fderiv ℝ).convolutionExists_left _ (hc1.continuous_fderiv one_ne_zero) hw.1 x
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex]
  simp only [precompL_apply, lsmul_apply]
  have hψ : IsTestFunction (fun y => ρ (x - y)) :=
    ⟨hρ.comp (contDiff_const.sub contDiff_id), hρs.comp_homeomorph (Homeomorph.subLeft x)⟩
  have hweak := hw.2.2 _ hψ i
  have hder : ∀ y, fderiv ℝ (fun y => ρ (x - y)) y (unitVector i) =
      -fderiv ℝ ρ (x - y) (unitVector i) := by
    intro y
    have h1 : HasFDerivAt (fun y => ρ (x - y))
        ((fderiv ℝ ρ (x - y)).comp (-ContinuousLinearMap.id ℝ Space)) y :=
      ((hc1.differentiable one_ne_zero) (x - y)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).const_sub x)
    rw [h1.fderiv]
    simp
  simp_rw [hder, neg_smul, integral_neg, neg_neg] at hweak
  have e1 : ∫ t, ρ t • G (x - t) (unitVector i) = ∫ y, ρ (x - y) • G y (unitVector i) := by
    rw [← integral_sub_left_eq_self (fun y => ρ (x - y) • G y (unitVector i)) volume x]
    simp only [sub_sub_cancel]
  have e2 : ∫ t, (fderiv ℝ ρ t (unitVector i)) • w (x - t) =
      ∫ y, (fderiv ℝ ρ (x - y) (unitVector i)) • w y := by
    rw [← integral_sub_left_eq_self (fun y => (fderiv ℝ ρ (x - y) (unitVector i)) • w y) volume x]
    simp only [sub_sub_cancel]
  rw [e1, e2, hweak]

theorem matSq_fderiv_smoothing_le {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρs : HasCompactSupport ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρ1 : ∫ t, ρ t = 1)
    {w : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hw : IsWeakGradient w G)
    (h2 : LocallyIntegrable (fun y => matSq (G y))) (x : Space) :
    matSq (fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, volume] w) x) ≤
      (ρ ⋆[lsmul ℝ ℝ, volume] (fun y => matSq (G y))) x := by
  have hρc : Continuous ρ := hρ.continuous
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hGm : AEStronglyMeasurable (fun t => G (x - t)) volume :=
    hw.2.1.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
  have hF : ConvolutionExistsAt ρ (fun y => matSq (G y)) x (lsmul ℝ ℝ) volume :=
    hρs.convolutionExists_left _ hρc h2 x
  have hF' : Integrable (fun t => ρ t * matSq (G (x - t))) := by
    simpa [ConvolutionExistsAt] using hF
  have hM : ConvolutionExistsAt ρ G x (lsmul ℝ ℝ) volume :=
    hρs.convolutionExists_left _ hρc hw.2.1 x
  have hv : ∀ i : Fin 3, Integrable (fun t => ρ t • G (x - t) (unitVector i)) := by
    intro i
    simpa using (ContinuousLinearMap.apply ℝ Space (unitVector i)).integrable_comp hM
  have hv2 : ∀ i : Fin 3, Integrable (fun t => ρ t * ‖G (x - t) (unitVector i)‖ ^ 2) := by
    intro i
    refine hF'.mono' (hρc.aestronglyMeasurable.mul
      ((((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable
        hGm).norm).pow 2)) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hρ0 t) (sq_nonneg _))]
    refine mul_le_mul_of_nonneg_left ?_ (hρ0 t)
    unfold matSq
    exact Finset.single_le_sum (f := fun j => ‖G (x - t) (unitVector j)‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  unfold matSq
  simp_rw [fderiv_smoothing_column hρ hρs hw x, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hv2 i)]
  exact Finset.sum_le_sum fun i _ => sq_norm_average_le hρ0 hρi hρ1 (hv i) (hv2 i)

theorem norm_smoothing_sixth_le {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρs : HasCompactSupport ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρ1 : ∫ t, ρ t = 1)
    {w : Space → Space} (hw : LocallyIntegrable w) (h6 : LocallyIntegrable (fun y => ‖w y‖ ^ 6))
    (x : Space) :
    ‖(ρ ⋆[lsmul ℝ ℝ, volume] w) x‖ ^ 6 ≤ (ρ ⋆[lsmul ℝ ℝ, volume] (fun y => ‖w y‖ ^ 6)) x := by
  have hρc : Continuous ρ := hρ.continuous
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have ha : ConvolutionExistsAt ρ w x (lsmul ℝ ℝ) volume := hρs.convolutionExists_left _ hρc hw x
  have hb : ConvolutionExistsAt ρ (fun y => ‖w y‖ ^ 6) x (lsmul ℝ ℝ) volume :=
    hρs.convolutionExists_left _ hρc h6 x
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  exact sixth_norm_average_le hρ0 hρi hρ1 ha (by simpa [ConvolutionExistsAt] using hb)

theorem smoothing_isometry {ρ : Space → ℝ}
    (A : Space ≃ₗᵢ[ℝ] Space) (hρA : ∀ y, ρ (A y) = ρ y) {w : Space → Space} (hwA : ∀ᵐ y, w (A y) = A (w y)) (x : Space) :
    (ρ ⋆[lsmul ℝ ℝ, volume] w) (A x) = A ((ρ ⋆[lsmul ℝ ℝ, volume] w) x) := by
  simp only [convolution_def, lsmul_apply]
  have hmp : MeasurePreserving A volume volume := A.measurePreserving
  rw [← hmp.integral_comp A.toHomeomorph.measurableEmbedding]
  have hae : ∀ᵐ t, w (A (x - t)) = A (w (x - t)) :=
    (quasiMeasurePreserving_sub_left_of_right_invariant volume x).ae hwA
  have h1 : ∫ t, ρ (A t) • w (A x - A t) = ∫ t, A (ρ t • w (x - t)) := by
    refine integral_congr_ae (hae.mono fun t ht => ?_)
    simp only [hρA, ← map_sub, ht, map_smul]
  rw [h1]
  exact A.toLinearIsometry.integral_comp_comm _

theorem flipPoint_apply (y : Space) :
    flipPoint y 0 = y 0 ∧ flipPoint y 1 = -y 1 ∧ flipPoint y 2 = -y 2 := by
  simp [flipPoint, unitVector]

theorem flipPoint_ext {a b : Space} (h0 : a 0 = b 0) (h1 : a 1 = b 1) (h2 : a 2 = b 2) : a = b := by
  ext i
  fin_cases i <;> assumption

def flipLinear : Space →ₗ[ℝ] Space where
  toFun := flipPoint
  map_add' x y := by
    obtain ⟨a0, a1, a2⟩ := flipPoint_apply (x + y)
    obtain ⟨b0, b1, b2⟩ := flipPoint_apply x
    obtain ⟨c0, c1, c2⟩ := flipPoint_apply y
    refine flipPoint_ext ?_ ?_ ?_ <;> simp only [PiLp.add_apply, a0, a1, a2, b0, b1, b2, c0, c1, c2] <;> ring
  map_smul' c x := by
    obtain ⟨a0, a1, a2⟩ := flipPoint_apply (c • x)
    obtain ⟨b0, b1, b2⟩ := flipPoint_apply x
    refine flipPoint_ext ?_ ?_ ?_ <;> simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply] <;>
      simp only [a0, a1, a2, b0, b1, b2, PiLp.smul_apply, smul_eq_mul] <;> ring

theorem flipPoint_flipPoint (y : Space) : flipPoint (flipPoint y) = y := by
  obtain ⟨a0, a1, a2⟩ := flipPoint_apply (flipPoint y)
  obtain ⟨b0, b1, b2⟩ := flipPoint_apply y
  refine flipPoint_ext ?_ ?_ ?_ <;> simp only [a0, a1, a2, b0, b1, b2, neg_neg]

theorem norm_flipPoint (y : Space) : ‖flipPoint y‖ = ‖y‖ := by
  obtain ⟨b0, b1, b2⟩ := flipPoint_apply y
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, b0, b1, b2, neg_sq]

def flipIsometry : Space ≃ₗᵢ[ℝ] Space where
  toLinearEquiv := LinearEquiv.ofInvolutive flipLinear flipPoint_flipPoint
  norm_map' := norm_flipPoint

theorem flipIsometry_apply (y : Space) : flipIsometry y = flipPoint y := rfl

theorem exists_rotationIsometry (ψ : ℝ) : ∃ A : Space ≃ₗᵢ[ℝ] Space, ∀ y, A y = axialRot ψ y :=
  Coercive.axialRotationHolds_proof.1 ψ

theorem scaledBump_axialRot (s ψ : ℝ) (y : Space) : scaledBump s (axialRot ψ y) = scaledBump s y := by
  obtain ⟨A, hA⟩ := exists_rotationIsometry ψ
  rw [← hA, scaledBump_isometry]

theorem scaledBump_flip (s : ℝ) (y : Space) : scaledBump s (flipPoint y) = scaledBump s y := by
  rw [← flipIsometry_apply, scaledBump_isometry]

theorem fderiv_scaledBump (s : ℝ) (y : Space) :
    fderiv ℝ (scaledBump s) y =
      (fderiv ℝ roundBump (s⁻¹ • y)).comp (s⁻¹ • ContinuousLinearMap.id ℝ Space) := by
  have hb : DifferentiableAt ℝ roundBump (s⁻¹ • y) :=
    (roundBump_contDiff.differentiable (by simp)) _
  exact (hb.hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul s⁻¹)).fderiv

theorem exists_fderiv_roundBump_bound : ∃ M, ∀ x, ‖fderiv ℝ roundBump x‖ ≤ M :=
  (roundBump_contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (roundBump_hasCompactSupport.fderiv ℝ)

theorem norm_fderiv_scaledBump_le {s M : ℝ} (hs : 0 < s)
    (hM : ∀ x, ‖fderiv ℝ roundBump x‖ ≤ M) (y : Space) : ‖fderiv ℝ (scaledBump s) y‖ ≤ M / s := by
  rw [fderiv_scaledBump]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hs.le)
  intro v
  rw [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply]
  calc ‖fderiv ℝ roundBump (s⁻¹ • y) (s⁻¹ • v)‖
        ≤ ‖fderiv ℝ roundBump (s⁻¹ • y)‖ * ‖s⁻¹ • v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ M * (s⁻¹ * ‖v‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs]
        exact mul_le_mul_of_nonneg_right (hM _) (by positivity)
    _ = M / s * ‖v‖ := by ring

theorem fderiv_scaledBump_eq_zero_of_lt {s : ℝ} (hs : 0 < s) {y : Space} (hy : ‖y‖ < s) :
    fderiv ℝ (scaledBump s) y = 0 := by
  have h : scaledBump s =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy)] with z hz
    exact scaledBump_eq_one hs (mem_ball_zero_iff.1 hz).le
  rw [h.fderiv_eq, fderiv_const_apply]

theorem fderiv_scaledBump_eq_zero_of_gt {s : ℝ} (hs : 0 < s) {y : Space} (hy : 2 * s < ‖y‖) :
    fderiv ℝ (scaledBump s) y = 0 := by
  have h : scaledBump s =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact scaledBump_eq_zero hs (le_of_lt hz)
  rw [h.fderiv_eq, fderiv_const_apply]

theorem norm_add_sq_le_split {E : Type*} [SeminormedAddCommGroup E] (a b : E) {δ : ℝ}
    (hδ : 0 < δ) : ‖a + b‖ ^ 2 ≤ (1 + δ) * ‖a‖ ^ 2 + (1 + δ⁻¹) * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h2 : 0 ≤ ‖a + b‖ := norm_nonneg _
  have key : δ⁻¹ * (δ * ‖a‖ - ‖b‖) ^ 2 = δ * ‖a‖ ^ 2 + δ⁻¹ * ‖b‖ ^ 2 - 2 * ‖a‖ * ‖b‖ := by
    field_simp
    ring
  have h3 : 0 ≤ δ⁻¹ * (δ * ‖a‖ - ‖b‖) ^ 2 := mul_nonneg (inv_nonneg.2 hδ.le) (sq_nonneg _)
  have h4 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ h2 h1 2
  nlinarith

theorem matSq_fderiv_cutoff_le {s δ : ℝ} (hδ : 0 < δ) {W : Space → Space}
    (hW : ContDiff ℝ 1 W) (y : Space) :
    matSq (fderiv ℝ (fun z => scaledBump s z • W z) y) ≤
      (1 + δ) * matSq (fderiv ℝ W y) +
        (1 + δ⁻¹) * (3 * (‖fderiv ℝ (scaledBump s) y‖ ^ 2 * ‖W y‖ ^ 2)) := by
  have hc : ContDiff ℝ 1 (scaledBump s) := (scaledBump_contDiff s).of_le (by norm_num)
  rw [fderiv_fun_smul (hc.differentiable one_ne_zero y) (hW.differentiable one_ne_zero y)]
  have key : ∀ i : Fin 3,
      ‖(scaledBump s y • fderiv ℝ W y + (fderiv ℝ (scaledBump s) y).smulRight (W y))
          (unitVector i)‖ ^ 2 ≤
        (1 + δ) * ‖fderiv ℝ W y (unitVector i)‖ ^ 2 +
          (1 + δ⁻¹) * (‖fderiv ℝ (scaledBump s) y‖ ^ 2 * ‖W y‖ ^ 2) := by
    intro i
    have he : ‖unitVector i‖ = 1 := by simp [unitVector]
    have hc0 := roundBump_nonneg (s⁻¹ • y)
    have hc1 := roundBump_le_one (s⁻¹ • y)
    rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    refine (norm_add_sq_le_split _ _ hδ).trans ?_
    have h1 : ‖scaledBump s y • fderiv ℝ W y (unitVector i)‖ ^ 2 ≤
        ‖fderiv ℝ W y (unitVector i)‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, scaledBump, abs_of_nonneg hc0]
      exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_left (norm_nonneg _) hc1) 2
    have h2 : ‖fderiv ℝ (scaledBump s) y (unitVector i) • W y‖ ^ 2 ≤
        ‖fderiv ℝ (scaledBump s) y‖ ^ 2 * ‖W y‖ ^ 2 := by
      rw [norm_smul, mul_pow]
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (by positivity)
      calc ‖fderiv ℝ (scaledBump s) y (unitVector i)‖
          ≤ ‖fderiv ℝ (scaledBump s) y‖ * ‖unitVector i‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (scaledBump s) y‖ := by rw [he, mul_one]
    have hd1 : 0 ≤ 1 + δ := by linarith
    have hd2 : 0 ≤ 1 + δ⁻¹ := by positivity
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hd1) (mul_le_mul_of_nonneg_left h2 hd2)
  simp only [matSq, Fin.sum_univ_three]
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  linarith

theorem le_add_cube_div_sq' {u a : ℝ} (hu : 0 ≤ u) (ha : 0 < a) : u ≤ a + u ^ 3 / a ^ 2 := by
  rcases le_or_gt u a with h | h
  · have : 0 ≤ u ^ 3 / a ^ 2 := by positivity
    linarith
  · have h2 : u ≤ u ^ 3 / a ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h3 : a ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ ha.le h.le 2
      have h4 := mul_le_mul_of_nonneg_left h3 hu
      nlinarith
    linarith

theorem integral_fderiv_scaledBump_sq_mul_le {R M s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hM : ∀ x, ‖fderiv ℝ roundBump x‖ ≤ M) {W : Space → Space} (hW : ContDiff ℝ 1 W)
    (h6 : Integrable (fun y => ‖W y‖ ^ 6)) :
    Integrable (fun y => ‖fderiv ℝ (scaledBump R) y‖ ^ 2 * ‖W y‖ ^ 2) ∧
    ∫ y, ‖fderiv ℝ (scaledBump R) y‖ ^ 2 * ‖W y‖ ^ 2 ≤
      M ^ 2 * (8 * volume.real (Metric.ball (0 : Space) 1) * s +
        (∫ y in (Metric.ball (0 : Space) R)ᶜ, ‖W y‖ ^ 6) / s ^ 2) := by
  have ha : 0 < s / R := div_pos hs hR
  have hB : MeasurableSet (Metric.closedBall (0 : Space) (2 * R)) := Metric.isClosed_closedBall.measurableSet
  have hO : MeasurableSet (Metric.ball (0 : Space) R)ᶜ := Metric.isOpen_ball.measurableSet.compl
  have hIB : Integrable ((Metric.closedBall (0 : Space) (2 * R)).indicator (1 : Space → ℝ)) := by
    have : IntegrableOn (fun _ : Space => (1 : ℝ)) (Metric.closedBall (0 : Space) (2 * R)) :=
      integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne
    exact (integrable_indicator_iff hB).2 this
  have hIO : Integrable ((Metric.ball (0 : Space) R)ᶜ.indicator (fun y => ‖W y‖ ^ 6)) := h6.indicator hO
  have hI := (hIB.const_mul ((M / R) ^ 2 * (s / R))).add (hIO.const_mul ((M / R) ^ 2 / (s / R) ^ 2))
  have hdom : ∀ y, ‖fderiv ℝ (scaledBump R) y‖ ^ 2 * ‖W y‖ ^ 2 ≤
      (M / R) ^ 2 * (s / R) * (Metric.closedBall (0 : Space) (2 * R)).indicator 1 y +
        (M / R) ^ 2 / (s / R) ^ 2 * (Metric.ball (0 : Space) R)ᶜ.indicator (fun y => ‖W y‖ ^ 6) y := by
    intro y
    have hIB0 : 0 ≤ (Metric.closedBall (0 : Space) (2 * R)).indicator (1 : Space → ℝ) y :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) y
    have hIO0 : 0 ≤ (Metric.ball (0 : Space) R)ᶜ.indicator (fun y => ‖W y‖ ^ 6) y :=
      Set.indicator_nonneg (fun _ _ => by positivity) y
    have hrhs : 0 ≤ (M / R) ^ 2 * (s / R) * (Metric.closedBall (0 : Space) (2 * R)).indicator 1 y +
        (M / R) ^ 2 / (s / R) ^ 2 * (Metric.ball (0 : Space) R)ᶜ.indicator (fun y => ‖W y‖ ^ 6) y := by
      positivity
    by_cases h1 : ‖y‖ < R
    · rw [fderiv_scaledBump_eq_zero_of_lt hR h1]
      simpa using hrhs
    by_cases h2 : 2 * R < ‖y‖
    · rw [fderiv_scaledBump_eq_zero_of_gt hR h2]
      simpa using hrhs
    have hyB : y ∈ Metric.closedBall (0 : Space) (2 * R) := mem_closedBall_zero_iff.2 (not_lt.1 h2)
    have hyO : y ∈ (Metric.ball (0 : Space) R)ᶜ := fun hy => h1 (mem_ball_zero_iff.1 hy)
    rw [Set.indicator_of_mem hyB, Set.indicator_of_mem hyO, Pi.one_apply, mul_one]
    have hD2 : ‖fderiv ℝ (scaledBump R) y‖ ^ 2 ≤ (M / R) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_scaledBump_le hR hM y) 2
    have hi := le_add_cube_div_sq' (sq_nonneg ‖W y‖) ha
    have h6' : (‖W y‖ ^ 2) ^ 3 = ‖W y‖ ^ 6 := by ring
    rw [h6'] at hi
    calc ‖fderiv ℝ (scaledBump R) y‖ ^ 2 * ‖W y‖ ^ 2 ≤ (M / R) ^ 2 * ‖W y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hD2 (by positivity)
      _ ≤ (M / R) ^ 2 * (s / R + ‖W y‖ ^ 6 / (s / R) ^ 2) :=
          mul_le_mul_of_nonneg_left hi (by positivity)
      _ = (M / R) ^ 2 * (s / R) + (M / R) ^ 2 / (s / R) ^ 2 * ‖W y‖ ^ 6 := by ring
  have hcont : Continuous (fun y => ‖fderiv ℝ (scaledBump R) y‖ ^ 2 * ‖W y‖ ^ 2) :=
    ((((scaledBump_contDiff R).of_le (by norm_num)).continuous_fderiv
      one_ne_zero).norm.pow 2).mul (hW.continuous.norm.pow 2)
  have hg : Integrable (fun y => ‖fderiv ℝ (scaledBump R) y‖ ^ 2 * ‖W y‖ ^ 2) := by
    refine Integrable.mono' hI hcont.aestronglyMeasurable (Eventually.of_forall (fun y => ?_))
    rw [Real.norm_of_nonneg (by positivity)]
    exact hdom y
  refine ⟨hg, ?_⟩
  calc ∫ y, ‖fderiv ℝ (scaledBump R) y‖ ^ 2 * ‖W y‖ ^ 2
      ≤ ∫ y, ((M / R) ^ 2 * (s / R) * (Metric.closedBall (0 : Space) (2 * R)).indicator 1 y +
        (M / R) ^ 2 / (s / R) ^ 2 * (Metric.ball (0 : Space) R)ᶜ.indicator (fun y => ‖W y‖ ^ 6) y) :=
        integral_mono hg hI hdom
    _ = (M / R) ^ 2 * (s / R) * volume.real (Metric.closedBall (0 : Space) (2 * R)) +
        (M / R) ^ 2 / (s / R) ^ 2 * ∫ y in (Metric.ball (0 : Space) R)ᶜ, ‖W y‖ ^ 6 := by
        rw [integral_add (hIB.const_mul _) (hIO.const_mul _), integral_const_mul,
          integral_const_mul, integral_indicator_one hB, integral_indicator hO]
    _ = _ := by
        rw [Measure.addHaar_real_closedBall volume (0 : Space) (by positivity : (0 : ℝ) ≤ 2 * R),
          finrank_euclideanSpace_fin]
        field_simp
        ring

theorem axialRadius_le (x t : Space) :
    Real.sqrt (x 0 ^ 2 + x 1 ^ 2) ≤ Real.sqrt (t 0 ^ 2 + t 1 ^ 2) + ‖x - t‖ := by
  have hd : ∀ i, x i = t i + (x - t) i := fun i => by simp
  have hdn : Real.sqrt ((x - t) 0 ^ 2 + (x - t) 1 ^ 2) ≤ ‖x - t‖ := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    apply Real.sqrt_le_sqrt
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg ((x - t) 2)]
  have hb := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ t 0 ^ 2 + t 1 ^ 2)
  have hc := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (x - t) 0 ^ 2 + (x - t) 1 ^ 2)
  have hbc : |t 0 * (x - t) 0 + t 1 * (x - t) 1| ≤
      Real.sqrt (t 0 ^ 2 + t 1 ^ 2) * Real.sqrt ((x - t) 0 ^ 2 + (x - t) 1 ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (t 0 * (x - t) 1 - t 1 * (x - t) 0)])
  have h0 := Real.sqrt_nonneg (t 0 ^ 2 + t 1 ^ 2)
  have h1 := Real.sqrt_nonneg ((x - t) 0 ^ 2 + (x - t) 1 ^ 2)
  calc Real.sqrt (x 0 ^ 2 + x 1 ^ 2)
      ≤ Real.sqrt ((Real.sqrt (t 0 ^ 2 + t 1 ^ 2) + Real.sqrt ((x - t) 0 ^ 2 + (x - t) 1 ^ 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [hd 0, hd 1]
        nlinarith [le_abs_self (t 0 * (x - t) 0 + t 1 * (x - t) 1)]
    _ = Real.sqrt (t 0 ^ 2 + t 1 ^ 2) + Real.sqrt ((x - t) 0 ^ 2 + (x - t) 1 ^ 2) :=
        Real.sqrt_sq (by positivity)
    _ ≤ _ := by linarith

theorem coord_sub_le (x t : Space) (i : Fin 3) : x i ≤ t i + ‖x - t‖ := by
  have h := PiLp.norm_apply_le (x - t) i
  rw [Real.norm_eq_abs] at h
  have : x i - t i = (x - t) i := by simp
  linarith [le_abs_self ((x - t) i)]

theorem continuous_axialRadius : Continuous (fun y : Space => Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) := by
  fun_prop

theorem continuous_coord (i : Fin 3) : Continuous (fun y : Space => y i) := by
  fun_prop

theorem volume_coord_zero (i : Fin 3) : volume {y : Space | y i = 0} = 0 := by
  have hne : LinearMap.ker ((EuclideanSpace.proj i : Space →L[ℝ] ℝ) : Space →ₗ[ℝ] ℝ) ≠ ⊤ := by
    intro htop
    have h : EuclideanSpace.single i (1 : ℝ) ∈
        LinearMap.ker ((EuclideanSpace.proj i : Space →L[ℝ] ℝ) : Space →ₗ[ℝ] ℝ) := by
      rw [htop]
      exact Submodule.mem_top
    simp at h
  have h := Measure.addHaar_submodule volume _ hne
  convert h using 2
  ext y
  simp


end SquareInternal

end TailBand

end CertCell

end Breakdown
