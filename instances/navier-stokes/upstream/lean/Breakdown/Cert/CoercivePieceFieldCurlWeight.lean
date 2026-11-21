import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoerciveFieldModes
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.CoercivePieceFieldCurlWeightSlice
import Breakdown.Cert.CoercivePieceFieldCurlWeightIncrement
import Breakdown.Cert.CoercivePieceFieldCurlWeightTest
import Breakdown.Cert.CoercivePieceFieldCurlWeightPointwise
import Breakdown.Cert.CoercivePieceFieldCurlWeightSumSecondPartials

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace CurlWeight.Internal

open Internal.PerturbationFacts

theorem weakPartial_lineDeriv {h : Space → ℝ} {L : NNReal} (hh : LipschitzWith L h) (k : Fin 3) :
    IsWeakPartial h (fun y => lineDeriv ℝ h y (unitVector k)) k := by
  intro φ hφ
  obtain ⟨C, hC⟩ := hφ.1.lipschitzWith_of_hasCompactSupport hφ.2 (by simp)
  have e := LipschitzWith.integral_lineDeriv_mul_eq (μ := volume) hh hC hφ.2 (unitVector k)
  have hd : ∀ x, lineDeriv ℝ φ x (-unitVector k) = -fderiv ℝ φ x (unitVector k) := by
    intro x
    rw [((hφ.1.differentiable (by simp)) x).lineDeriv_eq_fderiv, map_neg]
  simp only [hd, neg_mul, integral_neg] at e
  have e2 : ∫ y, φ y * lineDeriv ℝ h y (unitVector k) = ∫ y, lineDeriv ℝ h y (unitVector k) * φ y := by
    congr 1
    funext y
    ring
  exact e2.trans e

theorem lineDeriv_eq_zero_of_not_mem {h : Space → ℝ} {y : Space} (hy : y ∉ tsupport h) (w : Space) :
    lineDeriv ℝ h y w = 0 := by
  have hev : (fun t : ℝ => h (y + t • w)) =ᶠ[𝓝 0] fun _ => 0 := by
    have h0 : ∀ᶠ x in 𝓝 y, h x = 0 := notMem_tsupport_iff_eventuallyEq.1 hy
    have hc : Tendsto (fun t : ℝ => y + t • w) (𝓝 0) (𝓝 y) := by
      have := ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).smul_const w).const_add y
      simpa using this
    exact hc.eventually h0
  unfold lineDeriv
  rw [hev.deriv_eq]
  simp

theorem support_convolve_subset (n : ℕ) (f : Space → ℝ) :
    Function.support (convolve (kernel n) f) ⊆ Metric.cthickening 2 (tsupport f) := by
  intro y hy
  have hs := support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hs
  have hka : a ∈ Metric.ball (0 : Space) (bump n).rOut := by
    have := (bump n).support_normed_eq (μ := volume)
    rw [kernel, this] at ha
    exact ha
  have hr : (bump n).rOut ≤ 2 := by
    show 2 / ((n : ℝ) + 1) ≤ 2
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  refine Metric.mem_cthickening_of_dist_le (a + b) b 2 (tsupport f) (subset_tsupport _ hb) ?_
  rw [dist_eq_norm, add_sub_cancel_right]
  rw [Metric.mem_ball, dist_zero_right] at hka
  linarith

theorem abs_convolve_le (n : ℕ) {f : Space → ℝ} {M : ℝ}
    (hM : ∀ y, |f y| ≤ M) (y : Space) : |convolve (kernel n) f y| ≤ M := by
  have hi : Integrable (kernel n) volume :=
    (kernel_contDiff n).continuous.integrable_of_hasCompactSupport (kernel_hasCompactSupport n)
  unfold convolve
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  calc |∫ t, kernel n t * f (y - t)| ≤ ∫ t, kernel n t * M := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (hi.mul_const M) (Eventually.of_forall fun t => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg n t)]
        exact mul_le_mul_of_nonneg_left (hM _) (kernel_nonneg n t)
    _ = M := by
        rw [integral_mul_const, show ∫ t, kernel n t = 1 from (bump n).integral_normed, one_mul]


theorem convolve_eq_zero_of_notMem {f : Space → ℝ} {S : Set Space} (hf : tsupport f ⊆ S) (n : ℕ) {y : Space}
    (hy : y ∉ Metric.cthickening 2 S) : convolve (kernel n) f y = 0 := by
  by_contra hne
  exact hy ((Metric.cthickening_subset_of_subset 2 hf) (support_convolve_subset n f hne))

theorem tendsto_integral_convolve_mul {f w : Space → ℝ} {M : ℝ} (hf : LocallyIntegrable f volume)
    (hM : ∀ y, |f y| ≤ M) {S : Set Space} (hS : tsupport f ⊆ S) (hSc : IsCompact S)
    (hw : LocallyIntegrable w volume)
    (hlim : ∀ᵐ y, Tendsto (fun n : ℕ => convolve (kernel n) f y) atTop (𝓝 (f y))) :
    Tendsto (fun n : ℕ => ∫ y, convolve (kernel n) f y * w y) atTop (𝓝 (∫ y, f y * w y)) := by
  have hK : IsCompact (Metric.cthickening 2 S) := hSc.cthickening
  refine tendsto_integral_of_dominated_convergence ((Metric.cthickening 2 S).indicator fun y => M * ‖w y‖)
    (fun n => ?_) ?_ (fun n => ?_) ?_
  · exact ((kernel_hasCompactSupport n).continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (kernel_contDiff n).continuous hf).aestronglyMeasurable.mul hw.aestronglyMeasurable
  · exact (integrable_indicator_iff hK.measurableSet).2 ((hw.integrableOn_isCompact hK).norm.const_mul M)
  · refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ Metric.cthickening 2 S
    · rw [Set.indicator_of_mem hy, norm_mul, Real.norm_eq_abs (convolve _ _ y)]
      exact mul_le_mul_of_nonneg_right (abs_convolve_le n hM y) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hy, convolve_eq_zero_of_notMem hS n hy, zero_mul, norm_zero]
  · filter_upwards [hlim] with y hy
    exact hy.mul_const (w y)

theorem weakPartial_increment_test {u d : Space → ℝ} {k : Fin 3} (hu : LocallyIntegrable u volume)
    (hd : LocallyIntegrable d volume) (hw : IsWeakPartial u d k) {h : Space → ℝ} {L : NNReal}
    (hh : LipschitzWith L h) (hc : HasCompactSupport h) :
    ∫ y, h y * d y = -∫ y, lineDeriv ℝ h y (unitVector k) * u y := by
  have hloc : LocallyIntegrable h volume := hh.continuous.locallyIntegrable
  have hDl : LocallyIntegrable (fun y => lineDeriv ℝ h y (unitVector k)) volume :=
    hh.locallyIntegrable_lineDeriv (unitVector k)
  have hDb : ∀ y, |lineDeriv ℝ h y (unitVector k)| ≤ L := fun y => by
    have := norm_lineDeriv_le_of_lipschitz ℝ hh (x₀ := y) (v := unitVector k)
    rwa [norm_unitVector_eq, mul_one, Real.norm_eq_abs] at this
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hh.continuous
  have hMb : ∀ y, |h y| ≤ M := fun y => by rw [← Real.norm_eq_abs]; exact hM y
  have hsD : tsupport (fun y => lineDeriv ℝ h y (unitVector k)) ⊆ tsupport h := by
    refine closure_minimal (fun y hy => ?_) (isClosed_tsupport h)
    by_contra hn
    exact hy (lineDeriv_eq_zero_of_not_mem hn _)
  have hid : ∀ n : ℕ, ∫ y, convolve (kernel n) h y * d y =
      -∫ y, convolve (kernel n) (fun y => lineDeriv ℝ h y (unitVector k)) y * u y := by
    intro n
    have htest : IsTestFunction (convolve (kernel n) h) :=
      ⟨convolve_contDiff (kernel_contDiff n) (kernel_hasCompactSupport n) hloc,
        HasCompactSupport.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
          (kernel_hasCompactSupport n) hc⟩
    rw [hw _ htest]
    congr 2
    funext y
    rw [fderiv_convolve (kernel_contDiff n) (kernel_hasCompactSupport n) hloc k y,
      convolve_partial_eq (kernel_contDiff n) (kernel_hasCompactSupport n) (weakPartial_lineDeriv hh k) y]
  have T1 := tendsto_integral_convolve_mul hloc hMb subset_rfl hc.isCompact hd
    (Eventually.of_forall fun y => ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
      bump_rOut_tendsto hh.continuous y)
  have T2 := tendsto_integral_convolve_mul hDl hDb hsD hc.isCompact hu
    (ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) (φ := bump)
      (K := 2) bump_rOut_tendsto (Eventually.of_forall fun n => le_of_eq (by
        show 2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1))
        ring)) hDl)
  have T3 : Tendsto (fun n : ℕ => ∫ y, convolve (kernel n) h y * d y) atTop
      (𝓝 (-∫ y, lineDeriv ℝ h y (unitVector k) * u y)) := by
    simp only [hid]
    exact T2.neg
  exact tendsto_nhds_unique T1 T3

theorem increment_mul_bounded {a θ : Space → ℝ} {La Lθ : NNReal} (ha : LipschitzWith La a)
    (hθ : LipschitzWith Lθ θ) {A Mθ : ℝ} (hA : ∀ y, |a y| ≤ A) (hM : ∀ y, |θ y| ≤ Mθ) :
    ∃ K : NNReal, LipschitzWith K (fun y => a y * θ y) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hM0 : 0 ≤ Mθ := (abs_nonneg _).trans (hM 0)
  refine ⟨⟨A * Lθ + Mθ * La, by positivity⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have h1 := hθ.dist_le_mul x y
  have h2 := ha.dist_le_mul x y
  rw [Real.dist_eq] at h1 h2 ⊢
  have e : a x * θ x - a y * θ y = a x * (θ x - θ y) + θ y * (a x - a y) := by ring
  rw [e]
  have hd0 : 0 ≤ dist x y := dist_nonneg
  calc |a x * (θ x - θ y) + θ y * (a x - a y)| ≤ |a x| * |θ x - θ y| + |θ y| * |a x - a y| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ A * (Lθ * dist x y) + Mθ * (La * dist x y) := by
        gcongr
        · exact hA x
        · exact hM y
    _ = ((⟨A * Lθ + Mθ * La, by positivity⟩ : NNReal) : ℝ) * dist x y := by
        simp only
        ring

theorem weakPartial_increment_weight {u d : Space → ℝ} {k : Fin 3} (hu : LocallyIntegrable u volume)
    (hd : LocallyIntegrable d volume) (hw : IsWeakPartial u d k) {a : Space → ℝ} {La : NNReal}
    (ha : LipschitzWith La a) {A : ℝ} (hA : ∀ y, |a y| ≤ A) {θ : Space → ℝ} (hθ : IsTestFunction θ) :
    ∫ y, (a y * θ y) * d y =
      -∫ y, (θ y * lineDeriv ℝ a y (unitVector k) + a y * fderiv ℝ θ y (unitVector k)) * u y := by
  obtain ⟨Lθ, hLθ⟩ := hθ.1.lipschitzWith_of_hasCompactSupport hθ.2 (by simp)
  obtain ⟨Mθ, hMθ⟩ := hθ.2.exists_bound_of_continuous hθ.1.continuous
  obtain ⟨K, hK⟩ := increment_mul_bounded ha hLθ hA (fun y => by rw [← Real.norm_eq_abs]; exact hMθ y)
  have hc : HasCompactSupport (fun y => a y * θ y) := hθ.2.mul_left
  rw [weakPartial_increment_test hu hd hw hK hc]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ha.ae_lineDifferentiableAt (μ := volume) (unitVector k)] with y hy
  have h1 := hy.hasLineDerivAt
  have h2 : HasLineDerivAt ℝ θ (fderiv ℝ θ y (unitVector k)) y (unitVector k) :=
    ((hθ.1.differentiable (by simp)) y).hasFDerivAt.hasLineDerivAt (unitVector k)
  have h3 : HasLineDerivAt ℝ (fun y => a y * θ y)
      (lineDeriv ℝ a y (unitVector k) * θ y + a y * fderiv ℝ θ y (unitVector k)) y (unitVector k) := by
    unfold HasLineDerivAt at h1 h2 ⊢
    have := h1.mul h2
    simp only [zero_smul, add_zero] at this
    convert this using 1 <;> rfl
  rw [h3.lineDeriv]
  ring

namespace SliceAssembly

theorem locallyIntegrable_re {F : Space → ℂ} (hF : LocallyIntegrable F volume) :
    LocallyIntegrable (fun y => (F y).re) volume := by
  rw [locallyIntegrable_iff] at hF ⊢
  intro k hk
  exact (hF k hk).re

theorem locallyIntegrable_im {F : Space → ℂ} (hF : LocallyIntegrable F volume) :
    LocallyIntegrable (fun y => (F y).im) volume := by
  rw [locallyIntegrable_iff] at hF ⊢
  intro k hk
  exact (hF k hk).im

theorem locallyIntegrable_const_mul {u : Space → ℝ} (hu : LocallyIntegrable u volume) (c : ℝ) :
    LocallyIntegrable (fun y => c * u y) volume := by
  rw [locallyIntegrable_iff] at hu ⊢
  intro k hk
  exact (hu k hk).const_mul c

theorem integrable_bounded_mul {w u : Space → ℝ} {R M : ℝ} (hw : AEStronglyMeasurable w volume)
    (hM : ∀ y, |w y| ≤ M) (hs : ∀ y, R < ‖y‖ → w y = 0) (hu : LocallyIntegrable u volume) :
    Integrable (fun y => w y * u y) volume := by
  have hK : IsCompact (Metric.closedBall (0 : Space) R) := isCompact_closedBall 0 R
  have h1 : IntegrableOn (fun y => w y * u y) (Metric.closedBall (0 : Space) R) volume :=
    Integrable.bdd_mul (c := M) (hu.integrableOn_isCompact hK) hw.restrict
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y)
  refine h1.integrable_of_forall_notMem_eq_zero fun y hy => ?_
  have : R < ‖y‖ := by
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    exact hy
  rw [hs y this, zero_mul]

theorem weakPartial_differentiable_weight {u d : Space → ℝ} {k : Fin 3} (hu : LocallyIntegrable u volume)
    (hd : LocallyIntegrable d volume) (hw : IsWeakPartial u d k) {a : Space → ℝ} {La : NNReal}
    (ha : LipschitzWith La a) {A : ℝ} (hA : ∀ y, |a y| ≤ A) {θ : Space → ℝ}
    {θ' : Space → Space →L[ℝ] ℝ} (hθ : ∀ y, HasFDerivAt θ (θ' y) y) {C : ℝ} (hC : ∀ y, ‖θ' y‖ ≤ C)
    (hθc : HasCompactSupport θ) :
    ∫ y, (a y * θ y) * d y =
      -∫ y, (θ y * lineDeriv ℝ a y (unitVector k) + a y * θ' y (unitVector k)) * u y := by
  have hdiff : Differentiable ℝ θ := fun y => (hθ y).differentiableAt
  have hLθ : LipschitzWith (Real.toNNReal C) θ :=
    lipschitzWith_of_nnnorm_fderiv_le hdiff fun y => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal', (hθ y).fderiv]
      exact (hC y).trans (le_max_left _ _)
  obtain ⟨Mθ, hMθ⟩ := hθc.exists_bound_of_continuous hdiff.continuous
  obtain ⟨K, hK⟩ := increment_mul_bounded ha hLθ hA (fun y => by rw [← Real.norm_eq_abs]; exact hMθ y)
  have hc : HasCompactSupport (fun y => a y * θ y) := hθc.mul_left
  rw [weakPartial_increment_test hu hd hw hK hc]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ha.ae_lineDifferentiableAt (μ := volume) (unitVector k)] with y hy
  have h1 := hy.hasLineDerivAt
  have h2 : HasLineDerivAt ℝ θ (θ' y (unitVector k)) y (unitVector k) :=
    (hθ y).hasLineDerivAt (unitVector k)
  have h3 : HasLineDerivAt ℝ (fun y => a y * θ y)
      (lineDeriv ℝ a y (unitVector k) * θ y + a y * θ' y (unitVector k)) y (unitVector k) := by
    unfold HasLineDerivAt at h1 h2 ⊢
    have := h1.mul h2
    simp only [zero_smul, add_zero] at this
    convert this using 1 <;> rfl
  rw [h3.lineDeriv]
  ring

theorem weakPartial_sum {κ : Type*} [Fintype κ] {u d : κ → Space → ℝ} {k : Fin 3}
    (hu : ∀ t, LocallyIntegrable (u t) volume) (hd : ∀ t, LocallyIntegrable (d t) volume)
    (hw : ∀ t, IsWeakPartial (u t) (d t) k) (c : κ → ℝ) :
    IsWeakPartial (fun y => ∑ t, c t * u t y) (fun y => ∑ t, c t * d t y) k := by
  intro φ hφ
  have i1 : ∀ t, Integrable (fun y => φ y * d t y) volume := fun t => by
    simpa only [smul_eq_mul] using (hd t).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  have hφ' : Continuous (fun y => fderiv ℝ φ y (unitVector k)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ's : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector k)) :=
    hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector k)
  have i2 : ∀ t, Integrable (fun y => fderiv ℝ φ y (unitVector k) * u t y) volume := fun t => by
    simpa only [smul_eq_mul] using (hu t).integrable_smul_left_of_hasCompactSupport hφ' hφ's
  have e1 : (fun y => φ y * ∑ t, c t * d t y) = fun y => ∑ t, c t * (φ y * d t y) := by
    funext y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  have e2 : (fun y => fderiv ℝ φ y (unitVector k) * ∑ t, c t * u t y) =
      fun y => ∑ t, c t * (fderiv ℝ φ y (unitVector k) * u t y) := by
    funext y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [e1, e2, integral_finsetSum _ fun t _ => (i1 t).const_mul _,
    integral_finsetSum _ fun t _ => (i2 t).const_mul _, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul, integral_const_mul, hw t φ hφ, mul_neg]

theorem weight_term_eq {a θ p t u d : Space → ℝ}
    (W : ∫ y, (a y * θ y) * d y = -∫ y, (θ y * p y + a y * t y) * u y)
    (h1 : Integrable (fun y => θ y * p y * u y) volume) (h2 : Integrable (fun y => a y * t y * u y) volume) :
    ∫ y, a y * t y * u y = -(∫ y, a y * θ y * d y) - ∫ y, θ y * p y * u y := by
  have e : ∫ y, (θ y * p y + a y * t y) * u y = (∫ y, θ y * p y * u y) + ∫ y, a y * t y * u y := by
    rw [← integral_add h1 h2]
    congr 1
    funext y
    ring
  have e2 : ∫ y, a y * θ y * d y = ∫ y, (a y * θ y) * d y := rfl
  linarith

theorem term_pair_eq {a θr θi p tr ti ωr ωi dr di : Space → ℝ} (e : ℝ)
    (Wr : ∫ y, (a y * θr y) * di y = -∫ y, (θr y * p y + a y * tr y) * ωi y)
    (Wi : ∫ y, (a y * θi y) * dr y = -∫ y, (θi y * p y + a y * ti y) * ωr y)
    (hA1 : Integrable (fun y => a y * tr y * ωi y) volume) (hA2 : Integrable (fun y => a y * ti y * ωr y) volume)
    (hB1 : Integrable (fun y => a y * θr y * di y) volume) (hC1 : Integrable (fun y => θr y * p y * ωi y) volume)
    (hB2 : Integrable (fun y => a y * θi y * dr y) volume) (hC2 : Integrable (fun y => θi y * p y * ωr y) volume) :
    ∫ y, e * (-(a y * tr y * ωi y) + a y * ti y * ωr y) =
      ∫ y, e * (a y * θr y * di y + θr y * p y * ωi y - a y * θi y * dr y - θi y * p y * ωr y) := by
  have er := weight_term_eq Wr hC1 hA1
  have ei := weight_term_eq Wi hC2 hA2
  rw [integral_const_mul, integral_const_mul]
  congr 1
  have s1 : ∫ y, (-(a y * tr y * ωi y) + a y * ti y * ωr y) =
      (∫ y, -(a y * tr y * ωi y)) + ∫ y, a y * ti y * ωr y := integral_add hA1.neg hA2
  have s2 : ∫ y, (a y * θr y * di y + θr y * p y * ωi y - a y * θi y * dr y - θi y * p y * ωr y) =
      (∫ y, (a y * θr y * di y + θr y * p y * ωi y - a y * θi y * dr y)) - ∫ y, θi y * p y * ωr y :=
    integral_sub ((hB1.add hC1).sub hB2) hC2
  have s3 : ∫ y, (a y * θr y * di y + θr y * p y * ωi y - a y * θi y * dr y) =
      (∫ y, (a y * θr y * di y + θr y * p y * ωi y)) - ∫ y, a y * θi y * dr y :=
    integral_sub (hB1.add hC1) hB2
  have s4 : ∫ y, (a y * θr y * di y + θr y * p y * ωi y) =
      (∫ y, a y * θr y * di y) + ∫ y, θr y * p y * ωi y := integral_add hB1 hC1
  rw [s1, s2, s3, s4, integral_neg]
  linarith

theorem integral_sum_three {F : Fin 3 → Fin 3 → Fin 3 → Space → ℝ}
    (hF : ∀ i j l, Integrable (F i j l) volume) :
    ∫ y, ∑ i, ∑ j, ∑ l, F i j l y = ∑ i, ∑ j, ∑ l, ∫ y, F i j l y := by
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hF i j l]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hF i j l]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact integral_finsetSum _ fun l _ => hF i j l

theorem re_curl_eq (g : Fin 3 × Fin 3 → ℂ) (i : Fin 3) :
    (curlOfGrad g i).re = ∑ q : Fin 3 × Fin 3, alternatingSymbol i q.1 q.2 * (g (q.2, q.1)).re := by
  simp only [curlOfGrad, Complex.re_sum, Complex.re_ofReal_mul, Fintype.sum_prod_type]

theorem im_curl_eq (g : Fin 3 × Fin 3 → ℂ) (i : Fin 3) :
    (curlOfGrad g i).im = ∑ q : Fin 3 × Fin 3, alternatingSymbol i q.1 q.2 * (g (q.2, q.1)).im := by
  simp only [curlOfGrad, Complex.im_sum, Complex.im_ofReal_mul, Fintype.sum_prod_type]

theorem re_curlSecondDeriv_eq (h : Fin 3 × Fin 3 × Fin 3 → ℂ) (i j : Fin 3) :
    (∑ m : Fin 3, ∑ n : Fin 3, (alternatingSymbol i m n : ℂ) * h (n, j, m)).re =
      ∑ q : Fin 3 × Fin 3, alternatingSymbol i q.1 q.2 * (h (q.2, j, q.1)).re := by
  simp only [Complex.re_sum, Complex.re_ofReal_mul, Fintype.sum_prod_type]

theorem im_curlSecondDeriv_eq (h : Fin 3 × Fin 3 × Fin 3 → ℂ) (i j : Fin 3) :
    (∑ m : Fin 3, ∑ n : Fin 3, (alternatingSymbol i m n : ℂ) * h (n, j, m)).im =
      ∑ q : Fin 3 × Fin 3, alternatingSymbol i q.1 q.2 * (h (q.2, j, q.1)).im := by
  simp only [Complex.im_sum, Complex.im_ofReal_mul, Fintype.sum_prod_type]

theorem integrand_expand (a : ℝ) (w z : Fin 3 × Fin 3 → ℂ) :
    (Complex.I * (a : ℂ) * cdot (curlOfGrad w) (curlOfGrad z)).re =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l *
        (-(a * (z (l, j)).re * (curlOfGrad w i).im) + a * (z (l, j)).im * (curlOfGrad w i).re) := by
  simp only [cdot, curlOfGrad, Fin.sum_univ_three, map_add, map_mul, Complex.conj_ofReal, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

end SliceAssembly

open SliceAssembly in
theorem slice_bound_abstract {a : Space → ℝ} {La : NNReal} (ha : LipschitzWith La a) {A A' : ℝ}
    (hA : ∀ y, |a y| ≤ A)
    (hA' : ∀ᵐ y, ∑ j : Fin 3, (lineDeriv ℝ a y (unitVector j)) ^ 2 ≤ A' ^ 2 ∧ 0 ≤ A')
    {R : ℝ} {θ : Space → Fin 3 → ℂ} {Dθ : Fin 3 → Space → (Space →L[ℝ] ℂ)} {Cθ : Fin 3 → ℝ}
    (hθ : ∀ l y, HasFDerivAt (fun x => θ x l) (Dθ l y) y) (hθb : ∀ l y, ‖Dθ l y‖ ≤ Cθ l)
    (hθ0 : ∀ l y, R < ‖y‖ → θ y l = 0)
    {gψ : Space → Fin 3 × Fin 3 → ℂ} (hDe : ∀ l y j, Dθ l y (unitVector j) = gψ y (l, j))
    {g : Space → Fin 3 × Fin 3 → ℂ} {h : Space → Fin 3 × Fin 3 × Fin 3 → ℂ} {Δ : Space → Fin 3 → ℂ}
    (hgl : ∀ n m : Fin 3, LocallyIntegrable (fun y => g y (n, m)) volume)
    (hhl : ∀ n j m : Fin 3, LocallyIntegrable (fun y => h y (n, j, m)) volume)
    (hwp : ∀ n j m : Fin 3,
      IsWeakPartial (fun y => (g y (n, m)).re) (fun y => (h y (n, j, m)).re) j ∧
      IsWeakPartial (fun y => (g y (n, m)).im) (fun y => (h y (n, j, m)).im) j)
    (hL : ∀ᵐ y, ∀ l : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ m : Fin 3, ∑ n : Fin 3,
      (alternatingSymbol i j l : ℂ) * (alternatingSymbol i m n : ℂ) * h y (n, j, m) = Δ y l) :
    ENNReal.ofReal |∫ y, (Complex.I * ((a y : ℝ) : ℂ) * cdot (curlOfGrad (g y)) (curlOfGrad (gψ y))).re| ≤
      ∫⁻ y, ENNReal.ofReal ((A * Real.sqrt (cnormSq (Δ y)) + A' * Real.sqrt (cnormSq (curlOfGrad (g y))))
        * Real.sqrt (cnormSq (θ y))) := by
  obtain ⟨ωr, hωr⟩ : ∃ F : Fin 3 → Space → ℝ, ∀ i y, F i y = (curlOfGrad (g y) i).re :=
    ⟨fun i y => _, fun _ _ => rfl⟩
  obtain ⟨ωi, hωi⟩ : ∃ F : Fin 3 → Space → ℝ, ∀ i y, F i y = (curlOfGrad (g y) i).im :=
    ⟨fun i y => _, fun _ _ => rfl⟩
  obtain ⟨dr, hdr⟩ : ∃ F : Fin 3 → Fin 3 → Space → ℝ, ∀ i j y,
      F i j y = (∑ m : Fin 3, ∑ n : Fin 3, (alternatingSymbol i m n : ℂ) * h y (n, j, m)).re :=
    ⟨fun i j y => _, fun _ _ _ => rfl⟩
  obtain ⟨di, hdi⟩ : ∃ F : Fin 3 → Fin 3 → Space → ℝ, ∀ i j y,
      F i j y = (∑ m : Fin 3, ∑ n : Fin 3, (alternatingSymbol i m n : ℂ) * h y (n, j, m)).im :=
    ⟨fun i j y => _, fun _ _ _ => rfl⟩
  obtain ⟨θr, hθr⟩ : ∃ F : Fin 3 → Space → ℝ, ∀ l y, F l y = (θ y l).re := ⟨fun l y => _, fun _ _ => rfl⟩
  obtain ⟨θi, hθi⟩ : ∃ F : Fin 3 → Space → ℝ, ∀ l y, F l y = (θ y l).im := ⟨fun l y => _, fun _ _ => rfl⟩
  obtain ⟨p, hp⟩ : ∃ F : Fin 3 → Space → ℝ, ∀ j y, F j y = lineDeriv ℝ a y (unitVector j) :=
    ⟨fun j y => _, fun _ _ => rfl⟩
  have eωr : ∀ i, ωr i = fun y => ∑ q : Fin 3 × Fin 3, alternatingSymbol i q.1 q.2 * (g y (q.2, q.1)).re :=
    fun i => funext fun y => by rw [hωr, re_curl_eq]
  have eωi : ∀ i, ωi i = fun y => ∑ q : Fin 3 × Fin 3, alternatingSymbol i q.1 q.2 * (g y (q.2, q.1)).im :=
    fun i => funext fun y => by rw [hωi, im_curl_eq]
  have edr : ∀ i j, dr i j = fun y => ∑ q : Fin 3 × Fin 3, alternatingSymbol i q.1 q.2 * (h y (q.2, j, q.1)).re :=
    fun i j => funext fun y => by rw [hdr, re_curlSecondDeriv_eq]
  have edi : ∀ i j, di i j = fun y => ∑ q : Fin 3 × Fin 3, alternatingSymbol i q.1 q.2 * (h y (q.2, j, q.1)).im :=
    fun i j => funext fun y => by rw [hdi, im_curlSecondDeriv_eq]
  have lωr : ∀ i, LocallyIntegrable (ωr i) volume := fun i => by
    rw [eωr]
    exact locallyIntegrable_finsetSum _ fun (q : Fin 3 × Fin 3) _ =>
      locallyIntegrable_const_mul (locallyIntegrable_re (hgl q.2 q.1)) _
  have lωi : ∀ i, LocallyIntegrable (ωi i) volume := fun i => by
    rw [eωi]
    exact locallyIntegrable_finsetSum _ fun (q : Fin 3 × Fin 3) _ =>
      locallyIntegrable_const_mul (locallyIntegrable_im (hgl q.2 q.1)) _
  have ldr : ∀ i j, LocallyIntegrable (dr i j) volume := fun i j => by
    rw [edr]
    exact locallyIntegrable_finsetSum _ fun (q : Fin 3 × Fin 3) _ =>
      locallyIntegrable_const_mul (locallyIntegrable_re (hhl q.2 j q.1)) _
  have ldi : ∀ i j, LocallyIntegrable (di i j) volume := fun i j => by
    rw [edi]
    exact locallyIntegrable_finsetSum _ fun (q : Fin 3 × Fin 3) _ =>
      locallyIntegrable_const_mul (locallyIntegrable_im (hhl q.2 j q.1)) _
  have wr : ∀ i j, IsWeakPartial (ωr i) (dr i j) j := fun i j => by
    rw [eωr, edr]
    exact weakPartial_sum (fun q : Fin 3 × Fin 3 => locallyIntegrable_re (hgl q.2 q.1))
      (fun q : Fin 3 × Fin 3 => locallyIntegrable_re (hhl q.2 j q.1)) (fun q : Fin 3 × Fin 3 => (hwp q.2 j q.1).1) _
  have wi : ∀ i j, IsWeakPartial (ωi i) (di i j) j := fun i j => by
    rw [eωi, edi]
    exact weakPartial_sum (fun q : Fin 3 × Fin 3 => locallyIntegrable_im (hgl q.2 q.1))
      (fun q : Fin 3 × Fin 3 => locallyIntegrable_im (hhl q.2 j q.1)) (fun q : Fin 3 × Fin 3 => (hwp q.2 j q.1).2) _
  have hDθ0 : ∀ l y, R < ‖y‖ → Dθ l y = 0 := by
    intro l y hy
    have hev : (fun x => θ x l) =ᶠ[𝓝 y] fun _ => 0 := by
      have ho : IsOpen {x : Space | R < ‖x‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [ho.mem_nhds hy] with x hx using hθ0 l x hx
    exact (hθ l y).unique ((hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hev)
  have hre : ∀ l y, HasFDerivAt (θr l) (Complex.reCLM.comp (Dθ l y)) y := fun l y => by
    have e : θr l = fun x => Complex.reCLM (θ x l) := funext fun x => by rw [hθr]; rfl
    rw [e]
    exact Complex.reCLM.hasFDerivAt.comp y (hθ l y)
  have him : ∀ l y, HasFDerivAt (θi l) (Complex.imCLM.comp (Dθ l y)) y := fun l y => by
    have e : θi l = fun x => Complex.imCLM (θ x l) := funext fun x => by rw [hθi]; rfl
    rw [e]
    exact Complex.imCLM.hasFDerivAt.comp y (hθ l y)
  have hreb : ∀ l y, ‖Complex.reCLM.comp (Dθ l y)‖ ≤ Cθ l := fun l y =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by rw [Complex.reCLM_norm, one_mul]; exact hθb l y)
  have himb : ∀ l y, ‖Complex.imCLM.comp (Dθ l y)‖ ≤ Cθ l := fun l y =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by rw [Complex.imCLM_norm, one_mul]; exact hθb l y)
  have θr0 : ∀ l y, R < ‖y‖ → θr l y = 0 := fun l y hy => by rw [hθr, hθ0 l y hy, Complex.zero_re]
  have θi0 : ∀ l y, R < ‖y‖ → θi l y = 0 := fun l y hy => by rw [hθi, hθ0 l y hy, Complex.zero_im]
  have hsr : ∀ l, HasCompactSupport (θr l) := fun l =>
    HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) fun y hy => θr0 l y (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
      exact hy)
  have hsi : ∀ l, HasCompactSupport (θi l) := fun l =>
    HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) fun y hy => θi0 l y (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
      exact hy)
  have cθr : ∀ l, Continuous (θr l) := fun l => continuous_iff_continuousAt.2 fun y => (hre l y).continuousAt
  have cθi : ∀ l, Continuous (θi l) := fun l => continuous_iff_continuousAt.2 fun y => (him l y).continuousAt
  have bθr : ∀ l, ∃ M, ∀ y, |θr l y| ≤ M := fun l => by
    obtain ⟨M, hM⟩ := (hsr l).exists_bound_of_continuous (cθr l)
    exact ⟨M, fun y => by rw [← Real.norm_eq_abs]; exact hM y⟩
  have bθi : ∀ l, ∃ M, ∀ y, |θi l y| ≤ M := fun l => by
    obtain ⟨M, hM⟩ := (hsi l).exists_bound_of_continuous (cθi l)
    exact ⟨M, fun y => by rw [← Real.norm_eq_abs]; exact hM y⟩
  choose Mr hMr using bθr
  choose Mi hMi using bθi
  have ca : Continuous a := ha.continuous
  have mp : ∀ j, AEStronglyMeasurable (p j) volume := fun j => by
    have e : p j = fun y => lineDeriv ℝ a y (unitVector j) := funext fun y => hp j y
    rw [e]
    exact (ha.locallyIntegrable_lineDeriv (unitVector j)).aestronglyMeasurable
  have bp : ∀ j y, |p j y| ≤ La := fun j y => by
    have := norm_lineDeriv_le_of_lipschitz ℝ ha (x₀ := y) (v := unitVector j)
    rwa [norm_unitVector_eq, mul_one, Real.norm_eq_abs, ← hp] at this
  have etr : ∀ l j, (fun y => (Complex.reCLM.comp (Dθ l y)) (unitVector j)) =
      fun y => fderiv ℝ (θr l) y (unitVector j) := fun l j => funext fun y => by rw [(hre l y).fderiv]
  have eti : ∀ l j, (fun y => (Complex.imCLM.comp (Dθ l y)) (unitVector j)) =
      fun y => fderiv ℝ (θi l) y (unitVector j) := fun l j => funext fun y => by rw [(him l y).fderiv]
  have mtr : ∀ l j, AEStronglyMeasurable (fun y => (Complex.reCLM.comp (Dθ l y)) (unitVector j)) volume :=
    fun l j => by rw [etr]; exact (measurable_fderiv_apply_const ℝ (θr l) (unitVector j)).aestronglyMeasurable
  have mti : ∀ l j, AEStronglyMeasurable (fun y => (Complex.imCLM.comp (Dθ l y)) (unitVector j)) volume :=
    fun l j => by rw [eti]; exact (measurable_fderiv_apply_const ℝ (θi l) (unitVector j)).aestronglyMeasurable
  have btr : ∀ l j y, |(Complex.reCLM.comp (Dθ l y)) (unitVector j)| ≤ Cθ l := fun l j y => by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [norm_unitVector_eq, mul_one]
    exact hreb l y
  have bti : ∀ l j y, |(Complex.imCLM.comp (Dθ l y)) (unitVector j)| ≤ Cθ l := fun l j y => by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [norm_unitVector_eq, mul_one]
    exact himb l y
  have ztr : ∀ l j y, R < ‖y‖ → (Complex.reCLM.comp (Dθ l y)) (unitVector j) = 0 := fun l j y hy => by
    rw [hDθ0 l y hy]; simp
  have zti : ∀ l j y, R < ‖y‖ → (Complex.imCLM.comp (Dθ l y)) (unitVector j) = 0 := fun l j y hy => by
    rw [hDθ0 l y hy]; simp
  have hA0 : ∀ y, |a y| ≤ A := hA
  have iA1 : ∀ i j l, Integrable (fun y => a y * (Complex.reCLM.comp (Dθ l y)) (unitVector j) * ωi i y) volume :=
    fun i j l => integrable_bounded_mul (R := R) (M := A * Cθ l) (ca.aestronglyMeasurable.mul (mtr l j))
      (fun y => by rw [abs_mul]; exact mul_le_mul (hA0 y) (btr l j y) (abs_nonneg _) ((abs_nonneg _).trans (hA0 y)))
      (fun y hy => by rw [ztr l j y hy, mul_zero]) (lωi i)
  have iA2 : ∀ i j l, Integrable (fun y => a y * (Complex.imCLM.comp (Dθ l y)) (unitVector j) * ωr i y) volume :=
    fun i j l => integrable_bounded_mul (R := R) (M := A * Cθ l) (ca.aestronglyMeasurable.mul (mti l j))
      (fun y => by rw [abs_mul]; exact mul_le_mul (hA0 y) (bti l j y) (abs_nonneg _) ((abs_nonneg _).trans (hA0 y)))
      (fun y hy => by rw [zti l j y hy, mul_zero]) (lωr i)
  have iB1 : ∀ i j l, Integrable (fun y => a y * θr l y * di i j y) volume :=
    fun i j l => integrable_bounded_mul (R := R) (M := A * Mr l) (ca.mul (cθr l)).aestronglyMeasurable
      (fun y => by rw [abs_mul]; exact mul_le_mul (hA0 y) (hMr l y) (abs_nonneg _) ((abs_nonneg _).trans (hA0 y)))
      (fun y hy => by rw [θr0 l y hy, mul_zero]) (ldi i j)
  have iB2 : ∀ i j l, Integrable (fun y => a y * θi l y * dr i j y) volume :=
    fun i j l => integrable_bounded_mul (R := R) (M := A * Mi l) (ca.mul (cθi l)).aestronglyMeasurable
      (fun y => by rw [abs_mul]; exact mul_le_mul (hA0 y) (hMi l y) (abs_nonneg _) ((abs_nonneg _).trans (hA0 y)))
      (fun y hy => by rw [θi0 l y hy, mul_zero]) (ldr i j)
  have iC1 : ∀ i j l, Integrable (fun y => θr l y * p j y * ωi i y) volume :=
    fun i j l => integrable_bounded_mul (R := R) (M := Mr l * La) ((cθr l).aestronglyMeasurable.mul (mp j))
      (fun y => by rw [abs_mul]; exact mul_le_mul (hMr l y) (bp j y) (abs_nonneg _) ((abs_nonneg _).trans (hMr l y)))
      (fun y hy => by rw [θr0 l y hy, zero_mul]) (lωi i)
  have iC2 : ∀ i j l, Integrable (fun y => θi l y * p j y * ωr i y) volume :=
    fun i j l => integrable_bounded_mul (R := R) (M := Mi l * La) ((cθi l).aestronglyMeasurable.mul (mp j))
      (fun y => by rw [abs_mul]; exact mul_le_mul (hMi l y) (bp j y) (abs_nonneg _) ((abs_nonneg _).trans (hMi l y)))
      (fun y hy => by rw [θi0 l y hy, zero_mul]) (lωr i)
  have hterm : ∀ i j l,
      ∫ y, alternatingSymbol i j l * (-(a y * (Complex.reCLM.comp (Dθ l y)) (unitVector j) * ωi i y)
        + a y * (Complex.imCLM.comp (Dθ l y)) (unitVector j) * ωr i y) =
      ∫ y, alternatingSymbol i j l * (a y * θr l y * di i j y + θr l y * p j y * ωi i y
        - a y * θi l y * dr i j y - θi l y * p j y * ωr i y) := by
    intro i j l
    have Wr := weakPartial_differentiable_weight (lωi i) (ldi i j) (wi i j) ha hA (hre l) (hreb l) (hsr l)
    have Wi := weakPartial_differentiable_weight (lωr i) (ldr i j) (wr i j) ha hA (him l) (himb l) (hsi l)
    simp only [← hp] at Wr Wi
    exact term_pair_eq _ Wr Wi (iA1 i j l) (iA2 i j l) (iB1 i j l) (iC1 i j l) (iB2 i j l) (iC2 i j l)
  have hpt : ∀ y, (Complex.I * ((a y : ℝ) : ℂ) * cdot (curlOfGrad (g y)) (curlOfGrad (gψ y))).re =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l *
        (-(a y * (Complex.reCLM.comp (Dθ l y)) (unitVector j) * ωi i y)
          + a y * (Complex.imCLM.comp (Dθ l y)) (unitVector j) * ωr i y) := by
    intro y
    rw [integrand_expand]
    simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply, hDe, hωr, hωi]
  have hint : ∫ y, (Complex.I * ((a y : ℝ) : ℂ) * cdot (curlOfGrad (g y)) (curlOfGrad (gψ y))).re =
      ∫ y, ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * (a y * θr l y * di i j y
        + θr l y * p j y * ωi i y - a y * θi l y * dr i j y - θi l y * p j y * ωr i y) := by
    simp only [hpt]
    refine (integral_sum_three (F := fun i j l y => alternatingSymbol i j l *
        (-(a y * (Complex.reCLM.comp (Dθ l y)) (unitVector j) * ωi i y)
          + a y * (Complex.imCLM.comp (Dθ l y)) (unitVector j) * ωr i y))
        (fun i j l => ((iA1 i j l).neg.add (iA2 i j l)).const_mul _)).trans ?_
    refine Eq.trans ?_ (integral_sum_three (F := fun i j l y => alternatingSymbol i j l *
        (a y * θr l y * di i j y + θr l y * p j y * ωi i y - a y * θi l y * dr i j y - θi l y * p j y * ωr i y))
        (fun i j l => (((((iB1 i j l).add (iC1 i j l)).sub (iB2 i j l)).sub (iC2 i j l))).const_mul _)).symm
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
      hterm i j l
  rw [hint, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [hL, hA'] with y hy1 hy2
  rw [Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  have hL' : ∀ l, ∑ i, ∑ j, (alternatingSymbol i j l : ℂ) *
      (∑ m : Fin 3, ∑ n : Fin 3, (alternatingSymbol i m n : ℂ) * h y (n, j, m)) = Δ y l := by
    intro l
    rw [← hy1 l]
    simp only [Finset.mul_sum, mul_assoc]
  have hp2 : ∑ j : Fin 3, (fun j => p j y) j ^ 2 ≤ A' ^ 2 := by
    simp only [hp]
    exact hy2.1
  simp only [hθr, hθi, hdr, hdi, hωr, hωi]
  exact slice_pointwise_le (hA y) hp2 hy2.2 hL'

theorem curlWeightSlice_abs_le_proof (hD : ModeDerivativeHolds)
    {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) (ι : ℤ × ℤ) {n : ℕ} (c : Fin n → ℝ) (f : Fin n → Space → ℝ)
    (hf : ∀ β, ∃ K, LipschitzWith K (f β)) {A A' : ℝ} (hA : ∀ y, |∑ β, c β * f β y| ≤ A)
    (hA' : ∀ y, (∀ β, DifferentiableAt ℝ (f β) y) → ‖fderiv ℝ (fun x => ∑ β, c β * f β x) y‖ ≤ A') :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ENNReal.ofReal |∫ y, (Complex.I * ((∑ β, c β * f β y : ℝ) : ℂ)
          * cdot (curlOfGrad (modeGrad ι G σ y)) (curlOfGrad (modeGrad ι (gradField ψ) σ y))).re| ≤
        ∫⁻ y, ENNReal.ofReal ((A * Real.sqrt (cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) σ y))
          + A' * Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G σ y))))
          * Real.sqrt (cnormSq (modeVel ι ψ σ y))) := by
  obtain ⟨R, hR⟩ := hψ.2.2.1
  obtain ⟨La, hLa⟩ := increment_weightSum c f hf
  have hA'' := ae_lineDeriv_sq_le c f hf hA'
  refine ae_restrict_of_ae ?_
  filter_upwards [ae_modeSlice_weak hD hv ι, ae_modeSlice_sumSecondPartials hD hv ι] with σ hS hL
  obtain ⟨hgl, hhl, hwp⟩ := hS
  choose Cψ Dψ hDψ hDψe hDψb using fun l => hasFDerivAt_modeVel_testField hψ ι σ l
  have hθ0 : ∀ l y, R < ‖y‖ → modeVel ι ψ σ y l = 0 := fun l y hy => by
    rw [Breakdown.Coercive.Internal.FieldModes.modeVel_eq_zero hR ι σ hy]
    rfl
  exact slice_bound_abstract (a := fun y => ∑ β, c β * f β y) hLa hA hA'' (R := R) (θ := modeVel ι ψ σ)
    (Dθ := Dψ) hDψ hDψb hθ0 (gψ := modeGrad ι (gradField ψ) σ) (fun l y j => hDψe l y j)
    (g := modeGrad ι G σ) (h := modeSecondDeriv ι H σ) (Δ := modeVel ι (fun σ y => secondDerivTrace (H σ y)) σ)
    hgl hhl hwp hL

theorem curlWeightSlice_abs_le (_hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (_hR : ModeRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) (ι : ℤ × ℤ) {n : ℕ} (c : Fin n → ℝ) (f : Fin n → Space → ℝ)
    (hf : ∀ β, ∃ K, LipschitzWith K (f β)) {A A' : ℝ} (hA : ∀ y, |∑ β, c β * f β y| ≤ A)
    (hA' : ∀ y, (∀ β, DifferentiableAt ℝ (f β) y) → ‖fderiv ℝ (fun x => ∑ β, c β * f β x) y‖ ≤ A') :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ENNReal.ofReal |∫ y, (Complex.I * ((∑ β, c β * f β y : ℝ) : ℂ)
          * cdot (curlOfGrad (modeGrad ι G σ y)) (curlOfGrad (modeGrad ι (gradField ψ) σ y))).re| ≤
        ∫⁻ y, ENNReal.ofReal ((A * Real.sqrt (cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) σ y))
          + A' * Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G σ y))))
          * Real.sqrt (cnormSq (modeVel ι ψ σ y))) :=
  curlWeightSlice_abs_le_proof hD hv hψ ι c f hf hA hA'

theorem curlWeightPairing_abs_le (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) (ι : ℤ × ℤ) {n : ℕ} (c : Fin n → ℝ) (f : Fin n → Space → ℝ)
    (hf : ∀ β, ∃ K, LipschitzWith K (f β)) {A A' : ℝ} (hA : ∀ y, |∑ β, c β * f β y| ≤ A)
    (hA' : ∀ y, (∀ β, DifferentiableAt ℝ (f β) y) → ‖fderiv ℝ (fun x => ∑ β, c β * f β x) y‖ ≤ A') :
    ENNReal.ofReal |∫ z, (Complex.I * ((∑ β, c β * f β z.2 : ℝ) : ℂ)
        * cdot (curlOfGrad (modeGrad ι G z.1 z.2)) (curlOfGrad (modeGrad ι (gradField ψ) z.1 z.2))).re
        ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)| ≤
      ∫⁻ z, ENNReal.ofReal ((A * Real.sqrt (cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2))
        + A' * Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2))))
        * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2))) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  have hS := curlWeightSlice_abs_le hP hD hR hv hψ ι c f hf hA hA'
  have hTr : Continuous (fun B : Space →L[ℝ] Space →L[ℝ] Space => secondDerivTrace B) := by
    unfold secondDerivTrace
    exact continuous_finsetSum _ fun j _ =>
      (continuous_id.clm_apply continuous_const).clm_apply continuous_const
  have hCu : Continuous (fun x : Fin 3 × Fin 3 → ℂ => curlOfGrad x) := by
    unfold curlOfGrad
    fun_prop
  have m1 := Breakdown.Coercive.Internal.FieldModes.continuous_cnormSq.measurable.comp_aemeasurable
    (Breakdown.Coercive.Internal.FieldModes.aemeasurable_modeVel (X := fun σ y => secondDerivTrace (H σ y))
      (hTr.comp_aestronglyMeasurable hv.measurable_secondDeriv) ι)
  have m2 := Breakdown.Coercive.Internal.FieldModes.continuous_cnormSq.measurable.comp_aemeasurable
    (hCu.measurable.comp_aemeasurable (Breakdown.Coercive.Internal.FieldModes.aemeasurable_modeGrad hv.measurable_gradient ι))
  have m3 := Breakdown.Coercive.Internal.FieldModes.continuous_cnormSq.measurable.comp_aemeasurable
    (Breakdown.Coercive.Internal.FieldModes.aemeasurable_modeVel hψ.1.continuous.aestronglyMeasurable ι)
  have hmeas : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal
      ((A * Real.sqrt (cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2))
        + A' * Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2))))
        * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2)))) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
    (((m1.sqrt.const_mul A).add (m2.sqrt.const_mul A')).mul m3.sqrt).ennreal_ofReal
  by_cases hF : Integrable (fun z : ℝ × Space => (Complex.I * ((∑ β, c β * f β z.2 : ℝ) : ℂ)
      * cdot (curlOfGrad (modeGrad ι G z.1 z.2)) (curlOfGrad (modeGrad ι (gradField ψ) z.1 z.2))).re)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)
  · rw [integral_prod _ hF, lintegral_prod _ hmeas, ← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
    filter_upwards [hS] with σ hσ
    rw [Real.enorm_eq_ofReal_abs]
    exact hσ
  · rw [integral_undef hF, abs_zero, ENNReal.ofReal_zero]
    exact zero_le

end CurlWeight.Internal

end Coercive

end Breakdown
