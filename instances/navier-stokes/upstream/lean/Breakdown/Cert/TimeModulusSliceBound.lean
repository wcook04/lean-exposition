import Breakdown.Cert.TestDense
import Breakdown.Cert.HalfOrderGraphMem

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.TimeModulus.SliceBound

theorem lintegral_enorm_sq_eq (f : Space → Space) (μ : Measure Space) :
    ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

theorem toReal_sq_eq_integral {g : Space → Space} {μ : Measure Space} (hg : AEStronglyMeasurable g μ) : (eLpNorm g 2 μ).toReal ^ 2 = ∫ y, ‖g y‖ ^ 2 ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun y => ‖g y‖ ^ 2)
    (Eventually.of_forall fun y => by positivity) (hg.norm.pow 2)]
  have e : ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ 2) ∂μ = ∫⁻ y, ‖g y‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [e, lintegral_enorm_sq_eq, ENNReal.toReal_pow]


theorem cut_norm (x y : Freq.X) (A : Set Space)
    (hy : ((y : L2C) : Space → CSpace) =ᵐ[volume] fun ξ => A.indicator (fun _ => (1 : ℝ)) ξ • (x : L2C) ξ) :
    ‖x - y‖ = (eLpNorm (Aᶜ.indicator ((x : L2C) : Space → CSpace)) 2 volume).toReal := by
  have e : ((x - y : Freq.X) : L2C) = (x : L2C) - (y : L2C) := rfl
  change ‖((x - y : Freq.X) : L2C)‖ = _
  rw [e, Lp.norm_def]
  refine congrArg ENNReal.toReal (eLpNorm_congr_ae ?_)
  filter_upwards [Lp.coeFn_sub (x : L2C) (y : L2C), hy] with ξ h1 h2
  rw [h1, Pi.sub_apply, h2]
  by_cases hA : ξ ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hA), one_smul, sub_self]
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_mem (Set.mem_compl hA), zero_smul, sub_zero]

theorem cut_pair (x k : Freq.X) (h : IsHalfSspOf x k) (n : ℕ) :
    ∃ y m l : Freq.X, IsHalfSspOf y m ∧ IsSspOf y l ∧
      ‖x - y‖ = (eLpNorm ((Freq.Internal.NiceDense.outerSet n).indicator ((x : L2C) : Space → CSpace)) 2
        volume).toReal ∧
      ‖k - m‖ = (eLpNorm ((Freq.Internal.NiceDense.outerSet n).indicator ((k : L2C) : Space → CSpace)) 2
        volume).toReal := by
  set A : Set Space := {ξ | 1 / ((n : ℝ) + 1) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (n : ℝ) + 1} with hA
  have hAc : Aᶜ = Freq.Internal.NiceDense.outerSet n := by
    ext ξ
    simp only [hA, Set.mem_compl_iff, Set.mem_ofPred_eq, Freq.Internal.NiceDense.outerSet, not_and_or, not_le]
  have hAm : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hneg : ∀ ξ : Space, (-ξ ∈ A ↔ ξ ∈ A) := fun ξ => by simp [hA, norm_neg]
  have hone : ∀ ξ, |A.indicator (fun _ => (1 : ℝ)) ξ| ≤ 1 := fun ξ => by
    by_cases hξ : ξ ∈ A
    · rw [Set.indicator_of_mem hξ, abs_one]
    · rw [Set.indicator_of_notMem hξ, abs_zero]
      exact zero_le_one
  have heven : ∀ ξ, A.indicator (fun _ => (1 : ℝ)) (-ξ) = A.indicator (fun _ => (1 : ℝ)) ξ := fun ξ => by
    by_cases hξ : ξ ∈ A
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem ((hneg ξ).2 hξ)]
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem (fun h' => hξ ((hneg ξ).1 h'))]
  obtain ⟨y, hy⟩ := Internal.TestDense.exists_mul x (A.indicator fun _ => (1 : ℝ))
    (measurable_const.indicator hAm) 1 hone heven
  obtain ⟨m, hm⟩ := Internal.TestDense.exists_mul k (A.indicator fun _ => (1 : ℝ))
    (measurable_const.indicator hAm) 1 hone heven
  obtain ⟨l, hl⟩ := Internal.TestDense.exists_mul x (A.indicator sspFactor)
    ((by unfold sspFactor; fun_prop : Measurable sspFactor).indicator hAm) (4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2)
    (fun ξ => by
      by_cases hξ : ξ ∈ A
      · rw [Set.indicator_of_mem hξ]
        unfold sspFactor
        rw [abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hξ.2 2) (by positivity)
      · rw [Set.indicator_of_notMem hξ, abs_zero]
        positivity)
    (fun ξ => by
      by_cases hξ : ξ ∈ A
      · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem ((hneg ξ).2 hξ)]
        unfold sspFactor
        rw [norm_neg]
      · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem (fun h' => hξ ((hneg ξ).1 h'))])
  refine ⟨y, m, l, ?_, ?_, ?_, ?_⟩
  · unfold IsHalfSspOf at h ⊢
    filter_upwards [hy, hm, h] with ξ e1 e2 e3
    rw [e1, e2, e3, smul_smul, smul_smul, mul_comm]
  · unfold IsSspOf
    filter_upwards [hy, hl] with ξ e1 e2
    rw [e1, e2, smul_smul]
    congr 1
    by_cases hξ : ξ ∈ A
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ, mul_one]
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, mul_zero]
  · rw [cut_norm x y A hy, hAc]
  · rw [cut_norm k m A hm, hAc]

theorem halfSsp_test_dense {x k : Freq.X} (h : IsHalfSspOf x k) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ, IsTestField φ ∧ ‖embedX φ - x‖ < ε ∧ ‖solField (negSsp φ) - k‖ < ε := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨n, hn1, hn2⟩ := ((Freq.Internal.NiceDense.tail_small (Lp.memLp (x : L2C)) hε3).and
    (Freq.Internal.NiceDense.tail_small (Lp.memLp (k : L2C)) hε3)).exists
  obtain ⟨y, m, l, hym, hyl, ex, ek⟩ := cut_pair x k h n
  have hx : ‖x - y‖ < ε / 3 := ex ▸ ENNReal.toReal_lt_of_lt_ofReal hn1
  have hk : ‖k - m‖ < ε / 3 := ek ▸ ENNReal.toReal_lt_of_lt_ofReal hn2
  obtain ⟨φ, hφ, h1, h2⟩ := testDense_holds.1 y l hyl (ε / 3) hε3
  have hL : IsSspOf (embedX φ - y) (embedX (negSsp φ) - l) :=
    Internal.TestDense.isSspOf_sub (embedNegSsp_holds φ hφ) hyl
  have hH : IsHalfSspOf (embedX φ - y) (solField (negSsp φ) - m) :=
    Internal.TestDense.isHalfSspOf_sub (Internal.TestDense.halfSsp_embed_solField_negSsp hφ) hym
  have hsq := Internal.SupBoundHalfSsp.inner_eq_norm_sq hL hH
  have hle : ‖solField (negSsp φ) - m‖ ^ 2 ≤ (ε / 3) ^ 2 := by
    rw [← hsq]
    calc inner ℝ (embedX φ - y) (embedX (negSsp φ) - l)
        ≤ ‖embedX φ - y‖ * ‖embedX (negSsp φ) - l‖ := real_inner_le_norm _ _
      _ ≤ (ε / 3) * (ε / 3) := mul_le_mul h1.le h2.le (norm_nonneg _) hε3.le
      _ = (ε / 3) ^ 2 := by ring
  have hn : ‖solField (negSsp φ) - m‖ ≤ ε / 3 := by
    nlinarith [norm_nonneg (solField (negSsp φ) - m)]
  refine ⟨φ, hφ, ?_, ?_⟩
  · calc ‖embedX φ - x‖ ≤ ‖embedX φ - y‖ + ‖y - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 3 + ε / 3 := add_lt_add h1 (by rw [norm_sub_rev]; exact hx)
      _ < ε := by linarith
  · calc ‖solField (negSsp φ) - k‖ ≤ ‖solField (negSsp φ) - m‖ + ‖m - k‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 3 + ε / 3 := add_lt_add_of_le_of_lt hn (by rw [norm_sub_rev]; exact hk)
      _ < ε := by linarith

theorem exists_cutoff (R : ℝ) (hR : 0 < R) : ∃ χ : Space → ℝ, ∃ L : ℝ, ContDiff ℝ ∞ χ ∧
    (∀ y, 0 ≤ χ y) ∧ (∀ y, χ y ≤ 1) ∧ (∀ y ∈ Metric.closedBall (0 : Space) R, χ y = 1) ∧
    (∀ y, y ∉ Metric.closedBall (0 : Space) (R + 1) → χ y = 0 ∧ fderiv ℝ χ y = 0) ∧ 0 ≤ L ∧
    ∀ y, ‖fderiv ℝ χ y‖ ≤ L := by
  let b : ContDiffBump (0 : Space) := ⟨R, R + 1, hR, by linarith⟩
  have hc : ContDiff ℝ ∞ (b : Space → ℝ) := b.contDiff
  obtain ⟨L, hL⟩ := (hc.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (b.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hz : ∀ z ∈ (Metric.closedBall (0 : Space) (R + 1))ᶜ, b z = 0 := fun z hz => by
    have : z ∉ Function.support b := by
      rw [b.support_eq]
      exact fun h => hz (Metric.ball_subset_closedBall h)
    simpa using this
  refine ⟨b, max L 0, hc, fun y => b.nonneg, fun y => b.le_one, fun y hy => b.one_of_mem_closedBall hy,
    fun y hy => ⟨hz y hy, ?_⟩, le_max_right _ _, fun y => (hL y).trans (le_max_left _ _)⟩
  have hev : (b : Space → ℝ) =ᶠ[𝓝 y] fun _ => 0 :=
    Filter.eventuallyEq_of_mem (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hy) hz
  rw [hev.fderiv_eq]
  exact fderiv_const_apply 0

theorem fderiv_cut_apply {χ : Space → ℝ} {φ : Space → Space} (hχ : ContDiff ℝ ∞ χ)
    (hφ : ContDiff ℝ ∞ φ) (y v : Space) :
    fderiv ℝ (fun z => χ z ^ 2 • φ z) y v =
      (2 * χ y * fderiv ℝ χ y v) • φ y + χ y ^ 2 • fderiv ℝ φ y v := by
  have h1 : HasFDerivAt χ (fderiv ℝ χ y) y := (hχ.differentiable (by simp) y).hasFDerivAt
  have h2 : HasFDerivAt φ (fderiv ℝ φ y) y := (hφ.differentiable (by simp) y).hasFDerivAt
  have h3 := (h1.pow 2).smul h2
  rw [show (fun z => χ z ^ 2 • φ z) = ((fun x => χ x ^ 2) • φ) from rfl, h3.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [add_comm]
  congr 2
  simp

theorem cross_bound {χ c L p d q : ℝ} (hχ : 0 ≤ χ) (hc : |c| ≤ L)
    (hq : |q| ≤ p * d) : -(2 * χ * c * q) ≤ (1 / 2) * χ ^ 2 * d ^ 2 + 2 * L ^ 2 * p ^ 2 := by
  have hL : 0 ≤ L := (abs_nonneg c).trans hc
  have h1 : |2 * χ * c * q| = 2 * χ * (|c| * |q|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hχ, abs_two]
    ring
  have h2 : |c| * |q| ≤ L * (p * d) := mul_le_mul hc hq (abs_nonneg q) hL
  have h3 : 2 * χ * (|c| * |q|) ≤ 2 * χ * (L * (p * d)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : 2 * χ * (L * (p * d)) ≤ (1 / 2) * χ ^ 2 * d ^ 2 + 2 * L ^ 2 * p ^ 2 := by
    nlinarith [sq_nonneg (χ * d - 2 * L * p)]
  linarith [neg_le_abs (2 * χ * c * q)]

theorem ball_integral_mul_le {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (r : ℝ) :
    ∫ y in Metric.closedBall (0 : Space) r, ‖f y‖ * ‖g y‖ ≤
      Real.sqrt (∫ y in Metric.closedBall (0 : Space) r, ‖f y‖ ^ 2) * (eLpNorm g 2 volume).toReal := by
  have e2 : ENNReal.ofReal 2 = 2 := by norm_num
  have hf2 : MemLp (fun y => ‖f y‖) (ENNReal.ofReal 2)
      ((volume : Measure Space).restrict (Metric.closedBall (0 : Space) r)) := by
    rw [e2]; exact hf.norm.restrict _
  have hg2 : MemLp (fun y => ‖g y‖) (ENNReal.ofReal 2)
      ((volume : Measure Space).restrict (Metric.closedBall (0 : Space) r)) := by
    rw [e2]; exact hg.norm.restrict _
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun y => norm_nonneg (f y)) (Eventually.of_forall fun y => norm_nonneg (g y)) hf2 hg2
  simp only [Real.rpow_two] at h
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  have hD : (eLpNorm g 2 volume).toReal = Real.sqrt (∫ y, ‖g y‖ ^ 2) := by
    rw [← toReal_sq_eq_integral hg.1, Real.sqrt_sq ENNReal.toReal_nonneg]
  rw [hD]
  refine Real.sqrt_le_sqrt (setIntegral_le_integral (hg.integrable_norm_pow two_ne_zero)
    (Eventually.of_forall fun y => by positivity))

theorem test_bound (R : ℝ) (hR : 0 < R) : ∃ M : ℝ, 0 ≤ M ∧ ∀ φ, IsTestField φ → ∀ j : Fin 3,
    ∫ y in Metric.closedBall (0 : Space) R, ‖partialField φ j y‖ ^ 2 ≤
      M * (Real.sqrt (∫ y in Metric.closedBall (0 : Space) (R + 1), ‖φ y‖ ^ 2) *
        (eLpNorm (negSsp φ) 2 volume).toReal +
        ∫ y in Metric.closedBall (0 : Space) (R + 1), ‖φ y‖ ^ 2) := by
  obtain ⟨χ, L, hχ, hχ0, hχ1, hχR, hχout, hL0, hL⟩ := exists_cutoff R hR
  refine ⟨2 + 12 * L ^ 2, by positivity, fun φ hφ j => ?_⟩
  have hφs := hφ.1
  have hΔ := isTestField_negSsp hφ
  have hBm : MeasurableSet (Metric.closedBall (0 : Space) (R + 1)) := measurableSet_closedBall
  have hBc : IsCompact (Metric.closedBall (0 : Space) (R + 1)) := isCompact_closedBall 0 (R + 1)
  have hint : ∀ F : Space → ℝ, Continuous F →
      (∀ y, y ∉ Metric.closedBall (0 : Space) (R + 1) → F y = 0) → Integrable F := fun F hF h0 =>
    hF.integrable_of_hasCompactSupport (HasCompactSupport.intro hBc h0)
  have hintB : ∀ F : Space → ℝ, Continuous F →
      Integrable ((Metric.closedBall (0 : Space) (R + 1)).indicator F) := fun F hF =>
    (hF.continuousOn.integrableOn_compact hBc).integrable_indicator hBm
  set d : Fin 3 → Space → Space := fun i => Freq.Internal.NiceApprox.pd (unitVector i) φ with hd
  have hdc : ∀ i, ContDiff ℝ ∞ (d i) := fun i => Freq.Internal.NiceApprox.contDiff_pd hφs _
  set f : Space → Space := fun z => χ z ^ 2 • φ z with hfdef
  have hf : ContDiff ℝ ∞ f := (hχ.pow 2).smul hφs
  have hcc : ∀ i : Fin 3, Continuous fun y => fderiv ℝ χ y (unitVector i) := fun i =>
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfd : ∀ i : Fin 3, Continuous fun y => fderiv ℝ f y (unitVector i) := fun i =>
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdd : ∀ i : Fin 3, Continuous fun y => fderiv ℝ (d i) y (unitVector i) := fun i =>
    ((hdc i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hf0 : ∀ y, y ∉ Metric.closedBall (0 : Space) (R + 1) → f y = 0 := fun y hy => by
    simp [hfdef, (hχout y hy).1]
  have hfd0 : ∀ i : Fin 3, ∀ y, y ∉ Metric.closedBall (0 : Space) (R + 1) →
      fderiv ℝ f y (unitVector i) = 0 := fun i y hy => by
    rw [hfdef, fderiv_cut_apply hχ hφs, (hχout y hy).1]
    simp
  have hR_eq : ∀ i : Fin 3, ∀ y, inner ℝ (fderiv ℝ f y (unitVector i)) (d i y) =
      2 * χ y * fderiv ℝ χ y (unitVector i) * inner ℝ (φ y) (d i y) + χ y ^ 2 * ‖d i y‖ ^ 2 := by
    intro i y
    rw [hfdef, fderiv_cut_apply hχ hφs, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      show fderiv ℝ φ y (unitVector i) = d i y from rfl, real_inner_self_eq_norm_sq]
  have I1 : ∀ i : Fin 3, Integrable fun y => inner ℝ (fderiv ℝ f y (unitVector i)) (d i y) := fun i =>
    hint _ ((hfd i).inner (hdc i).continuous) fun y hy => by rw [hfd0 i y hy, inner_zero_left]
  have I2 : ∀ i : Fin 3, Integrable fun y => inner ℝ (f y) (fderiv ℝ (d i) y (unitVector i)) := fun i =>
    hint _ (hf.continuous.inner (hdd i)) fun y hy => by rw [hf0 y hy, inner_zero_left]
  have I3 : ∀ i : Fin 3, Integrable fun y => inner ℝ (f y) (d i y) := fun i =>
    hint _ (hf.continuous.inner (hdc i).continuous) fun y hy => by rw [hf0 y hy, inner_zero_left]
  have ibp : ∀ i : Fin 3, ∫ y, inner ℝ (f y) (fderiv ℝ (d i) y (unitVector i)) =
      -∫ y, inner ℝ (fderiv ℝ f y (unitVector i)) (d i y) := fun i =>
    integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume) (B := innerSL ℝ)
      (f := f) (g := d i) (v := unitVector i) (I1 i) (I2 i) (I3 i)
      (fun y _ => hf.differentiable (by simp) y) (fun y _ => (hdc i).differentiable (by simp) y)
  have hQ : ∀ y, ∑ i : Fin 3, inner ℝ (f y) (fderiv ℝ (d i) y (unitVector i)) =
      -(χ y ^ 2 * inner ℝ (φ y) (negSsp φ y)) := fun y => by
    rw [Freq.Internal.NiceApprox.negSsp_eq φ hφs]
    simp only [hfdef, hd, inner_neg_right, inner_sum, real_inner_smul_left]
    rw [mul_neg, neg_neg, Finset.mul_sum]
    rfl
  have hcont_main : Continuous fun y => χ y ^ 2 * inner ℝ (φ y) (negSsp φ y) :=
    (hχ.continuous.pow 2).mul (hφs.continuous.inner hΔ.1.continuous)
  have Imain : Integrable fun y => χ y ^ 2 * inner ℝ (φ y) (negSsp φ y) :=
    hint _ hcont_main fun y hy => by rw [(hχout y hy).1]; ring
  have hS2 : ∫ y, ∑ i : Fin 3, inner ℝ (fderiv ℝ f y (unitVector i)) (d i y) =
      ∫ y, χ y ^ 2 * inner ℝ (φ y) (negSsp φ y) := by
    rw [integral_finsetSum _ (fun i _ => I1 i)]
    have e : ∀ i : Fin 3, ∫ y, inner ℝ (fderiv ℝ f y (unitVector i)) (d i y) =
        -∫ y, inner ℝ (f y) (fderiv ℝ (d i) y (unitVector i)) := fun i => by rw [ibp i, neg_neg]
    rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_neg_distrib,
      ← integral_finsetSum _ (fun i _ => I2 i)]
    rw [integral_congr_ae (Eventually.of_forall hQ), integral_neg, neg_neg]
  set P : Space → ℝ := fun y => ∑ i : Fin 3, χ y ^ 2 * ‖d i y‖ ^ 2 with hP
  set N : Space → ℝ := (Metric.closedBall (0 : Space) (R + 1)).indicator fun y => ‖φ y‖ ^ 2 with hN
  have IP : Integrable P := hint _ (continuous_finsetSum _ fun i _ =>
      (hχ.continuous.pow 2).mul (((hdc i).continuous.norm).pow 2)) fun y hy => by
    simp [hP, (hχout y hy).1]
  have IN : Integrable N := hintB _ ((hφs.continuous.norm).pow 2)
  have hlow : ∀ y, (1 / 2) * P y - 6 * L ^ 2 * N y ≤
      ∑ i : Fin 3, inner ℝ (fderiv ℝ f y (unitVector i)) (d i y) := fun y => by
    have hi : ∀ i : Fin 3, (1 / 2) * (χ y ^ 2 * ‖d i y‖ ^ 2) - 2 * L ^ 2 * N y ≤
        inner ℝ (fderiv ℝ f y (unitVector i)) (d i y) := fun i => by
      rw [hR_eq i y]
      by_cases hy : y ∈ Metric.closedBall (0 : Space) (R + 1)
      · have hNy : N y = ‖φ y‖ ^ 2 := by rw [hN, Set.indicator_of_mem hy]
        have hc : |fderiv ℝ χ y (unitVector i)| ≤ L := by
          rw [← Real.norm_eq_abs]
          refine ((fderiv ℝ χ y).le_opNorm _).trans ?_
          rw [Freq.Internal.NiceApprox.norm_unitVector, mul_one]
          exact hL y
        have := cross_bound (hχ0 y) hc (abs_real_inner_le_norm (φ y) (d i y))
        rw [hNy]
        nlinarith
      · have hNy : N y = 0 := by rw [hN, Set.indicator_of_notMem hy]
        rw [hNy, (hχout y hy).1]
        simp
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hi i
    refine le_trans (le_of_eq ?_) hs
    simp only [hP, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hup : ∀ y, χ y ^ 2 * inner ℝ (φ y) (negSsp φ y) ≤
      (Metric.closedBall (0 : Space) (R + 1)).indicator (fun y => ‖φ y‖ * ‖negSsp φ y‖) y := fun y => by
    by_cases hy : y ∈ Metric.closedBall (0 : Space) (R + 1)
    · rw [Set.indicator_of_mem hy]
      have h1 := hχ1 y
      have h0 := hχ0 y
      have hq := abs_real_inner_le_norm (φ y) (negSsp φ y)
      have hsq : χ y ^ 2 ≤ 1 := by nlinarith
      have habs := le_abs_self (inner ℝ (φ y) (negSsp φ y))
      have hneg := neg_abs_le (inner ℝ (φ y) (negSsp φ y))
      nlinarith [sq_nonneg (χ y)]
    · rw [Set.indicator_of_notMem hy, (hχout y hy).1]
      simp
  have hball : ∀ y, (Metric.closedBall (0 : Space) R).indicator (fun y => ‖d j y‖ ^ 2) y ≤ P y := fun y => by
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · rw [Set.indicator_of_mem hy, hP]
      have e : ‖d j y‖ ^ 2 = χ y ^ 2 * ‖d j y‖ ^ 2 := by rw [hχR y hy]; ring
      rw [e]
      exact Finset.single_le_sum (f := fun i => χ y ^ 2 * ‖d i y‖ ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ j)
    · rw [Set.indicator_of_notMem hy]
      exact Finset.sum_nonneg fun i _ => by positivity
  have hB0m : MeasurableSet (Metric.closedBall (0 : Space) R) := measurableSet_closedBall
  have IB0 : Integrable ((Metric.closedBall (0 : Space) R).indicator fun y => ‖d j y‖ ^ 2) :=
    ((((hdc j).continuous.norm).pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).integrable_indicator hB0m
  have IU : Integrable ((Metric.closedBall (0 : Space) (R + 1)).indicator
      (fun y => ‖φ y‖ * ‖negSsp φ y‖)) := hintB _ (hφs.continuous.norm.mul hΔ.1.continuous.norm)
  have c1 : ∫ y in Metric.closedBall (0 : Space) R, ‖partialField φ j y‖ ^ 2 ≤ ∫ y, P y := by
    rw [← integral_indicator hB0m]
    exact integral_mono IB0 IP hball
  have c2 : ∫ y, ((1 / 2) * P y - 6 * L ^ 2 * N y) ≤ ∫ y, χ y ^ 2 * inner ℝ (φ y) (negSsp φ y) := by
    rw [← hS2]
    exact integral_mono ((IP.const_mul _).sub (IN.const_mul _))
      (integrable_finsetSum _ fun i _ => I1 i) hlow
  have c3 : ∫ y, χ y ^ 2 * inner ℝ (φ y) (negSsp φ y) ≤
      ∫ y in Metric.closedBall (0 : Space) (R + 1), ‖φ y‖ * ‖negSsp φ y‖ := by
    rw [← integral_indicator hBm]
    exact integral_mono Imain IU hup
  have c4 := ball_integral_mul_le (hφs.continuous.memLp_of_hasCompactSupport hφ.2.1)
    (hΔ.1.continuous.memLp_of_hasCompactSupport hΔ.2.1) (R + 1)
  have eN : ∫ y, N y = ∫ y in Metric.closedBall (0 : Space) (R + 1), ‖φ y‖ ^ 2 :=
    integral_indicator hBm
  rw [integral_sub (IP.const_mul _) (IN.const_mul _), integral_const_mul, integral_const_mul, eN] at c2
  have hX := Real.sqrt_nonneg (∫ y in Metric.closedBall (0 : Space) (R + 1), ‖φ y‖ ^ 2)
  have hD : 0 ≤ (eLpNorm (negSsp φ) 2 volume).toReal := ENNReal.toReal_nonneg
  have hX2 : 0 ≤ ∫ y in Metric.closedBall (0 : Space) (R + 1), ‖φ y‖ ^ 2 :=
    setIntegral_nonneg hBm fun y _ => by positivity
  have hXD := mul_nonneg hX hD
  nlinarith [mul_nonneg (sq_nonneg L) hXD, mul_nonneg (sq_nonneg L) hX2]

def ballNorm {p : ℝ≥0∞} (r : ℝ) (f : Lp Space p (volume : Measure Space)) : ℝ :=
  (eLpNorm (f : Space → Space) 2 (volume.restrict (Metric.closedBall (0 : Space) r))).toReal

theorem ballNorm_nonneg {p : ℝ≥0∞} (r : ℝ) (f : Lp Space p (volume : Measure Space)) : 0 ≤ ballNorm r f :=
  ENNReal.toReal_nonneg

theorem ball_eLpNorm_le {p : ℝ≥0∞} (hp : 2 ≤ p) (r : ℝ) (f : Space → Space)
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 2 ((volume : Measure Space).restrict (Metric.closedBall (0 : Space) r)) ≤
      eLpNorm f p (volume : Measure Space) *
        volume (Metric.closedBall (0 : Space) r) ^ (1 / (2 : ℝ≥0∞).toReal - 1 / p.toReal) := by
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp
    (hf.restrict (s := Metric.closedBall (0 : Space) r))).trans ?_
  rw [Measure.restrict_apply_univ]
  have h : eLpNorm f p ((volume : Measure Space).restrict (Metric.closedBall (0 : Space) r)) ≤
      eLpNorm f p (volume : Measure Space) := eLpNorm_mono_measure f Measure.restrict_le_self
  gcongr

theorem ballNorm_sub_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 ≤ p)
    (hq : 0 ≤ 1 / (2 : ℝ≥0∞).toReal - 1 / p.toReal) (r : ℝ)
    (f g : Lp Space p (volume : Measure Space)) :
    ballNorm r f ≤ ballNorm r g + ‖f - g‖ *
      (volume (Metric.closedBall (0 : Space) r) ^ (1 / (2 : ℝ≥0∞).toReal - 1 / p.toReal)).toReal := by
  have hc : volume (Metric.closedBall (0 : Space) r) ^ (1 / (2 : ℝ≥0∞).toReal - 1 / p.toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hq measure_closedBall_lt_top.ne
  have h1 : eLpNorm f 2 (volume.restrict (Metric.closedBall (0 : Space) r)) ≤
      eLpNorm g 2 (volume.restrict (Metric.closedBall (0 : Space) r)) +
        eLpNorm (f - g : Lp Space p (volume : Measure Space)) 2
          (volume.restrict (Metric.closedBall (0 : Space) r)) := by
    have e : (f : Space → Space) =ᵐ[volume.restrict (Metric.closedBall (0 : Space) r)]
        fun y => (g : Space → Space) y + ((f - g : Lp Space p (volume : Measure Space)) : Space → Space) y := by
      refine ae_restrict_of_ae ?_
      filter_upwards [Lp.coeFn_sub f g] with y hy
      rw [hy, Pi.sub_apply]
      abel
    rw [eLpNorm_congr_ae e]
    exact eLpNorm_add_le (Lp.aestronglyMeasurable g).restrict (Lp.aestronglyMeasurable _).restrict
      one_le_two
  have hfin : ∀ h : Lp Space p (volume : Measure Space),
      eLpNorm h 2 (volume.restrict (Metric.closedBall (0 : Space) r)) ≤
        ENNReal.ofReal ‖h‖ * volume (Metric.closedBall (0 : Space) r) ^
          (1 / (2 : ℝ≥0∞).toReal - 1 / p.toReal) := fun h => by
    refine (ball_eLpNorm_le hp r h (Lp.aestronglyMeasurable h)).trans ?_
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top h)]
  have hne : ∀ h : Lp Space p (volume : Measure Space),
      eLpNorm h 2 (volume.restrict (Metric.closedBall (0 : Space) r)) ≠ ⊤ := fun h =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc) (hfin h)
  unfold ballNorm
  calc (eLpNorm f 2 (volume.restrict (Metric.closedBall (0 : Space) r))).toReal
      ≤ (eLpNorm g 2 (volume.restrict (Metric.closedBall (0 : Space) r)) +
        eLpNorm (f - g : Lp Space p (volume : Measure Space)) 2
          (volume.restrict (Metric.closedBall (0 : Space) r))).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hne g, hne _⟩) h1
    _ = (eLpNorm g 2 (volume.restrict (Metric.closedBall (0 : Space) r))).toReal +
        (eLpNorm (f - g : Lp Space p (volume : Measure Space)) 2
          (volume.restrict (Metric.closedBall (0 : Space) r))).toReal :=
        ENNReal.toReal_add (hne g) (hne _)
    _ ≤ _ := by
        refine add_le_add le_rfl ((ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc)
          (hfin _)).trans_eq ?_)
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]

theorem continuous_ballNorm {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 ≤ p)
    (hq : 0 ≤ 1 / (2 : ℝ≥0∞).toReal - 1 / p.toReal) (r : ℝ)
    (T : Freq.X →L[ℝ] Lp Space p (volume : Measure Space)) :
    Continuous fun x => ballNorm r (T x) := by
  set c := (volume (Metric.closedBall (0 : Space) r) ^ (1 / (2 : ℝ≥0∞).toReal - 1 / p.toReal)).toReal
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  refine (LipschitzWith.of_le_add_mul (Real.toNNReal (‖T‖ * c)) fun x y => ?_).continuous
  refine (ballNorm_sub_le hp hq r (T x) (T y)).trans (add_le_add le_rfl ?_)
  rw [← map_sub, dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg (norm_nonneg _) hc0)]
  calc ‖T (x - y)‖ * c ≤ ‖T‖ * ‖x - y‖ * c := mul_le_mul_of_nonneg_right (T.le_opNorm _) hc0
    _ = ‖T‖ * c * ‖x - y‖ := by ring

theorem ballNorm_ne_top {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 ≤ p)
    (hq : 0 ≤ 1 / (2 : ℝ≥0∞).toReal - 1 / p.toReal) (r : ℝ) (f : Lp Space p (volume : Measure Space)) :
    eLpNorm f 2 (volume.restrict (Metric.closedBall (0 : Space) r)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
    (ENNReal.rpow_ne_top_of_nonneg hq
      (measure_closedBall_lt_top (μ := (volume : Measure Space)) (x := 0) (r := r)).ne)) ?_
  exact ball_eLpNorm_le hp r f (Lp.aestronglyMeasurable f)

theorem lintegral_ball_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 ≤ p)
    (hq : 0 ≤ 1 / (2 : ℝ≥0∞).toReal - 1 / p.toReal) (r : ℝ) (f : Lp Space p (volume : Measure Space)) :
    ∫⁻ y in Metric.closedBall (0 : Space) r, ‖(f : Space → Space) y‖ₑ ^ 2 =
      ENNReal.ofReal (ballNorm r f ^ 2) := by
  rw [lintegral_enorm_sq_eq, ballNorm, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (ballNorm_ne_top hp hq r f)]

theorem ennreal_bound {a v K M : ℝ} (hv : 0 ≤ v) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (h : a ^ 2 ≤ M * (v * K + v ^ 2)) :
    ENNReal.ofReal (a ^ 2) ≤ ENNReal.ofReal M *
      (ENNReal.ofReal (v ^ 2) ^ (1 / 2 : ℝ) * ENNReal.ofReal K + ENNReal.ofReal (v ^ 2)) := by
  have e : ENNReal.ofReal (v ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal v := by
    rw [ENNReal.ofReal_pow hv, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [e, ← ENNReal.ofReal_mul hv, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul hM]
  exact ENNReal.ofReal_le_ofReal h

theorem norm_solField_negSsp {φ : Space → Space} (hφ : IsTestField φ) :
    (eLpNorm (negSsp φ) 2 volume).toReal = ‖solField (negSsp φ)‖ := by
  have ht := isTestField_negSsp hφ
  have hm : MemLp (negSsp φ) 2 volume := ht.1.continuous.memLp_of_hasCompactSupport ht.2.1
  rw [← norm_toPhysH, toPhysH_solField_test ht, toLpOrZero, dif_pos hm, Lp.norm_toLp]

theorem test_pair_bound {R M : ℝ}
    (hMb : ∀ φ, IsTestField φ → ∀ j : Fin 3,
      ∫ y in Metric.closedBall (0 : Space) R, ‖partialField φ j y‖ ^ 2 ≤
        M * (Real.sqrt (∫ y in Metric.closedBall (0 : Space) (R + 1), ‖φ y‖ ^ 2) *
          (eLpNorm (negSsp φ) 2 volume).toReal +
          ∫ y in Metric.closedBall (0 : Space) (R + 1), ‖φ y‖ ^ 2))
    {φ : Space → Space} (hφ : IsTestField φ) (j : Fin 3) :
    ballNorm R (partialX j (embedX φ)) ^ 2 ≤
      M * (ballNorm (R + 1) (velocity (embedX φ)) * ‖solField (negSsp φ)‖ +
        ballNorm (R + 1) (velocity (embedX φ)) ^ 2) := by
  have hH := (h1Consistency_holds φ (Internal.TestDense.isH1Field_of_test hφ))
  have hp : ballNorm R (partialX j (embedX φ)) ^ 2 =
      ∫ y in Metric.closedBall (0 : Space) R, ‖partialField φ j y‖ ^ 2 := by
    rw [ballNorm, toReal_sq_eq_integral (Lp.aestronglyMeasurable _).restrict]
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hH.2.2 j] with y hy
    rw [hy]
  have hv2 : ballNorm (R + 1) (velocity (embedX φ)) ^ 2 =
      ∫ y in Metric.closedBall (0 : Space) (R + 1), ‖φ y‖ ^ 2 := by
    rw [ballNorm, toReal_sq_eq_integral (Lp.aestronglyMeasurable _).restrict]
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hH.2.1] with y hy
    rw [hy]
  have hv : ballNorm (R + 1) (velocity (embedX φ)) =
      Real.sqrt (∫ y in Metric.closedBall (0 : Space) (R + 1), ‖φ y‖ ^ 2) := by
    rw [← hv2, Real.sqrt_sq (ballNorm_nonneg _ _)]
  rw [hp, hv2, hv, ← norm_solField_negSsp hφ]
  exact hMb φ hφ j

theorem slice_local_bound_holds (R : ℝ) (hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x k : Freq.X, IsHalfSspOf x k → ∀ j : Fin 3,
      ∫⁻ y in Metric.closedBall (0 : Space) R, ‖(partialX j x : Space → Space) y‖ₑ ^ 2 ≤
        ENNReal.ofReal M * ((∫⁻ y in Metric.closedBall (0 : Space) (R + 1),
          ‖(velocity x : Space → Space) y‖ₑ ^ 2) ^ (1 / 2 : ℝ) * ‖k‖ₑ +
          ∫⁻ y in Metric.closedBall (0 : Space) (R + 1), ‖(velocity x : Space → Space) y‖ₑ ^ 2) := by
  choose M hM hMb using test_bound R hR
  refine ⟨M, hM, fun x k hxk j => ?_⟩
  have ha : Continuous fun x => ballNorm R (partialX j x) :=
    continuous_ballNorm (p := 2) le_rfl (by norm_num) R (partialX j)
  have hv : Continuous fun x => ballNorm (R + 1) (velocity x) :=
    continuous_ballNorm (p := 6) (by norm_num) (by norm_num) (R + 1) velocity
  have hcl : IsClosed {q : Freq.X × Freq.X | ballNorm R (partialX j q.1) ^ 2 ≤
      M * (ballNorm (R + 1) (velocity q.1) * ‖q.2‖ + ballNorm (R + 1) (velocity q.1) ^ 2)} :=
    isClosed_le ((ha.comp continuous_fst).pow 2) (continuous_const.mul
      (((hv.comp continuous_fst).mul continuous_snd.norm).add ((hv.comp continuous_fst).pow 2)))
  have hmem : (x, k) ∈ closure {q : Freq.X × Freq.X |
      ∃ φ, IsTestField φ ∧ q = (embedX φ, solField (negSsp φ))} := by
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨φ, hφ, h1, h2⟩ := halfSsp_test_dense hxk hε
    refine ⟨(embedX φ, solField (negSsp φ)), ⟨φ, hφ, rfl⟩, ?_⟩
    rw [Prod.dist_eq, max_lt_iff, dist_comm x, dist_comm k, dist_eq_norm, dist_eq_norm]
    exact ⟨h1, h2⟩
  have hreal := hcl.closure_subset_iff.2 (by
    rintro q ⟨φ, hφ, rfl⟩
    exact test_pair_bound hMb hφ j) hmem
  rw [lintegral_ball_eq (p := 2) le_rfl (by norm_num) R, lintegral_ball_eq (p := 6) (by norm_num)
    (by norm_num) (R + 1), ← ofReal_norm]
  exact ennreal_bound (ballNorm_nonneg _ _) (norm_nonneg _) hM hreal

end Internal.TimeModulus.SliceBound

end Breakdown.Cert
