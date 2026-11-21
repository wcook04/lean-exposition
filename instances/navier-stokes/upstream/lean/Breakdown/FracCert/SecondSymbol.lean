import Breakdown.FracCert.StFree
import Breakdown.FreqTr.H1Consistency
import Breakdown.FreqTr.BilinCompact
import Breakdown.Weak.GradientFreqTr

open scoped ContDiff ENNReal FourierTransform
open MeasureTheory Real Filter Topology

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace Internal.SecondSymbol

open Freq SchwartzMap LineDeriv

def hatOf (f : Space → Space) : L2C := freqTrR (complexify (toLpOrZero 2 f))

theorem integral_norm_sq_eq (u : L2C) : ∫ ξ, ‖(u : Space → CSpace) ξ‖ ^ 2 = ‖u‖ ^ 2 := by
  have h := integral_re (𝕜 := ℂ) (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) u u)
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) u, MeasureTheory.L2.inner_def, ← h]
  simp only [inner_self_eq_norm_sq (𝕜 := ℂ)]

theorem integral_sq_hat {f : Space → Space} (hf : MemLp f 2 volume) :
    ∫ y, ‖f y‖ ^ 2 = ∫ ξ, ‖(hatOf f : Space → CSpace) ξ‖ ^ 2 := by
  rw [integral_norm_sq_eq]
  have e : ‖hatOf f‖ = ‖complexify (toLpOrZero 2 f)‖ := by
    show ‖freqTrL2 (complexify (toLpOrZero 2 f))‖ = _
    exact freqTrL2.norm_map _
  rw [e, ← integral_norm_sq_eq]
  refine integral_congr_ae ?_
  filter_upwards [Freq.Internal.H1Consistency.complexify_toLp_ae hf] with y hy
  rw [hy, Freq.Internal.BilinCompact.norm_complexifyVec]

theorem cplx_deriv {f f' : Space → Space} (hf : MemLp f 2 volume) (hf' : MemLp f' 2 volume) {k : Fin 3}
    (hw : ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, fderiv ℝ φ y (unitVector k) • f y = -∫ y, φ y • f' y)
    {ψ : Space → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ) :
    ∫ y, fderiv ℝ ψ y (unitVector k) • complexifyVec (f y) = -∫ y, ψ y • complexifyVec (f' y) := by
  have ha : IsTestScalar (fun y => (ψ y).re) :=
    ⟨Complex.reCLM.contDiff.comp hψ, hs.comp_left Complex.zero_re⟩
  have hb : IsTestScalar (fun y => (ψ y).im) :=
    ⟨Complex.imCLM.contDiff.comp hψ, hs.comp_left Complex.zero_im⟩
  have hdψ : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hda : ∀ y v, (fderiv ℝ ψ y v).re = fderiv ℝ (fun y => (ψ y).re) y v := by
    intro y v
    have := (Complex.reCLM.hasFDerivAt.comp y (hdψ y).hasFDerivAt).fderiv
    rw [show (fun y => (ψ y).re) = Complex.reCLM ∘ ψ from rfl, this]
    rfl
  have hdb : ∀ y v, (fderiv ℝ ψ y v).im = fderiv ℝ (fun y => (ψ y).im) y v := by
    intro y v
    have := (Complex.imCLM.hasFDerivAt.comp y (hdψ y).hasFDerivAt).fderiv
    rw [show (fun y => (ψ y).im) = Complex.imCLM ∘ ψ from rfl, this]
    rfl
  have hlf := hf.locallyIntegrable (by norm_num)
  have hlf' := hf'.locallyIntegrable (by norm_num)
  have hint1 : ∀ φ : Space → ℝ, IsTestScalar φ →
      Integrable (fun y => fderiv ℝ φ y (unitVector k) • f y) volume :=
    fun φ hφ => hlf.integrable_smul_left_of_hasCompactSupport
      ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
      (Freq.Internal.NiceApprox.hasCompactSupport_pd hφ.2 (unitVector k))
  have hint2 : ∀ φ : Space → ℝ, IsTestScalar φ → Integrable (fun y => φ y • f' y) volume :=
    fun φ hφ => hlf'.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  have L := WeakProfile.Internal.GradientFreqTr.integral_smul_cv
    (a := fun y => fderiv ℝ ψ y (unitVector k)) (u := f)
    (by simpa only [hda] using hint1 _ ha) (by simpa only [hdb] using hint1 _ hb)
  have R := WeakProfile.Internal.GradientFreqTr.integral_smul_cv (a := ψ) (u := f')
    (hint2 _ ha) (hint2 _ hb)
  rw [L, R]
  simp only [hda, hdb]
  rw [hw _ ha, hw _ hb, map_neg, map_neg, smul_neg, neg_add]

theorem tendsto_cut_val {f' : Space → Space} (hf' : MemLp f' 2 volume) (Θ : 𝓢(Space, ℂ)) :
    Tendsto (fun n : ℕ => ∫ y, WeakProfile.Internal.GradientFreqTr.cutoff Θ ((n : ℝ) + 1) y •
        complexifyVec (f' y)) atTop (𝓝 (∫ y, Θ y • complexifyVec (f' y))) := by
  have hm : MemLp (fun y => complexifyVec (f' y)) 2 volume := complexifyVec.comp_memLp' hf'
  refine tendsto_integral_of_dominated_convergence (fun y => ‖Θ y‖ * ‖complexifyVec (f' y)‖)
    (fun n => ?_) ?_ (fun n => ?_) ?_
  · exact ((WeakProfile.Internal.GradientFreqTr.contDiff_cutoff (Θ.smooth ⊤) _).continuous).aestronglyMeasurable.smul
      hm.aestronglyMeasurable
  · exact (SchwartzMap.memLp Θ 2 volume).norm.integrable_mul hm.norm
  · refine ae_of_all _ fun y => ?_
    rw [norm_smul]
    gcongr
    show ‖Freq.Internal.NiceApprox.stdBump (((n : ℝ) + 1)⁻¹ • y) • Θ y‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ContDiffBump.nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (ContDiffBump.le_one _)
  · refine ae_of_all _ fun y => tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ⌈‖y‖⌉₊] with n hn
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : ‖y‖ ≤ (n : ℝ) + 1 := by
      have := Nat.le_ceil ‖y‖
      have h2 : (⌈‖y‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hb : Freq.Internal.NiceApprox.stdBump (((n : ℝ) + 1)⁻¹ • y) = 1 := by
      apply ContDiffBump.one_of_mem_closedBall
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
      show ((n : ℝ) + 1)⁻¹ * ‖y‖ ≤ 1
      rw [inv_mul_le_iff₀ hR]
      linarith
    show _ = (Freq.Internal.NiceApprox.stdBump (((n : ℝ) + 1)⁻¹ • y) • Θ y) • complexifyVec (f' y)
    rw [hb, one_smul]

theorem rapid_deriv {G : Space → (Space →L[ℝ] Space)} {f' : Space → Space}
    (hm : ∀ i, MemLp (WeakProfile.gradComponent G i) 2 volume) (hf' : MemLp f' 2 volume) {i k : Fin 3}
    (hw : ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, fderiv ℝ φ y (unitVector k) • G y (unitVector i) = -∫ y, φ y • f' y)
    (Θ : 𝓢(Space, ℂ)) :
    ∫ y, fderiv ℝ (Θ : Space → ℂ) y (unitVector k) • complexifyVec (G y (unitVector i)) =
      -∫ y, Θ y • complexifyVec (f' y) := by
  have hΘ : ContDiff ℝ ∞ (Θ : Space → ℂ) := Θ.smooth ⊤
  refine tendsto_nhds_unique (WeakProfile.Internal.GradientFreqTr.tendsto_cut hm Θ i k)
    ((tendsto_cut_val hf' Θ).neg.congr fun n => ?_)
  exact (cplx_deriv (f := WeakProfile.gradComponent G i) (hm i) hf' hw
    (WeakProfile.Internal.GradientFreqTr.contDiff_cutoff hΘ _)
    (WeakProfile.Internal.GradientFreqTr.hasCompactSupport_cutoff _ (by positivity))).symm


theorem hat_deriv {G : Space → (Space →L[ℝ] Space)} {f' : Space → Space}
    (hm : ∀ i, MemLp (WeakProfile.gradComponent G i) 2 volume) (hf' : MemLp f' 2 volume) {i k : Fin 3}
    (hw : ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, fderiv ℝ φ y (unitVector k) • G y (unitVector i) = -∫ y, φ y • f' y) :
    (hatOf f' : Space → CSpace) =ᵐ[volume] fun ξ => ((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) •
      (WeakProfile.Internal.GradientFreqTr.hatComp G i : Space → CSpace) ξ := by
  set U := complexify (toLpOrZero 2 (WeakProfile.gradComponent G i)) with hU
  set V := complexify (toLpOrZero 2 f') with hV
  have hTD : ∂_{unitVector k} (Lp.toTemperedDistribution U) = Lp.toTemperedDistribution V := by
    ext1 g
    rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
      Lp.toTemperedDistribution_apply]
    have e1 : ∫ x, (-∂_{unitVector k} g) x • (U : Space → CSpace) x =
        -∫ x, fderiv ℝ (g : Space → ℂ) x (unitVector k) • complexifyVec (G x (unitVector i)) := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [Freq.Internal.H1Consistency.complexify_toLp_ae (hm i)] with x hx
      rw [hx, neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, neg_smul]
      rfl
    have e2 : ∫ x, g x • (V : Space → CSpace) x = ∫ x, g x • complexifyVec (f' x) := by
      refine integral_congr_ae ?_
      filter_upwards [Freq.Internal.H1Consistency.complexify_toLp_ae hf'] with x hx
      rw [hx]
    rw [e1, e2, rapid_deriv hm hf' hw g, neg_neg]
  have hD := congrArg (fun T => 𝓕 T) hTD
  rw [TemperedDistribution.fourier_lineDerivOp_eq, Lp.fourier_toTemperedDistribution_eq,
    Lp.fourier_toTemperedDistribution_eq] at hD
  have hc : Continuous (fun ξ : Space => (2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) := by fun_prop
  have hloc : LocallyIntegrable (fun ξ => ((𝓕 V : L2C) : Space → CSpace) ξ -
      ((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) • ((𝓕 U : L2C) : Space → CSpace) ξ) volume :=
    ((Lp.memLp _).locallyIntegrable (by norm_num)).sub
      (((Lp.memLp _).locallyIntegrable (by norm_num)).continuous_smul hc)
  have hz := Freq.Internal.H1Consistency.ae_zero_of_rapid hloc (fun g => ?_)
  · filter_upwards [hz] with ξ hξ
    exact sub_eq_zero.1 hξ
  have hg := congrArg (fun T => T g) hD
  simp only [smul_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply] at hg
  rw [SchwartzMap.smulLeftCLM_apply (by fun_prop)] at hg
  have hin : ∀ x : Space, inner ℝ x (unitVector k) = x k := fun x => by
    rw [unitVector, EuclideanSpace.inner_single_right]
    simp
  simp only [hin] at hg
  have hi1 : Integrable (fun x => g x • ((𝓕 V : L2C) : Space → CSpace) x) :=
    Freq.Internal.H1Consistency.integrable_rapid_smul g (Lp.memLp _)
  have hi2 : Integrable (fun x => (((x k : ℝ) : ℂ) • g x) • ((𝓕 U : L2C) : Space → CSpace) x) := by
    have := Freq.Internal.H1Consistency.integrable_rapid_smul
      (SchwartzMap.smulLeftCLM ℂ (fun x : Space => ((inner ℝ x (unitVector k) : ℝ) : ℂ)) g)
      (Lp.memLp (𝓕 U : L2C))
    rw [SchwartzMap.smulLeftCLM_apply (by fun_prop)] at this
    simpa only [hin] using this
  have hpt : ∀ x, g x • (((𝓕 V : L2C) : Space → CSpace) x -
      (2 * π * Complex.I * ((x k : ℝ) : ℂ)) • ((𝓕 U : L2C) : Space → CSpace) x) =
      g x • ((𝓕 V : L2C) : Space → CSpace) x -
        (2 * π * Complex.I) • ((((x k : ℝ) : ℂ) • g x) • ((𝓕 U : L2C) : Space → CSpace) x) := fun x => by
    simp only [smul_sub, smul_smul, smul_eq_mul]
    congr 2
    ring
  have hi3 : Integrable (fun x => (2 * π * Complex.I) •
      ((((x k : ℝ) : ℂ) • g x) • ((𝓕 U : L2C) : Space → CSpace) x)) := by
    convert hi2.smul (2 * π * Complex.I) using 1 <;> rfl
  simp_rw [hpt]
  rw [integral_sub hi1 hi3, integral_smul, hg, sub_self]

theorem memLp_comp {G : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (h2 : Integrable (fun y => entrySq (G y))) (i : Fin 3) :
    MemLp (WeakProfile.gradComponent G i) 2 volume := by
  have hm : AEStronglyMeasurable (WeakProfile.gradComponent G i) volume :=
    (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable hG
  refine (memLp_two_iff_integrable_sq_norm hm).2 (h2.mono' (hm.norm.pow 2) (ae_of_all _ fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact Finset.single_le_sum (f := fun j => ‖G y (unitVector j)‖ ^ 2) (fun j _ => by positivity)
    (Finset.mem_univ i)

theorem memLp_second {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : AEStronglyMeasurable H volume)
    (h2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2))
    (i j : Fin 3) : MemLp (fun y => H y (unitVector i) (unitVector j)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => H y (unitVector i) (unitVector j)) volume :=
    ((ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp
      (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector i)).continuous).comp_aestronglyMeasurable hH
  refine (memLp_two_iff_integrable_sq_norm hm).2 (h2.mono' (hm.norm.pow 2) (ae_of_all _ fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖H y (unitVector i) (unitVector j)‖ ^ 2
      ≤ ∑ j' : Fin 3, ‖H y (unitVector i) (unitVector j')‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖H y (unitVector i) (unitVector j')‖ ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, ‖H y (unitVector i') (unitVector j')‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, ‖H y (unitVector i') (unitVector j')‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem norm_le_sum (A : Space →L[ℝ] Space) : ‖A‖ ≤ ∑ i : Fin 3, ‖A (unitVector i)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun x => ?_
  have hx : ∑ i : Fin 3, x i • unitVector i = x := by
    simpa [unitVector] using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  calc ‖A x‖ = ‖∑ i : Fin 3, x i • A (unitVector i)‖ := by
        conv_lhs => rw [← hx]
        rw [map_sum]
        simp only [map_smul]
    _ ≤ ∑ i : Fin 3, ‖x i • A (unitVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖x‖ * ‖A (unitVector i)‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul]
        gcongr
        exact PiLp.norm_apply_le x i
    _ = (∑ i : Fin 3, ‖A (unitVector i)‖) * ‖x‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem hat_negSum {f : Fin 3 → Space → Space} (hf : ∀ k, MemLp (f k) 2 volume) :
    (hatOf (fun y => -∑ k, f k y) : Space → CSpace) =ᵐ[volume]
      fun ξ => -∑ k, (hatOf (f k) : Space → CSpace) ξ := by
  have hs : MemLp (fun y => -∑ k, f k y) 2 volume := (memLp_finsetSum _ fun k _ => hf k).neg
  have hL : toLpOrZero 2 (fun y => -∑ k, f k y) = -∑ k, toLpOrZero 2 (f k) := by
    apply Lp.ext
    filter_upwards [Freq.Internal.H1Consistency.toLpOrZero_ae hs,
      Lp.coeFn_neg (∑ k, toLpOrZero 2 (f k)),
      Lp.coeFn_finsetSum Finset.univ (fun k => toLpOrZero 2 (f k)),
      ae_all_iff.2 fun k => Freq.Internal.H1Consistency.toLpOrZero_ae (hf k)] with y h1 h2 h3 h4
    rw [h1, h2, Pi.neg_apply, h3, Finset.sum_apply]
    simp only [h4]
  have hH : hatOf (fun y => -∑ k, f k y) = -∑ k, hatOf (f k) := by
    simp only [hatOf, hL, map_neg, map_sum]
  rw [hH]
  filter_upwards [Lp.coeFn_neg (∑ k, hatOf (f k)),
    Lp.coeFn_finsetSum Finset.univ (fun k => hatOf (f k))] with ξ h1 h2
  rw [h1, Pi.neg_apply, h2, Finset.sum_apply]

theorem freqPow_two (ξ : Space) : freqPow 2 ξ = (2 * π) ^ 2 * ‖ξ‖ ^ 2 := by
  rw [freqPow, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

theorem norm_coef_smul (t : ℝ) (z : CSpace) :
    ‖((2 * π * Complex.I) * ((t : ℝ) : ℂ)) • z‖ ^ 2 = (2 * π) ^ 2 * t ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_smul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos pi_pos]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, show (2 * π * 1 * |t| * ‖z‖) ^ 2 = (2 * π) ^ 2 * |t| ^ 2 * ‖z‖ ^ 2 by ring, sq_abs]

theorem algebra_id (ξ : Space) (hξ : ξ ≠ 0) (a : Fin 3 → CSpace) (s : CSpace)
    (hc : ∀ j k : Fin 3, (ξ k : ℝ) • a j = (ξ j : ℝ) • a k)
    (hs : s = -∑ k : Fin 3, ((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) • a k) :
    ‖s‖ ^ 2 / freqPow 2 ξ = ∑ j, ‖a j‖ ^ 2 ∧
      ∑ k : Fin 3, ∑ i : Fin 3, ‖((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) • a i‖ ^ 2 = ‖s‖ ^ 2 := by
  have hn : ‖ξ‖ ^ 2 = ∑ k, (ξ k) ^ 2 := Freq.Internal.H1Consistency.norm_sq_eq ξ
  have hpos : 0 < ‖ξ‖ ^ 2 := by positivity
  have key : ∀ j, (ξ j : ℝ) • s = -(((2 * π * Complex.I) * ((‖ξ‖ ^ 2 : ℝ) : ℂ)) • a j) := by
    intro j
    rw [hs, smul_neg, Finset.smul_sum]
    congr 1
    have : ∀ k, (ξ j : ℝ) • (((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) • a k) =
        ((2 * π * Complex.I) * (((ξ k) ^ 2 : ℝ) : ℂ)) • a j := by
      intro k
      rw [smul_comm, hc k j, ← Complex.coe_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [Finset.sum_congr rfl fun k _ => this k, ← Finset.sum_smul, hn]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  have hsq : ∀ j, (ξ j) ^ 2 * ‖s‖ ^ 2 = (2 * π) ^ 2 * (‖ξ‖ ^ 2) ^ 2 * ‖a j‖ ^ 2 := by
    intro j
    have h := congrArg (fun w : CSpace => ‖w‖ ^ 2) (key j)
    simp only [norm_neg] at h
    rw [norm_coef_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
    exact h
  have hsum : ‖ξ‖ ^ 2 * ‖s‖ ^ 2 = (2 * π) ^ 2 * (‖ξ‖ ^ 2) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
    calc ‖ξ‖ ^ 2 * ‖s‖ ^ 2 = ∑ j, (ξ j) ^ 2 * ‖s‖ ^ 2 := by rw [hn, Finset.sum_mul]
      _ = ∑ j, (2 * π) ^ 2 * (‖ξ‖ ^ 2) ^ 2 * ‖a j‖ ^ 2 := Finset.sum_congr rfl fun j _ => hsq j
      _ = _ := by rw [Finset.mul_sum]
  have hs2 : ‖s‖ ^ 2 = (2 * π) ^ 2 * ‖ξ‖ ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
    exact mul_left_cancel₀ hpos.ne' (by rw [hsum]; ring)
  refine ⟨?_, ?_⟩
  · rw [freqPow_two, hs2]
    field_simp
  · simp only [norm_coef_smul]
    rw [hs2, hn]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]

end Internal.SecondSymbol

open Internal.SecondSymbol in
theorem secondSymbolEnergy : SecondSymbolEnergyStatement := by
  intro m v G H hv
  have hmG : ∀ i, MemLp (WeakProfile.gradComponent G i) 2 volume :=
    fun i => memLp_comp hv.measurable_gradient hv.gradient_two i
  have hmH : ∀ i j, MemLp (fun y => H y (unitVector i) (unitVector j)) 2 volume :=
    fun i j => memLp_second hv.measurable_second hv.second_two i j
  have hloc : LocallyIntegrable G volume := by
    have hs : LocallyIntegrable (fun y => ∑ i : Fin 3, ‖G y (unitVector i)‖) volume :=
      locallyIntegrable_finsetSum _ fun i _ => (hmG i).norm.locallyIntegrable (by norm_num)
    refine hs.mono hv.measurable_gradient (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    exact (norm_le_sum (G y)).trans (le_abs_self _)
  have hwg : IsWeakGradient v G :=
    ⟨hv.velocity_six.locallyIntegrable (by norm_num), hloc, fun φ hφ i => by
      rw [hv.weak_gradient φ hφ i, neg_neg]⟩
  have hA : ∀ k i, (hatOf (fun y => H y (unitVector k) (unitVector i)) : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => ((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) •
        (WeakProfile.Internal.GradientFreqTr.hatComp G i : Space → Freq.CSpace) ξ :=
    fun k i => hat_deriv hmG (hmH k i) (fun φ hφ => hv.weak_second φ hφ i k)
  have hB : ∀ j k, ∀ᵐ ξ ∂volume,
      (ξ k : ℝ) • (WeakProfile.Internal.GradientFreqTr.hatComp G j : Freq.L2C) ξ =
        (ξ j : ℝ) • (WeakProfile.Internal.GradientFreqTr.hatComp G k : Freq.L2C) ξ :=
    fun j k => WeakProfile.Internal.GradientFreqTr.compat hwg hmG j k
  have hS : (secondSymbol H : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => -∑ k, (hatOf (fun y => H y (unitVector k) (unitVector k)) : Space → Freq.CSpace) ξ :=
    hat_negSum (f := fun k y => H y (unitVector k) (unitVector k)) (fun k => hmH k k)
  have hpt : ∀ᵐ ξ ∂volume,
      ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 / freqPow 2 ξ =
        ∑ j, ‖(WeakProfile.Internal.GradientFreqTr.hatComp G j : Space → Freq.CSpace) ξ‖ ^ 2 ∧
      ∑ k : Fin 3, ∑ i : Fin 3,
          ‖(hatOf (fun y => H y (unitVector k) (unitVector i)) : Space → Freq.CSpace) ξ‖ ^ 2 =
        ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 := by
    filter_upwards [hS, ae_all_iff.2 fun k => ae_all_iff.2 fun i => hA k i,
      ae_all_iff.2 fun j => ae_all_iff.2 fun k => hB j k, Freq.Internal.H1Consistency.ae_ne_zero]
      with ξ hs ha hb hξ
    have hs' : (secondSymbol H : Space → Freq.CSpace) ξ = -∑ k : Fin 3,
        ((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) •
          (WeakProfile.Internal.GradientFreqTr.hatComp G k : Space → Freq.CSpace) ξ := by
      rw [hs]
      simp only [ha]
    obtain ⟨h1, h2⟩ := algebra_id ξ hξ
      (fun j => (WeakProfile.Internal.GradientFreqTr.hatComp G j : Space → Freq.CSpace) ξ) _ hb hs'
    refine ⟨h1, ?_⟩
    simp only [ha]
    exact h2
  have hiG : ∀ j, Integrable (fun ξ =>
      ‖(WeakProfile.Internal.GradientFreqTr.hatComp G j : Space → Freq.CSpace) ξ‖ ^ 2) volume :=
    fun j => (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _)
  have hiH : ∀ k i, Integrable (fun ξ =>
      ‖(hatOf (fun y => H y (unitVector k) (unitVector i)) : Space → Freq.CSpace) ξ‖ ^ 2) volume :=
    fun k i => (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _)
  have hphysG : ∀ j, Integrable (fun y => ‖G y (unitVector j)‖ ^ 2) volume :=
    fun j => (memLp_two_iff_integrable_sq_norm (hmG j).1).1 (hmG j)
  have hphysH : ∀ k i, Integrable (fun y => ‖H y (unitVector k) (unitVector i)‖ ^ 2) volume :=
    fun k i => (memLp_two_iff_integrable_sq_norm (hmH k i).1).1 (hmH k i)
  have hsumG := integrable_finsetSum Finset.univ fun j _ => hiG j
  refine ⟨hsumG.congr (hpt.mono fun ξ h => h.1.symm), ?_, ?_, ?_⟩
  · calc ∫ y, entrySq (G y) = ∑ j, ∫ y, ‖G y (unitVector j)‖ ^ 2 := by
          unfold entrySq
          exact integral_finsetSum _ fun j _ => hphysG j
      _ = ∑ j, ∫ ξ, ‖(WeakProfile.Internal.GradientFreqTr.hatComp G j : Space → Freq.CSpace) ξ‖ ^ 2 :=
          Finset.sum_congr rfl fun j _ => integral_sq_hat (hmG j)
      _ = ∫ ξ, ∑ j, ‖(WeakProfile.Internal.GradientFreqTr.hatComp G j : Space → Freq.CSpace) ξ‖ ^ 2 :=
          (integral_finsetSum _ fun j _ => hiG j).symm
      _ = _ := integral_congr_ae (hpt.mono fun ξ h => h.1.symm)
  · calc ∫ y, fullSecondSq (H y) = ∑ k : Fin 3, ∑ i : Fin 3, ∫ y, ‖H y (unitVector k) (unitVector i)‖ ^ 2 := by
          unfold fullSecondSq
          rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ => hphysH k i]
          exact Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun i _ => hphysH k i
      _ = ∑ k : Fin 3, ∑ i : Fin 3,
          ∫ ξ, ‖(hatOf (fun y => H y (unitVector k) (unitVector i)) : Space → Freq.CSpace) ξ‖ ^ 2 :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => integral_sq_hat (hmH k i)
      _ = ∫ ξ, ∑ k : Fin 3, ∑ i : Fin 3,
          ‖(hatOf (fun y => H y (unitVector k) (unitVector i)) : Space → Freq.CSpace) ξ‖ ^ 2 := by
          rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ => hiH k i]
          exact Finset.sum_congr rfl fun k _ => (integral_finsetSum _ fun i _ => hiH k i).symm
      _ = _ := integral_congr_ae (hpt.mono fun ξ h => h.2)
  · have hmS : MemLp (negSecondTrace H) 2 volume := (memLp_finsetSum _ fun k _ => hmH k k).neg
    calc ∫ y, ‖secondTrace (H y)‖ ^ 2 = ∫ y, ‖negSecondTrace H y‖ ^ 2 := by
          simp only [negSecondTrace, norm_neg]
      _ = _ := integral_sq_hat hmS

end SteadyCert

end Breakdown
