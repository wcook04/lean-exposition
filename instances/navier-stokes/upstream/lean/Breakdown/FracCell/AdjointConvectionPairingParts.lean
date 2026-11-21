import Breakdown.FracCell.ReductionAdjointDefs
import Breakdown.FreqTr.H1Consistency
import Breakdown.FreqTr.VelocityInjective
import Breakdown.Uniqueness.CutoffBounds

open MeasureTheory
open scoped ContDiff Convolution FourierTransform

noncomputable section

namespace Breakdown

namespace FracInternal

namespace ConvectionPairing

open SteadyCert SchwartzMap LineDeriv

theorem test_complex {f F : Space → Space} (j : Fin 3) (hf : LocallyIntegrable f volume)
    (hF : LocallyIntegrable F volume)
    (hd : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, fderiv ℝ φ y (unitVector j) • f y = -∫ y, φ y • F y)
    {ψ : Space → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, fderiv ℝ ψ x (unitVector j) • Freq.complexifyVec (f x) = -∫ x, ψ x • Freq.complexifyVec (F x) := by
  have hr : IsTestScalar (fun x => (ψ x).re) :=
    ⟨Complex.reCLM.contDiff.comp hψ, hψc.comp_left Complex.zero_re⟩
  have hi : IsTestScalar (fun x => (ψ x).im) :=
    ⟨Complex.imCLM.contDiff.comp hψ, hψc.comp_left Complex.zero_im⟩
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hdr : ∀ x, fderiv ℝ (fun x => (ψ x).re) x (unitVector j) = (fderiv ℝ ψ x (unitVector j)).re := by
    intro x
    have h : HasFDerivAt (fun x => (ψ x).re) (Complex.reCLM.comp (fderiv ℝ ψ x)) x :=
      Complex.reCLM.hasFDerivAt.comp x (hψd x).hasFDerivAt
    rw [h.fderiv]
    rfl
  have hdi : ∀ x, fderiv ℝ (fun x => (ψ x).im) x (unitVector j) = (fderiv ℝ ψ x (unitVector j)).im := by
    intro x
    have h : HasFDerivAt (fun x => (ψ x).im) (Complex.imCLM.comp (fderiv ℝ ψ x)) x :=
      Complex.imCLM.hasFDerivAt.comp x (hψd x).hasFDerivAt
    rw [h.fderiv]
    rfl
  have dec : ∀ (c : ℂ) (u : Space), c • Freq.complexifyVec u =
      Freq.complexifyVec (c.re • u) + Complex.I • Freq.complexifyVec (c.im • u) := by
    intro c u
    ext i
    apply Complex.ext <;> simp [Freq.complexifyVec]
  have cd : ∀ φ : Space → ℝ, IsTestScalar φ → Continuous (fun x => fderiv ℝ φ x (unitVector j)) := fun φ h =>
    (h.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have I1 := hf.integrable_smul_left_of_hasCompactSupport (cd _ hr) (hr.2.fderiv_apply (𝕜 := ℝ) (unitVector j))
  have I2 := hf.integrable_smul_left_of_hasCompactSupport (cd _ hi) (hi.2.fderiv_apply (𝕜 := ℝ) (unitVector j))
  have I3 := hF.integrable_smul_left_of_hasCompactSupport hr.1.continuous hr.2
  have I4 := hF.integrable_smul_left_of_hasCompactSupport hi.1.continuous hi.2
  have e1 : ∫ x, fderiv ℝ ψ x (unitVector j) • Freq.complexifyVec (f x) =
      Freq.complexifyVec (∫ x, fderiv ℝ (fun x => (ψ x).re) x (unitVector j) • f x) +
        Complex.I • Freq.complexifyVec (∫ x, fderiv ℝ (fun x => (ψ x).im) x (unitVector j) • f x) := by
    have J2 : Integrable (fun x => Complex.I •
        Freq.complexifyVec (fderiv ℝ (fun x => (ψ x).im) x (unitVector j) • f x)) volume :=
      (Freq.complexifyVec.integrable_comp I2).smul Complex.I
    rw [← Freq.complexifyVec.integral_comp_comm I1, ← Freq.complexifyVec.integral_comp_comm I2,
      ← integral_smul, ← integral_add (Freq.complexifyVec.integrable_comp I1) J2]
    congr 1
    funext x
    rw [dec, hdr, hdi]
  have e2 : ∫ x, ψ x • Freq.complexifyVec (F x) =
      Freq.complexifyVec (∫ x, (ψ x).re • F x) + Complex.I • Freq.complexifyVec (∫ x, (ψ x).im • F x) := by
    have J4 : Integrable (fun x => Complex.I • Freq.complexifyVec ((ψ x).im • F x)) volume :=
      (Freq.complexifyVec.integrable_comp I4).smul Complex.I
    rw [← Freq.complexifyVec.integral_comp_comm I3, ← Freq.complexifyVec.integral_comp_comm I4,
      ← integral_smul, ← integral_add (Freq.complexifyVec.integrable_comp I3) J4]
    congr 1
    funext x
    rw [dec]
  rw [e1, e2, hd _ hr, hd _ hi, map_neg, map_neg, smul_neg, neg_add]

theorem dir_rapid {f F : Space → Space} (j : Fin 3) (hf : MemLp f 2 volume) (hF : MemLp F 2 volume)
    (hd : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, fderiv ℝ φ y (unitVector j) • f y = -∫ y, φ y • F y)
    (g : 𝓢(Space, ℂ)) :
    ∫ x, (-∂_{unitVector j} g) x • Freq.complexifyVec (f x) = ∫ x, g x • Freq.complexifyVec (F x) := by
  obtain ⟨c, hc⟩ := norm_fderiv_radialCutoff_le
  have hr : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hfc := Freq.Internal.H1Consistency.memLp_complexify hf
  have hFc := Freq.Internal.H1Consistency.memLp_complexify hF
  have hgd : ∀ x, (∂_{unitVector j} g) x = fderiv ℝ g x (unitVector j) := fun x =>
    SchwartzMap.lineDerivOp_apply_eq_fderiv _ g x
  have hgs : ContDiff ℝ ∞ (⇑g) := g.smooth ⊤
  have hχs : ∀ n : ℕ, ContDiff ℝ ∞ (fun x => ((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ)) := fun n =>
    Complex.ofRealCLM.contDiff.comp (contDiff_radialCutoff (hr n))
  have hψs : ∀ n : ℕ, ContDiff ℝ ∞ (fun x => ((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ) * g x) := fun n =>
    (hχs n).mul hgs
  have hψc : ∀ n : ℕ, HasCompactSupport (fun x => ((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ) * g x) := fun n =>
    ((hasCompactSupport_radialCutoff (hr n)).comp_left Complex.ofReal_zero).mul_right
  have hder : ∀ (n : ℕ) x, fderiv ℝ (fun x => ((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ) * g x) x (unitVector j) =
      ((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ) * (∂_{unitVector j} g) x +
        ((fderiv ℝ (radialCutoff ((n : ℝ) + 1)) x (unitVector j) : ℝ) : ℂ) * g x := by
    intro n x
    have h1 : HasFDerivAt (fun x => ((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (fderiv ℝ (radialCutoff ((n : ℝ) + 1)) x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x
        (((contDiff_radialCutoff (hr n)).differentiable (by simp)) x).hasFDerivAt
    have h2 := h1.mul ((hgs.differentiable (by simp)) x).hasFDerivAt
    rw [show (fun x => ((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ) * g x) =
      (fun x => ((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ)) * ⇑g from rfl, h2.fderiv, hgd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply, smul_eq_mul]
    ring
  have scale : ∀ {a s : Space → ℂ} {b : Space → Freq.CSpace} (M : ℝ), Integrable (fun x => a x • b x) volume →
      Continuous a → Continuous s → AEStronglyMeasurable b volume → (∀ x, ‖s x‖ ≤ M) →
      Integrable (fun x => (s x * a x) • b x) volume := by
    intro a s b M hab ha hs hb hM
    refine (hab.norm.const_mul M).mono' ((hs.mul ha).aestronglyMeasurable.smul hb) (ae_of_all _ fun x => ?_)
    rw [norm_smul, norm_mul, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_right (hM x) (by positivity)
  have ig := Freq.Internal.H1Consistency.integrable_rapid_smul (∂_{unitVector j} g) hfc
  have ig2 := Freq.Internal.H1Consistency.integrable_rapid_smul g hfc
  have ig3 := Freq.Internal.H1Consistency.integrable_rapid_smul g hFc
  have cχ : ∀ n : ℕ, Continuous (fun x => ((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ)) := fun n => (hχs n).continuous
  have cdχ : ∀ n : ℕ, Continuous (fun x => ((fderiv ℝ (radialCutoff ((n : ℝ) + 1)) x (unitVector j) : ℝ) : ℂ)) :=
    fun n => Complex.continuous_ofReal.comp
      (((contDiff_radialCutoff (hr n)).continuous_fderiv (by simp)).clm_apply continuous_const)
  have bχ : ∀ (n : ℕ) x, ‖((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ)‖ ≤ 1 := fun n x => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (radialCutoff_nonneg _ _)]
    exact radialCutoff_le_one _ _
  have bdχ : ∀ (n : ℕ) x, ‖((fderiv ℝ (radialCutoff ((n : ℝ) + 1)) x (unitVector j) : ℝ) : ℂ)‖ ≤
      c / ((n : ℝ) + 1) := fun n x => by
    rw [Complex.norm_real]
    refine le_trans ?_ (hc _ (hr n) x)
    have := (fderiv ℝ (radialCutoff ((n : ℝ) + 1)) x).le_opNorm (unitVector j)
    simpa [unitVector] using this
  have hc0 : 0 ≤ c := by
    have := (norm_nonneg _).trans (hc 1 one_pos 0)
    simpa using this
  have bdχ' : ∀ (n : ℕ) x, ‖((fderiv ℝ (radialCutoff ((n : ℝ) + 1)) x (unitVector j) : ℝ) : ℂ)‖ ≤ c := fun n x =>
    (bdχ n x).trans (div_le_self hc0 (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
  have cg : Continuous (fun x => (∂_{unitVector j} g) x) := (∂_{unitVector j} g).continuous
  have K1 : ∀ n : ℕ, Integrable (fun x => (((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ) * (∂_{unitVector j} g) x) •
      Freq.complexifyVec (f x)) volume := fun n => scale 1 ig cg (cχ n) hfc.1 (bχ n)
  have K2 : ∀ n : ℕ, Integrable (fun x => (((fderiv ℝ (radialCutoff ((n : ℝ) + 1)) x (unitVector j) : ℝ) : ℂ) *
      g x) • Freq.complexifyVec (f x)) volume := fun n => scale c ig2 g.continuous (cdχ n) hfc.1 (bdχ' n)
  have key : ∀ n : ℕ, (∫ x, (((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ) * (∂_{unitVector j} g) x) •
        Freq.complexifyVec (f x)) +
      ∫ x, (((fderiv ℝ (radialCutoff ((n : ℝ) + 1)) x (unitVector j) : ℝ) : ℂ) * g x) • Freq.complexifyVec (f x) =
      -∫ x, (((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ) * g x) • Freq.complexifyVec (F x) := by
    intro n
    have h := test_complex j (hf.locallyIntegrable (by norm_num)) (hF.locallyIntegrable (by norm_num)) hd
      (hψs n) (hψc n)
    simp only [hder n, add_smul] at h
    rw [integral_add (K1 n) (K2 n)] at h
    exact h
  have ev : ∀ x, ∀ᶠ n : ℕ in Filter.atTop, radialCutoff ((n : ℝ) + 1) x = 1 := by
    intro x
    filter_upwards [Filter.eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
    apply radialCutoff_eq_one (hr n)
    have h1 := Nat.le_ceil ‖x‖
    have h2 : (⌈‖x‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have limA : Filter.Tendsto (fun n : ℕ => ∫ x, (((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ) *
      (∂_{unitVector j} g) x) • Freq.complexifyVec (f x)) Filter.atTop
      (nhds (∫ x, (∂_{unitVector j} g) x • Freq.complexifyVec (f x))) := by
    refine tendsto_integral_of_dominated_convergence _
      (fun n => (K1 n).aestronglyMeasurable) ig.norm (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [norm_smul, norm_mul, norm_smul, mul_assoc]
      exact (mul_le_of_le_one_left (by positivity) (bχ n x))
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [ev x] with n hn
      rw [hn]
      simp
  have limC : Filter.Tendsto (fun n : ℕ => ∫ x, (((radialCutoff ((n : ℝ) + 1) x : ℝ) : ℂ) * g x) •
      Freq.complexifyVec (F x)) Filter.atTop (nhds (∫ x, g x • Freq.complexifyVec (F x))) := by
    refine tendsto_integral_of_dominated_convergence _
      (fun n => (scale 1 ig3 g.continuous (cχ n) hFc.1 (bχ n)).aestronglyMeasurable) ig3.norm
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [norm_smul, norm_mul, norm_smul, mul_assoc]
      exact (mul_le_of_le_one_left (by positivity) (bχ n x))
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [ev x] with n hn
      rw [hn]
      simp
  have limB : Filter.Tendsto (fun n : ℕ => ∫ x, (((fderiv ℝ (radialCutoff ((n : ℝ) + 1)) x (unitVector j) : ℝ) : ℂ) *
      g x) • Freq.complexifyVec (f x)) Filter.atTop (nhds 0) := by
    have h0 : (0 : Freq.CSpace) = ∫ _x : Space, (0 : Freq.CSpace) := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (fun x => c * ‖g x • Freq.complexifyVec (f x)‖)
      (fun n => (K2 n).aestronglyMeasurable) (ig2.norm.const_mul c) (fun n => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => ?_)
    · rw [norm_smul, norm_mul, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_right (bdχ' n x) (by positivity)
    · have hlim : Filter.Tendsto (fun n : ℕ => c * (1 / ((n : ℝ) + 1)) * ‖g x • Freq.complexifyVec (f x)‖)
          Filter.atTop (nhds 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c).mul_const ‖g x • Freq.complexifyVec (f x)‖
        simpa using this
      refine squeeze_zero_norm (fun n => ?_) hlim
      rw [norm_smul, norm_mul, norm_smul, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [mul_one_div]
      exact mul_le_mul_of_nonneg_right (bdχ n x) (norm_nonneg _)
  have lim1 := Filter.Tendsto.add limA limB
  simp only [key, add_zero] at lim1
  have e := tendsto_nhds_unique lim1 limC.neg
  have hneg : ∀ x, (-∂_{unitVector j} g) x • Freq.complexifyVec (f x) =
      -((∂_{unitVector j} g) x • Freq.complexifyVec (f x)) := fun x => by
    rw [SchwartzMap.neg_apply, neg_smul]
  simp only [hneg, integral_neg, e, neg_neg]

theorem lineDeriv_dir {f F : Space → Space} (j : Fin 3) (hf : MemLp f 2 volume) (hF : MemLp F 2 volume)
    (hd : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, fderiv ℝ φ y (unitVector j) • f y = -∫ y, φ y • F y) :
    ∂_{unitVector j} (Lp.toTemperedDistribution (Freq.complexify (Freq.toLpOrZero 2 f))) =
      Lp.toTemperedDistribution (Freq.complexify (Freq.toLpOrZero 2 F)) := by
  ext1 g
  rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have e1 : ∫ x, (-∂_{unitVector j} g) x • (Freq.complexify (Freq.toLpOrZero 2 f) : Space → Freq.CSpace) x =
      ∫ x, (-∂_{unitVector j} g) x • Freq.complexifyVec (f x) := by
    apply integral_congr_ae
    filter_upwards [Freq.Internal.H1Consistency.complexify_toLp_ae hf] with x hx
    rw [hx]
  have e2 : ∫ x, g x • (Freq.complexify (Freq.toLpOrZero 2 F) : Space → Freq.CSpace) x =
      ∫ x, g x • Freq.complexifyVec (F x) := by
    apply integral_congr_ae
    filter_upwards [Freq.Internal.H1Consistency.complexify_toLp_ae hF] with x hx
    rw [hx]
  rw [e1, e2]
  exact dir_rapid j hf hF hd g

theorem freq_dir {U V : Freq.L2C} (j : Fin 3)
    (hD0 : ∂_{unitVector j} (Lp.toTemperedDistribution U) = Lp.toTemperedDistribution V) :
    ((𝓕 V : Freq.L2C) : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => ((2 * Real.pi * Complex.I) * ((ξ j : ℝ) : ℂ)) • ((𝓕 U : Freq.L2C) : Space → Freq.CSpace) ξ := by
  have hD := congrArg (fun T => 𝓕 T) hD0
  rw [TemperedDistribution.fourier_lineDerivOp_eq, Lp.fourier_toTemperedDistribution_eq,
    Lp.fourier_toTemperedDistribution_eq] at hD
  have hc : Continuous (fun ξ : Space => (2 * Real.pi * Complex.I) * ((ξ j : ℝ) : ℂ)) := by fun_prop
  have hloc : LocallyIntegrable (fun ξ => ((𝓕 V : Freq.L2C) : Space → Freq.CSpace) ξ -
      ((2 * Real.pi * Complex.I) * ((ξ j : ℝ) : ℂ)) • ((𝓕 U : Freq.L2C) : Space → Freq.CSpace) ξ) volume :=
    ((Lp.memLp _).locallyIntegrable (by norm_num)).sub
      (((Lp.memLp _).locallyIntegrable (by norm_num)).continuous_smul hc)
  have hz := Freq.Internal.H1Consistency.ae_zero_of_rapid hloc (fun g => ?_)
  · filter_upwards [hz] with ξ hξ
    exact sub_eq_zero.1 hξ
  have hg := congrArg (fun T => T g) hD
  simp only [ContinuousLinearMap.smul_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply] at hg
  rw [SchwartzMap.smulLeftCLM_apply (by fun_prop)] at hg
  have hin : ∀ x : Space, inner ℝ x (unitVector j) = x j := fun x => by
    rw [unitVector, EuclideanSpace.inner_single_right]
    simp
  simp only [hin] at hg
  have hi1 : Integrable (fun x => g x • ((𝓕 V : Freq.L2C) : Space → Freq.CSpace) x) :=
    Freq.Internal.H1Consistency.integrable_rapid_smul g (Lp.memLp _)
  have hi2 : Integrable (fun x => (((x j : ℝ) : ℂ) • g x) • ((𝓕 U : Freq.L2C) : Space → Freq.CSpace) x) := by
    have := Freq.Internal.H1Consistency.integrable_rapid_smul
      (SchwartzMap.smulLeftCLM ℂ (fun x : Space => ((inner ℝ x (unitVector j) : ℝ) : ℂ)) g)
      (Lp.memLp (𝓕 U : Freq.L2C))
    rw [SchwartzMap.smulLeftCLM_apply (by fun_prop)] at this
    simpa only [hin] using this
  have hpt : ∀ x, g x • (((𝓕 V : Freq.L2C) : Space → Freq.CSpace) x -
      (2 * Real.pi * Complex.I * ((x j : ℝ) : ℂ)) • ((𝓕 U : Freq.L2C) : Space → Freq.CSpace) x) =
      g x • ((𝓕 V : Freq.L2C) : Space → Freq.CSpace) x -
        (2 * Real.pi * Complex.I) • ((((x j : ℝ) : ℂ) • g x) • ((𝓕 U : Freq.L2C) : Space → Freq.CSpace) x) := by
    intro x
    simp only [smul_sub, smul_smul, smul_eq_mul]
    congr 2
    ring
  have hi3 : Integrable (fun x => (2 * Real.pi * Complex.I) •
      ((((x j : ℝ) : ℂ) • g x) • ((𝓕 U : Freq.L2C) : Space → Freq.CSpace) x)) := by
    convert hi2.smul (2 * Real.pi * Complex.I) using 1 <;> rfl
  simp_rw [hpt]
  rw [integral_sub hi1 hi3, integral_smul, hg, sub_self]

theorem real_pair_eq {a b : Space → Space} (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
    ∫ y, inner ℝ (a y) (b y) = RCLike.re (∫ ξ, inner ℂ
      (((𝓕 (Freq.complexify (Freq.toLpOrZero 2 a)) : Freq.L2C) : Space → Freq.CSpace) ξ)
      (((𝓕 (Freq.complexify (Freq.toLpOrZero 2 b)) : Freq.L2C) : Space → Freq.CSpace) ξ)) := by
  have h1 : ∫ y, inner ℝ (a y) (b y) = inner ℝ (Freq.toLpOrZero 2 a) (Freq.toLpOrZero 2 b) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Freq.Internal.H1Consistency.toLpOrZero_ae ha,
      Freq.Internal.H1Consistency.toLpOrZero_ae hb] with y e1 e2
    rw [e1, e2]
  rw [h1, ← Freq.Internal.VelocityInjective.complexify_inner, ← Freq.Internal.VelocityInjective.freqTrR_inner,
    Freq.Internal.VelocityInjective.l2c_real_inner, L2.inner_def]
  rfl

theorem pair_of_dir {ζ Z w W : Space → Space} (j : Fin 3) (hζ : MemLp ζ 2 volume) (hZ : MemLp Z 2 volume)
    (hw : MemLp w 2 volume) (hW : MemLp W 2 volume)
    (hζd : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, fderiv ℝ φ y (unitVector j) • ζ y = -∫ y, φ y • Z y)
    (hwd : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, fderiv ℝ φ y (unitVector j) • w y = -∫ y, φ y • W y) :
    ∫ y, inner ℝ (Z y) (w y) = -∫ y, inner ℝ (ζ y) (W y) := by
  have h1 := freq_dir j (lineDeriv_dir j hζ hZ hζd)
  have h2 := freq_dir j (lineDeriv_dir j hw hW hwd)
  rw [real_pair_eq hZ hw, real_pair_eq hζ hW]
  have i1 : ∫ ξ, inner ℂ (((𝓕 (Freq.complexify (Freq.toLpOrZero 2 Z)) : Freq.L2C) : Space → Freq.CSpace) ξ)
      (((𝓕 (Freq.complexify (Freq.toLpOrZero 2 w)) : Freq.L2C) : Space → Freq.CSpace) ξ) =
      ∫ ξ, -(((2 * Real.pi * Complex.I) * ((ξ j : ℝ) : ℂ)) * inner ℂ
        (((𝓕 (Freq.complexify (Freq.toLpOrZero 2 ζ)) : Freq.L2C) : Space → Freq.CSpace) ξ)
        (((𝓕 (Freq.complexify (Freq.toLpOrZero 2 w)) : Freq.L2C) : Space → Freq.CSpace) ξ)) := by
    apply integral_congr_ae
    filter_upwards [h1] with ξ hξ
    rw [hξ, inner_smul_left]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  have i2 : ∫ ξ, inner ℂ (((𝓕 (Freq.complexify (Freq.toLpOrZero 2 ζ)) : Freq.L2C) : Space → Freq.CSpace) ξ)
      (((𝓕 (Freq.complexify (Freq.toLpOrZero 2 W)) : Freq.L2C) : Space → Freq.CSpace) ξ) =
      ∫ ξ, ((2 * Real.pi * Complex.I) * ((ξ j : ℝ) : ℂ)) * inner ℂ
        (((𝓕 (Freq.complexify (Freq.toLpOrZero 2 ζ)) : Freq.L2C) : Space → Freq.CSpace) ξ)
        (((𝓕 (Freq.complexify (Freq.toLpOrZero 2 w)) : Freq.L2C) : Space → Freq.CSpace) ξ) := by
    apply integral_congr_ae
    filter_upwards [h2] with ξ hξ
    rw [hξ, inner_smul_right]
  rw [i1, i2, integral_neg, map_neg]

theorem weak_of_C1 {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hv : LocallyIntegrable v volume)
    (k : Fin 3) (hG : LocallyIntegrable (fun y => G y (unitVector k)) volume) (hw : IsWeakGradientOf v G)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∫ y, fderiv ℝ ψ y (unitVector k) • v y = -∫ y, ψ y • G y (unitVector k) := by
  have hK : IsCompact (tsupport ψ) := hψc
  have hK1 : IsCompact (Metric.cthickening 1 (tsupport ψ)) := hK.cthickening
  let φ : ℕ → ContDiffBump (0 : Space) := fun n =>
    ⟨1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 1), by positivity,
      one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩
  have hφr : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hr1 : ∀ n, (φ n).rOut ≤ 1 := fun n => by
    show 1 / ((n : ℝ) + 1) ≤ 1
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have cb : ∀ g : Space → ℝ, Continuous g → tsupport g ⊆ tsupport ψ → ∀ M : ℝ, (∀ x, ‖g x‖ ≤ M) →
      ∀ n x, ‖((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ≤ 3 * M ∧
        (x ∉ Metric.cthickening 1 (tsupport ψ) →
          ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x = 0) := by
    intro g hg hgs M hM n x
    constructor
    · have h := (φ n).dist_normed_convolution_le (μ := volume) (x₀ := x) (ε := 2 * M) hg.aestronglyMeasurable
        (fun t _ => (dist_le_norm_add_norm _ _).trans (by linarith [hM t, hM x]))
      linarith [norm_sub_norm_le (((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) (g x),
        hM x, dist_eq_norm (((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) (g x)]
    · intro hx
      have hz : ∀ t, dist x t < 1 → g t = 0 := by
        intro t ht
        refine image_eq_zero_of_notMem_tsupport fun hm => hx ?_
        exact Metric.mem_cthickening_of_dist_le x t 1 _ (hgs hm) ht.le
      have h := (φ n).dist_normed_convolution_le (μ := volume) (x₀ := x) (ε := 0) hg.aestronglyMeasurable
        (fun t ht => by
          rw [hz t ((dist_comm x t ▸ Metric.mem_ball.1 ht).trans_le (hr1 n)), hz x (by simp)]
          simp)
      rw [hz x (by simp)] at h
      exact dist_le_zero.1 h
  have dψc : Continuous (fun y => fderiv ℝ ψ y (unitVector k)) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have dψs : tsupport (fun y => fderiv ℝ ψ y (unitVector k)) ⊆ tsupport ψ :=
    tsupport_fderiv_apply_subset ℝ (unitVector k)
  obtain ⟨M0, hM0⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  obtain ⟨M1, hM1⟩ := dψc.bounded_above_of_compact_support (hψc.fderiv_apply (𝕜 := ℝ) (unitVector k))
  have hT : ∀ n, IsTestScalar ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) := fun n =>
    ⟨(φ n).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (n := ⊤) (φ n).contDiff_normed
      hψ.continuous.locallyIntegrable, (φ n).hasCompactSupport_normed.convolution _ hψc⟩
  have cc : ∀ n, Continuous ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun y => fderiv ℝ ψ y (unitVector k))) := fun n =>
    ((φ n).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (n := 0) (φ n).contDiff_normed
      dψc.locallyIntegrable).continuous
  have hder : ∀ n x, fderiv ℝ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) x (unitVector k) =
      ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => fderiv ℝ ψ y (unitVector k))) x := by
    intro n x
    have hd := hψc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      ((φ n).integrable_normed (μ := volume)).locallyIntegrable hψ x
    rw [hd.fderiv, convolution_precompR_apply _ ((φ n).integrable_normed (μ := volume)).locallyIntegrable (hψc.fderiv (𝕜 := ℝ))
      (hψ.continuous_fderiv one_ne_zero) x (unitVector k)]
  have eq : ∀ n, ∫ y, ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun y => fderiv ℝ ψ y (unitVector k))) y • v y =
      -∫ y, ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) y • G y (unitVector k) := by
    intro n
    have h := hw _ (hT n) k
    simp only [hder] at h
    exact h
  have hKm : MeasurableSet (Metric.cthickening 1 (tsupport ψ)) := hK1.measurableSet
  have lim1 : Filter.Tendsto (fun n => ∫ y, ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun y => fderiv ℝ ψ y (unitVector k))) y • v y) Filter.atTop
      (nhds (∫ y, fderiv ℝ ψ y (unitVector k) • v y)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => (Metric.cthickening 1 (tsupport ψ)).indicator (fun y => 3 * M1 * ‖v y‖) y)
      (fun n => (cc n).aestronglyMeasurable.smul hv.aestronglyMeasurable)
      (IntegrableOn.integrable_indicator (f := fun y => 3 * M1 * ‖v y‖)
        ((hv.integrableOn_isCompact hK1).norm.const_mul (3 * M1)) hKm)
      (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · by_cases hy : y ∈ Metric.cthickening 1 (tsupport ψ)
      · rw [Set.indicator_of_mem hy, norm_smul]
        exact mul_le_mul_of_nonneg_right (cb _ dψc dψs M1 hM1 n y).1 (norm_nonneg _)
      · rw [Set.indicator_of_notMem hy, (cb _ dψc dψs M1 hM1 n y).2 hy, zero_smul, norm_zero]
    · exact (ContDiffBump.convolution_tendsto_right_of_continuous hφr dψc y).smul_const (v y)
  have lim2 : Filter.Tendsto (fun n => ∫ y, ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) y •
      G y (unitVector k)) Filter.atTop (nhds (∫ y, ψ y • G y (unitVector k))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => (Metric.cthickening 1 (tsupport ψ)).indicator (fun y => 3 * M0 * ‖G y (unitVector k)‖) y)
      (fun n => (hT n).1.continuous.aestronglyMeasurable.smul hG.aestronglyMeasurable)
      (IntegrableOn.integrable_indicator (f := fun y => 3 * M0 * ‖G y (unitVector k)‖)
        ((hG.integrableOn_isCompact hK1).norm.const_mul (3 * M0)) hKm)
      (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · by_cases hy : y ∈ Metric.cthickening 1 (tsupport ψ)
      · rw [Set.indicator_of_mem hy, norm_smul]
        exact mul_le_mul_of_nonneg_right (cb _ hψ.continuous subset_rfl M0 hM0 n y).1 (norm_nonneg _)
      · rw [Set.indicator_of_notMem hy, (cb _ hψ.continuous subset_rfl M0 hM0 n y).2 hy, zero_smul, norm_zero]
    · exact (ContDiffBump.convolution_tendsto_right_of_continuous hφr hψ.continuous y).smul_const _
  simp only [eq] at lim1
  exact tendsto_nhds_unique lim1 lim2.neg

end ConvectionPairing

end FracInternal

end Breakdown
