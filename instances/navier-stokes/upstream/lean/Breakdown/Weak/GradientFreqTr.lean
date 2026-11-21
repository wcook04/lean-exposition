import Breakdown.Weak.StatementsSlice
import Breakdown.FreqTr.GradCompat
import Breakdown.FreqTr.EmbedMem
import Breakdown.FreqTr.PartialDecay
import Breakdown.FreqTr.NiceApprox
import Breakdown.FreqTr.FreqTrConjSym

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff FourierTransform SchwartzMap

noncomputable section

namespace Breakdown.WeakProfile

open Freq

namespace Internal.GradientFreqTr

open SchwartzMap LineDeriv
open Freq.Internal.NiceApprox (pd contDiff_pd hasCompactSupport_pd pd_comm stdBump norm_unitVector)

theorem memLp_grad {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} {C : ℝ}
    (h : IsSlice f g C) : MemLp g 2 volume := by
  have hm : AEStronglyMeasurable g volume := h.grad.2.1.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).2 ⟨hm.norm.pow 2, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt h.two ENNReal.ofReal_lt_top)
  exact lintegral_congr fun y => Real.enorm_eq_ofReal (by positivity)

theorem memLp_comp {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} {C : ℝ}
    (h : IsSlice f g C) (k : Fin 3) : MemLp (gradComponent g k) 2 volume :=
  (ContinuousLinearMap.apply ℝ Space (unitVector k)).comp_memLp' (memLp_grad h)

theorem sym_real {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} (hw : IsWeakGradient f g)
    {φ : Space → ℝ} (hφ : IsTestFunction φ) (j k : Fin 3) :
    ∫ y, fderiv ℝ φ y (unitVector k) • gradComponent g j y =
      ∫ y, fderiv ℝ φ y (unitVector j) • gradComponent g k y := by
  have ht : ∀ v : Space, IsTestFunction (pd v φ) := fun v =>
    ⟨contDiff_pd hφ.1 v, hasCompactSupport_pd hφ.2 v⟩
  have e1 := hw.2.2 _ (ht (unitVector k)) j
  have e2 := hw.2.2 _ (ht (unitVector j)) k
  have hc := pd_comm hφ.1 (unitVector j) (unitVector k)
  show ∫ y, pd (unitVector k) φ y • g y (unitVector j) =
    ∫ y, pd (unitVector j) φ y • g y (unitVector k)
  rw [e1, e2]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  show pd (unitVector j) (pd (unitVector k) φ) y • f y =
    pd (unitVector k) (pd (unitVector j) φ) y • f y
  rw [hc]

theorem smul_cv (z : ℂ) (w : Space) :
    z • complexifyVec w = complexifyVec (z.re • w) + Complex.I • complexifyVec (z.im • w) := by
  ext i
  simp [complexifyVec]
  linear_combination (-((w i : ℝ) : ℂ)) * Complex.re_add_im z

theorem integral_smul_cv {a : Space → ℂ} {u : Space → Space}
    (h1 : Integrable (fun y => (a y).re • u y) volume)
    (h2 : Integrable (fun y => (a y).im • u y) volume) :
    ∫ y, a y • complexifyVec (u y) =
      complexifyVec (∫ y, (a y).re • u y) + Complex.I • complexifyVec (∫ y, (a y).im • u y) := by
  rw [show (fun y => a y • complexifyVec (u y)) = fun y => complexifyVec ((a y).re • u y) +
      Complex.I • complexifyVec ((a y).im • u y) from funext fun y => smul_cv _ _]
  have i1 : Integrable (fun y => complexifyVec ((a y).re • u y)) volume :=
    complexifyVec.integrable_comp h1
  have i2 : Integrable (fun y => Complex.I • complexifyVec ((a y).im • u y)) volume :=
    (complexifyVec.integrable_comp h2).smul Complex.I
  rw [integral_add i1 i2, integral_smul, complexifyVec.integral_comp_comm h1, complexifyVec.integral_comp_comm h2]

theorem sym_cplx {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} (hw : IsWeakGradient f g)
    (hm : ∀ i, MemLp (gradComponent g i) 2 volume)
    {ψ : Space → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ) (j k : Fin 3) :
    ∫ y, fderiv ℝ ψ y (unitVector k) • complexifyVec (gradComponent g j y) =
      ∫ y, fderiv ℝ ψ y (unitVector j) • complexifyVec (gradComponent g k y) := by
  have ha : IsTestFunction (fun y => (ψ y).re) :=
    ⟨Complex.reCLM.contDiff.comp hψ, hs.comp_left Complex.zero_re⟩
  have hb : IsTestFunction (fun y => (ψ y).im) :=
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
  have hint : ∀ (φ : Space → ℝ), IsTestFunction φ → ∀ (v : Space) (i : Fin 3),
      Integrable (fun y => fderiv ℝ φ y v • gradComponent g i y) volume :=
    fun φ hφ v i => ((hm i).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const) (hasCompactSupport_pd hφ.2 v)
  have key : ∀ (v : Space) (i : Fin 3), ∫ y, fderiv ℝ ψ y v • complexifyVec (gradComponent g i y) =
      complexifyVec (∫ y, fderiv ℝ (fun y => (ψ y).re) y v • gradComponent g i y) +
        Complex.I • complexifyVec (∫ y, fderiv ℝ (fun y => (ψ y).im) y v • gradComponent g i y) := by
    intro v i
    rw [integral_smul_cv]
    · simp only [hda, hdb]
    · simpa only [hda] using hint _ ha v i
    · simpa only [hdb] using hint _ hb v i
  rw [key, key, sym_real hw ha j k, sym_real hw hb j k]

def cutoff (Θ : Space → ℂ) (R : ℝ) : Space → ℂ := fun y => stdBump (R⁻¹ • y) • Θ y

theorem contDiff_cutoff {Θ : Space → ℂ} (hΘ : ContDiff ℝ ∞ Θ) (R : ℝ) :
    ContDiff ℝ ∞ (cutoff Θ R) :=
  (stdBump.contDiff.comp (contDiff_id.const_smul R⁻¹)).smul hΘ

theorem hasCompactSupport_cutoff (Θ : Space → ℂ) {R : ℝ} (hR : R ≠ 0) :
    HasCompactSupport (cutoff Θ R) :=
  (stdBump.hasCompactSupport.comp_smul (inv_ne_zero hR)).smul_right

theorem fderiv_cutoff_eq (Θ : Space → ℂ) {R : ℝ} (hR : 0 < R) {y : Space} (hy : ‖y‖ < R) :
    fderiv ℝ (cutoff Θ R) y = fderiv ℝ Θ y := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds (show y ∈ Metric.ball (0 : Space) R by simpa using hy)]
    with x hx
  have h1 : stdBump (R⁻¹ • x) = 1 := by
    apply stdBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hR]
    have : ‖x‖ < R := by simpa using hx
    show R⁻¹ * ‖x‖ ≤ 1
    rw [inv_mul_le_iff₀ hR]
    linarith
  simp [cutoff, h1]

theorem fderiv_cutoff_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ (Θ : Space → ℂ), ContDiff ℝ ∞ Θ → ∀ R : ℝ, 1 ≤ R →
    ∀ (y : Space) (j : Fin 3),
      ‖fderiv ℝ (cutoff Θ R) y (unitVector j)‖ ≤ ‖fderiv ℝ Θ y (unitVector j)‖ + B * ‖Θ y‖ := by
  have hc : Continuous (fderiv ℝ (stdBump : Space → ℝ)) :=
    (stdBump.contDiff (n := 1)).continuous_fderiv (by simp)
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support (stdBump.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨B, hB0, fun Θ hΘ R hR y j => ?_⟩
  have hR0 : 0 < R := by linarith
  have hdΘ : DifferentiableAt ℝ Θ y := (hΘ.differentiable (by simp)) y
  have hdb : Differentiable ℝ (stdBump : Space → ℝ) := (stdBump.contDiff (n := 1)).differentiable (by simp)
  have hlin : HasFDerivAt (fun x : Space => R⁻¹ • x) (R⁻¹ • ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id y).const_smul R⁻¹
  have hcomp : HasFDerivAt (fun x : Space => stdBump (R⁻¹ • x))
      ((fderiv ℝ (stdBump : Space → ℝ) (R⁻¹ • y)).comp (R⁻¹ • ContinuousLinearMap.id ℝ Space)) y :=
    (hdb (R⁻¹ • y)).hasFDerivAt.comp y hlin
  have hcd : DifferentiableAt ℝ (fun x : Space => stdBump (R⁻¹ • x)) y := hcomp.differentiableAt
  have hf : fderiv ℝ (cutoff Θ R) y (unitVector j) =
      stdBump (R⁻¹ • y) • fderiv ℝ Θ y (unitVector j) +
        fderiv ℝ (stdBump : Space → ℝ) (R⁻¹ • y) (R⁻¹ • unitVector j) • Θ y := by
    rw [show cutoff Θ R = fun x => stdBump (R⁻¹ • x) • Θ x from rfl, fderiv_fun_smul hcd hdΘ,
      hcomp.fderiv]
    simp
  rw [hf]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg stdBump.nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) stdBump.le_one
  · rw [norm_smul]
    gcongr
    calc ‖fderiv ℝ (stdBump : Space → ℝ) (R⁻¹ • y) (R⁻¹ • unitVector j)‖
        ≤ ‖fderiv ℝ (stdBump : Space → ℝ) (R⁻¹ • y)‖ * ‖R⁻¹ • unitVector j‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ B * 1 := by
          apply mul_le_mul (hB _) _ (norm_nonneg _) hB0
          rw [norm_smul, norm_unitVector, mul_one, Real.norm_eq_abs, abs_inv, abs_of_pos hR0]
          exact inv_le_one_of_one_le₀ hR
      _ = B := mul_one B

end Internal.GradientFreqTr

namespace Internal.GradientFreqTr

open SchwartzMap LineDeriv
open Freq.Internal.NiceApprox (pd contDiff_pd hasCompactSupport_pd pd_comm stdBump norm_unitVector)

theorem tendsto_cut {g : Space → (Space →L[ℝ] Space)}
    (hm : ∀ i, MemLp (gradComponent g i) 2 volume) (Θ : 𝓢(Space, ℂ)) (j k : Fin 3) :
    Tendsto (fun n : ℕ => ∫ y, fderiv ℝ (cutoff Θ ((n : ℝ) + 1)) y (unitVector k) •
        complexifyVec (gradComponent g j y)) atTop
      (𝓝 (∫ y, fderiv ℝ (Θ : Space → ℂ) y (unitVector k) • complexifyVec (gradComponent g j y))) := by
  obtain ⟨B, hB0, hB⟩ := fderiv_cutoff_bound
  have hΘ : ContDiff ℝ ∞ (Θ : Space → ℂ) := Θ.smooth ⊤
  have hmj : MemLp (fun y => complexifyVec (gradComponent g j y)) 2 volume :=
    complexifyVec.comp_memLp' (hm j)
  have hd : MemLp (fun y => ‖fderiv ℝ (Θ : Space → ℂ) y (unitVector k)‖ + B * ‖Θ y‖) 2 volume :=
    ((SchwartzMap.memLp (∂_{unitVector k} Θ) 2 volume).norm).add
      ((SchwartzMap.memLp Θ 2 volume).norm.const_mul B)
  refine tendsto_integral_of_dominated_convergence
    (fun y => (‖fderiv ℝ (Θ : Space → ℂ) y (unitVector k)‖ + B * ‖Θ y‖) *
      ‖complexifyVec (gradComponent g j y)‖) (fun n => ?_) ?_ (fun n => ?_) ?_
  · exact (((contDiff_cutoff hΘ _).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable.smul hmj.aestronglyMeasurable
  · exact hd.integrable_mul hmj.norm
  · refine ae_of_all _ fun y => ?_
    rw [norm_smul]
    gcongr
    exact hB Θ hΘ _ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) y k
  · refine ae_of_all _ fun y => tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ⌈‖y‖⌉₊] with n hn
    have h1 : ‖y‖ < (n : ℝ) + 1 := by
      have := Nat.le_ceil ‖y‖
      have h2 : (⌈‖y‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [fderiv_cutoff_eq _ (by positivity) h1]

theorem sym_rapid {f : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (hw : IsWeakGradient f g) (hm : ∀ i, MemLp (gradComponent g i) 2 volume)
    (Θ : 𝓢(Space, ℂ)) (j k : Fin 3) :
    ∫ y, fderiv ℝ (Θ : Space → ℂ) y (unitVector k) • complexifyVec (gradComponent g j y) =
      ∫ y, fderiv ℝ (Θ : Space → ℂ) y (unitVector j) • complexifyVec (gradComponent g k y) := by
  have hΘ : ContDiff ℝ ∞ (Θ : Space → ℂ) := Θ.smooth ⊤
  refine tendsto_nhds_unique (tendsto_cut hm Θ j k) ((tendsto_cut hm Θ k j).congr fun n => ?_)
  exact (sym_cplx hw hm (contDiff_cutoff hΘ _) (hasCompactSupport_cutoff _ (by positivity)) j k).symm

def hatComp (g : Space → (Space →L[ℝ] Space)) (k : Fin 3) : L2C :=
  freqTrR (complexify (toLpOrZero 2 (gradComponent g k)))

theorem coe_comp {g : Space → (Space →L[ℝ] Space)} {k : Fin 3}
    (hm : MemLp (gradComponent g k) 2 volume) :
    (complexify (toLpOrZero 2 (gradComponent g k)) : Space → CSpace) =ᵐ[volume]
      fun x => complexifyVec (gradComponent g k x) := by
  have h1 : toLpOrZero 2 (gradComponent g k) = hm.toLp _ := by
    simp [toLpOrZero, hm]
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec
    (toLpOrZero 2 (gradComponent g k)), hm.coeFn_toLp] with x hx hx'
  rw [complexify, hx, h1, hx']

theorem pair_deriv {g : Space → (Space →L[ℝ] Space)}
    (hm : ∀ i, MemLp (gradComponent g i) 2 volume) (Ψ : 𝓢(Space, ℂ)) (j k : Fin 3) :
    (-(2 * π * Complex.I)) • ∫ ξ, (smulLeftCLM ℂ (inner ℝ · (unitVector k)) Ψ) ξ •
        (hatComp g j : Space → CSpace) ξ =
      ∫ x, fderiv ℝ ((𝓕 Ψ : 𝓢(Space, ℂ)) : Space → ℂ) x (unitVector k) •
        complexifyVec (gradComponent g j x) := by
  rw [← integral_smul]
  have h1 : ∀ ξ, (-(2 * π * Complex.I)) • ((smulLeftCLM ℂ (inner ℝ · (unitVector k)) Ψ) ξ •
      (hatComp g j : Space → CSpace) ξ) =
      ((-(2 * π * Complex.I)) • smulLeftCLM ℂ (inner ℝ · (unitVector k)) Ψ) ξ •
        (hatComp g j : Space → CSpace) ξ := by
    intro ξ
    rw [smul_apply, smul_assoc]
  simp only [h1]
  rw [show (hatComp g j : L2C) = freqTrL2 (complexify (toLpOrZero 2 (gradComponent g j))) from rfl,
    Freq.Internal.GradCompat.pair_freqTr, ← lineDerivOp_fourier_eq]
  refine integral_congr_ae ?_
  filter_upwards [coe_comp (hm j)] with x hx
  rw [hx]
  rfl

theorem pair_sym {f : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (hw : IsWeakGradient f g) (hm : ∀ i, MemLp (gradComponent g i) 2 volume)
    (Ψ : 𝓢(Space, ℂ)) (j k : Fin 3) :
    ∫ ξ, (smulLeftCLM ℂ (inner ℝ · (unitVector k)) Ψ) ξ • (hatComp g j : Space → CSpace) ξ =
      ∫ ξ, (smulLeftCLM ℂ (inner ℝ · (unitVector j)) Ψ) ξ • (hatComp g k : Space → CSpace) ξ := by
  have hc : (-(2 * π * Complex.I)) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  apply smul_right_injective CSpace hc
  simp only
  rw [pair_deriv hm, pair_deriv hm, sym_rapid hw hm]

theorem compat {f : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (hw : IsWeakGradient f g) (hm : ∀ i, MemLp (gradComponent g i) 2 volume) (j k : Fin 3) :
    ∀ᵐ ξ ∂volume, (ξ k : ℝ) • (hatComp g j : L2C) ξ = (ξ j : ℝ) • (hatComp g k : L2C) ξ := by
  have hL : ∀ j k : Fin 3, LocallyIntegrable (fun ξ : Space => (ξ k : ℝ) • (hatComp g j : L2C) ξ) volume :=
    fun j k => LocallyIntegrable.continuous_smul (by fun_prop)
      ((Lp.memLp (hatComp g j)).locallyIntegrable (by norm_num))
  refine ae_eq_of_integral_contDiff_smul_eq (hL j k) (hL k j) fun φ hφ hφs => ?_
  have h₁ : HasCompactSupport (fun ξ => (φ ξ : ℂ)) := hφs.comp_left Complex.ofReal_zero
  have h₂ : ContDiff ℝ ∞ (fun ξ => (φ ξ : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  set Ψ : 𝓢(Space, ℂ) := h₁.toSchwartzMap h₂ with hΨ
  have e : ∀ j k : Fin 3, ∫ ξ, φ ξ • ((ξ k : ℝ) • (hatComp g j : L2C) ξ) =
      ∫ ξ, (smulLeftCLM ℂ (inner ℝ · (unitVector k)) Ψ) ξ • (hatComp g j : Space → CSpace) ξ := by
    intro j k
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    have ht : (inner ℝ · (unitVector k) : Space → ℝ).HasTemperateGrowth :=
      ((innerSL ℝ).flip (unitVector k)).hasTemperateGrowth
    dsimp only
    rw [smulLeftCLM_apply_apply ht]
    have hi : inner ℝ ξ (unitVector k) = ξ k := by
      simp [unitVector, EuclideanSpace.inner_single_right]
    have hΨx : Ψ ξ = (φ ξ : ℂ) := rfl
    simp only [hi, hΨx]
    rw [smul_smul, ← Complex.coe_smul]
    congr 1
    rw [Complex.real_smul]
    push_cast
    ring
  rw [e, e]
  exact pair_sym hw hm Ψ j k

end Internal.GradientFreqTr

namespace Internal.GradientFreqTr

theorem div_hat {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} {C : ℝ} (h : IsSlice f g C) :
    ∀ᵐ ξ ∂volume, ∑ i : Fin 3, (hatComp g i : Space → CSpace) ξ i = 0 := by
  have hm := memLp_comp h
  have hz : ∑ i : Fin 3, ContinuousLinearMap.compLpL 2 volume (Freq.Internal.EmbedMem.coordReal i)
      (toLpOrZero 2 (gradComponent g i)) = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    have hc : ∀ i : Fin 3, toLpOrZero 2 (gradComponent g i) = (hm i).toLp _ := fun i => by
      simp [toLpOrZero, hm i]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin 3 => ContinuousLinearMap.compLpL 2
        volume (Freq.Internal.EmbedMem.coordReal i) (toLpOrZero 2 (gradComponent g i))),
      ae_all_iff.2 fun i : Fin 3 => ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume)
        (Freq.Internal.EmbedMem.coordReal i) (toLpOrZero 2 (gradComponent g i)),
      ae_all_iff.2 fun i : Fin 3 => (hm i).coeFn_toLp, h.div] with x hs hi ht hdiv
    rw [hs, Finset.sum_apply]
    simp only [hi]
    simp only [hc, ht, Freq.Internal.EmbedMem.coordReal_apply]
    rw [← Finset.sum_smul]
    have hd : ∑ i : Fin 3, gradComponent g i x i = 0 := hdiv
    rw [hd, zero_smul]
    rfl
  have hF : ∑ i : Fin 3, ContinuousLinearMap.compLpL 2 volume (Freq.Internal.EmbedMem.coordCplx i)
      (hatComp g i) = 0 := by
    have := congrArg (fun u => freqTrR (complexify u)) hz
    simp only [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Freq.Internal.EmbedMem.complexify_compLpL _ (Freq.Internal.EmbedMem.coordCplx i)
      (Freq.Internal.EmbedMem.complexifyVec_coord i)]
    exact (Freq.Internal.EmbedMem.freqTrL2_compLpL (Freq.Internal.EmbedMem.coordCplx i) _).symm
  have hae : (((∑ i : Fin 3, ContinuousLinearMap.compLpL 2 volume
      (Freq.Internal.EmbedMem.coordCplx i) (hatComp g i) : L2C)) : Space → CSpace) =ᵐ[volume] 0 := by
    rw [hF]
    exact Lp.coeFn_zero _ _ _
  filter_upwards [hae, Lp.coeFn_finsetSum Finset.univ (fun i : Fin 3 =>
      ContinuousLinearMap.compLpL 2 volume (Freq.Internal.EmbedMem.coordCplx i) (hatComp g i)),
    ae_all_iff.2 fun i : Fin 3 => ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume)
      (Freq.Internal.EmbedMem.coordCplx i) (hatComp g i)] with ξ h0 hs hi
  rw [hs, Finset.sum_apply] at h0
  simp only [hi, Freq.Internal.EmbedMem.coordCplx_apply] at h0
  have := congrArg (fun w : CSpace => w 0) h0
  simpa [← Finset.sum_smul] using this

def gradSum (g : Space → (Space →L[ℝ] Space)) : L2C :=
  ∑ k : Fin 3, fieldOp id (fun ξ => cmul (gradSymbol k ξ)) (hatComp g k)

theorem gradSum_ae (g : Space → (Space →L[ℝ] Space)) :
    (gradSum g : Space → CSpace) =ᵐ[volume]
      fun ξ => ∑ k : Fin 3, gradSymbol k ξ • (hatComp g k : Space → CSpace) ξ := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun k : Fin 3 => fieldOp id (fun ξ => cmul (gradSymbol k ξ)) (hatComp g k)),
    ae_all_iff.2 fun k : Fin 3 => Freq.Internal.EmbedMem.gradOp_ae fieldOpRealized_holds k
      (hatComp g k)] with ξ hs hk
  rw [gradSum, hs, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => hk k

theorem long_gradSum {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} {C : ℝ}
    (h : IsSlice f g C) : fieldOp id longitudinal (gradSum g) = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hc : ∀ᵐ ξ ∂volume, ∀ j k : Fin 3,
      (ξ k : ℝ) • (hatComp g j : Space → CSpace) ξ = (ξ j : ℝ) • (hatComp g k : Space → CSpace) ξ :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun k => compat h.grad (memLp_comp h) j k
  filter_upwards [Freq.Internal.EmbedMem.longitudinal_ae fieldOpRealized_holds (gradSum g),
    gradSum_ae g, hc, div_hat h] with ξ hl ho hcξ hd
  rw [hl, ho, Pi.zero_apply]
  have hcomp : ∀ k : Fin 3, ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * (hatComp g k : Space → CSpace) ξ i = 0 := by
    intro k
    have hik : ∀ i : Fin 3, ((ξ i : ℝ) : ℂ) * (hatComp g k : Space → CSpace) ξ i =
        ((ξ k : ℝ) : ℂ) * (hatComp g i : Space → CSpace) ξ i := by
      intro i
      have := congrArg (fun w : CSpace => w i) (hcξ i k)
      simpa [Complex.real_smul] using this.symm
    rw [Finset.sum_congr rfl fun i _ => hik i, ← Finset.mul_sum, hd, mul_zero]
  have hinner : inner ℂ (freqVec ξ)
      (∑ k : Fin 3, gradSymbol k ξ • (hatComp g k : Space → CSpace) ξ) = 0 := by
    rw [inner_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [inner_smul_right, Freq.Internal.EmbedMem.inner_freqVec, hcomp k, mul_zero]
  show ((‖ξ‖ ^ 2)⁻¹ : ℝ) • (inner ℂ (freqVec ξ)
    (∑ k : Fin 3, gradSymbol k ξ • (hatComp g k : Space → CSpace) ξ) • freqVec ξ) = 0
  rw [hinner, zero_smul, smul_zero]

theorem gradSum_mem {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} {C : ℝ}
    (h : IsSlice f g C) : gradSum g ∈ Sig := by
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [LinearMap.mem_ker]
    show reflConj (gradSum g) - gradSum g = 0
    rw [sub_eq_zero, gradSum, map_sum]
    exact Finset.sum_congr rfl fun k _ => Freq.Internal.EmbedMem.conjSym_grad fieldOpRealized_holds k _
      (freqTrConjSym fieldOpRealized_holds _)
  · rw [LinearMap.mem_ker]
    exact long_gradSum h

theorem partial_gradSum {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} {C : ℝ}
    (h : IsSlice f g C) (j : Fin 3) :
    (partialX j (⟨gradSum g, gradSum_mem h⟩ : X) : Space → Space) =ᵐ[volume] gradComponent g j := by
  set G : Fin 3 → L2C := fun k => hatComp g k with hG
  have hT : (fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (gradSum g) : Space → CSpace) =ᵐ[volume]
      (G j : Space → CSpace) := by
    filter_upwards [Freq.Internal.PartialDecay.symbolOp_ae fieldOpRealized_holds _
        (Freq.Internal.PartialDecay.measurable_derivSymbol j)
        (fun ξ => by
          rw [Freq.Internal.PartialDecay.norm_derivSymbol]
          exact Freq.Internal.PartialDecay.coord_div_le_one ξ j) (gradSum g),
      gradSum_ae g, Freq.Internal.PartialDecay.ae_ne_zero,
      ae_all_iff.2 fun j => ae_all_iff.2 fun k => compat h.grad (memLp_comp h) j k]
      with ξ ea eb hξ hc
    rw [ea, eb]
    ext i
    simp [Finset.sum_apply]
    have hn : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hξ)
    have hn2 : ((‖ξ‖ : ℝ) : ℂ) ^ 2 = ∑ k, ((ξ k : ℝ) : ℂ) ^ 2 := by
      exact_mod_cast Freq.Internal.PartialDecay.norm_sq_space ξ
    have hc' : ∀ a b : Fin 3, ((ξ b : ℝ) : ℂ) * ((G a : Space → CSpace) ξ) i =
        ((ξ a : ℝ) : ℂ) * ((G b : Space → CSpace) ξ) i := by
      intro a b
      have := congrArg (fun v : CSpace => v i) (hc a b)
      simpa [Complex.real_smul] using this
    unfold derivSymbol gradSymbol
    exact Freq.Internal.PartialDecay.symbol_identity (fun k => ((ξ k : ℝ) : ℂ))
      (fun k => ((G k : Space → CSpace) ξ) i) _ hn hn2 hc' j
  have heq : fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (gradSum g) = G j := Lp.ext hT
  have hp : partialX j (⟨gradSum g, gradSum_mem h⟩ : X) = toPhys (G j) := by
    show toPhys (fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (gradSum g)) = _
    rw [heq]
  rw [hp]
  change (toPhys (freqTrR (complexify (toLpOrZero 2 (gradComponent g j)))) : Space → Space)
    =ᵐ[volume] _
  exact (Freq.Internal.PartialDecay.toPhys_freqTr_complexify _).trans
    (Freq.Internal.PartialDecay.toLpOrZero_ae (memLp_comp h j))

end Internal.GradientFreqTr

theorem gradientFreqTr_holds : GradientFreqTr := fun _ g _ h =>
  ⟨⟨Internal.GradientFreqTr.gradSum g, Internal.GradientFreqTr.gradSum_mem h⟩,
    Internal.GradientFreqTr.partial_gradSum h⟩

end Breakdown.WeakProfile
