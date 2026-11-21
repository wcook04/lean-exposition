import Breakdown.FracCert.PowerSymbolSplit
import Breakdown.FreqTr.NiceApprox
import Breakdown.FracCert.SecondSymbol

open scoped ContDiff ENNReal SchwartzMap
open MeasureTheory Real Filter Topology
open LineDeriv

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace Internal.SecondPairRapid

open SchwartzMap LineDeriv
open Freq.Internal.NiceApprox (stdBump)

def IsRapidPairable (f : Space → Space) : Prop :=
  ∀ w : Space → ℝ, (∀ q : ℝ≥0∞, MemLp w q volume) → Integrable (fun y => w y * ‖f y‖)

theorem pairable_two {f : Space → Space} (hf : MemLp f 2 volume) : IsRapidPairable f :=
  fun _ hw => (hw 2).integrable_mul hf.norm

theorem pairable_six {f : Space → Space} (hf : MemLp f 6 volume) : IsRapidPairable f := by
  intro w hw
  have : ENNReal.HolderTriple (ENNReal.ofReal (6 / 5)) 6 1 := by
    constructor
    have h6 : (6 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 6) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    rw [h6, ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  exact (hw (ENNReal.ofReal (6 / 5))).integrable_mul hf.norm

theorem integrable_smul {f : Space → Space} (hd : IsRapidPairable f) (hm : AEStronglyMeasurable f volume)
    {w : Space → ℝ} (hw : ∀ q : ℝ≥0∞, MemLp w q volume) : Integrable (fun y => w y • f y) :=
  (hd _ fun q => (hw q).norm).mono' ((hw 1).1.smul hm) (ae_of_all _ fun _ => (norm_smul _ _).le)

theorem integrable_inner {f : Space → Space} (hd : IsRapidPairable f) (hm : AEStronglyMeasurable f volume)
    (Φ : 𝓢(Space, Space)) : Integrable (fun y => inner ℝ (f y) (Φ y)) := by
  refine (hd (fun y => ‖Φ y‖) fun q => (Φ.memLp q).norm).mono'
    (hm.inner Φ.continuous.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, mul_comm]
  exact abs_real_inner_le_norm _ _

def cut (ψ : Space → ℝ) (R : ℝ) : Space → ℝ := fun y => stdBump (R⁻¹ • y) * ψ y

theorem contDiff_cut {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (R : ℝ) : ContDiff ℝ ∞ (cut ψ R) :=
  (stdBump.contDiff.comp (contDiff_id.const_smul R⁻¹)).mul hψ

theorem test_cut {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) {R : ℝ} (hR : R ≠ 0) : IsTestScalar (cut ψ R) :=
  ⟨contDiff_cut hψ R, (stdBump.hasCompactSupport.comp_smul (inv_ne_zero hR)).mul_right⟩

theorem cut_eq (ψ : Space → ℝ) {R : ℝ} (hR : 0 < R) {y : Space} (hy : ‖y‖ ≤ R) : cut ψ R y = ψ y := by
  have h1 : stdBump (R⁻¹ • y) = 1 := by
    apply stdBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    show R⁻¹ * ‖y‖ ≤ 1
    rw [inv_mul_le_iff₀ hR]
    linarith
  simp [cut, h1]

theorem fderiv_cut_eq (ψ : Space → ℝ) {R : ℝ} (hR : 0 < R) {y : Space} (hy : ‖y‖ < R) :
    fderiv ℝ (cut ψ R) y = fderiv ℝ ψ y := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds (show y ∈ Metric.ball (0 : Space) R by simpa using hy)]
    with x hx
  exact cut_eq ψ hR (by simpa using (le_of_lt (by simpa using hx : ‖x‖ < R)))

theorem cut_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → ∀ R : ℝ, 1 ≤ R →
    ∀ (y : Space) (j : Fin 3),
      ‖fderiv ℝ (cut ψ R) y (unitVector j)‖ ≤ ‖fderiv ℝ ψ y (unitVector j)‖ + B * ‖ψ y‖ := by
  have hc : Continuous (fderiv ℝ (stdBump : Space → ℝ)) :=
    (stdBump.contDiff (n := 1)).continuous_fderiv (by simp)
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support (stdBump.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨B, hB0, fun ψ hψ R hR y j => ?_⟩
  have hR0 : 0 < R := by linarith
  have hdψ : DifferentiableAt ℝ ψ y := (hψ.differentiable (by simp)) y
  have hdb : Differentiable ℝ (stdBump : Space → ℝ) :=
    (stdBump.contDiff (n := 1)).differentiable (by simp)
  have hlin : HasFDerivAt (fun x : Space => R⁻¹ • x) (R⁻¹ • ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id y).const_smul R⁻¹
  have hcomp : HasFDerivAt (fun x : Space => stdBump (R⁻¹ • x))
      ((fderiv ℝ (stdBump : Space → ℝ) (R⁻¹ • y)).comp (R⁻¹ • ContinuousLinearMap.id ℝ Space)) y :=
    (hdb (R⁻¹ • y)).hasFDerivAt.comp y hlin
  have hf : fderiv ℝ (cut ψ R) y (unitVector j) =
      stdBump (R⁻¹ • y) * fderiv ℝ ψ y (unitVector j) +
        ψ y * fderiv ℝ (stdBump : Space → ℝ) (R⁻¹ • y) (R⁻¹ • unitVector j) := by
    rw [show cut ψ R = fun x => stdBump (R⁻¹ • x) * ψ x from rfl,
      fderiv_fun_mul hcomp.differentiableAt hdψ, hcomp.fderiv]
    simp
  rw [hf]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Real.norm_eq_abs (stdBump _), abs_of_nonneg stdBump.nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) stdBump.le_one
  · rw [norm_mul, mul_comm]
    gcongr
    calc ‖fderiv ℝ (stdBump : Space → ℝ) (R⁻¹ • y) (R⁻¹ • unitVector j)‖
        ≤ ‖fderiv ℝ (stdBump : Space → ℝ) (R⁻¹ • y)‖ * ‖R⁻¹ • unitVector j‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ B * 1 := by
          apply mul_le_mul (hB _) _ (norm_nonneg _) hB0
          rw [norm_smul, Freq.Internal.NiceApprox.norm_unitVector, mul_one, Real.norm_eq_abs, abs_inv,
            abs_of_pos hR0]
          exact inv_le_one_of_one_le₀ hR
      _ = B := mul_one B

theorem eventually_big (y : Space) : ∀ᶠ n : ℕ in atTop, ‖y‖ < (n : ℝ) + 1 := by
  filter_upwards [Filter.eventually_ge_atTop ⌈‖y‖⌉₊] with n hn
  have := Nat.le_ceil ‖y‖
  have h2 : (⌈‖y‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem weak_ext {f f' : Space → Space} {k : Fin 3} (hd : IsRapidPairable f)
    (hm : AEStronglyMeasurable f volume) (hd' : IsRapidPairable f') (hm' : AEStronglyMeasurable f' volume)
    (hw : ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, fderiv ℝ φ y (unitVector k) • f y = -∫ y, φ y • f' y)
    (ψ : 𝓢(Space, ℝ)) :
    ∫ y, fderiv ℝ (ψ : Space → ℝ) y (unitVector k) • f y = -∫ y, ψ y • f' y := by
  obtain ⟨B, hB0, hB⟩ := cut_bound
  have hψ : ContDiff ℝ ∞ (ψ : Space → ℝ) := ψ.smooth ⊤
  have L : Tendsto (fun n : ℕ => ∫ y, fderiv ℝ (cut ψ ((n : ℝ) + 1)) y (unitVector k) • f y) atTop
      (𝓝 (∫ y, fderiv ℝ (ψ : Space → ℝ) y (unitVector k) • f y)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => (‖fderiv ℝ (ψ : Space → ℝ) y (unitVector k)‖ + B * ‖ψ y‖) * ‖f y‖) (fun n => ?_) ?_
      (fun n => ?_) ?_
    · exact (((contDiff_cut hψ _).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable.smul hm
    · exact hd _ fun q => ((∂_{unitVector k} ψ).memLp q).norm.add ((ψ.memLp q).norm.const_mul B)
    · refine ae_of_all _ fun y => ?_
      rw [norm_smul]
      gcongr
      exact hB ψ hψ _ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) y k
    · refine ae_of_all _ fun y => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_big y] with n hn
      rw [fderiv_cut_eq _ (by positivity) hn]
  have R : Tendsto (fun n : ℕ => ∫ y, cut ψ ((n : ℝ) + 1) y • f' y) atTop
      (𝓝 (∫ y, ψ y • f' y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖ψ y‖ * ‖f' y‖) (fun n => ?_) ?_
      (fun n => ?_) ?_
    · exact (contDiff_cut hψ _).continuous.aestronglyMeasurable.smul hm'
    · exact hd' _ fun q => (ψ.memLp q).norm
    · refine ae_of_all _ fun y => ?_
      rw [norm_smul]
      gcongr
      show ‖stdBump (((n : ℝ) + 1)⁻¹ • y) * ψ y‖ ≤ _
      rw [norm_mul, Real.norm_eq_abs (stdBump _), abs_of_nonneg stdBump.nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _) stdBump.le_one
    · refine ae_of_all _ fun y => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_big y] with n hn
      rw [cut_eq _ (by positivity) hn.le]
  exact tendsto_nhds_unique L (R.neg.congr fun n =>
    (hw _ (test_cut hψ (by positivity : (0 : ℝ) < (n : ℝ) + 1).ne')).symm)

theorem inner_expand (x w : Space) : inner ℝ x w = ∑ i : Fin 3, inner ℝ (unitVector i) (w i • x) := by
  simp [unitVector, inner_smul_right, PiLp.inner_apply, mul_comm]

theorem weak_vec {f f' : Space → Space} {k : Fin 3} (hd : IsRapidPairable f)
    (hm : AEStronglyMeasurable f volume) (hd' : IsRapidPairable f') (hm' : AEStronglyMeasurable f' volume)
    (hw : ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, fderiv ℝ φ y (unitVector k) • f y = -∫ y, φ y • f' y)
    (Φ : 𝓢(Space, Space)) :
    ∫ y, inner ℝ (f y) ((∂_{unitVector k} Φ) y) = -∫ y, inner ℝ (f' y) (Φ y) := by
  let ψ : Fin 3 → 𝓢(Space, ℝ) := fun i => SchwartzMap.postcompCLM (EuclideanSpace.proj i) Φ
  have hψ : ∀ i y, ψ i y = Φ y i := fun i y => by simp [ψ, SchwartzMap.postcompCLM_apply]
  have hdψ : ∀ i y, fderiv ℝ (ψ i : Space → ℝ) y (unitVector k) = (∂_{unitVector k} Φ) y i := by
    intro i y
    have e : (ψ i : Space → ℝ) = (EuclideanSpace.proj i : Space →L[ℝ] ℝ) ∘ Φ :=
      funext fun y => by simp [hψ]
    rw [e, ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y
      (Φ.differentiableAt).hasFDerivAt).fderiv]
    simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hL : ∀ i, Integrable (fun y => fderiv ℝ (ψ i : Space → ℝ) y (unitVector k) • f y) :=
    fun i => integrable_smul hd hm fun q => (∂_{unitVector k} (ψ i)).memLp q volume
  have hR : ∀ i, Integrable (fun y => ψ i y • f' y) :=
    fun i => integrable_smul hd' hm' fun q => (ψ i).memLp q
  calc ∫ y, inner ℝ (f y) ((∂_{unitVector k} Φ) y)
      = ∫ y, ∑ i, inner ℝ (unitVector i) (fderiv ℝ (ψ i : Space → ℝ) y (unitVector k) • f y) := by
        congr 1
        funext y
        rw [inner_expand]
        simp only [hdψ]
    _ = ∑ i, inner ℝ (unitVector i) (∫ y, fderiv ℝ (ψ i : Space → ℝ) y (unitVector k) • f y) := by
        rw [integral_finsetSum _ fun i _ => (hL i).const_inner _]
        exact Finset.sum_congr rfl fun i _ => integral_inner (hL i) _
    _ = ∑ i, inner ℝ (unitVector i) (-∫ y, ψ i y • f' y) := by
        simp only [weak_ext hd hm hd' hm' hw]
    _ = -∫ y, inner ℝ (f' y) (Φ y) := by
        rw [show (fun y => inner ℝ (f' y) (Φ y)) =
            fun y => ∑ i, inner ℝ (unitVector i) (ψ i y • f' y) from
            funext fun y => by rw [inner_expand]; simp only [hψ],
          integral_finsetSum _ fun i _ => (hR i).const_inner _, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [inner_neg_right, integral_inner (hR i)]

end Internal.SecondPairRapid

open Internal.SecondPairRapid in
theorem rapidSecondPair : RapidSecondPairStatement := by
  intro k v G H hS φ
  have hGm : ∀ j, MemLp (fun y => G y (unitVector j)) 2 volume := fun j =>
    Internal.SecondSymbol.memLp_comp hS.measurable_gradient hS.gradient_two j
  have hHm : ∀ j, MemLp (fun y => H y (unitVector j) (unitVector j)) 2 volume := fun j =>
    Internal.SecondSymbol.memLp_second hS.measurable_second hS.second_two j j
  have hv := pairable_six hS.velocity_six
  have s1 : ∀ j, ∫ y, inner ℝ (v y) ((∂_{unitVector j} (∂_{unitVector j} φ)) y) =
      -∫ y, inner ℝ (G y (unitVector j)) ((∂_{unitVector j} φ) y) := fun j =>
    weak_vec hv hS.measurable_velocity (pairable_two (hGm j)) (hGm j).1
      (fun ψ hψ => hS.weak_gradient ψ hψ j) _
  have s2 : ∀ j, ∫ y, inner ℝ (G y (unitVector j)) ((∂_{unitVector j} φ) y) =
      -∫ y, inner ℝ (H y (unitVector j) (unitVector j)) (φ y) := fun j =>
    weak_vec (pairable_two (hGm j)) (hGm j).1 (pairable_two (hHm j)) (hHm j).1
      (fun ψ hψ => hS.weak_second ψ hψ j j) _
  rw [← Freq.Internal.NiceApprox.negSspS_apply]
  have e1 : ∀ y, inner ℝ (v y) ((Freq.Internal.NiceApprox.negSspS φ) y) =
      -∑ j, inner ℝ (v y) ((∂_{unitVector j} (∂_{unitVector j} φ)) y) := by
    intro y
    simp [Freq.Internal.NiceApprox.negSspS, inner_sum, inner_neg_right]
  have e2 : ∀ y, inner ℝ (negSecondTrace H y) (φ y) =
      -∑ j, inner ℝ (H y (unitVector j) (unitVector j)) (φ y) := by
    intro y
    simp [negSecondTrace, secondTrace, sum_inner, inner_neg_left]
  simp only [e1, e2]
  rw [integral_neg, integral_neg,
    integral_finsetSum _ fun j _ => integrable_inner hv hS.measurable_velocity _,
    integral_finsetSum _ fun j _ => integrable_inner (pairable_two (hHm j)) (hHm j).1 φ]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [s1, s2, neg_neg]

end SteadyCert

end Breakdown
