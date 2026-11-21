import Breakdown.FracCert.FarFieldGradientFreeParts
import Breakdown.FracCert.KernelScaling
import Breakdown.FracCert.KernelDecay
import Breakdown.FracCert.WeakRegular
import Breakdown.FracCert.WeakSymbolL1
import Breakdown.FracCert.WeakFieldSmooth
import Breakdown.Uniqueness.RegPhysAuxProductPart2
import Breakdown.Frac.PAxial

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff FourierTransform SchwartzMap ComplexConjugate

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

namespace FarFieldGradientFreeInternal

theorem profileField_continuous (U : X) (hM : HasAllMoments U) : Continuous (profileField U) := by
  have h0 := (symbolL1OfMoments U hM).1 0
  simp only [pow_zero, one_mul] at h0
  exact WeakRegularInternal.continuous_physField_of
    ((integrable_norm_iff (WeakRegularInternal.aesm_symbolX U)).1 h0)

theorem profileField_bounded (U : X) (hM : HasAllMoments U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖profileField U y‖ ≤ C := by
  have hw := WeakRegularInternal.moments_clean U (symbolL1OfMoments U hM).1
  obtain ⟨-, hb⟩ := fieldSmoothOfMoments _ hw (WeakRegularInternal.cleanSymbol_conjSym _)
  obtain ⟨C, hC⟩ := hb 0
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  have h := hC y
  rw [norm_iteratedFDeriv_zero, WeakRegularInternal.physField_clean] at h
  exact h.trans (le_max_left _ _)

theorem tensorSq_continuous {V : Space → Space} (hV : Continuous V) : Continuous (tensorSq V) := by
  unfold tensorSq
  refine continuous_pi fun j => continuous_pi fun k => ?_
  exact ((continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp hV)).mul
    ((continuous_apply k).comp ((PiLp.continuous_ofLp 2 _).comp hV))

theorem tensorSq_norm_le {V : Space → Space} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖V y‖ ≤ C) (y : Space) :
    ‖tensorSq V y‖ ≤ C * C := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC0 hC0)).2 fun j => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC0 hC0)).2 fun k => ?_
  rw [tensorSq, norm_mul]
  exact mul_le_mul ((PiLp.norm_apply_le _ _).trans (hC y)) ((PiLp.norm_apply_le _ _).trans (hC y))
    (norm_nonneg _) hC0


theorem kernel_measurable (α : ℝ) (i j k : Fin 3) :
    Measurable (fun p : ℝ × Space => projDivKernel α p.1 i j k p.2) := by
  simp only [projDivKernel, Real.fourierInv_eq']
  refine (StronglyMeasurable.integral_prod_right ?_).measurable
  refine Measurable.stronglyMeasurable ?_
  unfold projDivSymbol
  fun_prop

theorem kernel_integrable (hk : KernelDecayStatement) {α t : ℝ} (hα : 0 < α) (ht : 0 < t)
    (i j k : Fin 3) : Integrable (projDivKernel α t i j k) :=
  ((kernelScaling_of hk) α hα i j k t ht).2.2.1

def kernelMass (α : ℝ) : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ z, ‖projDivKernel α 1 i j k z‖

theorem kernelMass_nonneg (α : ℝ) : 0 ≤ kernelMass α := by
  unfold kernelMass
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
    integral_nonneg fun z => norm_nonneg _

theorem norm_le_three (v : Space) (c : ℝ) (h : ∀ i, ‖v i‖ ≤ c) : ‖v‖ ≤ 3 * c := by
  have hc : 0 ≤ c := (norm_nonneg _).trans (h 0)
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 3 * c)]
  refine Real.sqrt_le_sqrt ?_
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have n0 := norm_nonneg (v 0)
  have n1 := norm_nonneg (v 1)
  have n2 := norm_nonneg (v 2)
  nlinarith [mul_le_mul h0 h0 n0 hc, mul_le_mul h1 h1 n1 hc, mul_le_mul h2 h2 n2 hc]

theorem heatDivConv_norm_le (hk : KernelDecayStatement) {α t : ℝ} (hα : 0 < α) (ht : 0 < t)
    (F : Space → Fin 3 → Fin 3 → ℝ) (B : ℝ) (hB : ∀ y, ‖F y‖ ≤ B) (x : Space) :
    ‖heatDivConv α t F x‖ ≤ 3 * (B * (t ^ (-(1 / (2 * α))) * kernelMass α)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hsc := kernelScaling_of hk α hα
  have hterm : ∀ i j k : Fin 3, ‖∫ z, (projDivKernel α t i j k (x - z)).re * F z j k‖ ≤
      B * (t ^ (-(1 / (2 * α))) * ∫ z, ‖projDivKernel α 1 i j k z‖) := fun i j k => by
    have hK := kernel_integrable hk hα ht i j k
    have hg : Integrable (fun z => ‖projDivKernel α t i j k (x - z)‖ * B) :=
      ((hK.comp_sub_left x).norm).mul_const B
    refine (norm_integral_le_of_norm_le hg (Eventually.of_forall fun z => ?_)).trans (le_of_eq ?_)
    · rw [norm_mul]
      exact mul_le_mul ((Complex.abs_re_le_norm _).trans_eq' (Real.norm_eq_abs _))
        ((norm_le_pi_norm (F z j) k).trans ((norm_le_pi_norm (F z) j).trans (hB z)))
        (norm_nonneg _) (norm_nonneg _)
    · rw [integral_mul_const, integral_sub_left_eq_self (fun z => ‖projDivKernel α t i j k z‖),
        (hsc i j k t ht).2.2.2.1]
      ring
  refine norm_le_three _ _ fun i => ?_
  have hv : (heatDivConv α t F x) i = ∑ j : Fin 3, ∑ k : Fin 3,
      ∫ z, (projDivKernel α t i j k (x - z)).re * F z j k := rfl
  rw [hv]
  have hsum : ∑ j : Fin 3, ∑ k : Fin 3, ∫ z, ‖projDivKernel α 1 i j k z‖ ≤ kernelMass α := by
    unfold kernelMass
    exact Finset.single_le_sum (f := fun i : Fin 3 => ∑ j : Fin 3, ∑ k : Fin 3,
      ∫ z, ‖projDivKernel α 1 i j k z‖)
      (fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
        integral_nonneg fun z => norm_nonneg _) (Finset.mem_univ i)
  have htp : 0 ≤ t ^ (-(1 / (2 * α))) := Real.rpow_nonneg ht.le _
  calc ‖∑ j : Fin 3, ∑ k : Fin 3, ∫ z, (projDivKernel α t i j k (x - z)).re * F z j k‖
      ≤ ∑ j : Fin 3, ∑ k : Fin 3, ‖∫ z, (projDivKernel α t i j k (x - z)).re * F z j k‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, B * (t ^ (-(1 / (2 * α))) * ∫ z, ‖projDivKernel α 1 i j k z‖) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm i j k
    _ = B * (t ^ (-(1 / (2 * α))) * ∑ j : Fin 3, ∑ k : Fin 3, ∫ z, ‖projDivKernel α 1 i j k z‖) := by
        simp only [Finset.mul_sum]
    _ ≤ B * (t ^ (-(1 / (2 * α))) * kernelMass α) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum htp) hB0

theorem exp_neg_lt_one {τ : ℝ} (h : 0 < τ) : Real.exp (-τ) < 1 := by
  have h1 := Real.exp_lt_exp.mpr (show -τ < 0 by linarith)
  rwa [Real.exp_zero] at h1

theorem single_measurable (i : Fin 3) : Measurable (fun r : ℝ => EuclideanSpace.single i r) := by
  have e : (fun r : ℝ => EuclideanSpace.single i r) = fun r => r • EuclideanSpace.single i (1 : ℝ) := by
    funext r
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [e]
  exact measurable_id.smul_const _

theorem meas_rot {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℝ) (g : Ω → Space) (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun τ => axialRotation (f τ) (g τ)) := by
  simp only [axialRotationSpec.1]
  unfold axialRotationFormula
  have hc : ∀ i : Fin 3, Measurable (fun τ => (g τ) i) := fun i =>
    (EuclideanSpace.proj i).continuous.measurable.comp hg
  refine ((single_measurable 0).comp ?_).add ((single_measurable 1).comp ?_) |>.add
    ((single_measurable 2).comp (hc 2))
  · exact ((Real.measurable_cos.comp hf).mul (hc 0)).sub ((Real.measurable_sin.comp hf).mul (hc 1))
  · exact ((Real.measurable_sin.comp hf).mul (hc 0)).add ((Real.measurable_cos.comp hf).mul (hc 1))

theorem meas_heat {Ω : Type*} [MeasurableSpace Ω] (α : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ)
    (hF : Continuous F) (t : Ω → ℝ) (x : Ω → Space) (ht : Measurable t) (hx : Measurable x) :
    Measurable (fun τ => heatDivConv α (t τ) F (x τ)) := by
  unfold heatDivConv
  refine (WithLp.measurable_toLp 2 _).comp ?_
  refine measurable_pi_lambda _ fun i => ?_
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
  have hmap : Measurable (fun q : Ω × Space => (t q.1, x q.1 - q.2)) :=
    (ht.comp measurable_fst).prodMk ((hx.comp measurable_fst).sub measurable_snd)
  have hFm : Measurable (fun q : Ω × Space => F q.2 j k) :=
    ((continuous_apply k).comp ((continuous_apply j).comp hF)).measurable.comp measurable_snd
  have hm : Measurable (fun q : Ω × Space =>
      (projDivKernel α (t q.1) i j k (x q.1 - q.2)).re * F q.2 j k) :=
    (Complex.measurable_re.comp ((kernel_measurable α i j k).comp hmap)).mul hFm
  exact (StronglyMeasurable.integral_prod_right' hm.stronglyMeasurable).measurable

theorem joint_measurable (α a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (hF : Continuous F) :
    Measurable (fun p : Space × ℝ => pushForward (axialRotation (a * p.2))
        (scaleField α (Real.exp (-p.2)) (heatDivConv α (1 - Real.exp (-p.2)) F)) p.1) := by
  have hsymm : ∀ θ, (axialRotation θ).symm = axialRotation (-θ) := axialRotationSpec.2.2.2.1
  simp only [pushForward, scaleField, hsymm]
  have hx : Measurable (fun p : Space × ℝ =>
      Real.exp (-p.2) ^ (1 / (2 * α)) • axialRotation (-(a * p.2)) p.1) :=
    (by fun_prop : Measurable fun p : Space × ℝ => Real.exp (-p.2) ^ (1 / (2 * α))).smul
      (meas_rot (fun p : Space × ℝ => -(a * p.2)) (fun p => p.1) (by fun_prop) measurable_fst)
  have hH := meas_heat α F hF (fun p : Space × ℝ => 1 - Real.exp (-p.2))
    (fun p : Space × ℝ => Real.exp (-p.2) ^ (1 / (2 * α)) • axialRotation (-(a * p.2)) p.1)
    (by fun_prop) hx
  have hin : Measurable (fun p : Space × ℝ => Real.exp (-p.2) ^ (1 - 1 / (2 * α)) • heatDivConv α
      (1 - Real.exp (-p.2)) F (Real.exp (-p.2) ^ (1 / (2 * α)) • axialRotation (-(a * p.2)) p.1)) :=
    (by fun_prop : Measurable fun p : Space × ℝ => Real.exp (-p.2) ^ (1 - 1 / (2 * α))).smul hH
  exact meas_rot (fun p : Space × ℝ => a * p.2) _ (by fun_prop) hin

theorem integrand_norm_le (hk : KernelDecayStatement) {α : ℝ} (hα : 0 < α) (a : ℝ)
    (F : Space → Fin 3 → Fin 3 → ℝ) (B : ℝ) (hB : ∀ y, ‖F y‖ ≤ B) (y : Space) (τ : ℝ) (hτ0 : 0 < τ) :
    ‖pushForward (axialRotation (a * τ))
        (scaleField α (Real.exp (-τ)) (heatDivConv α (1 - Real.exp (-τ)) F)) y‖ ≤
      3 * (B * kernelMass α) * (Real.exp (-τ) ^ (1 - 1 / (2 * α)) *
          (1 - Real.exp (-τ)) ^ (-(1 / (2 * α)))) := by
  have ht : 0 < 1 - Real.exp (-τ) := sub_pos.mpr (exp_neg_lt_one hτ0)
  simp only [pushForward, scaleField, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos (-τ)).le _)]
  have hh := heatDivConv_norm_le hk hα ht F B hB
    (Real.exp (-τ) ^ (1 / (2 * α)) • (axialRotation (a * τ)).symm y)
  have he : 0 ≤ Real.exp (-τ) ^ (1 - 1 / (2 * α)) := Real.rpow_nonneg (Real.exp_pos _).le _
  calc Real.exp (-τ) ^ (1 - 1 / (2 * α)) * ‖heatDivConv α (1 - Real.exp (-τ)) F
        (Real.exp (-τ) ^ (1 / (2 * α)) • (axialRotation (a * τ)).symm y)‖
      ≤ Real.exp (-τ) ^ (1 - 1 / (2 * α)) *
          (3 * (B * ((1 - Real.exp (-τ)) ^ (-(1 / (2 * α))) * kernelMass α))) :=
        mul_le_mul_of_nonneg_left hh he
    _ = 3 * (B * kernelMass α) * (Real.exp (-τ) ^ (1 - 1 / (2 * α)) *
          (1 - Real.exp (-τ)) ^ (-(1 / (2 * α)))) := by ring

theorem one_sub_exp_ge {τ : ℝ} (h0 : 0 < τ) (h1 : τ ≤ 1) : τ / 2 ≤ 1 - Real.exp (-τ) := by
  have e1 : Real.exp (-τ) * Real.exp τ = 1 := by rw [← Real.exp_add]; simp
  have h2 := Real.add_one_le_exp τ
  have h3 := Real.exp_pos (-τ)
  nlinarith [mul_le_mul_of_nonneg_left h2 h3.le]

theorem weight_integrable {α : ℝ} (hα1 : 1 < α) :
    IntegrableOn (fun τ : ℝ => Real.exp (-τ) ^ (1 - 1 / (2 * α)) *
      (1 - Real.exp (-τ)) ^ (-(1 / (2 * α)))) (Ioi 0) := by
  set s : ℝ := 1 / (2 * α) with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs1 : s < 1 := by rw [hs, div_lt_one (by linarith)]; linarith
  have hmeas : Measurable (fun τ : ℝ => Real.exp (-τ) ^ (1 - s) * (1 - Real.exp (-τ)) ^ (-s)) := by
    fun_prop
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hint : IntegrableOn (fun τ : ℝ => τ ^ (-s)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine (hint.const_mul 2).mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun τ hτ => ?_)
    have hτ0 : 0 < τ := hτ.1
    have hge := one_sub_exp_ge hτ0 hτ.2
    have hp : 0 < 1 - Real.exp (-τ) := by linarith
    have ha : Real.exp (-τ) ^ (1 - s) ≤ 1 :=
      Real.rpow_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith)) (by linarith)
    have hb : (1 - Real.exp (-τ)) ^ (-s) ≤ (2⁻¹ * τ) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have hc : (2⁻¹ * τ) ^ (-s) = (2 : ℝ) ^ s * τ ^ (-s) := by
      rw [Real.mul_rpow (by norm_num) hτ0.le, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num),
        inv_inv]
    have hd : (2 : ℝ) ^ s ≤ 2 := by
      calc (2 : ℝ) ^ s ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1.le
        _ = 2 := Real.rpow_one 2
    have hn : 0 ≤ Real.exp (-τ) ^ (1 - s) * (1 - Real.exp (-τ)) ^ (-s) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    have hτs : 0 ≤ τ ^ (-s) := Real.rpow_nonneg hτ0.le _
    have hq : 0 ≤ (1 - Real.exp (-τ)) ^ (-s) := Real.rpow_nonneg hp.le _
    calc Real.exp (-τ) ^ (1 - s) * (1 - Real.exp (-τ)) ^ (-s) ≤ 1 * (1 - Real.exp (-τ)) ^ (-s) :=
          mul_le_mul_of_nonneg_right ha hq
      _ ≤ 1 * ((2 : ℝ) ^ s * τ ^ (-s)) := by rw [← hc]; linarith
      _ ≤ 2 * τ ^ (-s) := by nlinarith
  · have hc : 0 < 1 - s := by linarith
    have hint := (exp_neg_integrableOn_Ioi 1 hc).const_mul ((1 - Real.exp (-1)) ^ (-s))
    refine hint.mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
    have hτ1 : 1 < τ := hτ
    have hp1 : 0 < 1 - Real.exp (-1) := sub_pos.mpr (exp_neg_lt_one (by norm_num))
    have hle : Real.exp (-τ) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have hb : (1 - Real.exp (-τ)) ^ (-s) ≤ (1 - Real.exp (-1)) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hp1 (by linarith) (by linarith)
    have he : Real.exp (-τ) ^ (1 - s) = Real.exp (-(1 - s) * τ) := by
      rw [← Real.exp_mul]; ring_nf
    have hn : 0 ≤ Real.exp (-τ) ^ (1 - s) * (1 - Real.exp (-τ)) ^ (-s) := by
      have : 0 < 1 - Real.exp (-τ) := by linarith [Real.exp_pos (-1)]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hn, he, mul_comm]
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le


theorem symbol_continuousAt (α t : ℝ) (hα : 0 < α) (i j k : Fin 3) {η : Space} (hη : η ≠ 0) :
    ContinuousAt (projDivSymbol α t i j k) η := by
  have hn : ‖η‖ ^ 2 ≠ 0 := by positivity
  unfold projDivSymbol
  have h1 : ContinuousAt (fun ξ : Space => (2 * π * ‖ξ‖) ^ (2 * α)) η :=
    ContinuousAt.rpow_const (by fun_prop) (Or.inr (by linarith))
  have h2 : ContinuousAt (fun ξ : Space => ξ i * ξ j / ‖ξ‖ ^ 2) η :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hn
  fun_prop

theorem kernel_pairing_step (hk : KernelDecayStatement) (α t : ℝ) (hα : 0 < α) (ht : 0 < t) (i j k : Fin 3)
    (z : Space) (c : ℝ) (hc : 0 < c) (R : Space ≃ₗᵢ[ℝ] Space) (Q : Space → ℂ) (hQc : Continuous Q)
    (hQs : HasCompactSupport Q) (hQ0 : Q 0 = 0) :
    Integrable (fun ξ => Q ξ * (Complex.exp ((2 * π * inner ℝ (c • R.symm ξ) z : ℝ) * Complex.I) *
        projDivSymbol α t i j k (-(c • R.symm ξ)))) ∧
    ∫ x, projDivKernel α t i j k (x - z) * 𝓕⁻ Q (R (c • x)) =
      ∫ ξ, Q ξ * (Complex.exp ((2 * π * inner ℝ (c • R.symm ξ) z : ℝ) * Complex.I) *
        projDivSymbol α t i j k (-(c • R.symm ξ))) := by
  set K := projDivKernel α t i j k with hK
  set m := projDivSymbol α t i j k with hm
  have hKi : Integrable K := ((kernelScaling_of hk) α hα i j k t ht).2.2.1
  have hKc : Continuous K := (KernelDecayInternal.kernel_contDiff α t hα ht i j k).continuous
  have hQi : Integrable Q := hQc.integrable_of_hasCompactSupport hQs
  have hmi : Integrable m := by
    have h := KernelDecayInternal.symbol_moment α t hα ht i j k 0
    simp only [pow_zero, one_mul] at h
    exact (integrable_norm_iff (KernelDecayInternal.symbol_measurable α t i j k).aestronglyMeasurable).1 h
  have hFm : Integrable (𝓕 m) := by
    refine (hKi.comp_neg).congr (Eventually.of_forall fun x => ?_)
    show 𝓕⁻ m (-x) = 𝓕 m x
    rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  have hinv : ∀ w : Space, w ≠ 0 → 𝓕⁻ K w = m (-w) := by
    intro w hw
    have eK : K = 𝓕⁻ m := rfl
    rw [eK, Real.fourierInv_eq_fourier_neg]
    exact hmi.fourier_fourierInv_eq hFm (symbol_continuousAt α t hα i j k (neg_ne_zero.2 hw))
  have hE : ∀ (ξ x : Space), inner ℝ ξ (R (c • x)) = inner ℝ (c • R.symm ξ) x := by
    intro ξ x
    rw [real_inner_comm, LinearIsometryEquiv.inner_map_eq_flip, real_inner_smul_left,
      real_inner_smul_left, real_inner_comm]
  set f : Space → Space → ℂ := fun x ξ => K (x - z) *
    (Complex.exp ((2 * π * inner ℝ (c • R.symm ξ) x : ℝ) * Complex.I) * Q ξ) with hf
  have hexp : ∀ r : ℝ, ‖Complex.exp ((r : ℂ) * Complex.I)‖ = 1 := fun r => Complex.norm_exp_ofReal_mul_I r
  have hfi : Integrable (Function.uncurry f) (volume.prod volume) := by
    have hb : Integrable (fun p : Space × Space => ‖K (p.1 - z)‖ * ‖Q p.2‖) (volume.prod volume) :=
      (hKi.comp_sub_right z).norm.mul_prod hQi.norm
    refine hb.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hc1 : Continuous (Function.uncurry f) := by
        simp only [hf, Function.uncurry_def]
        fun_prop
      exact hc1.aestronglyMeasurable
    · simp only [Function.uncurry, hf]
      rw [norm_mul, norm_mul, hexp, one_mul]
  have hLHS : ∀ x, K (x - z) * 𝓕⁻ Q (R (c • x)) = ∫ ξ, f x ξ := by
    intro x
    rw [Real.fourierInv_eq', ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hf, smul_eq_mul, hE]
  have hinner : ∀ ξ, ∫ x, f x ξ = Q ξ * (Complex.exp ((2 * π * inner ℝ (c • R.symm ξ) z : ℝ) * Complex.I) *
        m (-(c • R.symm ξ))) := by
    intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      simp [hf, hQ0]
    have hw : c • R.symm ξ ≠ 0 := smul_ne_zero hc.ne' (by simpa using hξ)
    set w := c • R.symm ξ with hwdef
    have e1 : ∫ x, f x ξ = ∫ x, (fun u => K u * (Complex.exp ((2 * π * inner ℝ w (u + z) : ℝ) * Complex.I) * Q ξ)) (x - z) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hf, sub_add_cancel, hwdef]
    rw [e1, integral_sub_right_eq_self (fun u => K u * (Complex.exp ((2 * π * inner ℝ w (u + z) : ℝ) * Complex.I) * Q ξ)) z]
    have e2 : ∀ u, K u * (Complex.exp ((2 * π * inner ℝ w (u + z) : ℝ) * Complex.I) * Q ξ) =
        (Q ξ * Complex.exp ((2 * π * inner ℝ w z : ℝ) * Complex.I)) *
          (Complex.exp ((2 * π * inner ℝ u w : ℝ) * Complex.I) • K u) := by
      intro u
      rw [inner_add_right, real_inner_comm u w, smul_eq_mul]
      push_cast
      rw [mul_add, add_mul, Complex.exp_add]
      ring
    simp_rw [e2]
    rw [integral_const_mul, ← Real.fourierInv_eq', hinv w hw]
    ring
  refine ⟨?_, ?_⟩
  · refine hfi.integral_prod_right.congr (Eventually.of_forall fun ξ => ?_)
    exact hinner ξ
  · simp_rw [hLHS]
    rw [integral_integral_swap hfi]
    exact integral_congr_ae (Eventually.of_forall hinner)


theorem real_contract (η : Space) (j : Fin 3) :
    ∑ i : Fin 3, ((if i = j then (1 : ℝ) else 0) - η i * η j / ‖η‖ ^ 2) * η i = 0 := by
  by_cases hη : η = 0
  · subst hη; simp
  have hn : ‖η‖ ^ 2 = η 0 ^ 2 + η 1 ^ 2 + η 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp [sq_abs]
  have hp : ‖η‖ ^ 2 ≠ 0 := by
    have : 0 < ‖η‖ := norm_pos_iff.2 hη
    positivity
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Fin.sum_univ_three]
  rw [sub_eq_zero]
  field_simp
  rw [hn]

theorem symbol_contract (α t : ℝ) (j k : Fin 3) (η : Space) :
    ∑ i : Fin 3, projDivSymbol α t i j k η * ((η i : ℝ) : ℂ) = 0 := by
  have h := real_contract η j
  have e : ∀ i : Fin 3, projDivSymbol α t i j k η * ((η i : ℝ) : ℂ) =
      (((2 * π * η k : ℝ) : ℂ) * Complex.I * ((Real.exp (-(t * (2 * π * ‖η‖) ^ (2 * α))) : ℝ) : ℂ)) *
        ((((if i = j then (1 : ℝ) else 0) - η i * η j / ‖η‖ ^ 2) * η i : ℝ) : ℂ) := by
    intro i
    unfold projDivSymbol
    push_cast
    ring
  simp_rw [e]
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, h, Complex.ofReal_zero, mul_zero]

theorem symm_apply_eq_sum (R : Space ≃ₗᵢ[ℝ] Space) (v : Space) (i : Fin 3) :
    (R.symm v) i = ∑ l : Fin 3, (R (unitVector i)) l * v l := by
  have h1 : (R.symm v) i = inner ℝ (R.symm v) (unitVector i) := by
    simp [unitVector, EuclideanSpace.inner_single_right]
  rw [h1, LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_symm, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [mul_comm]

theorem inverse_transform_norm_le (Q : Space → ℂ) (y : Space) : ‖𝓕⁻ Q y‖ ≤ ∫ ξ, ‖Q ξ‖ := by
  rw [Real.fourierInv_eq']
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun ξ => ?_)))
  simp only [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem kernel_core (hk : KernelDecayStatement) {α t : ℝ} (hα : 0 < α) (ht : 0 < t) (j k : Fin 3)
    (z : Space) {c : ℝ} (hc : 0 < c) (R : Space ≃ₗᵢ[ℝ] Space) (q : Space → CSpace)
    (hqs : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) (hqf : ∃ c' : Space → ℂ, ∀ ξ, q ξ = c' ξ • freqVec ξ) :
    ∑ i : Fin 3, ∫ x, (projDivKernel α t i j k (x - z)).re * (R.symm (physField q (R (c • x)))) i = 0 := by
  obtain ⟨c', hc'⟩ := hqf
  have hqi : Integrable q := hqs.continuous.integrable_of_hasCompactSupport hqc
  have hql : ∀ ξ (l : Fin 3), q ξ l = c' ξ * ((ξ l : ℝ) : ℂ) := by
    intro ξ l
    rw [hc']
    simp [freqVec, complexifyVec]
  set Q : Fin 3 → Space → ℂ := fun l ξ => q ξ l with hQ
  have hQs : ∀ l, ContDiff ℝ ∞ (Q l) := fun l =>
    ((EuclideanSpace.proj l : CSpace →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hqs
  have hQc : ∀ l, HasCompactSupport (Q l) := fun l => by
    show HasCompactSupport ((fun w : CSpace => w l) ∘ q)
    exact hqc.comp_left (by simp)
  have hQ0 : ∀ l, Q l 0 = 0 := fun l => by simp [hQ, hql]
  have hFQ : ∀ l, Continuous (𝓕⁻ (Q l)) := fun l => by
    have h := SchwartzMap.fourierInv_coe ((hQc l).toSchwartzMap (hQs l))
    have e : ⇑((hQc l).toSchwartzMap (hQs l)) = Q l := rfl
    rw [e] at h
    rw [← h]
    exact SchwartzMap.continuous _
  have hcomp : ∀ y (l : Fin 3), (physField q y) l = (𝓕⁻ (Q l) y).re := by
    intro y l
    show (𝓕⁻ q y l).re = _
    rw [SmoothFlow.Internal.ConvProduct.freqTrInv_apply_eq hqi]
  set r : Fin 3 → Fin 3 → ℝ := fun i l => (R (unitVector i)) l with hr
  have hreal : ∀ i x, (projDivKernel α t i j k x).im = 0 := fun i x =>
    ((kernelScaling_of hk) α hα i j k t ht).2.1 x
  set G : Fin 3 → Space → ℂ := fun i x => ∑ l : Fin 3, (r i l : ℂ) *
    (projDivKernel α t i j k (x - z) * 𝓕⁻ (Q l) (R (c • x))) with hG
  have hpt : ∀ i x, (projDivKernel α t i j k (x - z)).re * (R.symm (physField q (R (c • x)))) i =
      (G i x).re := by
    intro i x
    rw [symm_apply_eq_sum]
    simp only [hG, hcomp, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.re_ofReal_mul, Complex.mul_re, hreal, zero_mul, sub_zero]
    ring
  have hGi : ∀ i l, Integrable (fun x => projDivKernel α t i j k (x - z) * 𝓕⁻ (Q l) (R (c • x))) := by
    intro i l
    refine (((kernelScaling_of hk) α hα i j k t ht).2.2.1.comp_sub_right z).mul_bdd
      (c := ∫ ξ, ‖Q l ξ‖) ?_ (Eventually.of_forall fun x => inverse_transform_norm_le _ _)
    exact ((hFQ l).comp (R.continuous.comp (continuous_const_smul c))).aestronglyMeasurable
  have hGi' : ∀ i, Integrable (G i) := fun i =>
    integrable_finsetSum _ fun l _ => (hGi i l).const_mul _
  simp_rw [hpt]
  have hre : ∀ i, ∫ x, (G i x).re = (∫ x, G i x).re := fun i => integral_re (hGi' i)
  simp_rw [hre]
  rw [← Complex.re_sum]
  set η : Space → Space := fun ξ => -(c • R.symm ξ) with hη
  set E : Space → ℂ := fun ξ => Complex.exp ((2 * π * inner ℝ (c • R.symm ξ) z : ℝ) * Complex.I) with hE
  have hFS := fun i l => kernel_pairing_step hk α t hα ht i j k z c hc R (Q l) (hQs l).continuous (hQc l) (hQ0 l)
  have hsum : ∑ i : Fin 3, ∫ x, G i x =
      ∫ ξ, ∑ i : Fin 3, ∑ l : Fin 3, (r i l : ℂ) * (Q l ξ * (E ξ * projDivSymbol α t i j k (η ξ))) := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => (hFS i l).1.const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun l _ => (hGi i l).const_mul _,
      integral_finsetSum _ fun l _ => (hFS i l).1.const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, integral_const_mul, (hFS i l).2]
  have hz : ∀ ξ, ∑ i : Fin 3, ∑ l : Fin 3, (r i l : ℂ) * (Q l ξ * (E ξ * projDivSymbol α t i j k (η ξ))) = 0 := by
    intro ξ
    have e1 : ∀ i, ∑ l : Fin 3, (r i l : ℂ) * (Q l ξ * (E ξ * projDivSymbol α t i j k (η ξ))) =
        (E ξ * c' ξ * (-(c : ℂ)⁻¹)) * (projDivSymbol α t i j k (η ξ) * (((η ξ) i : ℝ) : ℂ)) := by
      intro i
      have hs : (((R.symm ξ) i : ℝ) : ℂ) = ∑ l : Fin 3, (r i l : ℂ) * ((ξ l : ℝ) : ℂ) := by
        rw [symm_apply_eq_sum]
        push_cast
        rfl
      have hηi : (((η ξ) i : ℝ) : ℂ) = -(c : ℂ) * (((R.symm ξ) i : ℝ) : ℂ) := by
        simp [hη]
      have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
      rw [hηi, hs]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hQ, hql]
      field_simp
    simp_rw [e1]
    rw [← Finset.mul_sum, symbol_contract, mul_zero]
  rw [hsum]
  simp_rw [hz]
  simp

theorem conv_pair_zero (hk : KernelDecayStatement) {α t : ℝ} (hα : 0 < α) (ht : 0 < t) {c : ℝ}
    (hc : 0 < c) (R : Space ≃ₗᵢ[ℝ] Space) (F : Space → Fin 3 → Fin 3 → ℝ) (B : ℝ) (hF : Continuous F)
    (hB : ∀ y, ‖F y‖ ≤ B) (q : Space → CSpace) (hqs : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    (hqf : ∃ c' : Space → ℂ, ∀ ξ, q ξ = c' ξ • freqVec ξ) :
    ∫ x, inner ℝ (heatDivConv α t F x) (R.symm (physField q (R (c • x)))) = 0 := by
  let M := hqc.toSchwartzMap hqs
  have eq' : physField q = fun y => realVec ((𝓕⁻ M) y) := WeakRegularInternal.physField_of_rapid M rfl
  have hgc : Continuous (physField q) := by
    rw [eq']
    exact realVec.continuous.comp (𝓕⁻ M).continuous
  have hgi : Integrable (physField q) := by
    rw [eq']
    exact realVec.integrable_comp ((𝓕⁻ M).integrable (μ := volume))
  set ψ : Space → Space := fun x => R.symm (physField q (R (c • x))) with hψ
  have hψc : Continuous ψ := R.symm.continuous.comp (hgc.comp (R.continuous.comp (continuous_const_smul c)))
  have hψi : Integrable ψ := by
    have h1 : Integrable (fun y => physField q (R y)) :=
      (R.measurePreserving.integrable_comp_emb R.toHomeomorph.measurableEmbedding).2 hgi
    have h2 : Integrable (fun x => physField q (R (c • x))) := h1.comp_smul hc.ne'
    exact ((R.symm.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space).integrable_comp h2
  have hψii : ∀ i : Fin 3, Integrable (fun x => ψ x i) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hψi
  have hψci : ∀ i : Fin 3, Continuous (fun x => ψ x i) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hψc
  have hKi : ∀ i j k : Fin 3, Integrable (projDivKernel α t i j k) := fun i j k =>
    ((kernelScaling_of hk) α hα i j k t ht).2.2.1
  have hKc : ∀ i j k : Fin 3, Continuous (projDivKernel α t i j k) := fun i j k =>
    (KernelDecayInternal.kernel_contDiff α t hα ht i j k).continuous
  set H : Fin 3 → Fin 3 → Fin 3 → Space × Space → ℝ := fun i j k p =>
    (projDivKernel α t i j k (p.1 - p.2)).re * F p.2 j k * ψ p.1 i with hH
  have hHi : ∀ i j k, Integrable (H i j k) (volume.prod volume) := by
    intro i j k
    have hprod : Integrable (fun p : Space × Space => ‖ψ p.1 i‖ * ‖projDivKernel α t i j k (p.1 - p.2)‖)
        (volume.prod volume) := by
      rw [integrable_prod_iff (by
        have : Continuous (fun p : Space × Space => ‖ψ p.1 i‖ * ‖projDivKernel α t i j k (p.1 - p.2)‖) := by
          have := hKc i j k
          have := hψci i
          fun_prop
        exact this.aestronglyMeasurable)]
      refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
      · exact ((hKi i j k).comp_sub_left x).norm.const_mul ‖ψ x i‖
      have e : ∀ x, ∫ z, ‖‖ψ x i‖ * ‖projDivKernel α t i j k (x - z)‖‖ =
          ‖ψ x i‖ * ∫ z, ‖projDivKernel α t i j k z‖ := by
        intro x
        simp only [norm_mul, norm_norm]
        rw [integral_const_mul, integral_sub_left_eq_self (fun z => ‖projDivKernel α t i j k z‖)]
      simp_rw [e]
      exact (hψii i).norm.mul_const _
    refine (hprod.const_mul B).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have : Continuous (H i j k) := by
        have h1 := hKc i j k
        have h2 := hψci i
        have h3 : Continuous (fun y => F y j k) := (continuous_apply k).comp ((continuous_apply j).comp hF)
        simp only [hH]
        fun_prop
      exact this.aestronglyMeasurable
    · simp only [hH, norm_mul]
      have hF' : ‖F p.2 j k‖ ≤ B := (norm_le_pi_norm (F p.2 j) k).trans ((norm_le_pi_norm (F p.2) j).trans (hB p.2))
      have hre : ‖(projDivKernel α t i j k (p.1 - p.2)).re‖ ≤ ‖projDivKernel α t i j k (p.1 - p.2)‖ :=
        (Complex.abs_re_le_norm _).trans_eq' (Real.norm_eq_abs _)
      calc ‖(projDivKernel α t i j k (p.1 - p.2)).re‖ * ‖F p.2 j k‖ * ‖ψ p.1 i‖
          ≤ ‖projDivKernel α t i j k (p.1 - p.2)‖ * B * ‖ψ p.1 i‖ := by gcongr
        _ = B * (‖ψ p.1 i‖ * ‖projDivKernel α t i j k (p.1 - p.2)‖) := by ring
  have hx : ∀ x, inner ℝ (heatDivConv α t F x) (ψ x) =
      ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, ∫ z, H i j k (x, z) := by
    intro x
    have hv : ∀ i, (heatDivConv α t F x) i = ∑ j : Fin 3, ∑ k : Fin 3,
        ∫ z, (projDivKernel α t i j k (x - z)).re * F z j k := fun i => rfl
    have hin : ∀ a b : ℝ, inner ℝ a b = a * b := fun a b => by
      rw [RCLike.inner_apply, conj_trivial, mul_comm]
    rw [PiLp.inner_apply]
    simp only [hv, hin, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_mul_const]
  refine (integral_congr_ae (Eventually.of_forall hx)).trans ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => integrable_finsetSum _
    fun i _ => (hHi i j k).integral_prod_left]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ => (hHi i j k).integral_prod_left]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_finsetSum _ fun i _ => (hHi i j k).integral_prod_left]
  have hswap : ∀ i, ∫ x, ∫ z, H i j k (x, z) = ∫ z, F z j k * ∫ x, (projDivKernel α t i j k (x - z)).re * ψ x i := by
    intro i
    rw [integral_integral_swap (hHi i j k)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hH]
    ring
  simp_rw [hswap]
  have hI : ∀ i, Integrable (fun z => F z j k * ∫ x, (projDivKernel α t i j k (x - z)).re * ψ x i) := by
    intro i
    refine ((hHi i j k).swap.integral_prod_left).congr (Eventually.of_forall fun z => ?_)
    dsimp only [Function.comp, Prod.swap]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hH]
    ring
  rw [← integral_finsetSum _ fun i _ => hI i]
  have hz : ∀ z, ∑ i : Fin 3, F z j k * ∫ x, (projDivKernel α t i j k (x - z)).re * ψ x i = 0 := by
    intro z
    rw [← Finset.mul_sum, kernel_core hk hα ht j k z hc R q hqs hqc hqf, mul_zero]
  simp_rw [hz]
  simp


open FarFieldGradientFreeInternal in
theorem farFieldTimeSplit (hk : KernelDecayStatement) : FarFieldTimeSplitStatement := by
  intro α h1 h2 a F B hF hB g hgc hgi
  have hα : 0 < α := by linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set Φ : ℝ → Space → Space := fun τ y => pushForward (axialRotation (a * τ))
    (scaleField α (Real.exp (-τ)) (heatDivConv α (1 - Real.exp (-τ)) F)) y with hΦ
  set w : ℝ → ℝ := fun τ => 3 * (B * kernelMass α) * (Real.exp (-τ) ^ (1 - 1 / (2 * α)) *
    (1 - Real.exp (-τ)) ^ (-(1 / (2 * α)))) with hw
  have hwi : IntegrableOn w (Ioi 0) := (weight_integrable h1).const_mul _
  have hmeas := joint_measurable α a F hF
  have hΦi : ∀ y, IntegrableOn (fun τ => Φ τ y) (Ioi 0) := by
    intro y
    refine hwi.mono' ((hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
    exact integrand_norm_le hk hα a F B hB y τ hτ
  have e1 : ∀ y, inner ℝ (farFieldOp α a F y) (g y) = -∫ τ in Ioi (0 : ℝ), inner ℝ (Φ τ y) (g y) := by
    intro y
    simp only [farFieldOp]
    rw [inner_neg_left, real_inner_comm, ← integral_inner (hΦi y)]
    simp_rw [real_inner_comm (g y)]
  simp_rw [e1]
  rw [integral_neg]
  congr 1
  refine integral_integral_swap ?_
  have hprod : Integrable (fun p : Space × ℝ => ‖g p.1‖ * w p.2) (volume.prod (volume.restrict (Ioi 0))) :=
    hgi.norm.mul_prod hwi
  refine hprod.mono' ?_ ?_
  · exact ((hmeas.inner (hgc.measurable.comp measurable_fst))).aestronglyMeasurable
  · have hr : volume.prod (volume.restrict (Ioi (0 : ℝ))) =
        ((volume : Measure Space).prod volume).restrict (univ ×ˢ Ioi 0) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hr, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ioi)]
    refine Eventually.of_forall fun p hp => ?_
    have hτ : 0 < p.2 := hp.2
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [mul_comm (‖g p.1‖)]
    exact mul_le_mul_of_nonneg_right (integrand_norm_le hk hα a F B hB p.1 p.2 hτ) (norm_nonneg _)

open FarFieldGradientFreeInternal in
theorem heatDivGradientFree (hk : KernelDecayStatement) : HeatDivGradientFreeStatement := by
  intro α hα t μ ht hμ R F B hF hB q hqs hqc hqf
  have hP : 0 < μ ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hμ _
  set l := μ ^ (1 / (2 * α)) with hl
  have key := conv_pair_zero hk (α := α) (t := t) (by linarith) ht (inv_pos.2 hP) R F B hF hB q hqs hqc hqf
  have e1 : ∀ w, inner ℝ (pushForward R (scaleField α μ (heatDivConv α t F)) (R w)) (physField q (R w)) =
      μ ^ (1 - 1 / (2 * α)) *
        (fun x => inner ℝ (heatDivConv α t F x) (R.symm (physField q (R (l⁻¹ • x))))) (l • w) := by
    intro w
    simp only [pushForward, scaleField, LinearIsometryEquiv.symm_apply_apply]
    rw [LinearIsometryEquiv.inner_map_eq_flip, real_inner_smul_left, smul_smul, inv_mul_cancel₀ hP.ne',
      one_smul]
  rw [← R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding]
  refine (integral_congr_ae (Eventually.of_forall e1)).trans ?_
  rw [integral_const_mul, Measure.integral_comp_smul (volume : Measure Space)
    (fun x => inner ℝ (heatDivConv α t F x) (R.symm (physField q (R (l⁻¹ • x))))) l, key, smul_zero,
    mul_zero]

end FarFieldGradientFreeInternal

open FarFieldGradientFreeInternal in
theorem farFieldGradientFree (hk : KernelDecayStatement) : FarFieldGradientFreeStatement := by
  intro α h1 h2 a U hM q _ hqs hqc _ hqf
  obtain ⟨C, hC0, hC⟩ := profileField_bounded U hM
  let M := hqc.toSchwartzMap hqs
  have eq' : physField q = fun y => realVec ((𝓕⁻ M) y) := WeakRegularInternal.physField_of_rapid M rfl
  have hgc : Continuous (physField q) := by
    rw [eq']
    exact realVec.continuous.comp (𝓕⁻ M).continuous
  have hgi : Integrable (physField q) := by
    rw [eq']
    exact realVec.integrable_comp ((𝓕⁻ M).integrable (μ := volume))
  rw [farFieldTimeSplit hk α h1 h2 a _ (C * C) (tensorSq_continuous (profileField_continuous U hM))
    (tensorSq_norm_le hC0 hC) _ hgc hgi]
  have hz : ∀ τ ∈ Ioi (0 : ℝ), ∫ y, inner ℝ (pushForward (axialRotation (a * τ))
      (scaleField α (Real.exp (-τ)) (heatDivConv α (1 - Real.exp (-τ)) (tensorSq (profileField U)))) y)
        (physField q y) = 0 := by
    intro τ hτ
    have ht : 0 < 1 - Real.exp (-τ) := by
      have : Real.exp (-τ) < 1 := Real.exp_lt_one_iff.2 (by simp only [mem_Ioi] at hτ; linarith)
      linarith
    exact heatDivGradientFree hk α h1 _ _ ht (Real.exp_pos _) _ _ (C * C) (tensorSq_continuous (profileField_continuous U hM))
      (tensorSq_norm_le hC0 hC) q hqs hqc hqf
  rw [setIntegral_congr_fun measurableSet_Ioi hz]
  simp

end Breakdown.FracCert
