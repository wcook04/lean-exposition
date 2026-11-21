import Breakdown.Cert.Basic
import Breakdown.FreqTr.Realization
import Breakdown.Torus.HeatDivFreeCont

open scoped ENNReal Topology Real
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

open Freq

def propagatorBound : ℝ :=
  ∫ τ in Set.Ioi 0, Real.exp (-τ / 4) * (2 * Real.exp 1 * (1 - Real.exp (-τ))) ^ (-(1 / 2 : ℝ))

namespace GradInv.Internal

def kernel (τ : ℝ) : ℝ := Real.exp (-τ / 4) * (2 * Real.exp 1 * (1 - Real.exp (-τ))) ^ (-(1 / 2 : ℝ))

theorem one_sub_exp_pos {τ : ℝ} (hτ : 0 < τ) : 0 < 1 - Real.exp (-τ) := by
  have h := Real.exp_lt_exp.mpr (show -τ < 0 by linarith)
  rw [Real.exp_zero] at h
  linarith

theorem rpow_neg_half_eq {y : ℝ} (hy : 0 ≤ y) : y ^ (-(1 / 2 : ℝ)) = (Real.sqrt y)⁻¹ := by
  rw [Real.rpow_neg hy, Real.sqrt_eq_rpow]

theorem phiFactor_sq_le_sharp {t : ℝ} (ht : 0 < t) (ξ : Space) :
    phiFactor t ξ ^ 2 ≤ (2 * Real.exp 1 * t)⁻¹ := by
  have hx : Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) ^ 2 = Real.exp (-(8 * π ^ 2 * t * ‖ξ‖ ^ 2)) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have e1 : phiFactor t ξ ^ 2 =
      (8 * π ^ 2 * t * ‖ξ‖ ^ 2) * Real.exp (-(8 * π ^ 2 * t * ‖ξ‖ ^ 2)) / (2 * t) := by
    unfold phiFactor
    rw [mul_pow, hx, eq_div_iff (by positivity)]
    ring
  have e2 : (2 * Real.exp 1 * t)⁻¹ = Real.exp (-1) / (2 * t) := by
    rw [Real.exp_neg, div_eq_mul_inv, ← mul_inv]
    ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right (Real.mul_exp_neg_le_exp_neg_one _) (by positivity)

theorem abs_phiFactor_le {t : ℝ} (ht : 0 < t) (ξ : Space) :
    |phiFactor t ξ| ≤ (2 * Real.exp 1 * t) ^ (-(1 / 2 : ℝ)) := by
  have hc : 0 < 2 * Real.exp 1 * t := by positivity
  have h0 : 0 ≤ phiFactor t ξ := Freq.Internal.Phi.phiFactor_nonneg (τ := t) ξ
  rw [rpow_neg_half_eq hc.le, ← Real.sqrt_inv, abs_of_nonneg h0, ← Real.sqrt_sq h0]
  exact Real.sqrt_le_sqrt (phiFactor_sq_le_sharp ht ξ)

theorem phiFactor_neg (t : ℝ) (ξ : Space) : phiFactor t (-ξ) = phiFactor t ξ := by
  simp only [phiFactor, norm_neg]

theorem smoothH_mem {t : ℝ} (ht : 0 < t) : ∀ x ∈ Sig,
    fieldOp id (fun ξ => phiFactor t ξ • ContinuousLinearMap.id ℝ CSpace) x ∈ Sig :=
  fun _ hx => Freq.Internal.Phi.scalarOp_mem fieldOpRealized (Freq.Internal.Phi.continuous_phiFactor t)
    (Freq.Internal.Phi.phiFactor_le ht) (phiFactor_neg t) hx

theorem smoothH_coe {t : ℝ} (ht : 0 < t) (x : HBar) :
    (smoothH t x : L2C) = fieldOp id (fun ξ => phiFactor t ξ • ContinuousLinearMap.id ℝ CSpace) x :=
  restrictX_coe (smoothH_mem ht) x

theorem norm_dilX_le_one {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) : ‖dilX μ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [dilation_holds.1 μ hμ x]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_one hμ.le hμ1 (by norm_num)) (norm_nonneg _)

end GradInv.Internal

open GradInv.Internal

theorem norm_smoothH_le (t : ℝ) (ht : 0 < t) (x : HBar) :
    ‖smoothH t x‖ ≤ (2 * Real.exp 1 * t) ^ (-(1 / 2 : ℝ)) * ‖x‖ := by
  have h := Freq.Internal.Phi.scalarOp_norm_le fieldOpRealized
    (Freq.Internal.Phi.continuous_phiFactor t) (abs_phiFactor_le ht) (x : L2C)
  rw [← smoothH_coe ht] at h
  exact h

theorem norm_slicePropagator_le (τ : ℝ) (hτ : 0 < τ) (x : HBar) :
    ‖slicePropagator τ x‖ ≤
      Real.exp (-τ / 4) * (2 * Real.exp 1 * (1 - Real.exp (-τ))) ^ (-(1 / 2 : ℝ)) * ‖x‖ := by
  have h1 := one_sub_exp_pos hτ
  have hd := dilation_holds.1 (Real.exp (-τ)) (Real.exp_pos _) (smoothH (1 - Real.exp (-τ)) x)
  have he : Real.exp (-τ) ^ (1 / 4 : ℝ) = Real.exp (-τ / 4) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [slicePropagator, ContinuousLinearMap.comp_apply, hd, he, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_smoothH_le _ h1 x) (Real.exp_pos _).le

namespace GradInv.Internal

theorem kernel_pos {τ : ℝ} (hτ : 0 < τ) : 0 < kernel τ :=
  mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (mul_pos (by positivity) (one_sub_exp_pos hτ)) _)

theorem continuousOn_kernel : ContinuousOn kernel (Ioi 0) := by
  have hc : Continuous fun τ : ℝ => 2 * Real.exp 1 * (1 - Real.exp (-τ)) := by fun_prop
  unfold kernel
  refine (Continuous.continuousOn (by fun_prop)).mul
    (hc.continuousOn.rpow_const fun τ hτ => Or.inl ?_)
  exact (mul_pos (by positivity) (one_sub_exp_pos hτ)).ne'

theorem inv_le_inv_add_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : b ^ 2 ≤ a ^ 2 * (1 + b ^ 2)) :
    a⁻¹ ≤ b⁻¹ + 1 := by
  have hs : 0 < b + a * (1 + b) := by positivity
  have key : b ≤ a * (1 + b) := by
    nlinarith [mul_pos ha hb, mul_pos (mul_pos ha ha) hb]
  have e : b⁻¹ + 1 = (1 + b) / b := by
    rw [eq_div_iff hb.ne', add_mul, inv_mul_cancel₀ hb.ne', one_mul]
  rw [e, inv_eq_one_div, div_le_div_iff₀ ha hb]
  nlinarith

theorem kernel_le {τ : ℝ} (hτ : 0 < τ) :
    kernel τ ≤ τ ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 4) * τ) + Real.exp (-(1 / 4) * τ) := by
  have h1 := one_sub_exp_pos hτ
  have hy0 : 0 < 2 * Real.exp 1 * (1 - Real.exp (-τ)) := mul_pos (by positivity) h1
  have hEt : Real.exp (-τ) * (1 + τ) ≤ 1 := by
    calc Real.exp (-τ) * (1 + τ) ≤ Real.exp (-τ) * Real.exp τ :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp τ]) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have he1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hyt : τ ≤ 2 * Real.exp 1 * (1 - Real.exp (-τ)) * (1 + τ) := by
    nlinarith [mul_pos h1 (show 0 < 1 + τ by linarith)]
  have hA : (2 * Real.exp 1 * (1 - Real.exp (-τ))) ^ (-(1 / 2 : ℝ)) ≤ τ ^ (-(1 / 2 : ℝ)) + 1 := by
    rw [rpow_neg_half_eq hy0.le, rpow_neg_half_eq hτ.le]
    refine inv_le_inv_add_one (Real.sqrt_pos.mpr hy0) (Real.sqrt_pos.mpr hτ) ?_
    rw [Real.sq_sqrt hy0.le, Real.sq_sqrt hτ.le]
    exact hyt
  have hexp : Real.exp (-τ / 4) = Real.exp (-(1 / 4) * τ) := by
    congr 1
    ring
  unfold kernel
  rw [hexp]
  calc Real.exp (-(1 / 4) * τ) * (2 * Real.exp 1 * (1 - Real.exp (-τ))) ^ (-(1 / 2 : ℝ))
      ≤ Real.exp (-(1 / 4) * τ) * (τ ^ (-(1 / 2 : ℝ)) + 1) :=
        mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le
    _ = τ ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 4) * τ) + Real.exp (-(1 / 4) * τ) := by ring

theorem integrableOn_majorant :
    IntegrableOn (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 4) * τ) + Real.exp (-(1 / 4) * τ))
      (Ioi 0) := by
  have h1 : IntegrableOn (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 4) * τ ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos (by norm_num)
  simp only [Real.rpow_one] at h1
  exact h1.add (exp_neg_integrableOn_Ioi 0 (by norm_num))

theorem integrableOn_kernel : IntegrableOn kernel (Ioi 0) := by
  refine Integrable.mono' integrableOn_majorant
    (continuousOn_kernel.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (kernel_pos hτ)]
  exact kernel_le hτ

theorem propagatorBound_eq : propagatorBound = ∫ τ in Ioi 0, kernel τ := rfl

end GradInv.Internal

theorem integrableOn_propagatorBound :
    IntegrableOn (fun τ : ℝ => Real.exp (-τ / 4) * (2 * Real.exp 1 * (1 - Real.exp (-τ))) ^ (-(1 / 2 : ℝ)))
      (Set.Ioi 0) :=
  integrableOn_kernel

theorem propagatorBound_pos : 0 < propagatorBound := by
  rw [propagatorBound_eq, setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => (kernel_pos hτ).le))
    integrableOn_kernel]
  have hs : Function.support kernel ∩ Ioi 0 = Ioi 0 :=
    inter_eq_right.mpr fun τ hτ => (kernel_pos hτ).ne'
  rw [hs, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

namespace GradInv.Internal

theorem norm_shiftLp (a : ℝ) (f : HH) : ‖shiftLp a f‖ = ‖f‖ :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun t : TimeCircle => t + (a : TimeCircle))
    (measurePreserving_add_right volume (a : TimeCircle))).norm_map f

theorem norm_slicePropagator_op_le {τ : ℝ} (hτ : 0 < τ) : ‖slicePropagator τ‖ ≤ kernel τ :=
  ContinuousLinearMap.opNorm_le_bound _ (kernel_pos hτ).le (norm_slicePropagator_le τ hτ)

theorem norm_propagatorIntegrand_le (P : ℝ) (f : HH) {τ : ℝ} (hτ : 0 < τ) :
    ‖propagatorIntegrand P f τ‖ ≤ kernel τ * ‖f‖ := by
  unfold propagatorIntegrand
  calc _ ≤ ‖ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) (slicePropagator τ)‖ *
        ‖shiftLp (-(τ / P)) f‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) (slicePropagator τ)‖ * ‖f‖ :=
        congrArg (‖ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) (slicePropagator τ)‖ * ·)
          (norm_shiftLp _ _)
    _ ≤ kernel τ * ‖f‖ := mul_le_mul_of_nonneg_right
          ((ContinuousLinearMap.norm_compLpL_le _).trans (norm_slicePropagator_op_le hτ)) (norm_nonneg _)

theorem norm_sq_eq_integral {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (g : Lp E 2 μ) : ‖g‖ ^ 2 = ∫ t, ‖(g : α → E) t‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with t
  rw [real_inner_self_eq_norm_sq]

theorem tendsto_apply_of_norm_le {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {l : Filter α} {A : α → E →L[ℝ] F} {B : E →L[ℝ] F}
    {u : α → E} {u₀ : E} {C : ℝ} (hA : Tendsto (fun a => A a u₀) l (𝓝 (B u₀)))
    (hC : ∀ᶠ a in l, ‖A a‖ ≤ C) (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun a => A a (u a)) l (𝓝 (B u₀)) := by
  have h1 : Tendsto (fun a => A a (u a - u₀)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 : Tendsto (fun a => C * ‖u a - u₀‖) l (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hu).const_mul C
    refine squeeze_zero' (Eventually.of_forall fun a => norm_nonneg _) ?_ h2
    filter_upwards [hC] with a ha
    exact (A a).le_of_opNorm_le ha _
  have h3 := h1.add hA
  simp only [map_sub, sub_add_cancel, zero_add] at h3
  exact h3

theorem tendsto_compLpL {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {l : Filter ℝ} [l.IsCountablyGenerated] {A : ℝ → E →L[ℝ] E}
    {B : E →L[ℝ] E} {C : ℝ} (hA : ∀ y, Tendsto (fun a => A a y) l (𝓝 (B y)))
    (hC : ∀ᶠ a in l, ‖A a‖ ≤ C) (h : Lp E 2 μ) :
    Tendsto (fun a => ContinuousLinearMap.compLpL 2 μ (A a) h) l
      (𝓝 (ContinuousLinearMap.compLpL 2 μ B h)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heq : ∀ a, ‖ContinuousLinearMap.compLpL 2 μ (A a) h -
      ContinuousLinearMap.compLpL 2 μ B h‖ ^ 2 =
      ∫ t, ‖A a ((h : α → E) t) - B ((h : α → E) t)‖ ^ 2 ∂μ := by
    intro a
    refine (norm_sq_eq_integral _).trans (integral_congr_ae ?_)
    filter_upwards [Lp.coeFn_sub (ContinuousLinearMap.compLpL 2 μ (A a) h)
        (ContinuousLinearMap.compLpL 2 μ B h),
      (A a).coeFn_compLpL h, B.coeFn_compLpL h] with t hs ha hb
    exact congrArg (fun v : E => ‖v‖ ^ 2) (hs.trans (congrArg₂ (· - ·) ha hb))
  have hint : Integrable (fun t => ‖(h : α → E) t‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable h)).1 (Lp.memLp h)
  have hlim : Tendsto (fun a => ∫ t, ‖A a ((h : α → E) t) - B ((h : α → E) t)‖ ^ 2 ∂μ)
      l (𝓝 (∫ _t, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => (C + ‖B‖) ^ 2 * ‖(h : α → E) t‖ ^ 2) ?_ ?_ (hint.const_mul _) ?_
    · exact Eventually.of_forall fun a =>
        ((((A a).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable h)).sub
          (B.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable h))).norm.pow 2)
    · filter_upwards [hC] with a ha
      refine Eventually.of_forall fun t => ?_
      have hle : ‖A a ((h : α → E) t) - B ((h : α → E) t)‖ ≤
          (C + ‖B‖) * ‖(h : α → E) t‖ := by
        calc _ ≤ ‖A a ((h : α → E) t)‖ + ‖B ((h : α → E) t)‖ := norm_sub_le _ _
          _ ≤ C * ‖(h : α → E) t‖ + ‖B‖ * ‖(h : α → E) t‖ :=
              add_le_add ((A a).le_of_opNorm_le ha _) (B.le_opNorm _)
          _ = (C + ‖B‖) * ‖(h : α → E) t‖ := by ring
      have hsq : ‖A a ((h : α → E) t) - B ((h : α → E) t)‖ ^ 2 ≤
          ((C + ‖B‖) * ‖(h : α → E) t‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      calc ‖‖A a ((h : α → E) t) - B ((h : α → E) t)‖ ^ 2‖ =
            ‖A a ((h : α → E) t) - B ((h : α → E) t)‖ ^ 2 := by
              simp only [norm_pow, norm_norm]
        _ ≤ ((C + ‖B‖) * ‖(h : α → E) t‖) ^ 2 := hsq
        _ = (C + ‖B‖) ^ 2 * ‖(h : α → E) t‖ ^ 2 := mul_pow _ _ _
    · refine Eventually.of_forall fun t => ?_
      have := ((tendsto_iff_norm_sub_tendsto_zero.1 (hA ((h : α → E) t))).pow 2)
      have e0 : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [e0] at this
      exact this
  rw [integral_zero] at hlim
  have h2 := Tendsto.congr (fun a => (heq a).symm) hlim
  have h3 := Tendsto.congr (fun a => Real.sqrt_sq (norm_nonneg _)) h2.sqrt
  rw [Real.sqrt_zero] at h3
  exact h3

theorem continuousOn_smoothH (x : HBar) : ContinuousOn (fun t => smoothH t x) (Ioi 0) := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  refine (Periodic.HeatDivFreeCont.Internal.phiOp_continuousOn fieldOpRealized (x : L2C)).congr
    fun t ht => ?_
  exact smoothH_coe ht x

theorem continuousOn_slicePropagator (x : HBar) :
    ContinuousOn (fun τ => slicePropagator τ x) (Ioi 0) := by
  intro τ₀ hτ₀
  have hmaps : MapsTo (fun τ : ℝ => 1 - Real.exp (-τ)) (Ioi 0) (Ioi 0) :=
    fun τ hτ => one_sub_exp_pos hτ
  have hu : Tendsto (fun τ => smoothH (1 - Real.exp (-τ)) x) (𝓝[Ioi 0] τ₀)
      (𝓝 (smoothH (1 - Real.exp (-τ₀)) x)) :=
    (continuousOn_smoothH x).comp (Continuous.continuousOn (by fun_prop)) hmaps τ₀ hτ₀
  have hD : Tendsto (fun τ => dilX (Real.exp (-τ)) (smoothH (1 - Real.exp (-τ₀)) x)) (𝓝[Ioi 0] τ₀)
      (𝓝 (dilX (Real.exp (-τ₀)) (smoothH (1 - Real.exp (-τ₀)) x))) :=
    (dilationCont_holds (smoothH (1 - Real.exp (-τ₀)) x)).comp
      (Continuous.continuousOn (f := fun τ : ℝ => Real.exp (-τ)) (by fun_prop))
      (fun τ _ => Real.exp_pos (-τ)) τ₀ hτ₀
  have hC : ∀ᶠ τ in 𝓝[Ioi 0] τ₀, ‖dilX (Real.exp (-τ))‖ ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact norm_dilX_le_one (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by have : (0 : ℝ) < τ := hτ; linarith))
  exact tendsto_apply_of_norm_le (A := fun τ => dilX (Real.exp (-τ)))
    (B := dilX (Real.exp (-τ₀))) (u := fun τ => smoothH (1 - Real.exp (-τ)) x) hD hC hu

theorem eventually_norm_slicePropagator_le {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
    ∀ᶠ τ in 𝓝[Ioi 0] τ₀, ‖slicePropagator τ‖ ≤ kernel τ₀ + 1 := by
  have hk : ContinuousAt kernel τ₀ := continuousOn_kernel.continuousAt (Ioi_mem_nhds hτ₀)
  have h1 : ∀ᶠ τ in 𝓝 τ₀, kernel τ < kernel τ₀ + 1 :=
    hk.eventually_lt continuousAt_const (lt_add_one _)
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with τ hτ hτ'
  exact (norm_slicePropagator_op_le hτ').trans hτ.le

theorem continuous_shift (P : ℝ) (f : HH) : Continuous (fun τ : ℝ => shiftLp (-(τ / P)) f) := by
  let F : C(ℝ × TimeCircle, TimeCircle) :=
    ⟨fun q => q.2 + (((-(q.1 / P)) : ℝ) : TimeCircle),
      continuous_snd.add ((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_fst.div_const P).neg)⟩
  exact continuous_const.compMeasurePreservingLp (ContinuousMap.curry F).continuous
    (fun τ => measurePreserving_add_right volume (((-(τ / P)) : ℝ) : TimeCircle)) (by norm_num)

theorem continuousOn_propagatorIntegrand (P : ℝ) (f : HH) :
    ContinuousOn (propagatorIntegrand P f) (Ioi 0) := by
  intro τ₀ hτ₀
  have hτ₀' : (0 : ℝ) < τ₀ := hτ₀
  have hL := tendsto_compLpL (fun y => continuousOn_slicePropagator y τ₀ hτ₀)
    (eventually_norm_slicePropagator_le hτ₀') (shiftLp (-(τ₀ / P)) f)
  have hC : ∀ᶠ τ in 𝓝[Ioi 0] τ₀,
      ‖ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) (slicePropagator τ)‖ ≤ kernel τ₀ + 1 := by
    filter_upwards [eventually_norm_slicePropagator_le hτ₀'] with τ hτ
    exact (ContinuousLinearMap.norm_compLpL_le _).trans hτ
  exact tendsto_apply_of_norm_le
    (A := fun τ => ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) (slicePropagator τ))
    (B := ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) (slicePropagator τ₀))
    (u := fun τ => shiftLp (-(τ / P)) f) hL hC
    ((continuous_shift P f).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

end GradInv.Internal

theorem integrable_propagatorIntegrand (P : ℝ) (f : HH) :
    MeasureTheory.IntegrableOn (propagatorIntegrand P f) (Set.Ioi 0) := by
  refine Integrable.mono' (Integrable.mul_const integrableOn_kernel ‖f‖)
    ((continuousOn_propagatorIntegrand P f).aestronglyMeasurable measurableSet_Ioi) ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun τ hτ => norm_propagatorIntegrand_le P f hτ)

namespace GradInv.Internal

theorem norm_integral_propagator_le (P : ℝ) (f : HH) :
    ‖∫ τ in Ioi (0 : ℝ), propagatorIntegrand P f τ‖ ≤ propagatorBound * ‖f‖ := by
  calc ‖∫ τ in Ioi (0 : ℝ), propagatorIntegrand P f τ‖ ≤ ∫ τ in Ioi (0 : ℝ), kernel τ * ‖f‖ :=
        norm_integral_le_of_norm_le (Integrable.mul_const integrableOn_kernel ‖f‖)
          ((ae_restrict_iff' measurableSet_Ioi).mpr
            (Eventually.of_forall fun τ hτ => norm_propagatorIntegrand_le P f hτ))
    _ = propagatorBound * ‖f‖ := integral_mul_const ‖f‖ kernel

theorem propagatorIntegrand_add (P : ℝ) (f g : HH) :
    propagatorIntegrand P (f + g) = fun τ => propagatorIntegrand P f τ + propagatorIntegrand P g τ := by
  funext τ
  simp only [propagatorIntegrand, map_add]

theorem propagatorIntegrand_smul (P c : ℝ) (f : HH) :
    propagatorIntegrand P (c • f) = fun τ => c • propagatorIntegrand P f τ := by
  funext τ
  simp only [propagatorIntegrand, map_smul]

theorem integral_propagatorIntegrand_add (P : ℝ) (f g : HH) :
    ∫ τ in Ioi (0 : ℝ), propagatorIntegrand P (f + g) τ =
      (∫ τ in Ioi (0 : ℝ), propagatorIntegrand P f τ) + ∫ τ in Ioi (0 : ℝ), propagatorIntegrand P g τ :=
  calc _ = ∫ τ in Ioi (0 : ℝ), (propagatorIntegrand P f τ + propagatorIntegrand P g τ) :=
        congrArg (fun F : ℝ → HH => ∫ τ in Ioi (0 : ℝ), F τ) (propagatorIntegrand_add P f g)
    _ = _ := integral_add (integrable_propagatorIntegrand P f) (integrable_propagatorIntegrand P g)

theorem integral_propagatorIntegrand_smul (P c : ℝ) (f : HH) :
    ∫ τ in Ioi (0 : ℝ), propagatorIntegrand P (c • f) τ = c • ∫ τ in Ioi (0 : ℝ), propagatorIntegrand P f τ :=
  calc _ = ∫ τ in Ioi (0 : ℝ), c • propagatorIntegrand P f τ :=
        congrArg (fun F : ℝ → HH => ∫ τ in Ioi (0 : ℝ), F τ) (propagatorIntegrand_smul P c f)
    _ = _ := integral_smul c _

def integralLinear (P : ℝ) : HH →ₗ[ℝ] HH where
  toFun f := ∫ τ in Ioi (0 : ℝ), propagatorIntegrand P f τ
  map_add' f g := integral_propagatorIntegrand_add P f g
  map_smul' c f := integral_propagatorIntegrand_smul P c f

end GradInv.Internal

theorem exists_gradInvSpec (P : ℝ) : ∃ T, GradInvSpec P T :=
  ⟨(integralLinear P).mkContinuous propagatorBound (norm_integral_propagator_le P), fun _ => rfl⟩

theorem gradInv_spec (P : ℝ) : GradInvSpec P (gradInv P) := by
  have h := exists_gradInvSpec P
  rw [gradInv, dif_pos h]
  exact h.choose_spec

theorem norm_gradInv_le (P : ℝ) (f : HH) : ‖gradInv P f‖ ≤ propagatorBound * ‖f‖ := by
  rw [gradInv_spec P f]
  exact norm_integral_propagator_le P f

end Breakdown.Cert
