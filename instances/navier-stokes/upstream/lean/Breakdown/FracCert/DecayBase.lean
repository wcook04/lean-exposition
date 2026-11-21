import Breakdown.FracCert.StDecay
import Breakdown.FracCert.WeakRegular
import Breakdown.FracCert.KernelScaling
import Breakdown.Frac.PAxial

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff FourierTransform

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

namespace FarFieldAddInternal

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

theorem comp_integrable (hk : KernelDecayStatement) {α t : ℝ} (hα : 0 < α) (ht : 0 < t)
    (F : Space → Fin 3 → Fin 3 → ℝ) (hF : Continuous F) (B : ℝ) (hB : ∀ y, ‖F y‖ ≤ B)
    (x : Space) (i j k : Fin 3) :
    Integrable (fun z => (projDivKernel α t i j k (x - z)).re * F z j k) := by
  have h1 : Integrable (fun z => (projDivKernel α t i j k (x - z)).re) :=
    ((kernel_integrable hk hα ht i j k).comp_sub_left x).re
  refine h1.mul_bdd (c := B) ?_ (Eventually.of_forall fun z => ?_)
  · exact ((continuous_apply k).comp ((continuous_apply j).comp hF)).aestronglyMeasurable
  · exact (norm_le_pi_norm (F z j) k).trans ((norm_le_pi_norm (F z) j).trans (hB z))

theorem heatDivConv_add (hk : KernelDecayStatement) {α t : ℝ} (hα : 0 < α) (ht : 0 < t)
    (F G : Space → Fin 3 → Fin 3 → ℝ) (hF : Continuous F) (hG : Continuous G) (A B : ℝ)
    (hA : ∀ y, ‖F y‖ ≤ A) (hB : ∀ y, ‖G y‖ ≤ B) (x : Space) :
    heatDivConv α t (F + G) x = heatDivConv α t F x + heatDivConv α t G x := by
  have hI : ∀ i j k : Fin 3, ∫ z, (projDivKernel α t i j k (x - z)).re * (F + G) z j k =
      (∫ z, (projDivKernel α t i j k (x - z)).re * F z j k) +
        ∫ z, (projDivKernel α t i j k (x - z)).re * G z j k := fun i j k => by
    simp only [Pi.add_apply, mul_add]
    exact integral_add (comp_integrable hk hα ht F hF A hA x i j k)
      (comp_integrable hk hα ht G hG B hB x i j k)
  simp only [heatDivConv, hI, Finset.sum_add_distrib]
  rfl

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
    (F : Space → Fin 3 → Fin 3 → ℝ) (B : ℝ) (hB : ∀ y, ‖F y‖ ≤ B)
    (x : Space) :
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

end FarFieldAddInternal


def FarFieldAddStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (F G : Space → Fin 3 → Fin 3 → ℝ),
    Continuous F → Continuous G → (∃ A : ℝ, ∀ y, ‖F y‖ ≤ A) → (∃ B : ℝ, ∀ y, ‖G y‖ ≤ B) →
    farFieldOp α a (F + G) = farFieldOp α a F + farFieldOp α a G

namespace FarFieldAddInternal

theorem exp_neg_lt_one {τ : ℝ} (h : 0 < τ) : Real.exp (-τ) < 1 := by
  have h1 := Real.exp_lt_exp.mpr (show -τ < 0 by linarith)
  rwa [Real.exp_zero] at h1

theorem integrand_add (hk : KernelDecayStatement) {α : ℝ} (hα : 0 < α) (a : ℝ)
    (F G : Space → Fin 3 → Fin 3 → ℝ) (hF : Continuous F) (hG : Continuous G) (A B : ℝ)
    (hA : ∀ y, ‖F y‖ ≤ A) (hB : ∀ y, ‖G y‖ ≤ B) (y : Space) (τ : ℝ) (hτ : 0 < τ) :
    pushForward (axialRotation (a * τ))
        (scaleField α (Real.exp (-τ)) (heatDivConv α (1 - Real.exp (-τ)) (F + G))) y =
      pushForward (axialRotation (a * τ))
          (scaleField α (Real.exp (-τ)) (heatDivConv α (1 - Real.exp (-τ)) F)) y +
        pushForward (axialRotation (a * τ))
          (scaleField α (Real.exp (-τ)) (heatDivConv α (1 - Real.exp (-τ)) G)) y := by
  have ht : 0 < 1 - Real.exp (-τ) := sub_pos.mpr (exp_neg_lt_one (by linarith))
  simp only [pushForward, scaleField, heatDivConv_add hk hα ht F G hF hG A B hA hB, smul_add,
    map_add]

theorem single_measurable (i : Fin 3) : Measurable (fun r : ℝ => EuclideanSpace.single i r) := by
  have e : (fun r : ℝ => EuclideanSpace.single i r) = fun r => r • EuclideanSpace.single i (1 : ℝ) := by
    funext r
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [e]
  exact measurable_id.smul_const _

theorem meas_rot (f : ℝ → ℝ) (g : ℝ → Space) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun τ => axialRotation (f τ) (g τ)) := by
  simp only [axialRotationSpec.1]
  unfold axialRotationFormula
  have hc : ∀ i : Fin 3, Measurable (fun τ => (g τ) i) := fun i =>
    (EuclideanSpace.proj i).continuous.measurable.comp hg
  refine ((single_measurable 0).comp ?_).add ((single_measurable 1).comp ?_) |>.add
    ((single_measurable 2).comp (hc 2))
  · exact ((Real.measurable_cos.comp hf).mul (hc 0)).sub ((Real.measurable_sin.comp hf).mul (hc 1))
  · exact ((Real.measurable_sin.comp hf).mul (hc 0)).add ((Real.measurable_cos.comp hf).mul (hc 1))

theorem meas_heat (α : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (hF : Continuous F) (t : ℝ → ℝ)
    (x : ℝ → Space) (ht : Measurable t) (hx : Measurable x) :
    Measurable (fun τ => heatDivConv α (t τ) F (x τ)) := by
  unfold heatDivConv
  refine (WithLp.measurable_toLp 2 _).comp ?_
  refine measurable_pi_lambda _ fun i => ?_
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
  have hmap : Measurable (fun q : ℝ × Space => (t q.1, x q.1 - q.2)) :=
    (ht.comp measurable_fst).prodMk ((hx.comp measurable_fst).sub measurable_snd)
  have hFm : Measurable (fun q : ℝ × Space => F q.2 j k) :=
    ((continuous_apply k).comp ((continuous_apply j).comp (hF.comp continuous_snd))).measurable
  have hm : Measurable (fun q : ℝ × Space =>
      (projDivKernel α (t q.1) i j k (x q.1 - q.2)).re * F q.2 j k) :=
    (Complex.measurable_re.comp ((kernel_measurable α i j k).comp hmap)).mul hFm
  exact (StronglyMeasurable.integral_prod_right' hm.stronglyMeasurable).measurable

theorem integrand_measurable (α a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (hF : Continuous F)
    (y : Space) : Measurable (fun τ : ℝ => pushForward (axialRotation (a * τ))
        (scaleField α (Real.exp (-τ)) (heatDivConv α (1 - Real.exp (-τ)) F)) y) := by
  have hsymm : ∀ θ, (axialRotation θ).symm = axialRotation (-θ) := axialRotationSpec.2.2.2.1
  simp only [pushForward, scaleField, hsymm]
  have hx : Measurable (fun τ : ℝ => Real.exp (-τ) ^ (1 / (2 * α)) • axialRotation (-(a * τ)) y) :=
    (by fun_prop : Measurable fun τ : ℝ => Real.exp (-τ) ^ (1 / (2 * α))).smul
      (meas_rot (fun τ => -(a * τ)) (fun _ => y) (by fun_prop) measurable_const)
  have hH := meas_heat α F hF (fun τ => 1 - Real.exp (-τ))
    (fun τ : ℝ => Real.exp (-τ) ^ (1 / (2 * α)) • axialRotation (-(a * τ)) y) (by fun_prop) hx
  have hin : Measurable (fun τ : ℝ => Real.exp (-τ) ^ (1 - 1 / (2 * α)) • heatDivConv α
      (1 - Real.exp (-τ)) F (Real.exp (-τ) ^ (1 / (2 * α)) • axialRotation (-(a * τ)) y)) :=
    (by fun_prop : Measurable fun τ : ℝ => Real.exp (-τ) ^ (1 - 1 / (2 * α))).smul hH
  exact meas_rot (fun τ => a * τ) _ (by fun_prop) hin

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

theorem integrand_integrable (hk : KernelDecayStatement) {α : ℝ} (hα1 : 1 < α) (a : ℝ)
    (F : Space → Fin 3 → Fin 3 → ℝ) (hF : Continuous F) (B : ℝ) (hB : ∀ y, ‖F y‖ ≤ B)
    (y : Space) : IntegrableOn (fun τ : ℝ => pushForward (axialRotation (a * τ))
        (scaleField α (Real.exp (-τ)) (heatDivConv α (1 - Real.exp (-τ)) F)) y) (Ioi 0) := by
  have hα : 0 < α := by linarith
  have hw := (weight_integrable hα1).const_mul (3 * (B * kernelMass α))
  refine hw.mono' (integrand_measurable α a F hF y).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
  have hτ0 : 0 < τ := hτ
  have ht : 0 < 1 - Real.exp (-τ) := sub_pos.mpr (exp_neg_lt_one (by linarith))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hm0 := kernelMass_nonneg α
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

end FarFieldAddInternal

open FarFieldAddInternal in
theorem farFieldAdd_of (hk : KernelDecayStatement) : FarFieldAddStatement := by
  intro α hα1 hα2 a F G hF hG ⟨A, hA⟩ ⟨B, hB⟩
  have hα : 0 < α := by linarith
  funext y
  simp only [farFieldOp, Pi.add_apply]
  rw [← neg_add, ← integral_add (integrand_integrable hk hα1 a F hF A hA y)
    (integrand_integrable hk hα1 a G hG B hB y)]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun τ hτ =>
    integrand_add hk hα a F G hF hG A B hA hB y τ hτ


namespace DecayBaseInternal

def outer (u v : Space → Space) : Space → Fin 3 → Fin 3 → ℝ := fun y j k => u y j * v y k

theorem norm_outer_le (u v : Space → Space) (y : Space) : ‖outer u v y‖ ≤ ‖u y‖ * ‖v y‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr fun j => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr fun k => ?_
  simp only [outer, norm_mul]
  exact mul_le_mul (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _) (norm_nonneg _) (norm_nonneg _)

theorem continuous_outer {u v : Space → Space} (hu : Continuous u) (hv : Continuous v) :
    Continuous (outer u v) := by
  refine continuous_pi fun j => continuous_pi fun k => ?_
  exact ((EuclideanSpace.proj j).continuous.comp hu).mul ((EuclideanSpace.proj k).continuous.comp hv)

theorem outer_add_right (u v w : Space → Space) : outer u (v + w) = outer u v + outer u w := by
  funext y j k
  simp [outer, mul_add]

theorem outer_add_left (u v w : Space → Space) : outer (u + v) w = outer u w + outer v w := by
  funext y j k
  simp [outer, add_mul]

theorem field_facts (h3 : SymbolL1OfMomentsStatement) (h4 : FieldSmoothOfMomentsStatement) (U : X)
    (hmom : HasAllMoments U) :
    Continuous (profileField U) ∧ ∃ M : ℝ, ∀ y, ‖profileField U y‖ ≤ M := by
  obtain ⟨hw, -⟩ := h3 U hmom
  obtain ⟨hs, hb⟩ := h4 _ (WeakRegularInternal.moments_clean U hw)
    (WeakRegularInternal.cleanSymbol_conjSym _)
  rw [WeakRegularInternal.physField_clean U] at hs hb
  obtain ⟨C, hC⟩ := hb 0
  exact ⟨hs.continuous, C, fun y => by have h := hC y; rw [norm_iteratedFDeriv_zero] at h; exact h⟩

theorem field_small (U : X) : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ y, R ≤ ‖y‖ → ‖profileField U y‖ ≤ ε := by
  intro ε hε
  have ht := tendsto_integral_exp_inner_smul_cocompact (V := Space) (symbolX U)
  have hev := (tendsto_order.1 ht.norm).2 ε (by simpa using hε)
  rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop] at hev
  obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_comap.mp hev)
  refine ⟨R, fun y hy => ?_⟩
  have h := hR ‖y‖ hy (-y) (norm_neg y)
  have e : profileField U y = realVec (𝓕⁻ (symbolX U) y) := rfl
  rw [e]
  refine (WeakRegularInternal.norm_realVec_le' _).trans ?_
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_eq]
  exact h.le

theorem farField_zero_order (h2 : FarFieldBoundStatement) {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4)
    (a β : ℝ) (hβ0 : 0 ≤ β) (hβ3 : β < 3) (hβγ : β ≠ 2 * α - 1) :
    ∃ C : ℝ, ∀ (F : Space → Fin 3 → Fin 3 → ℝ) (A : ℝ), Continuous F →
      (∀ y, (1 + ‖y‖) ^ β * ‖F y‖ ≤ A) →
      Continuous (farFieldOp α a F) ∧
        ∀ y, (1 + ‖y‖) ^ (min β (2 * α - 1)) * ‖farFieldOp α a F y‖ ≤ C * (2 * A) := by
  have e : (2 * α - 1 + ((0 : ℕ) : ℝ)) = 2 * α - 1 := by simp
  obtain ⟨C, hC⟩ := h2 α hα1 hα2 a β β 0 hβ0 hβ3 hβ0 (by have : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero; linarith) (by rw [e]; exact hβγ)
  refine ⟨C, fun F A hF hA => ?_⟩
  have hA' : ∀ y, (1 + ‖y‖) ^ β * ‖iteratedFDeriv ℝ 0 F y‖ ≤ A := fun y => by
    rw [norm_iteratedFDeriv_zero]; exact hA y
  obtain ⟨hc, hb⟩ := hC F A A (contDiff_zero.mpr hF) hA' hA
  refine ⟨hc.continuous, fun y => ?_⟩
  have h := hb y
  rw [norm_iteratedFDeriv_zero, e] at h
  linarith

theorem decay_first (h2 : FarFieldBoundStatement) (hadd : FarFieldAddStatement) {α : ℝ}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (a β : ℝ) (hβ0 : 0 ≤ β) (hβ3 : β < 3) (hβγ : β < 2 * α - 1)
    (V : Space → Space) (hVc : Continuous V) (M : ℝ) (hM : ∀ y, ‖V y‖ ≤ M)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ y, R ≤ ‖y‖ → ‖V y‖ ≤ ε)
    (hfix : V = farFieldOp α a (outer V V)) :
    ∃ G : ℝ, ∀ y, (1 + ‖y‖) ^ β * ‖V y‖ ≤ G := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨C0, hC0⟩ := farField_zero_order h2 hα1 hα2 a 0 le_rfl (by norm_num)
    (by intro h; linarith)
  obtain ⟨Cb, hCb⟩ := farField_zero_order h2 hα1 hα2 a β hβ0 hβ3 hβγ.ne
  have hmin0 : min (0 : ℝ) (2 * α - 1) = 0 := min_eq_left (by linarith)
  have hminb : min β (2 * α - 1) = β := min_eq_left hβγ.le
  rw [hmin0] at hC0
  rw [hminb] at hCb
  set S : ℝ := |C0| + |Cb| + 1 with hS
  have hSpos : 0 < S := by positivity
  set ε : ℝ := 1 / (4 * S) with hεdef
  have hε : 0 < ε := by positivity
  have hεS : S * (2 * ε) = 1 / 2 := by rw [hεdef]; field_simp; ring
  have hC0ε : |C0| * (2 * ε) ≤ 1 / 2 := by
    rw [← hεS]; exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg Cb]) (by positivity)
  have hCbε : |Cb| * (2 * ε) ≤ 1 / 2 := by
    rw [← hεS]; exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C0]) (by positivity)
  obtain ⟨R, hR⟩ := hsmall ε hε
  set χ : Space → ℝ := fun y => min 1 (max 0 (R + 1 - ‖y‖)) with hχdef
  have hχc : Continuous χ :=
    continuous_const.min (continuous_const.max (continuous_const.sub continuous_norm))
  have hχ0 : ∀ y, 0 ≤ χ y := fun y => le_min zero_le_one (le_max_left _ _)
  have hχ1 : ∀ y, χ y ≤ 1 := fun y => min_le_left _ _
  have hχin : ∀ y, ‖y‖ ≤ R → χ y = 1 := fun y hy =>
    min_eq_left (le_max_of_le_right (by linarith))
  have hχout : ∀ y, R + 1 ≤ ‖y‖ → χ y = 0 := fun y hy => by
    simp only [hχdef]
    rw [max_eq_left (by linarith)]
    exact min_eq_right zero_le_one
  set V1 : Space → Space := fun y => χ y • V y with hV1def
  set V2 : Space → Space := fun y => (1 - χ y) • V y with hV2def
  have hV12 : V = V1 + V2 := by
    funext y
    simp only [Pi.add_apply, hV1def, hV2def, ← add_smul, add_sub_cancel, one_smul]
  have hV1c : Continuous V1 := hχc.smul hVc
  have hV2c : Continuous V2 := (continuous_const.sub hχc).smul hVc
  have hV1M : ∀ y, ‖V1 y‖ ≤ M := fun y => by
    simp only [hV1def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ0 y)]
    calc χ y * ‖V y‖ ≤ 1 * ‖V y‖ := mul_le_mul_of_nonneg_right (hχ1 y) (norm_nonneg _)
      _ ≤ M := by rw [one_mul]; exact hM y
  have hV2ε : ∀ y, ‖V2 y‖ ≤ ε := fun y => by
    simp only [hV2def, norm_smul, Real.norm_eq_abs]
    rcases le_or_gt ‖y‖ R with hy | hy
    · rw [hχin y hy, sub_self, abs_zero, zero_mul]; exact hε.le
    · rw [abs_of_nonneg (by linarith [hχ1 y])]
      calc (1 - χ y) * ‖V y‖ ≤ 1 * ε :=
            mul_le_mul (by linarith [hχ0 y]) (hR y hy.le) (norm_nonneg _) zero_le_one
        _ = ε := one_mul ε
  have hV2M : ∀ y, ‖V2 y‖ ≤ M := fun y => by
    simp only [hV2def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hχ1 y] : 0 ≤ 1 - χ y)]
    calc (1 - χ y) * ‖V y‖ ≤ 1 * ‖V y‖ :=
          mul_le_mul_of_nonneg_right (by linarith [hχ0 y]) (norm_nonneg _)
      _ ≤ M := by rw [one_mul]; exact hM y
  have hw0 : ∀ y : Space, 0 ≤ (1 + ‖y‖) ^ β := fun y => by positivity
  set G0 : ℝ := (2 + |R|) ^ β * (M * M) with hG0
  have hG0nn : 0 ≤ G0 := by positivity
  have hV1w : ∀ y, (1 + ‖y‖) ^ β * ‖outer V1 V y‖ ≤ G0 := fun y => by
    rcases le_or_gt (R + 1) ‖y‖ with hy | hy
    · have : V1 y = 0 := by simp only [hV1def, hχout y hy, zero_smul]
      have h0 : ‖outer V1 V y‖ = 0 := by
        refine le_antisymm ((norm_outer_le V1 V y).trans ?_) (norm_nonneg _)
        rw [this, norm_zero, zero_mul]
      rw [h0, mul_zero]; exact hG0nn
    · have hw : (1 + ‖y‖) ^ β ≤ (2 + |R|) ^ β :=
        Real.rpow_le_rpow (by positivity) (by linarith [le_abs_self R]) hβ0
      calc (1 + ‖y‖) ^ β * ‖outer V1 V y‖ ≤ (2 + |R|) ^ β * (M * M) :=
            mul_le_mul hw ((norm_outer_le V1 V y).trans
              (mul_le_mul (hV1M y) (hM y) (norm_nonneg _) hM0)) (norm_nonneg _) (by positivity)
        _ = G0 := rfl
  have hsupT : ∀ (Q : Space → Space) (q : ℝ), Continuous Q → 0 ≤ q → (∀ y, ‖Q y‖ ≤ q) →
      Continuous (farFieldOp α a (outer V2 Q)) ∧ ∀ y, ‖farFieldOp α a (outer V2 Q) y‖ ≤ q / 2 := by
    intro Q q hQc hq hQ
    obtain ⟨hc, hb⟩ := hC0 (outer V2 Q) (ε * q) (continuous_outer hV2c hQc) (fun y => by
      rw [Real.rpow_zero, one_mul]
      exact (norm_outer_le V2 Q y).trans (mul_le_mul (hV2ε y) (hQ y) (norm_nonneg _) hε.le))
    refine ⟨hc, fun y => ?_⟩
    have h := hb y
    rw [Real.rpow_zero, one_mul] at h
    have : C0 * (2 * (ε * q)) ≤ q / 2 := by
      calc C0 * (2 * (ε * q)) ≤ |C0| * (2 * (ε * q)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ = (|C0| * (2 * ε)) * q := by ring
        _ ≤ (1 / 2) * q := mul_le_mul_of_nonneg_right hC0ε hq
        _ = q / 2 := by ring
    linarith
  have hwT : ∀ (Q : Space → Space) (q : ℝ), Continuous Q → 0 ≤ q →
      (∀ y, (1 + ‖y‖) ^ β * ‖Q y‖ ≤ q) →
      ∀ y, (1 + ‖y‖) ^ β * ‖farFieldOp α a (outer V2 Q) y‖ ≤ q / 2 := by
    intro Q q hQc hq hQ y
    obtain ⟨-, hb⟩ := hCb (outer V2 Q) (ε * q) (continuous_outer hV2c hQc) (fun y => by
      calc (1 + ‖y‖) ^ β * ‖outer V2 Q y‖ ≤ (1 + ‖y‖) ^ β * (‖V2 y‖ * ‖Q y‖) :=
            mul_le_mul_of_nonneg_left (norm_outer_le V2 Q y) (hw0 y)
        _ = ‖V2 y‖ * ((1 + ‖y‖) ^ β * ‖Q y‖) := by ring
        _ ≤ ε * q := mul_le_mul (hV2ε y) (hQ y) (by positivity) hε.le)
    have h := hb y
    have : Cb * (2 * (ε * q)) ≤ q / 2 := by
      calc Cb * (2 * (ε * q)) ≤ |Cb| * (2 * (ε * q)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ = (|Cb| * (2 * ε)) * q := by ring
        _ ≤ (1 / 2) * q := mul_le_mul_of_nonneg_right hCbε hq
        _ = q / 2 := by ring
    linarith
  have hbd : ∀ (u Q : Space → Space) (m q : ℝ), 0 ≤ m → (∀ y, ‖u y‖ ≤ m) → (∀ y, ‖Q y‖ ≤ q) →
      ∃ A : ℝ, ∀ y, ‖outer u Q y‖ ≤ A := fun u Q m q hm hu hQ =>
    ⟨m * q, fun y => (norm_outer_le u Q y).trans (mul_le_mul (hu y) (hQ y) (norm_nonneg _) hm)⟩
  have hTadd : ∀ (P Q : Space → Space) (p q : ℝ), Continuous P → Continuous Q →
      (∀ y, ‖P y‖ ≤ p) → (∀ y, ‖Q y‖ ≤ q) →
      farFieldOp α a (outer V2 (P + Q)) = farFieldOp α a (outer V2 P) + farFieldOp α a (outer V2 Q) := by
    intro P Q p q hPc hQc hP hQ
    rw [outer_add_right]
    exact hadd α hα1 hα2 a _ _ (continuous_outer hV2c hPc) (continuous_outer hV2c hQc)
      (hbd V2 P ε p hε.le hV2ε hP) (hbd V2 Q ε q hε.le hV2ε hQ)
  set g : Space → Space := farFieldOp α a (outer V1 V) with hgdef
  obtain ⟨hgc, hgs⟩ := hC0 (outer V1 V) (M * M) (continuous_outer hV1c hVc) (fun y => by
    rw [Real.rpow_zero, one_mul]
    exact (norm_outer_le V1 V y).trans (mul_le_mul (hV1M y) (hM y) (norm_nonneg _) hM0))
  obtain ⟨-, hgw⟩ := hCb (outer V1 V) G0 (continuous_outer hV1c hVc) hV1w
  set Gs : ℝ := |C0| * (2 * (M * M)) with hGs
  have hgs' : ∀ y, ‖g y‖ ≤ Gs := fun y => by
    have h := hgs y
    rw [Real.rpow_zero, one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  set G : ℝ := |Cb| * (2 * G0) with hG
  have hGnn : 0 ≤ G := by positivity
  have hgw' : ∀ y, (1 + ‖y‖) ^ β * ‖g y‖ ≤ G := fun y =>
    (hgw y).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hsplit : V = g + farFieldOp α a (outer V2 V) := by
    have e : outer V V = outer V1 V + outer V2 V := by rw [← outer_add_left, ← hV12]
    calc V = farFieldOp α a (outer V V) := hfix
      _ = g + farFieldOp α a (outer V2 V) := by
        rw [e]
        exact hadd α hα1 hα2 a _ _ (continuous_outer hV1c hVc) (continuous_outer hV2c hVc)
          (hbd V1 V M M hM0 hV1M hM) (hbd V2 V M M hM0 hV2M hM)
  have key : ∀ n : ℕ, ∃ P Q : Space → Space, Continuous P ∧ Continuous Q ∧
      (∃ B : ℝ, ∀ y, ‖P y‖ ≤ B) ∧ (∀ y, (1 + ‖y‖) ^ β * ‖P y‖ ≤ 2 * G) ∧
      (∀ y, ‖Q y‖ ≤ M / 2 ^ n) ∧ V = P + Q := by
    intro n
    induction n with
    | zero =>
      refine ⟨0, V, continuous_const, hVc, ⟨0, fun y => by simp⟩, fun y => by simp; positivity,
        fun y => by simpa using hM y, by simp⟩
    | succ n ih =>
      obtain ⟨P, Q, hPc, hQc, ⟨B, hB⟩, hPw, hQs, hVPQ⟩ := ih
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
      have hq0 : 0 ≤ M / 2 ^ n := by positivity
      obtain ⟨hTPc, hTPs⟩ := hsupT P B hPc hB0 hB
      obtain ⟨hTQc, hTQs⟩ := hsupT Q _ hQc hq0 hQs
      have hTPw := hwT P (2 * G) hPc (by positivity) hPw
      refine ⟨g + farFieldOp α a (outer V2 P), farFieldOp α a (outer V2 Q), hgc.add hTPc, hTQc,
        ⟨Gs + B / 2, fun y => ?_⟩, fun y => ?_, fun y => ?_, ?_⟩
      · rw [Pi.add_apply]
        exact (norm_add_le _ _).trans (add_le_add (hgs' y) (hTPs y))
      · rw [Pi.add_apply]
        calc (1 + ‖y‖) ^ β * ‖g y + farFieldOp α a (outer V2 P) y‖
            ≤ (1 + ‖y‖) ^ β * (‖g y‖ + ‖farFieldOp α a (outer V2 P) y‖) :=
              mul_le_mul_of_nonneg_left (norm_add_le _ _) (hw0 y)
          _ = (1 + ‖y‖) ^ β * ‖g y‖ + (1 + ‖y‖) ^ β * ‖farFieldOp α a (outer V2 P) y‖ := by ring
          _ ≤ G + 2 * G / 2 := add_le_add (hgw' y) (hTPw y)
          _ = 2 * G := by ring
      · rw [pow_succ, ← div_div]; exact hTQs y
      · calc V = g + farFieldOp α a (outer V2 V) := hsplit
          _ = g + farFieldOp α a (outer V2 (P + Q)) := by rw [← hVPQ]
          _ = g + (farFieldOp α a (outer V2 P) + farFieldOp α a (outer V2 Q)) := by
            rw [hTadd P Q B (M / 2 ^ n) hPc hQc hB hQs]
          _ = (g + farFieldOp α a (outer V2 P)) + farFieldOp α a (outer V2 Q) := by rw [add_assoc]
  refine ⟨2 * G, fun y => ?_⟩
  have hn : ∀ n : ℕ, (1 + ‖y‖) ^ β * ‖V y‖ ≤ 2 * G + (1 + ‖y‖) ^ β * (M / 2 ^ n) := by
    intro n
    obtain ⟨P, Q, -, -, -, hPw, hQs, hVPQ⟩ := key n
    have e : V y = P y + Q y := by rw [hVPQ]; rfl
    rw [e]
    calc (1 + ‖y‖) ^ β * ‖P y + Q y‖ ≤ (1 + ‖y‖) ^ β * (‖P y‖ + ‖Q y‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (hw0 y)
      _ = (1 + ‖y‖) ^ β * ‖P y‖ + (1 + ‖y‖) ^ β * ‖Q y‖ := by ring
      _ ≤ 2 * G + (1 + ‖y‖) ^ β * (M / 2 ^ n) :=
          add_le_add (hPw y) (mul_le_mul_of_nonneg_left (hQs y) (hw0 y))
  have ht : Tendsto (fun n : ℕ => 2 * G + (1 + ‖y‖) ^ β * (M / 2 ^ n)) atTop
      (𝓝 (2 * G + (1 + ‖y‖) ^ β * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)))
  have := ge_of_tendsto' ht hn
  simpa using this

theorem decay_second (h2 : FarFieldBoundStatement) {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4)
    (a : ℝ) (V : Space → Space) (hVc : Continuous V) (G : ℝ)
    (hG : ∀ y, (1 + ‖y‖) ^ (3 * (2 * α - 1) / 4) * ‖V y‖ ≤ G)
    (hfix : V = farFieldOp α a (outer V V)) :
    ∃ C : ℝ, ∀ y, ‖V y‖ ≤ C * (1 + ‖y‖) ^ (-(2 * α - 1)) := by
  set β : ℝ := 3 * (2 * α - 1) / 4 with hβ
  have hG0 : 0 ≤ G := le_trans (by positivity) (hG 0)
  obtain ⟨C2, hC2⟩ := farField_zero_order h2 hα1 hα2 a (2 * β) (by rw [hβ]; nlinarith)
    (by rw [hβ]; nlinarith) (by rw [hβ]; intro h; nlinarith)
  have hmin : min (2 * β) (2 * α - 1) = 2 * α - 1 := min_eq_right (by rw [hβ]; nlinarith)
  rw [hmin] at hC2
  obtain ⟨-, hb⟩ := hC2 (outer V V) (G * G) (continuous_outer hVc hVc) (fun y => by
    have hp : (0 : ℝ) < 1 + ‖y‖ := by positivity
    rw [two_mul, Real.rpow_add hp]
    calc (1 + ‖y‖) ^ β * (1 + ‖y‖) ^ β * ‖outer V V y‖
        ≤ (1 + ‖y‖) ^ β * (1 + ‖y‖) ^ β * (‖V y‖ * ‖V y‖) :=
          mul_le_mul_of_nonneg_left (norm_outer_le V V y) (by positivity)
      _ = ((1 + ‖y‖) ^ β * ‖V y‖) * ((1 + ‖y‖) ^ β * ‖V y‖) := by ring
      _ ≤ G * G := mul_le_mul (hG y) (hG y) (by positivity) hG0)
  refine ⟨C2 * (2 * (G * G)), fun y => ?_⟩
  have hp : (0 : ℝ) < 1 + ‖y‖ := by positivity
  have h := hb y
  rw [← hfix] at h
  have e : ‖V y‖ = (1 + ‖y‖) ^ (-(2 * α - 1)) * ((1 + ‖y‖) ^ (2 * α - 1) * ‖V y‖) := by
    rw [← mul_assoc, ← Real.rpow_add hp, neg_add_cancel, Real.rpow_zero, one_mul]
  rw [e, mul_comm (C2 * (2 * (G * G)))]
  exact mul_le_mul_of_nonneg_left h (by positivity)

end DecayBaseInternal

open DecayBaseInternal in
theorem profileDecayBase_of (h1 : ProfileFixedPointStatement) (h2 : FarFieldBoundStatement)
    (h3 : SymbolL1OfMomentsStatement) (h4 : FieldSmoothOfMomentsStatement)
    (hk : KernelDecayStatement) : ProfileDecayBaseStatement := by
  have hadd : FarFieldAddStatement := farFieldAdd_of hk
  intro α hα1 hα2 a U hU hmom
  obtain ⟨hVc, M, hM⟩ := field_facts h3 h4 U hmom
  have hfix : profileField U = farFieldOp α a (outer (profileField U) (profileField U)) :=
    funext (h1 α hα1 hα2 a U hU hmom)
  obtain ⟨G, hG⟩ := decay_first h2 hadd hα1 hα2 a (3 * (2 * α - 1) / 4) (by nlinarith)
    (by nlinarith) (by nlinarith) (profileField U) hVc M hM (field_small U) hfix
  exact decay_second h2 hα1 hα2 a (profileField U) hVc G hG hfix

end Breakdown.FracCert
