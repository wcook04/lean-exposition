import Breakdown.FracCert.DecayFixedPointParts
import Breakdown.FracCert.KernelScaling
import Breakdown.FracCert.KernelDecay
import Breakdown.FracCert.KernelRingCutoff
import Breakdown.FracCert.KernelPiece
import Breakdown.FracCert.KernelDyadicSum
import Breakdown.FracCert.WeakSymbolL1
import Breakdown.FracCert.WeakRegular
import Breakdown.Frac.PAxial
import Breakdown.Frac.TorusSelfSimilar

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

namespace FarFieldWeightedInternal

theorem kernelDecayHolds : KernelDecayStatement := kernelDecay_of ringCutoff pieceKernel dyadicSum

theorem kernelScalingHolds : KernelScalingStatement := kernelScaling_of kernelDecayHolds

def kk (α τ : ℝ) (z : Space) : ℝ≥0∞ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    ‖(((1 - Real.exp (-τ)) ^ (-(2 / α)) : ℝ) : ℂ) *
      projDivKernel α 1 i j k (((1 - Real.exp (-τ)) ^ (-(1 / (2 * α)))) • z)‖ₑ

theorem t_pos {τ : ℝ} (hτ : 0 < τ) : 0 < 1 - Real.exp (-τ) := by
  have : Real.exp (-τ) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  linarith

theorem kk_eq {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) (z : Space) :
    kk α τ z = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ‖projDivKernel α (1 - Real.exp (-τ)) i j k z‖ₑ := by
  unfold kk
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [((kernelScalingHolds α hα i j k _ (t_pos hτ)).1 z)]

theorem kernel_cont {α : ℝ} (hα : 0 < α) (i j k : Fin 3) {t : ℝ} (ht : 0 < t) :
    Continuous (projDivKernel α t i j k) :=
  ((kernelDecayHolds α hα i j k).1 t ht).continuous

theorem kk_meas {α : ℝ} (hα : 0 < α) : Measurable (fun p : ℝ × Space => kk α p.1 p.2) := by
  unfold kk
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    Finset.measurable_sum _ fun k _ => ?_
  have ht : Measurable (fun p : ℝ × Space => 1 - Real.exp (-p.1)) :=
    (continuous_const.sub (Real.continuous_exp.comp continuous_fst.neg)).measurable
  refine Measurable.enorm (Measurable.mul ?_ ?_)
  · exact Complex.measurable_ofReal.comp (ht.pow_const _)
  · exact (kernel_cont hα i j k one_pos).measurable.comp ((ht.pow_const _).smul measurable_snd)

theorem kk_meas_z {α : ℝ} (hα : 0 < α) (τ : ℝ) : Measurable (kk α τ) := by
  have h : Measurable (Function.uncurry (kk α)) := kk_meas hα
  exact h.of_uncurry_left

theorem kk_lintegral {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) :
    ∫⁻ z, kk α τ z = ENNReal.ofReal ((1 - Real.exp (-τ)) ^ (-(1 / (2 * α))) *
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ x, ‖projDivKernel α 1 i j k x‖) := by
  have ht := t_pos hτ
  have hm : ∀ i j k, Measurable (fun z => ‖projDivKernel α (1 - Real.exp (-τ)) i j k z‖ₑ) :=
    fun i j k => (kernel_cont hα i j k ht).measurable.enorm
  rw [lintegral_congr (kk_eq hα hτ)]
  rw [lintegral_finsetSum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    Finset.measurable_sum _ fun k _ => hm i j k]
  simp_rw [Finset.mul_sum]
  have hnn : ∀ i j k, 0 ≤ (1 - Real.exp (-τ)) ^ (-(1 / (2 * α))) * ∫ x, ‖projDivKernel α 1 i j k x‖ :=
    fun i j k => mul_nonneg (Real.rpow_nonneg ht.le _) (integral_nonneg fun _ => norm_nonneg _)
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => hnn i j k]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_finsetSum _ fun j _ => Finset.measurable_sum _ fun k _ => hm i j k]
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ => Finset.sum_nonneg fun k _ => hnn i j k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lintegral_finsetSum _ fun k _ => hm i j k]
  rw [ENNReal.ofReal_sum_of_nonneg fun k _ => hnn i j k]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs := kernelScalingHolds α hα i j k _ ht
  rw [← ofReal_integral_norm_eq_lintegral_enorm hs.2.2.1, hs.2.2.2.1]

theorem enorm_le_sum_comp (v : Space) : ‖v‖ₑ ≤ ∑ i : Fin 3, ‖v i‖ₑ := by
  rw [← ofReal_norm]
  simp_rw [← ofReal_norm]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => norm_nonneg _]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun i _ => norm_nonneg _, ?_⟩
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _

theorem heat_bound {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) (F : Space → Fin 3 → Fin 3 → ℝ)
    (hF : Continuous F) (x : Space) :
    ‖heatDivConv α (1 - Real.exp (-τ)) F x‖ₑ ≤ ∫⁻ z, kk α τ z * ‖F (x - z)‖ₑ := by
  have ht := t_pos hτ
  set K := fun i j k => projDivKernel α (1 - Real.exp (-τ)) i j k
  have hm : ∀ i j k, Measurable (fun z => ‖K i j k (x - z)‖ₑ * ‖F z‖ₑ) := fun i j k =>
    ((kernel_cont hα i j k ht).measurable.comp (measurable_const.sub measurable_id)).enorm.mul
      hF.measurable.enorm
  calc ‖heatDivConv α (1 - Real.exp (-τ)) F x‖ₑ
      ≤ ∑ i : Fin 3, ‖heatDivConv α (1 - Real.exp (-τ)) F x i‖ₑ := enorm_le_sum_comp _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫⁻ z, ‖K i j k (x - z)‖ₑ * ‖F z‖ₑ := by
        gcongr with i
        change ‖∑ j : Fin 3, ∑ k : Fin 3, ∫ z, (K i j k (x - z)).re * F z j k‖ₑ ≤ _
        refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
        rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
          ← ENNReal.ofReal_mul (norm_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_mul]
        exact mul_le_mul (Complex.abs_re_le_norm _) ((norm_le_pi_norm (F z j) k).trans
          (norm_le_pi_norm (F z) j)) (norm_nonneg _) (norm_nonneg _)
    _ = ∫⁻ z, (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ‖K i j k (x - z)‖ₑ) * ‖F z‖ₑ := by
        simp_rw [Finset.sum_mul]
        rw [lintegral_finsetSum _ fun i _ => Finset.measurable_sum _ fun j _ =>
          Finset.measurable_sum _ fun k _ => hm i j k]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum _ fun j _ => Finset.measurable_sum _ fun k _ => hm i j k]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_finsetSum _ fun k _ => hm i j k]
    _ = ∫⁻ z, (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ‖K i j k z‖ₑ) * ‖F (x - z)‖ₑ := by
        rw [← lintegral_sub_left_eq_self
          (fun z => (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ‖K i j k z‖ₑ) * ‖F (x - z)‖ₑ) x]
        simp only [sub_sub_cancel]
    _ = ∫⁻ z, kk α τ z * ‖F (x - z)‖ₑ := lintegral_congr fun z => by rw [kk_eq hα hτ]


theorem rot_symm (θ : ℝ) (y : Space) : (axialRotation θ).symm y = axialRotation (-θ) y := by
  rw [axialRotationSpec.2.2.2.1 θ]

theorem pointwise {α : ℝ} (hα : 0 < α) (a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (hF : Continuous F)
    (y : Space) :
    ‖farFieldOp α a F y‖ₑ ≤ ∫⁻ τ in Ioi (0 : ℝ), ∫⁻ z,
      ENNReal.ofReal (Real.exp (-τ) ^ (1 - 1 / (2 * α))) * kk α τ z *
        ‖F (Real.exp (-τ) ^ (1 / (2 * α)) • axialRotation (-(a * τ)) y - z)‖ₑ := by
  unfold farFieldOp
  rw [enorm_neg]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
  have hτ' : 0 < τ := hτ
  simp only [pushForward, scaleField, rot_symm]
  rw [← ofReal_norm, LinearIsometryEquiv.norm_map, norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _),
    ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _), ofReal_norm]
  simp_rw [mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  gcongr
  exact heat_bound hα hτ' F hF _

theorem arg_cont (α a : ℝ) (hα : 0 < α) :
    Continuous (fun q : Space × (ℝ × Space) =>
      Real.exp (-q.2.1) ^ (1 / (2 * α)) • axialRotation (-(a * q.2.1)) q.1 - q.2.2) := by
  have hpair : Continuous (fun q : Space × (ℝ × Space) => ((-(a * q.2.1), q.1) : ℝ × Space)) := by
    fun_prop
  have h0 : Continuous (fun p : ℝ × Space => axialRotation p.1 p.2) :=
    (Periodic.FracSelfSimilar.Internal.rot_contDiff axialRotationSpec).continuous
  have hr : Continuous (fun q : Space × (ℝ × Space) => axialRotation (-(a * q.2.1)) q.1) := by
    refine (h0.comp hpair).congr fun q => ?_
    simp only [Function.comp_apply]
  have hc : Continuous (fun q : Space × (ℝ × Space) => Real.exp (-q.2.1) ^ (1 / (2 * α))) :=
    (Real.continuous_exp.comp (continuous_fst.comp continuous_snd).neg).rpow_const
      fun _ => Or.inr (by positivity)
  exact (hc.smul hr).sub (continuous_snd.comp continuous_snd)

theorem lintegral_affine (g : Space → ℝ≥0∞) (hg : Measurable g) {c : ℝ} (hc : c ≠ 0)
    (R : Space ≃ₗᵢ[ℝ] Space) (z : Space) :
    ∫⁻ y, g (c • R y - z) = ENNReal.ofReal |(c ^ 3)⁻¹| * ∫⁻ x, g x := by
  have hs : Measurable (fun y : Space => c • y) := (continuous_const_smul c).measurable
  have h1 : ∫⁻ y, g (c • R y - z) = ∫⁻ y, g (c • y - z) :=
    (R.measurePreserving).lintegral_comp (f := fun y => g (c • y - z)) (hg.comp (hs.sub_const z))
  have h2 : ∫⁻ y, g (c • y - z) = ∫⁻ x, g (x - z) ∂(Measure.map (fun x : Space => c • x) volume) := by
    exact (lintegral_map (f := fun x => g (x - z)) (hg.comp (measurable_id.sub_const z)) hs).symm
  rw [h1, h2, Measure.map_addHaar_smul volume hc, lintegral_smul_measure,
    lintegral_sub_right_eq_self g z, finrank_euclideanSpace_fin]
  rfl

theorem cst_weighted {β : Type*} [MeasurableSpace β] (ν : Measure β) (u v ψ m : β → ℝ≥0∞)
    (hu : Measurable u) (hv : Measurable v) (hψ : Measurable ψ) (huv : ∀ p, u p * v p = m p ^ 2) :
    (∫⁻ p, m p * ψ p ∂ν) ^ (2 : ℝ) ≤ (∫⁻ p, u p ∂ν) * ∫⁻ p, v p * ψ p ^ (2 : ℝ) ∂ν := by
  have key : ∀ p, m p * ψ p = u p ^ (1 / 2 : ℝ) * (v p ^ (1 / 2 : ℝ) * ψ p) := by
    intro p
    rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), huv p, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
    (hu.pow_const (1 / 2 : ℝ)).aemeasurable ((hv.pow_const (1 / 2 : ℝ)).mul hψ).aemeasurable
  have e1 : ∀ p, (u p ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = u p := fun p => by
    rw [← ENNReal.rpow_mul]; norm_num
  have e2 : ∀ p, (v p ^ (1 / 2 : ℝ) * ψ p) ^ (2 : ℝ) = v p * ψ p ^ (2 : ℝ) := fun p => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]; norm_num
  simp only [Pi.mul_apply, e1, e2] at hH
  simp_rw [key]
  calc (∫⁻ p, u p ^ (1 / 2 : ℝ) * (v p ^ (1 / 2 : ℝ) * ψ p) ∂ν) ^ (2 : ℝ)
      ≤ ((∫⁻ p, u p ∂ν) ^ (1 / 2 : ℝ) * (∫⁻ p, v p * ψ p ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hH (by norm_num)
    _ = (∫⁻ p, u p ∂ν) * ∫⁻ p, v p * ψ p ^ (2 : ℝ) ∂ν := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

theorem t_lower {τ : ℝ} (hτ : 0 < τ) : τ / (1 + τ) ≤ 1 - Real.exp (-τ) := by
  have h1 : 1 + τ ≤ Real.exp τ := by linarith [Real.add_one_le_exp τ]
  have h2 : Real.exp (-τ) ≤ (1 + τ)⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ (by positivity) h1
  have h3 : τ / (1 + τ) = 1 - (1 + τ)⁻¹ := by field_simp; ring
  linarith

theorem t_pow_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) :
    (1 - Real.exp (-τ)) ^ (-(1 / (2 * α))) ≤ τ ^ (-(1 / (2 * α))) + τ ^ (1 - 1 / (2 * α)) := by
  have hp0 : 0 ≤ 1 / (2 * α) := by positivity
  have hp1 : 1 / (2 * α) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hq : 0 < τ / (1 + τ) := by positivity
  rw [Real.rpow_neg (t_pos hτ).le]
  calc ((1 - Real.exp (-τ)) ^ (1 / (2 * α)))⁻¹ ≤ ((τ / (1 + τ)) ^ (1 / (2 * α)))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hq _) (Real.rpow_le_rpow hq.le (t_lower hτ) hp0)
    _ = (1 + τ) ^ (1 / (2 * α)) / τ ^ (1 / (2 * α)) := by
        rw [Real.div_rpow hτ.le (by positivity), inv_div]
    _ ≤ (1 + τ) / τ ^ (1 / (2 * α)) := by
        gcongr
        calc (1 + τ) ^ (1 / (2 * α)) ≤ (1 + τ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) hp1
          _ = 1 + τ := Real.rpow_one _
    _ = τ ^ (-(1 / (2 * α))) + τ ^ (1 - 1 / (2 * α)) := by
        rw [Real.rpow_neg hτ.le, Real.rpow_sub hτ, Real.rpow_one, add_div, one_div]

theorem lam_finite {α : ℝ} (h1 : 1 < α) (h2 : α < 5 / 4) :
    ∫⁻ p : ℝ × Space, ENNReal.ofReal (Real.exp (-p.1) ^ (1 - 1 / (2 * α)) /
      Real.exp (-p.1) ^ (1 / (2 * α))) * kk α p.1 p.2
      ∂((volume.restrict (Ioi (0 : ℝ))).prod volume) < ⊤ := by
  have hα : 0 < α := by linarith
  have hmeas : Measurable (fun p : ℝ × Space => ENNReal.ofReal (Real.exp (-p.1) ^ (1 - 1 / (2 * α)) /
      Real.exp (-p.1) ^ (1 / (2 * α))) * kk α p.1 p.2) :=
    (ENNReal.measurable_ofReal.comp (((Real.measurable_exp.comp measurable_fst.neg).pow_const _).div
      ((Real.measurable_exp.comp measurable_fst.neg).pow_const _))).mul (kk_meas hα)
  rw [lintegral_prod _ hmeas.aemeasurable]
  set L := ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ x, ‖projDivKernel α 1 i j k x‖ with hLdef
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => integral_nonneg fun _ => norm_nonneg _
  have hb : 0 < 1 - 1 / α := by
    have : 1 / α < 1 := by rw [div_lt_one hα]; exact h1
    linarith
  have hp1 : 1 / (2 * α) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hbound : ∫⁻ τ in Ioi (0 : ℝ), ∫⁻ z, ENNReal.ofReal (Real.exp (-τ) ^ (1 - 1 / (2 * α)) /
      Real.exp (-τ) ^ (1 / (2 * α))) * kk α τ z ≤
      ∫⁻ τ in Ioi (0 : ℝ), ENNReal.ofReal (L * (τ ^ (-(1 / (2 * α))) * Real.exp (-(1 - 1 / α) * τ ^ (1 : ℝ)) +
        τ ^ (1 - 1 / (2 * α)) * Real.exp (-(1 - 1 / α) * τ ^ (1 : ℝ)))) := by
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun τ hτ => ?_))
    have hτ' : 0 < τ := hτ
    rw [lintegral_const_mul _ (kk_meas_z hα τ),
      kk_lintegral hα hτ', ← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _)
        (Real.rpow_nonneg (Real.exp_pos _).le _))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hE : Real.exp (-τ) ^ (1 - 1 / (2 * α)) / Real.exp (-τ) ^ (1 / (2 * α)) =
        Real.exp (-(1 - 1 / α) * τ ^ (1 : ℝ)) := by
      rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_sub, Real.rpow_one]
      congr 1
      field_simp
      ring
    rw [hE, ← hLdef]
    have hT := t_pow_le h1 hτ'
    have hEp : 0 ≤ Real.exp (-(1 - 1 / α) * τ ^ (1 : ℝ)) := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left hT (mul_nonneg hEp hL)
    nlinarith [this]
  refine hbound.trans_lt ?_
  refine Integrable.lintegral_lt_top ?_
  refine Integrable.const_mul ?_ L
  exact (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hb).add
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hb)

def aA (α τ : ℝ) : ℝ := Real.exp (-τ) ^ (1 - 1 / (2 * α))

def cC (α τ : ℝ) : ℝ := Real.exp (-τ) ^ (1 / (2 * α))

def psi (α a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (y : Space) (p : ℝ × Space) : ℝ≥0∞ :=
  ‖F (cC α p.1 • axialRotation (-(a * p.1)) y - p.2)‖ₑ

def mm (α : ℝ) (p : ℝ × Space) : ℝ≥0∞ := ENNReal.ofReal (aA α p.1) * kk α p.1 p.2

def m1 (α : ℝ) (p : ℝ × Space) : ℝ≥0∞ := ENNReal.ofReal (aA α p.1 / cC α p.1) * kk α p.1 p.2

def m2 (α : ℝ) (p : ℝ × Space) : ℝ≥0∞ := ENNReal.ofReal (aA α p.1 * cC α p.1) * kk α p.1 p.2

theorem aA_meas (α : ℝ) : Measurable (fun p : ℝ × Space => aA α p.1) := by
  unfold aA; exact (Real.measurable_exp.comp measurable_fst.neg).pow_const _

theorem cC_meas (α : ℝ) : Measurable (fun p : ℝ × Space => cC α p.1) := by
  unfold cC; exact (Real.measurable_exp.comp measurable_fst.neg).pow_const _

theorem cC_pos (α τ : ℝ) : 0 < cC α τ := Real.rpow_pos_of_pos (Real.exp_pos _) _

theorem aA_nonneg (α τ : ℝ) : 0 ≤ aA α τ := Real.rpow_nonneg (Real.exp_pos _).le _

theorem mm_meas {α : ℝ} (hα : 0 < α) : Measurable (mm α) := by
  unfold mm; exact (ENNReal.measurable_ofReal.comp (aA_meas α)).mul (kk_meas hα)

theorem m1_meas {α : ℝ} (hα : 0 < α) : Measurable (m1 α) := by
  unfold m1; exact (ENNReal.measurable_ofReal.comp ((aA_meas α).div (cC_meas α))).mul (kk_meas hα)

theorem m2_meas {α : ℝ} (hα : 0 < α) : Measurable (m2 α) := by
  unfold m2; exact (ENNReal.measurable_ofReal.comp ((aA_meas α).mul (cC_meas α))).mul (kk_meas hα)

theorem psi_meas {α : ℝ} (hα : 0 < α) (a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (hF : Continuous F) :
    Measurable (Function.uncurry (psi α a F)) := by
  have hc := hF.comp (arg_cont α a hα)
  have e : Function.uncurry (psi α a F) = fun q => ‖(F ∘ fun q : Space × (ℝ × Space) =>
      Real.exp (-q.2.1) ^ (1 / (2 * α)) • axialRotation (-(a * q.2.1)) q.1 - q.2.2) q‖ₑ := by
    funext q; rfl
  rw [e]
  exact hc.measurable.enorm

theorem huv (α : ℝ) (p : ℝ × Space) : m1 α p * m2 α p = mm α p ^ 2 := by
  simp only [m1, m2, mm]
  have hC := cC_pos α p.1
  have hA := aA_nonneg α p.1
  have e : ENNReal.ofReal (aA α p.1 / cC α p.1) * ENNReal.ofReal (aA α p.1 * cC α p.1) =
      ENNReal.ofReal (aA α p.1) * ENNReal.ofReal (aA α p.1) := by
    rw [← ENNReal.ofReal_mul (div_nonneg hA hC.le), ← ENNReal.ofReal_mul hA]
    congr 1
    rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ hC.ne']
  have r : ∀ x y k : ℝ≥0∞, x * k * (y * k) = (x * y) * (k * k) := fun x y k => by ring
  rw [r, e]
  ring

theorem real_id {A C : ℝ} (hC : 0 < C) : A * C * |(C ^ 3)⁻¹| ^ (2 / 3 : ℝ) = A / C := by
  rw [abs_of_pos (by positivity), Real.inv_rpow (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hC.le]
  have e : ((3 : ℕ) : ℝ) * (2 / 3 : ℝ) = 2 := by norm_num
  rw [e, Real.rpow_two, pow_two, mul_inv, ← mul_assoc, mul_assoc A C C⁻¹, mul_inv_cancel₀ hC.ne',
    mul_one, div_eq_mul_inv]

theorem pointwise' {α : ℝ} (hα : 0 < α) (a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (hF : Continuous F)
    (y : Space) :
    ‖farFieldOp α a F y‖ₑ ≤ ∫⁻ p, mm α p * psi α a F y p ∂((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hm : Measurable (fun p => mm α p * psi α a F y p) :=
    (mm_meas hα).mul (psi_meas hα a F hF).of_uncurry_left
  rw [lintegral_prod (fun p => mm α p * psi α a F y p) hm.aemeasurable]
  exact pointwise hα a F hF y

theorem weight_six : ∫⁻ y : Space, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (6 : ℝ) < ⊤ := by
  have hi := integrable_one_add_norm (E := Space) (μ := volume) (r := 6)
    (by rw [finrank_euclideanSpace_fin]; norm_num)
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) hi.lintegral_lt_top
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.inv_rpow (by positivity),
    ← Real.rpow_neg (by positivity)]

theorem hbase {α : ℝ} (h1 : 1 < α) (h2 : α < 5 / 4) (a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ)
    (hF : Continuous F) (hF3 : ∫⁻ x, ‖F x‖ₑ ^ (3 : ℝ) < ⊤) :
    ∫⁻ y, (ENNReal.ofReal ((1 + ‖y‖)⁻¹) * ‖farFieldOp α a F y‖ₑ) ^ (2 : ℝ) < ⊤ := by
  have hα : 0 < α := by linarith
  have hΛ : ∫⁻ p, m1 α p ∂((volume.restrict (Ioi (0 : ℝ))).prod volume) < ⊤ := lam_finite h1 h2
  have hW6 := weight_six
  have hwm : Measurable (fun y : Space => ENNReal.ofReal ((1 + ‖y‖)⁻¹)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hψ := psi_meas hα a F hF
  have hK : (∫⁻ y : Space, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (6 : ℝ)) ^ (1 / 3 : ℝ) *
      (∫⁻ x, ‖F x‖ₑ ^ (3 : ℝ)) ^ (2 / 3 : ℝ) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hW6.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hF3.ne)
  have hc3 : Real.HolderConjugate 3 (3 / 2) :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).2 (by norm_num)
  have inner : ∀ p : ℝ × Space, ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (2 : ℝ) *
      (m2 α p * psi α a F y p ^ (2 : ℝ)) ≤
      m1 α p * ((∫⁻ y : Space, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (6 : ℝ)) ^ (1 / 3 : ℝ) *
      (∫⁻ x, ‖F x‖ₑ ^ (3 : ℝ)) ^ (2 / 3 : ℝ)) := by
    intro p
    have hψm : Measurable (fun y => psi α a F y p) := hψ.of_uncurry_right
    have hch := lintegral_affine (fun x => ‖F x‖ₑ ^ (3 : ℝ)) (hF.measurable.enorm.pow_const _)
      (cC_pos α p.1).ne' (axialRotation (-(a * p.1))) p.2
    have hch' : ∫⁻ y, psi α a F y p ^ (3 : ℝ) =
        ENNReal.ofReal |(cC α p.1 ^ 3)⁻¹| * ∫⁻ x, ‖F x‖ₑ ^ (3 : ℝ) := hch
    calc ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (2 : ℝ) * (m2 α p * psi α a F y p ^ (2 : ℝ))
        = m2 α p * ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (2 : ℝ) * psi α a F y p ^ (2 : ℝ) := by
          have hm : Measurable (fun y : Space => ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (2 : ℝ) * psi α a F y p ^ (2 : ℝ)) :=
            (hwm.pow_const _).mul (hψm.pow_const _)
          rw [← lintegral_const_mul _ hm]
          refine lintegral_congr fun y => ?_
          ring
      _ ≤ m2 α p * ((∫⁻ y : Space, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (6 : ℝ)) ^ (1 / 3 : ℝ) *
          (∫⁻ y, psi α a F y p ^ (3 : ℝ)) ^ (2 / 3 : ℝ)) := by
          gcongr
          have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hc3 (hwm.pow_const (2 : ℝ)).aemeasurable
            (hψm.pow_const (2 : ℝ)).aemeasurable
          have e1 : ∀ y : Space, (ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (2 : ℝ)) ^ (3 : ℝ) =
              ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (6 : ℝ) := fun y => by
            rw [← ENNReal.rpow_mul]; norm_num
          have e2 : ∀ y : Space, (psi α a F y p ^ (2 : ℝ)) ^ (3 / 2 : ℝ) = psi α a F y p ^ (3 : ℝ) :=
            fun y => by rw [← ENNReal.rpow_mul]; norm_num
          simp only [Pi.mul_apply, e1, e2] at hH
          rw [show (1 : ℝ) / (3 / 2) = 2 / 3 by norm_num] at hH
          exact hH
      _ = m2 α p * ((∫⁻ y : Space, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (6 : ℝ)) ^ (1 / 3 : ℝ) *
          (ENNReal.ofReal |(cC α p.1 ^ 3)⁻¹| * ∫⁻ x, ‖F x‖ₑ ^ (3 : ℝ)) ^ (2 / 3 : ℝ)) := by
          rw [hch']
      _ = m1 α p * ((∫⁻ y : Space, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (6 : ℝ)) ^ (1 / 3 : ℝ) *
          (∫⁻ x, ‖F x‖ₑ ^ (3 : ℝ)) ^ (2 / 3 : ℝ)) := by
          simp only [m1, m2]
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
            ← real_id (A := aA α p.1) (cC_pos α p.1),
            ENNReal.ofReal_mul (mul_nonneg (aA_nonneg α p.1) (cC_pos α p.1).le)]
          ring
  have hjoint : Measurable (Function.uncurry fun (y : Space) (p : ℝ × Space) =>
      ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (2 : ℝ) * (m2 α p * psi α a F y p ^ (2 : ℝ))) :=
    ((hwm.comp measurable_fst).pow_const _).mul (((m2_meas hα).comp measurable_snd).mul (hψ.pow_const _))
  have hwne : ∀ y : Space, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (2 : ℝ) ≠ ⊤ := fun y =>
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  calc ∫⁻ y, (ENNReal.ofReal ((1 + ‖y‖)⁻¹) * ‖farFieldOp α a F y‖ₑ) ^ (2 : ℝ)
      ≤ ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (2 : ℝ) *
          ((∫⁻ p, m1 α p ∂((volume.restrict (Ioi (0 : ℝ))).prod volume)) *
          ∫⁻ p, m2 α p * psi α a F y p ^ (2 : ℝ) ∂((volume.restrict (Ioi (0 : ℝ))).prod volume)) := by
        refine lintegral_mono fun y => ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        gcongr
        exact (ENNReal.rpow_le_rpow (pointwise' hα a F hF y) (by norm_num)).trans
          (cst_weighted _ (m1 α) (m2 α) (psi α a F y) (mm α) (m1_meas hα) (m2_meas hα)
            hψ.of_uncurry_left (huv α))
    _ = ∫⁻ y, (∫⁻ p, m1 α p ∂((volume.restrict (Ioi (0 : ℝ))).prod volume)) *
          ∫⁻ p, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (2 : ℝ) * (m2 α p * psi α a F y p ^ (2 : ℝ))
            ∂((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul' _ _ (hwne y), mul_left_comm]
    _ = (∫⁻ p, m1 α p ∂((volume.restrict (Ioi (0 : ℝ))).prod volume)) *
          ∫⁻ y, ∫⁻ p, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (2 : ℝ) * (m2 α p * psi α a F y p ^ (2 : ℝ))
            ∂((volume.restrict (Ioi (0 : ℝ))).prod volume) := lintegral_const_mul' _ _ hΛ.ne
    _ = (∫⁻ p, m1 α p ∂((volume.restrict (Ioi (0 : ℝ))).prod volume)) *
          ∫⁻ p, (∫⁻ y, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (2 : ℝ) * (m2 α p * psi α a F y p ^ (2 : ℝ)))
            ∂((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
        rw [lintegral_lintegral_swap hjoint.aemeasurable]
    _ ≤ (∫⁻ p, m1 α p ∂((volume.restrict (Ioi (0 : ℝ))).prod volume)) *
          ∫⁻ p, m1 α p * ((∫⁻ y : Space, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (6 : ℝ)) ^ (1 / 3 : ℝ) *
            (∫⁻ x, ‖F x‖ₑ ^ (3 : ℝ)) ^ (2 / 3 : ℝ)) ∂((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
        exact mul_le_mul' le_rfl (lintegral_mono fun p => inner p)
    _ = (∫⁻ p, m1 α p ∂((volume.restrict (Ioi (0 : ℝ))).prod volume)) *
          ((∫⁻ p, m1 α p ∂((volume.restrict (Ioi (0 : ℝ))).prod volume)) *
          ((∫⁻ y : Space, ENNReal.ofReal ((1 + ‖y‖)⁻¹) ^ (6 : ℝ)) ^ (1 / 3 : ℝ) *
            (∫⁻ x, ‖F x‖ₑ ^ (3 : ℝ)) ^ (2 / 3 : ℝ))) := by
        rw [lintegral_mul_const _ (m1_meas hα)]
    _ < ⊤ := ENNReal.mul_lt_top hΛ (ENNReal.mul_lt_top hΛ hK)

theorem profile_cont (U : X) (hM : HasAllMoments U) : Continuous (profileField U) := by
  have h0 := (symbolL1OfMoments U hM).1 0
  simp only [pow_zero, one_mul] at h0
  exact WeakRegularInternal.continuous_physField_of
    ((integrable_norm_iff (WeakRegularInternal.aesm_symbolX U)).1 h0)


theorem profile_six (U : X) (hM : HasAllMoments U) : MemLp (profileField U) 6 volume :=
  (Lp.memLp (velocity U)).ae_eq (symbolL1OfMoments U hM).2

theorem tensor_cont {V : Space → Space} (hV : Continuous V) : Continuous (tensorSq V) := by
  unfold tensorSq
  refine continuous_pi fun j => continuous_pi fun k => ?_
  exact ((continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp hV)).mul
    ((continuous_apply k).comp ((PiLp.continuous_ofLp 2 _).comp hV))

theorem tensor_bound (V : Space → Space) (x : Space) : ‖tensorSq V x‖ ≤ ‖V x‖ ^ 2 := by
  refine (pi_norm_le_iff_of_nonneg (sq_nonneg _)).2 fun j => ?_
  refine (pi_norm_le_iff_of_nonneg (sq_nonneg _)).2 fun k => ?_
  rw [tensorSq, norm_mul, sq]
  exact mul_le_mul (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _) (norm_nonneg _) (norm_nonneg _)

theorem tensor_three (V : Space → Space) (hV : MemLp V 6 volume) :
    ∫⁻ x, ‖tensorSq V x‖ₑ ^ (3 : ℝ) < ⊤ := by
  have h6 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := volume) (p := 6) (by norm_num)
    (by norm_num) hV.2
  rw [show (6 : ℝ≥0∞).toReal = 6 by norm_num] at h6
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) h6
  calc ‖tensorSq V x‖ₑ ^ (3 : ℝ) ≤ (‖V x‖ₑ ^ (2 : ℝ)) ^ (3 : ℝ) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
          Real.rpow_two]
        exact ENNReal.ofReal_le_ofReal (tensor_bound V x)
    _ = ‖V x‖ₑ ^ (6 : ℝ) := by rw [← ENNReal.rpow_mul]; norm_num

def kf (α : ℝ) (i j k : Fin 3) (q : ℝ × Space) : ℝ :=
  ((((1 - Real.exp (-q.1)) ^ (-(2 / α)) : ℝ) : ℂ) *
    projDivKernel α 1 i j k (((1 - Real.exp (-q.1)) ^ (-(1 / (2 * α)))) • q.2)).re

theorem kf_meas {α : ℝ} (hα : 0 < α) (i j k : Fin 3) : Measurable (kf α i j k) := by
  unfold kf
  have ht : Measurable (fun q : ℝ × Space => 1 - Real.exp (-q.1)) :=
    (continuous_const.sub (Real.continuous_exp.comp continuous_fst.neg)).measurable
  exact Complex.measurable_re.comp ((Complex.measurable_ofReal.comp (ht.pow_const _)).mul
    ((kernel_cont hα i j k one_pos).measurable.comp ((ht.pow_const _).smul measurable_snd)))

theorem kf_eq {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) (i j k : Fin 3) (w : Space) :
    kf α i j k (τ, w) = (projDivKernel α (1 - Real.exp (-τ)) i j k w).re := by
  unfold kf
  rw [(kernelScalingHolds α hα i j k _ (t_pos hτ)).1 w]

def hform (α : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (q : ℝ × Space) : Space :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    (fun i => ∑ j : Fin 3, ∑ k : Fin 3, ∫ z, kf α i j k (q.1, q.2 - z) * F z j k)

theorem hform_eq {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) (F : Space → Fin 3 → Fin 3 → ℝ) (x : Space) :
    heatDivConv α (1 - Real.exp (-τ)) F x = hform α F (τ, x) := by
  unfold heatDivConv hform
  congr 1
  funext i
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [kf_eq hα hτ]

theorem hform_meas {α : ℝ} (hα : 0 < α) (F : Space → Fin 3 → Fin 3 → ℝ) (hF : Continuous F) :
    Measurable (hform α F) := by
  have hc : ∀ i j k : Fin 3, Measurable
      (fun q : ℝ × Space => ∫ z, kf α i j k (q.1, q.2 - z) * F z j k) := fun i j k => by
    have hFjk : Continuous (fun z : Space => F z j k) :=
      (continuous_apply k).comp ((continuous_apply j).comp hF)
    have hm : Measurable (fun r : (ℝ × Space) × Space => kf α i j k (r.1.1, r.1.2 - r.2) * F r.2 j k) :=
      ((kf_meas hα i j k).comp (measurable_fst.fst.prodMk (measurable_fst.snd.sub measurable_snd))).mul
        (hFjk.measurable.comp measurable_snd)
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have hv : Measurable (fun q : ℝ × Space => fun i : Fin 3 =>
      ∑ j : Fin 3, ∑ k : Fin 3, ∫ z, kf α i j k (q.1, q.2 - z) * F z j k) :=
    measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun j _ =>
      Finset.measurable_sum _ fun k _ => hc i j k
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp hv

def gform (α a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (q : Space × ℝ) : Space :=
  axialRotation (a * q.2) (Real.exp (-q.2) ^ (1 - 1 / (2 * α)) •
    hform α F (q.2, Real.exp (-q.2) ^ (1 / (2 * α)) • axialRotation (-(a * q.2)) q.1))

theorem g_eq {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) (a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (y : Space) :
    pushForward (axialRotation (a * τ)) (scaleField α (Real.exp (-τ))
      (heatDivConv α (1 - Real.exp (-τ)) F)) y = gform α a F (y, τ) := by
  simp only [pushForward, scaleField, rot_symm, gform, hform_eq hα hτ]

theorem gform_meas {α : ℝ} (hα : 0 < α) (a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (hF : Continuous F) :
    Measurable (gform α a F) := by
  have h0 : Continuous (fun p : ℝ × Space => axialRotation p.1 p.2) :=
    (Periodic.FracSelfSimilar.Internal.rot_contDiff axialRotationSpec).continuous
  have hpair : Continuous (fun q : Space × ℝ => ((-(a * q.2), q.1) : ℝ × Space)) := by fun_prop
  have hr : Continuous (fun q : Space × ℝ => axialRotation (-(a * q.2)) q.1) := by
    refine (h0.comp hpair).congr fun q => ?_
    simp only [Function.comp_apply]
  have hc : Continuous (fun q : Space × ℝ => Real.exp (-q.2) ^ (1 / (2 * α))) :=
    (Real.continuous_exp.comp continuous_snd.neg).rpow_const fun _ => Or.inr (by positivity)
  have hP : Measurable (fun q : Space × ℝ => ((q.2, Real.exp (-q.2) ^ (1 / (2 * α)) •
      axialRotation (-(a * q.2)) q.1) : ℝ × Space)) :=
    (continuous_snd.prodMk (hc.smul hr)).measurable
  have hH : Measurable (fun q : Space × ℝ => hform α F (q.2, Real.exp (-q.2) ^ (1 / (2 * α)) •
      axialRotation (-(a * q.2)) q.1)) := (hform_meas hα F hF).comp hP
  have hA : Measurable (fun q : Space × ℝ => Real.exp (-q.2) ^ (1 - 1 / (2 * α))) :=
    (Real.measurable_exp.comp measurable_snd.neg).pow_const _
  have hQ : Measurable (fun q : Space × ℝ => ((a * q.2, Real.exp (-q.2) ^ (1 - 1 / (2 * α)) •
      hform α F (q.2, Real.exp (-q.2) ^ (1 / (2 * α)) • axialRotation (-(a * q.2)) q.1)) : ℝ × Space)) :=
    (measurable_const.mul measurable_snd).prodMk (hA.smul hH)
  have e : gform α a F = (fun p : ℝ × Space => axialRotation p.1 p.2) ∘ (fun q : Space × ℝ =>
      ((a * q.2, Real.exp (-q.2) ^ (1 - 1 / (2 * α)) •
      hform α F (q.2, Real.exp (-q.2) ^ (1 / (2 * α)) • axialRotation (-(a * q.2)) q.1)) : ℝ × Space)) := by
    funext q; rfl
  rw [e]
  exact h0.measurable.comp hQ

theorem far_meas {α : ℝ} (hα : 0 < α) (a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (hF : Continuous F) :
    AEStronglyMeasurable (farFieldOp α a F) volume := by
  have e : farFieldOp α a F = fun y => -∫ τ in Ioi (0 : ℝ), gform α a F (y, τ) := by
    funext y
    unfold farFieldOp
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi fun τ hτ => g_eq hα hτ a F y
  rw [e]
  exact ((gform_meas hα a F hF).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioi (0 : ℝ)))).neg.aestronglyMeasurable


end FarFieldWeightedInternal

open FarFieldWeightedInternal in
theorem farFieldWeighted : FarFieldWeightedStatement := by
  intro α h1 h2 a U hM
  have hW := far_meas (by linarith) a _ (tensor_cont (profile_cont U hM))
  have hw : Continuous (fun y : Space => (1 + ‖y‖)⁻¹) :=
    (continuous_const.add continuous_norm).inv₀ fun y => (by have := norm_nonneg y; linarith : (0 : ℝ) < 1 + ‖y‖).ne'
  refine ⟨hw.aestronglyMeasurable.smul hW, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt ?_)
  have hbase := hbase h1 h2 a _ (tensor_cont (profile_cont U hM))
    (tensor_three _ (profile_six U hM))
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) hbase
  rw [enorm_smul, ← ofReal_norm (x := (1 + ‖y‖)⁻¹), Real.norm_of_nonneg (by positivity),
    show (2 : ℝ≥0∞).toReal = 2 by norm_num]


end Breakdown.FracCert
