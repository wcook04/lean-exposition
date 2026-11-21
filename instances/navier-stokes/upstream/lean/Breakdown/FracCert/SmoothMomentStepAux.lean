import Breakdown.FracCert.SmoothMomentStepSymbol
import Breakdown.Frac.RegPowerHeatSolenoidal
import Breakdown.Frac.RegPowerHeatGain
import Breakdown.Uniqueness.RegAprioriAuxMildPart1

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

private theorem momentWeight_measurable (m : ℕ) :
    Measurable fun ξ : Space => ‖ξ‖ ^ m * (2 * π * ‖ξ‖)⁻¹ := by
  fun_prop

private theorem homNormSq_symbolX_eq (m : ℕ) (x : X) :
    homNormSq m (symbolX x) ^ (1 / 2 : ℝ) =
      eLpNorm (fun ξ => (‖ξ‖ ^ m * (2 * π * ‖ξ‖)⁻¹) • (x : L2C) ξ) 2 volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  unfold homNormSq symbolX
  refine lintegral_congr fun ξ => ?_
  rw [mul_smul, enorm_smul (‖ξ‖ ^ m), ENNReal.rpow_two, mul_pow,
    Real.enorm_eq_ofReal (pow_nonneg (norm_nonneg _) _), ← ENNReal.ofReal_pow (pow_nonneg (norm_nonneg _) _),
    ← pow_mul, mul_comm m 2]

theorem smoothMomentNorm_add (m : ℕ) (x y : X) :
    homNormSq m (symbolX (x + y)) ^ (1 / 2 : ℝ) ≤
      homNormSq m (symbolX x) ^ (1 / 2 : ℝ) + homNormSq m (symbolX y) ^ (1 / 2 : ℝ) := by
  rw [homNormSq_symbolX_eq, homNormSq_symbolX_eq, homNormSq_symbolX_eq]
  have hae : (fun ξ => (‖ξ‖ ^ m * (2 * π * ‖ξ‖)⁻¹) • ((x + y : X) : L2C) ξ) =ᵐ[volume]
      (fun ξ => (‖ξ‖ ^ m * (2 * π * ‖ξ‖)⁻¹) • (x : L2C) ξ) +
        (fun ξ => (‖ξ‖ ^ m * (2 * π * ‖ξ‖)⁻¹) • (y : L2C) ξ) := by
    have h := Lp.coeFn_add (x : L2C) (y : L2C)
    filter_upwards [h] with ξ hξ
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [hξ, Pi.add_apply, smul_add]
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_add_le
    ((momentWeight_measurable m).aestronglyMeasurable.smul (Lp.aestronglyMeasurable _))
    ((momentWeight_measurable m).aestronglyMeasurable.smul (Lp.aestronglyMeasurable _)) one_le_two

private theorem heat_weight_le {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) (ξ : Space) :
    ‖ξ‖ ^ 2 * fracHeatFactor α τ ξ ^ 2 ≤ (1 / α) ^ (1 / α) * τ ^ (-(1 / α)) := by
  have hq : 0 < 1 / α := one_div_pos.2 hα
  have ha0 : 0 ≤ 2 * π * ‖ξ‖ := by positivity
  have hxa : ‖ξ‖ ≤ 2 * π * ‖ξ‖ := by
    have : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    nlinarith [norm_nonneg ξ]
  have hs : 0 ≤ 2 * τ * (2 * π * ‖ξ‖) ^ (2 * α) := by positivity
  have hf : fracHeatFactor α τ ξ ^ 2 = Real.exp (-(2 * τ * (2 * π * ‖ξ‖) ^ (2 * α))) := by
    unfold fracHeatFactor
    rw [max_eq_left hτ.le, sq, ← Real.exp_add]
    ring_nf
  have key := PowerInternal.gainRpowLeMulExp hs hq
  have hpow : (2 * τ * (2 * π * ‖ξ‖) ^ (2 * α)) ^ (1 / α) = (2 * τ) ^ (1 / α) * (2 * π * ‖ξ‖) ^ 2 := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg ha0 _), ← Real.rpow_mul ha0,
      show 2 * α * (1 / α) = 2 by field_simp]
    norm_cast
  rw [hpow] at key
  have h2τ : 0 < (2 * τ) ^ (1 / α) := Real.rpow_pos_of_pos (by positivity) _
  have hexp : Real.exp (2 * τ * (2 * π * ‖ξ‖) ^ (2 * α)) *
      Real.exp (-(2 * τ * (2 * π * ‖ξ‖) ^ (2 * α))) = 1 := by
    rw [← Real.exp_add]; simp
  have hE := Real.exp_pos (-(2 * τ * (2 * π * ‖ξ‖) ^ (2 * α)))
  have step : (2 * π * ‖ξ‖) ^ 2 * Real.exp (-(2 * τ * (2 * π * ‖ξ‖) ^ (2 * α))) ≤
      (1 / α) ^ (1 / α) * ((2 * τ) ^ (1 / α))⁻¹ := by
    rw [le_mul_inv_iff₀ h2τ]
    calc (2 * π * ‖ξ‖) ^ 2 * Real.exp (-(2 * τ * (2 * π * ‖ξ‖) ^ (2 * α))) * (2 * τ) ^ (1 / α)
        = ((2 * τ) ^ (1 / α) * (2 * π * ‖ξ‖) ^ 2) *
            Real.exp (-(2 * τ * (2 * π * ‖ξ‖) ^ (2 * α))) := by ring
      _ ≤ ((1 / α) ^ (1 / α) * Real.exp (2 * τ * (2 * π * ‖ξ‖) ^ (2 * α))) *
            Real.exp (-(2 * τ * (2 * π * ‖ξ‖) ^ (2 * α))) := mul_le_mul_of_nonneg_right key hE.le
      _ = (1 / α) ^ (1 / α) := by rw [mul_assoc, hexp, mul_one]
  have hmono : ((2 * τ) ^ (1 / α))⁻¹ ≤ τ ^ (-(1 / α)) := by
    rw [← Real.rpow_neg (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos hτ (by linarith) (by linarith)
  have hqq : 0 ≤ (1 / α) ^ (1 / α) := Real.rpow_nonneg hq.le _
  rw [hf]
  calc ‖ξ‖ ^ 2 * Real.exp (-(2 * τ * (2 * π * ‖ξ‖) ^ (2 * α)))
      ≤ (2 * π * ‖ξ‖) ^ 2 * Real.exp (-(2 * τ * (2 * π * ‖ξ‖) ^ (2 * α))) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hxa 2) hE.le
    _ ≤ (1 / α) ^ (1 / α) * ((2 * τ) ^ (1 / α))⁻¹ := step
    _ ≤ (1 / α) ^ (1 / α) * τ ^ (-(1 / α)) := mul_le_mul_of_nonneg_left hmono hqq

theorem smoothHeatMomentGain (α : ℝ) (hα : 1 < α) (k : ℕ) : ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → ∀ x : X,
    homNormSq (k + 1) (symbolX (fracHeatX α τ x)) ≤
      ENNReal.ofReal (C * τ ^ (-(1 / α))) * homNormSq k (symbolX x) := by
  refine ⟨(1 / α) ^ (1 / α), fun τ hτ x => ?_⟩
  have hae := powerHeatX α τ x
  unfold homNormSq
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hae] with ξ hξ
  unfold symbolX
  rw [hξ, Complex.coe_smul, smul_comm, enorm_smul, mul_pow,
    Real.enorm_eq_ofReal (Breakdown.FracInternal.RHeat.factor_pos α τ ξ).le,
    ← ENNReal.ofReal_pow (Breakdown.FracInternal.RHeat.factor_pos α τ ξ).le]
  have hw := heat_weight_le (by linarith : (0 : ℝ) < α) hτ ξ
  have e1 : ENNReal.ofReal (‖ξ‖ ^ (2 * (k + 1))) =
      ENNReal.ofReal (‖ξ‖ ^ 2) * ENNReal.ofReal (‖ξ‖ ^ (2 * k)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← pow_add]; ring_nf
  rw [e1]
  calc ENNReal.ofReal (‖ξ‖ ^ 2) * ENNReal.ofReal (‖ξ‖ ^ (2 * k)) *
        (ENNReal.ofReal (fracHeatFactor α τ ξ ^ 2) * ‖(2 * π * ‖ξ‖)⁻¹ • (x : L2C) ξ‖ₑ ^ 2)
      = ENNReal.ofReal (‖ξ‖ ^ 2 * fracHeatFactor α τ ξ ^ 2) *
          (ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * ‖(2 * π * ‖ξ‖)⁻¹ • (x : L2C) ξ‖ₑ ^ 2) := by
        rw [ENNReal.ofReal_mul (by positivity)]; ring
    _ ≤ _ := by gcongr

private theorem norm_pow_le_split (k : ℕ) (ξ η : Space) :
    ‖ξ‖ ^ k ≤ 2 ^ k * (‖η‖ ^ k + ‖ξ - η‖ ^ k) := by
  have h1 : ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by
    have := norm_add_le η (ξ - η)
    rwa [add_sub_cancel] at this
  have hM : ‖ξ‖ ≤ 2 * max ‖η‖ ‖ξ - η‖ := by
    have := le_max_left ‖η‖ ‖ξ - η‖
    have := le_max_right ‖η‖ ‖ξ - η‖
    linarith
  calc ‖ξ‖ ^ k ≤ (2 * max ‖η‖ ‖ξ - η‖) ^ k := pow_le_pow_left₀ (norm_nonneg _) hM k
    _ = 2 ^ k * max ‖η‖ ‖ξ - η‖ ^ k := mul_pow _ _ _
    _ ≤ _ := by
      have hp1 : (0 : ℝ) ≤ ‖η‖ ^ k := by positivity
      have hp2 : (0 : ℝ) ≤ ‖ξ - η‖ ^ k := by positivity
      gcongr
      rcases le_total ‖η‖ ‖ξ - η‖ with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith

private theorem lintegral_hom_conv_sq_le (k : ℕ) {a : Space → ℝ≥0∞} (ha : Measurable a) :
    ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * (∫⁻ η, a η * a (ξ - η)) ^ 2 ≤
      4 ^ (k + 1) * (∫⁻ η, a η) ^ 2 * ∫⁻ η, ENNReal.ofReal (‖η‖ ^ (2 * k)) * a η ^ 2 := by
  obtain ⟨s, hs_def⟩ : ∃ s : Space → ℝ≥0∞, s = fun ξ => ENNReal.ofReal (‖ξ‖ ^ k) := ⟨_, rfl⟩
  have hs : Measurable s := by rw [hs_def]; fun_prop
  obtain ⟨v, hv_def⟩ : ∃ v : Space → ℝ≥0∞, v = fun η => s η * a η := ⟨_, rfl⟩
  have hv : Measurable v := by rw [hv_def]; exact hs.mul ha
  obtain ⟨W, hW⟩ : ∃ W, W = ∫⁻ η, a η := ⟨_, rfl⟩
  have hsub : ∀ ξ, Measurable fun η : Space => ξ - η := fun ξ => measurable_const.sub measurable_id
  have hsq2 : ∀ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * k)) = s ξ ^ 2 := fun ξ => by
    rw [hs_def, ← ENNReal.ofReal_pow (by positivity), ← pow_mul, Nat.mul_comm]
  have hA : ∀ ξ, s ξ * ∫⁻ η, a η * a (ξ - η) ≤ 2 ^ (k + 1) * ∫⁻ η, v η * a (ξ - η) := by
    intro ξ
    rw [← lintegral_const_mul' _ _ (by rw [hs_def]; exact ENNReal.ofReal_ne_top)]
    have hsym : ∫⁻ η, a η * v (ξ - η) = ∫⁻ η, v η * a (ξ - η) := by
      have := lintegral_sub_left_eq_self (μ := volume) (fun η => a η * v (ξ - η)) ξ
      simp only [sub_sub_cancel] at this
      rw [← this]
      refine lintegral_congr fun η => ?_
      ring
    have m1 : Measurable fun η => v η * a (ξ - η) := hv.mul (ha.comp (hsub ξ))
    have m2 : Measurable fun η => a η * v (ξ - η) := ha.mul (hv.comp (hsub ξ))
    calc ∫⁻ η, s ξ * (a η * a (ξ - η)) ≤
          ∫⁻ η, 2 ^ k * (v η * a (ξ - η)) + 2 ^ k * (a η * v (ξ - η)) := by
          refine lintegral_mono fun η => ?_
          have h' : s ξ ≤ 2 ^ k * (s η + s (ξ - η)) := by
            rw [hs_def]
            simp only
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              show (2 : ℝ≥0∞) ^ k = ENNReal.ofReal (2 ^ k) by simp,
              ← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (norm_pow_le_split k ξ η)
          calc s ξ * (a η * a (ξ - η)) ≤ 2 ^ k * (s η + s (ξ - η)) * (a η * a (ξ - η)) := by
                gcongr
            _ = _ := by rw [hv_def]; ring
      _ = 2 ^ k * (∫⁻ η, v η * a (ξ - η)) + 2 ^ k * ∫⁻ η, a η * v (ξ - η) := by
          rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1, lintegral_const_mul _ m2]
      _ = 2 ^ (k + 1) * ∫⁻ η, v η * a (ξ - η) := by
          rw [hsym]
          ring
  have hC : ∀ ξ, (∫⁻ η, v η * a (ξ - η)) ^ 2 ≤ W * ∫⁻ η, a (ξ - η) * v η ^ 2 := by
    intro ξ
    have hm1 : Measurable fun η => a (ξ - η) := ha.comp (hsub ξ)
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
      (hm1.pow_const (1 / 2 : ℝ)).aemeasurable ((hm1.pow_const (1 / 2 : ℝ)).mul hv).aemeasurable
    have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
      rw [← ENNReal.rpow_mul]; norm_num
    have hhalf : ∀ x : ℝ≥0∞, x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := fun x => by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
    simp only [Pi.mul_apply, ← mul_assoc, hhalf, hsq, ENNReal.mul_rpow_of_nonneg _ _ zero_le_two,
      ENNReal.rpow_two] at h
    rw [lintegral_sub_left_eq_self a ξ, ← hW] at h
    have e1 : ∫⁻ η, v η * a (ξ - η) = ∫⁻ η, a (ξ - η) * v η :=
      lintegral_congr fun η => mul_comm _ _
    calc (∫⁻ η, v η * a (ξ - η)) ^ 2 ≤
          (W ^ (1 / 2 : ℝ) * (∫⁻ η, a (ξ - η) * v η ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
          rw [e1]
          gcongr ?_ ^ 2
      _ = W * ∫⁻ η, a (ξ - η) * v η ^ 2 := by
          rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul]
          norm_num
  have hD : ∫⁻ ξ, ∫⁻ η, a (ξ - η) * v η ^ 2 = W * ∫⁻ η, v η ^ 2 := by
    rw [lintegral_lintegral_swap]
    · rw [hW, ← lintegral_const_mul]
      · refine lintegral_congr fun η => ?_
        rw [lintegral_mul_const (v η ^ 2) (f := fun x => a (x - η)) (ha.comp (measurable_id.sub measurable_const)),
          lintegral_sub_right_eq_self a η]
      · exact hv.pow_const 2
    · exact ((ha.comp (measurable_fst.sub measurable_snd)).mul
        ((hv.comp measurable_snd).pow_const 2)).aemeasurable
  have hv2 : ∫⁻ η, v η ^ 2 = ∫⁻ η, ENNReal.ofReal (‖η‖ ^ (2 * k)) * a η ^ 2 := by
    refine lintegral_congr fun η => ?_
    rw [hv_def, hsq2, mul_pow]
  rw [← hW, ← hv2]
  calc ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * (∫⁻ η, a η * a (ξ - η)) ^ 2
        ≤ ∫⁻ ξ, 4 ^ (k + 1) * (W * ∫⁻ η, a (ξ - η) * v η ^ 2) := by
        refine lintegral_mono fun ξ => ?_
        calc ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * (∫⁻ η, a η * a (ξ - η)) ^ 2
            = (s ξ * ∫⁻ η, a η * a (ξ - η)) ^ 2 := by rw [hsq2, mul_pow]
          _ ≤ (2 ^ (k + 1) * ∫⁻ η, v η * a (ξ - η)) ^ 2 := by gcongr ?_ ^ 2; exact hA ξ
          _ = 4 ^ (k + 1) * (∫⁻ η, v η * a (ξ - η)) ^ 2 := by
            rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]
            norm_num
          _ ≤ _ := by gcongr; exact hC ξ
    _ = 4 ^ (k + 1) * (W * (W * ∫⁻ η, v η ^ 2)) := by
        have hG : Measurable fun ξ => ∫⁻ η, a (ξ - η) * v η ^ 2 :=
          ((ha.comp (measurable_fst.sub measurable_snd)).mul
            ((hv.comp measurable_snd).pow_const 2)).lintegral_prod_right'
        rw [lintegral_const_mul _ (hG.const_mul _), lintegral_const_mul _ hG, hD]
    _ = _ := by ring

theorem smoothConvMomentBound (k : ℕ) : ∃ C : ℝ, ∀ f : Space → CSpace, AEStronglyMeasurable f volume →
    ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * convEnormSum f ξ ^ 2 ≤
      ENNReal.ofReal C * (freqL1Norm f ^ 2 * homNormSq k f) := by
  refine ⟨81 * 4 ^ (k + 1), fun f hf => ?_⟩
  obtain ⟨g, hg_def⟩ : ∃ g, g = hf.mk f := ⟨_, rfl⟩
  have hg : Measurable fun η => ‖g η‖ₑ := by rw [hg_def]; exact hf.stronglyMeasurable_mk.measurable.enorm
  have hfg : f =ᵐ[volume] g := by rw [hg_def]; exact hf.ae_eq_mk
  have hpt : ∀ ξ, convEnormSum f ξ ≤ 9 * ∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ := by
    intro ξ
    have hsh : (fun η => f (ξ - η)) =ᵐ[volume] fun η => g (ξ - η) :=
      (Measure.measurePreserving_sub_left volume ξ).quasiMeasurePreserving.ae_eq hfg
    have hij : ∀ i j : Fin 3, ‖convC (fun η => f η j) (fun η => f η i) ξ‖ₑ ≤
        ∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ := by
      intro i j
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      calc ∫⁻ η, ‖f η j * f (ξ - η) i‖ₑ ≤ ∫⁻ η, ‖f η‖ₑ * ‖f (ξ - η)‖ₑ := by
            refine lintegral_mono fun η => ?_
            rw [enorm_mul]
            exact mul_le_mul' (PiLp.enorm_apply_le _ _) (PiLp.enorm_apply_le _ _)
        _ = ∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ := by
            refine lintegral_congr_ae ?_
            filter_upwards [hfg, hsh] with η h1 h2
            rw [h1, h2]
    calc convEnormSum f ξ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
      _ = 9 * ∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
          ring
  have hW : freqL1Norm f = ∫⁻ η, ‖g η‖ₑ := by
    unfold freqL1Norm
    refine lintegral_congr_ae ?_
    filter_upwards [hfg] with η h
    rw [h]
  have hZ : homNormSq k f = ∫⁻ η, ENNReal.ofReal (‖η‖ ^ (2 * k)) * ‖g η‖ₑ ^ 2 := by
    unfold homNormSq
    refine lintegral_congr_ae ?_
    filter_upwards [hfg] with η h
    rw [h]
  have hbase := lintegral_hom_conv_sq_le k hg
  calc ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * convEnormSum f ξ ^ 2
      ≤ ∫⁻ ξ, 81 * (ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * (∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ) ^ 2) := by
        refine lintegral_mono fun ξ => ?_
        calc ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * convEnormSum f ξ ^ 2
            ≤ ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * (9 * ∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ) ^ 2 := by
              gcongr
              exact hpt ξ
          _ = _ := by ring
    _ = 81 * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * (∫⁻ η, ‖g η‖ₑ * ‖g (ξ - η)‖ₑ) ^ 2 :=
        lintegral_const_mul' _ _ (by norm_num)
    _ ≤ 81 * (4 ^ (k + 1) * (∫⁻ η, ‖g η‖ₑ) ^ 2 *
          ∫⁻ η, ENNReal.ofReal (‖η‖ ^ (2 * k)) * ‖g η‖ₑ ^ 2) := by gcongr
    _ = _ := by
        rw [hW, hZ, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num)]
        norm_num
        ring

private theorem symbolX_aesm (x : X) : AEStronglyMeasurable (symbolX x) volume := by
  unfold symbolX
  exact (by fun_prop : Measurable fun ξ : Space => (2 * π * ‖ξ‖)⁻¹).aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable _)

private theorem symbolL1_zero_of_hom_zero (k : ℕ) (f : Space → CSpace) (hf : AEStronglyMeasurable f volume)
    (h : homNormSq k f = 0) : freqL1Norm f = 0 := by
  unfold homNormSq at h
  have hm : AEMeasurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * ‖f ξ‖ₑ ^ 2) volume :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable.mul (hf.enorm.pow_const 2)
  rw [lintegral_eq_zero_iff' hm] at h
  unfold freqL1Norm
  have hne : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]; exact measure_singleton 0
  refine lintegral_eq_zero_iff' hf.enorm |>.2 ?_
  filter_upwards [h, hne] with ξ hξ hξ0
  simp only [Pi.zero_apply, mul_eq_zero, ENNReal.ofReal_eq_zero, pow_eq_zero_iff', ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, and_true] at hξ ⊢
  rcases hξ with h1 | h1
  · have : 0 < ‖ξ‖ ^ (2 * k) := pow_pos (norm_pos_iff.2 hξ0) _
    linarith
  · exact h1

private theorem enorm_symbolX_le (y : X) (ξ : Space) (c : ℝ≥0∞) (h : ‖(y : L2C) ξ‖ₑ ≤ c) :
    ‖symbolX y ξ‖ₑ ≤ ENNReal.ofReal ((2 * π * ‖ξ‖)⁻¹) * c := by
  unfold symbolX
  rw [enorm_smul, Real.enorm_eq_ofReal (by positivity)]
  gcongr

private theorem bilin_weight_le {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) (ξ : Space) :
    ‖ξ‖ ^ 2 * ((2 * π * ‖ξ‖)⁻¹ * (fracPhiFactor α τ ξ * (2 * π * ‖ξ‖))) ^ 2 ≤
      4 * π ^ 2 * ((1 / α) ^ (1 / α) * 2 ^ (1 / α)) ^ 2 * τ ^ (-(2 / α)) := by
  have hq : 0 < 1 / α := one_div_pos.2 hα
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := hE ▸ (Real.exp_pos _).le
  have e1 : (2 * π * ‖ξ‖)⁻¹ * (fracPhiFactor α τ ξ * (2 * π * ‖ξ‖)) = 2 * π * ‖ξ‖ * E := by
    unfold fracPhiFactor
    rw [← hE]
    rcases eq_or_ne (2 * π * ‖ξ‖) 0 with h | h
    · rw [h]; simp
    · field_simp
  have e2 : fracHeatFactor α (τ / 2) ξ ^ 2 = E := by
    unfold fracHeatFactor
    rw [hE, max_eq_left (by linarith), sq, ← Real.exp_add]
    ring_nf
  have hw := heat_weight_le hα (by linarith : 0 < τ / 2) ξ
  rw [e2] at hw
  have hw0 : 0 ≤ ‖ξ‖ ^ 2 * E := by positivity
  have hsq : (‖ξ‖ ^ 2 * E) ^ 2 ≤ ((1 / α) ^ (1 / α) * (τ / 2) ^ (-(1 / α))) ^ 2 :=
    pow_le_pow_left₀ hw0 hw 2
  have e3 : ((1 / α) ^ (1 / α) * (τ / 2) ^ (-(1 / α))) ^ 2 =
      ((1 / α) ^ (1 / α) * 2 ^ (1 / α)) ^ 2 * τ ^ (-(2 / α)) := by
    rw [Real.div_rpow hτ.le (by norm_num), Real.rpow_neg hτ.le, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      show -(2 / α) = (-(1 / α)) * (2 : ℕ) by push_cast; ring, Real.rpow_mul hτ.le, Real.rpow_natCast,
      Real.rpow_neg hτ.le]
    field_simp
  rw [e1]
  calc ‖ξ‖ ^ 2 * (2 * π * ‖ξ‖ * E) ^ 2 = 4 * π ^ 2 * (‖ξ‖ ^ 2 * E) ^ 2 := by ring
    _ ≤ 4 * π ^ 2 * ((1 / α) ^ (1 / α) * (τ / 2) ^ (-(1 / α))) ^ 2 := by gcongr
    _ = _ := by rw [e3]; ring

set_option maxHeartbeats 1000000 in
theorem smoothBilinMomentGain (α : ℝ) (hα : 1 < α) (k : ℕ) : ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → ∀ x : X,
    homNormSq (k + 1) (symbolX (fracBilinX α τ x x)) ≤
      ENNReal.ofReal (C * τ ^ (-(2 / α))) * (freqL1Norm (symbolX x) ^ 2 * homNormSq k (symbolX x)) := by
  obtain ⟨C2, hC2⟩ := smoothConvMomentBound k
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 4 * π ^ 2 * ((1 / α) ^ (1 / α) * 2 ^ (1 / α)) ^ 2 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hD ▸ by positivity
  refine ⟨D * max C2 1 + 1, fun τ hτ x => ?_⟩
  have hpos : 0 < (D * max C2 1 + 1) * τ ^ (-(2 / α)) :=
    mul_pos (by have := le_max_right C2 1; positivity) (Real.rpow_pos_of_pos hτ _)
  by_cases hx : freqL1Norm (symbolX x) = ⊤
  · have hh : homNormSq k (symbolX x) ≠ 0 := fun h0 => by
      have := symbolL1_zero_of_hom_zero k _ (symbolX_aesm x) h0
      rw [this] at hx; exact ENNReal.zero_ne_top hx
    rw [hx, ENNReal.top_pow two_ne_zero, ENNReal.top_mul hh,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top
  have hxt : freqL1Norm (symbolX x) < ⊤ := lt_top_iff_ne_top.2 hx
  have hτD : 0 ≤ D * τ ^ (-(2 / α)) := mul_nonneg hD0 (Real.rpow_nonneg hτ.le _)
  calc homNormSq (k + 1) (symbolX (fracBilinX α τ x x))
      ≤ ∫⁻ ξ, ENNReal.ofReal (D * τ ^ (-(2 / α))) *
          (ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * convEnormSum (symbolX x) ξ ^ 2) := by
        unfold homNormSq
        refine lintegral_mono_ae ?_
        filter_upwards [smoothBilinSymbolBound α hα τ hτ x hxt] with ξ hξ
        have hw := bilin_weight_le (by linarith : (0 : ℝ) < α) hτ ξ
        rw [← hD] at hw
        have hinv : 0 ≤ (2 * π * ‖ξ‖)⁻¹ := by positivity
        have hφ : 0 ≤ fracPhiFactor α τ ξ * (2 * π * ‖ξ‖) := by unfold fracPhiFactor; positivity
        generalize fracBilinX α τ x x = y at hξ ⊢
        generalize convEnormSum (symbolX x) ξ = cv at hξ ⊢
        have h1 : ‖symbolX y ξ‖ₑ ≤
            ENNReal.ofReal ((2 * π * ‖ξ‖)⁻¹ * (fracPhiFactor α τ ξ * (2 * π * ‖ξ‖))) * cv := by
          rw [ENNReal.ofReal_mul hinv, mul_assoc]
          exact enorm_symbolX_le y ξ _ hξ
        calc ENNReal.ofReal (‖ξ‖ ^ (2 * (k + 1))) * ‖symbolX y ξ‖ₑ ^ 2
            ≤ ENNReal.ofReal (‖ξ‖ ^ (2 * (k + 1))) *
                (ENNReal.ofReal ((2 * π * ‖ξ‖)⁻¹ * (fracPhiFactor α τ ξ * (2 * π * ‖ξ‖))) *
                  cv) ^ 2 := by gcongr
          _ = ENNReal.ofReal (‖ξ‖ ^ 2 * ((2 * π * ‖ξ‖)⁻¹ * (fracPhiFactor α τ ξ * (2 * π * ‖ξ‖))) ^ 2) *
                (ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * cv ^ 2) := by
              rw [mul_pow, ← ENNReal.ofReal_pow (mul_nonneg hinv hφ),
                ENNReal.ofReal_mul (by positivity),
                show ‖ξ‖ ^ (2 * (k + 1)) = ‖ξ‖ ^ 2 * ‖ξ‖ ^ (2 * k) by ring,
                ENNReal.ofReal_mul (by positivity)]
              ring
          _ ≤ _ := by gcongr
    _ = ENNReal.ofReal (D * τ ^ (-(2 / α))) *
          ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * convEnormSum (symbolX x) ξ ^ 2 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (D * τ ^ (-(2 / α))) *
          (ENNReal.ofReal C2 * (freqL1Norm (symbolX x) ^ 2 * homNormSq k (symbolX x))) := by
        gcongr
        exact hC2 _ (symbolX_aesm x)
    _ ≤ ENNReal.ofReal (D * τ ^ (-(2 / α))) *
          (ENNReal.ofReal (max C2 1) * (freqL1Norm (symbolX x) ^ 2 * homNormSq k (symbolX x))) := by
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (D * max C2 1 * τ ^ (-(2 / α))) *
          (freqL1Norm (symbolX x) ^ 2 * homNormSq k (symbolX x)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hτD]
        congr 2
        ring
    _ ≤ _ := by
        gcongr
        linarith

private def momentWeight (m : ℕ) (ξ : Space) : ℝ := ‖ξ‖ ^ m * (2 * π * ‖ξ‖)⁻¹

private def truncWeight (m n : ℕ) (ξ : Space) : ℝ := min (momentWeight m ξ) n

private def truncOp (m n : ℕ) : L2C →L[ℝ] L2C :=
  fieldOp id (fun ξ => truncWeight m n ξ • ContinuousLinearMap.id ℝ CSpace)

private theorem momentWeight_nonneg (m : ℕ) (ξ : Space) : 0 ≤ momentWeight m ξ := by
  unfold momentWeight; positivity

private theorem truncWeight_nonneg (m n : ℕ) (ξ : Space) : 0 ≤ truncWeight m n ξ :=
  le_min (momentWeight_nonneg m ξ) (Nat.cast_nonneg n)

private theorem truncWeight_measurable (m n : ℕ) : Measurable (truncWeight m n) :=
  (momentWeight_measurable m).min measurable_const

private theorem truncOp_ae (m n : ℕ) (g : L2C) :
    (truncOp m n g : Space → CSpace) =ᵐ[volume] fun ξ => truncWeight m n ξ • g ξ := by
  have h := isRealizedBy_fieldOp_id (F := fun ξ => truncWeight m n ξ • ContinuousLinearMap.id ℝ CSpace)
    (C := n) ((truncWeight_measurable m n).aestronglyMeasurable.smul aestronglyMeasurable_const)
    (fun ξ => by
      refine (norm_smul_le _ _).trans ?_
      calc ‖truncWeight m n ξ‖ * ‖ContinuousLinearMap.id ℝ CSpace‖ ≤ (n : ℝ) * 1 :=
            mul_le_mul (by rw [Real.norm_eq_abs, abs_of_nonneg (truncWeight_nonneg m n ξ)]
                           exact min_le_right _ _)
              ContinuousLinearMap.norm_id_le (norm_nonneg _) (Nat.cast_nonneg n)
        _ = n := mul_one _) g
  filter_upwards [h] with ξ hξ
  rw [truncOp, hξ]
  rfl

private theorem enorm_sq_L2C (g : L2C) : ‖g‖ₑ ^ 2 = ∫⁻ ξ, ‖g ξ‖ₑ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := (g : Space → CSpace))
    (p := 2) two_ne_zero
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [Lp.enorm_def, h]

private theorem truncOp_enorm_sq (m n : ℕ) (g : L2C) :
    ‖truncOp m n g‖ₑ ^ 2 = ∫⁻ ξ, ‖truncWeight m n ξ • g ξ‖ₑ ^ 2 := by
  rw [enorm_sq_L2C]
  refine lintegral_congr_ae ?_
  filter_upwards [truncOp_ae m n g] with ξ hξ
  rw [hξ]

private theorem hom_lintegral (m : ℕ) (y : X) :
    homNormSq m (symbolX y) = ∫⁻ ξ, ‖momentWeight m ξ • (y : L2C) ξ‖ₑ ^ 2 := by
  unfold homNormSq symbolX momentWeight
  refine lintegral_congr fun ξ => ?_
  rw [mul_smul, enorm_smul (‖ξ‖ ^ m), mul_pow,
    Real.enorm_eq_ofReal (pow_nonneg (norm_nonneg _) _), ← ENNReal.ofReal_pow (pow_nonneg (norm_nonneg _) _),
    ← pow_mul, mul_comm m 2]

private theorem truncOp_le (m n : ℕ) (y : X) :
    ‖truncOp m n (y : L2C)‖ₑ ≤ homNormSq m (symbolX y) ^ (1 / 2 : ℝ) := by
  have h : ‖truncOp m n (y : L2C)‖ₑ ^ 2 ≤ homNormSq m (symbolX y) := by
    rw [truncOp_enorm_sq, hom_lintegral]
    refine lintegral_mono fun ξ => ?_
    gcongr
    rw [enorm_smul, enorm_smul, Real.enorm_eq_ofReal (truncWeight_nonneg m n ξ),
      Real.enorm_eq_ofReal (momentWeight_nonneg m ξ)]
    gcongr
    exact min_le_left _ _
  calc ‖truncOp m n (y : L2C)‖ₑ = (‖truncOp m n (y : L2C)‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    _ ≤ _ := ENNReal.rpow_le_rpow h (by norm_num)

theorem smoothMomentNorm_integral (m : ℕ) (f : ℝ → X) (a b : ℝ) (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) :
    homNormSq m (symbolX (∫ r in a..b, f r)) ^ (1 / 2 : ℝ) ≤
      ∫⁻ r in Ioo a b, homNormSq m (symbolX (f r)) ^ (1 / 2 : ℝ) := by
  obtain ⟨L, hL⟩ : ∃ L, L = ∫⁻ r in Ioo a b, homNormSq m (symbolX (f r)) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  rw [← hL]
  have key : ∀ n : ℕ, ‖truncOp m n ((∫ r in a..b, f r : X) : L2C)‖ₑ ≤ L := by
    intro n
    have hS := ((truncOp m n).comp (X.subtypeL)).intervalIntegral_comp_comm hf
    have e : truncOp m n ((∫ r in a..b, f r : X) : L2C) =
        ∫ r in a..b, ((truncOp m n).comp X.subtypeL) (f r) := hS.symm
    rw [e, intervalIntegral.integral_of_le hab]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [hL, setLIntegral_congr Ioo_ae_eq_Ioc]
    exact lintegral_mono fun r => truncOp_le m n (f r)
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun ξ => ‖truncWeight m n ξ • ((∫ r in a..b, f r : X) : L2C) ξ‖ₑ ^ 2) volume := fun n =>
    ((truncWeight_measurable m n).aestronglyMeasurable.smul (Lp.aestronglyMeasurable _)).enorm.pow_const 2
  have hmono : ∀ᵐ ξ ∂volume, Monotone fun n : ℕ =>
      ‖truncWeight m n ξ • ((∫ r in a..b, f r : X) : L2C) ξ‖ₑ ^ 2 := by
    refine Filter.Eventually.of_forall fun ξ n n' hnn' => ?_
    simp only
    gcongr
    rw [enorm_smul, enorm_smul, Real.enorm_eq_ofReal (truncWeight_nonneg m n ξ),
      Real.enorm_eq_ofReal (truncWeight_nonneg m n' ξ)]
    gcongr
    exact min_le_min le_rfl (by exact_mod_cast hnn')
  have hsq : homNormSq m (symbolX (∫ r in a..b, f r)) ≤ L ^ 2 := by
    calc homNormSq m (symbolX (∫ r in a..b, f r))
        = ∫⁻ ξ, ‖momentWeight m ξ • ((∫ r in a..b, f r : X) : L2C) ξ‖ₑ ^ 2 := hom_lintegral _ _
      _ ≤ ∫⁻ ξ, ⨆ n : ℕ, ‖truncWeight m n ξ • ((∫ r in a..b, f r : X) : L2C) ξ‖ₑ ^ 2 := by
          refine lintegral_mono fun ξ => ?_
          obtain ⟨n, hn⟩ := exists_nat_ge (momentWeight m ξ)
          refine le_iSup_of_le n (le_of_eq ?_)
          rw [truncWeight, min_eq_left hn]
      _ = ⨆ n : ℕ, ∫⁻ ξ, ‖truncWeight m n ξ • ((∫ r in a..b, f r : X) : L2C) ξ‖ₑ ^ 2 :=
          lintegral_iSup' hmeas hmono
      _ = ⨆ n : ℕ, ‖truncOp m n ((∫ r in a..b, f r : X) : L2C)‖ₑ ^ 2 := by
          simp_rw [truncOp_enorm_sq]
      _ ≤ L ^ 2 := iSup_le fun n => by gcongr; exact key n
  calc _ ≤ (L ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hsq (by norm_num)
    _ = L := by rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

end Breakdown.FracCert
