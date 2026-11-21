import Breakdown.Cert.CoercivePieceAbsorbMeasure
import Breakdown.Cert.CoerciveRotation

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEps

theorem norm_modeAverage_le {β : Type*} (ι : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ) (b : β) {K : ℝ}
    (hK : ∀ τ φ, |f τ φ b| ≤ K) : ‖modeAverage ι f b‖ ≤ K := by
  unfold modeAverage
  have hin : ∀ τ : ℝ, ‖∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f τ φ b : ℝ) : ℂ)‖
        ≤ K * |2 * Real.pi - 0| := by
    intro τ
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun φ _ => ?_
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, neg_zero, Real.exp_zero, one_mul]
    exact hK τ φ
  have h1 : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, h1]
  refine le_trans (mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_of_norm_le_const fun τ _ => hin τ) (by positivity)) (le_of_eq ?_)
  rw [sub_zero, sub_zero, abs_one, abs_of_pos Real.two_pi_pos]
  field_simp

theorem sqrt_cnormSq_le {β : Type*} [Fintype β] (x : β → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ b, ‖x b‖ ≤ K) : Real.sqrt (cnormSq x) ≤ Fintype.card β * K := by
  have hc : (1 : ℝ) ≤ Fintype.card β ∨ Fintype.card β = 0 := by
    rcases Nat.eq_zero_or_pos (Fintype.card β) with h0 | h0
    · right; exact_mod_cast h0
    · left; exact_mod_cast h0
  have hs : cnormSq x ≤ Fintype.card β * K ^ 2 := by
    unfold cnormSq
    calc ∑ b, ‖x b‖ ^ 2 ≤ ∑ _b : β, K ^ 2 :=
          Finset.sum_le_sum fun b _ => pow_le_pow_left₀ (norm_nonneg _) (h b) 2
      _ = Fintype.card β * K ^ 2 := by simp [Finset.sum_const, Finset.card_univ]
  rcases hc with hc | hc
  · have : cnormSq x ≤ (Fintype.card β * K) ^ 2 := by
      calc cnormSq x ≤ Fintype.card β * K ^ 2 := hs
        _ ≤ (Fintype.card β * K) ^ 2 := by nlinarith [sq_nonneg K]
    calc Real.sqrt (cnormSq x) ≤ Real.sqrt ((Fintype.card β * K) ^ 2) := Real.sqrt_le_sqrt this
      _ = Fintype.card β * K := Real.sqrt_sq (by positivity)
  · rw [hc] at hs ⊢
    simp only [Nat.cast_zero, zero_mul] at hs ⊢
    rw [Real.sqrt_eq_zero'.2 hs]

theorem abs_coord_le (x : Space) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i
  rwa [Real.norm_eq_abs] at this

theorem norm_unit (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem norm_rot_unit (φ : ℝ) (i : Fin 3) : ‖axialRot φ (unitVector i)‖ = 1 := by
  rw [RotationInternal.axialRot_norm, norm_unit]

section Amplitudes

variable (W : ℝ → Space → Space) {D : ℝ}
  (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
include hD

theorem velAmp_le (α : ℤ × ℤ) (σ : ℝ) (y : Space) : velAmp W α σ y ≤ 3 * (D / (1 + ‖y‖)) := by
  have hb : ∀ s x, ‖W s x‖ ≤ D / (1 + ‖x‖) := fun s x => by
    have := hD s x 0 (by norm_num)
    rwa [norm_iteratedFDeriv_zero, zero_add, pow_one] at this
  have hK : 0 ≤ D / (1 + ‖y‖) := le_trans (norm_nonneg _) (hb 0 y)
  have := sqrt_cnormSq_le (modeVel α W σ y) hK fun i => by
    refine norm_modeAverage_le α _ i fun τ φ => ?_
    refine le_trans (abs_coord_le _ i) ?_
    rw [RotationInternal.axialRot_norm]
    have := hb (σ + τ) (axialRot φ y)
    rwa [RotationInternal.axialRot_norm] at this
  simpa [velAmp] using this

theorem gradAmp_le (α : ℤ × ℤ) (σ : ℝ) (y : Space) :
    gradAmp (gradField W) α σ y ≤ 9 * (D / (1 + ‖y‖) ^ 2) := by
  have hb : ∀ s x, ‖fderiv ℝ (W s) x‖ ≤ D / (1 + ‖x‖) ^ 2 := fun s x => by
    have := hD s x 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at this
  have hK : 0 ≤ D / (1 + ‖y‖) ^ 2 := le_trans (norm_nonneg _) (hb 0 y)
  have := sqrt_cnormSq_le (modeGrad α (gradField W) σ y) hK fun ij => by
    refine norm_modeAverage_le α _ ij fun τ φ => ?_
    refine le_trans (abs_coord_le _ _) ?_
    rw [RotationInternal.axialRot_norm]
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    rw [norm_rot_unit, mul_one]
    have := hb (σ + τ) (axialRot φ y)
    rwa [RotationInternal.axialRot_norm] at this
  simpa [gradAmp] using this

theorem secondDerivAmp_le (α : ℤ × ℤ) (σ : ℝ) (y : Space) :
    secondDerivAmp (secondDerivField W) α σ y ≤ 27 * (D / (1 + ‖y‖) ^ 3) := by
  have hb : ∀ s x, ‖fderiv ℝ (fun x => fderiv ℝ (W s) x) x‖ ≤ D / (1 + ‖x‖) ^ 3 := fun s x => by
    have := hD s x 2 le_rfl
    have e : ‖iteratedFDeriv ℝ 1 (fderiv ℝ (W s)) x‖ = ‖iteratedFDeriv ℝ (1 + 1) (W s) x‖ :=
      norm_iteratedFDeriv_fderiv
    rw [norm_iteratedFDeriv_one] at e
    rw [show (fun x => fderiv ℝ (W s) x) = fderiv ℝ (W s) from rfl, e]
    simpa using this
  have hK : 0 ≤ D / (1 + ‖y‖) ^ 3 := le_trans (norm_nonneg _) (hb 0 y)
  have := sqrt_cnormSq_le (modeSecondDeriv α (secondDerivField W) σ y) hK fun ijl => by
    refine norm_modeAverage_le α _ ijl fun τ φ => ?_
    refine le_trans (abs_coord_le _ _) ?_
    rw [RotationInternal.axialRot_norm]
    refine le_trans (ContinuousLinearMap.le_opNorm₂ _ _ _) ?_
    rw [norm_rot_unit, norm_rot_unit, mul_one, mul_one]
    have := hb (σ + τ) (axialRot φ y)
    rwa [RotationInternal.axialRot_norm] at this
  simpa [secondDerivAmp] using this

theorem vortAmp_le (α : ℤ × ℤ) (σ : ℝ) (y : Space) :
    vortAmp (gradField W) α σ y ≤ 16 * (9 * (D / (1 + ‖y‖) ^ 2)) := by
  have h1 := gradAmp_le W hD α σ y
  have h0 : 0 ≤ gradAmp (gradField W) α σ y := Real.sqrt_nonneg _
  unfold vortAmp
  calc Real.sqrt (cnormSq (curlOfGrad (modeGrad α (gradField W) σ y)))
      ≤ Real.sqrt (16 ^ 2 * cnormSq (modeGrad α (gradField W) σ y)) :=
        Real.sqrt_le_sqrt (le_trans (Internal.PieceAbsorb.cnormSq_curlOfGrad_le _)
          (mul_le_mul_of_nonneg_right (by norm_num) (Internal.PieceAbsorb.cnormSq_nonneg' _)))
    _ = 16 * gradAmp (gradField W) α σ y := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]; rfl
    _ ≤ 16 * (9 * (D / (1 + ‖y‖) ^ 2)) := by linarith

theorem vortGradAmp_le (α : ℤ × ℤ) (σ : ℝ) (y : Space) :
    vortGradAmp (secondDerivField W) α σ y ≤ 27 * (27 * (D / (1 + ‖y‖) ^ 3)) := by
  have h1 := secondDerivAmp_le W hD α σ y
  unfold vortGradAmp
  calc Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv α (secondDerivField W) σ y)))
      ≤ Real.sqrt (27 ^ 2 * cnormSq (modeSecondDeriv α (secondDerivField W) σ y)) :=
        Real.sqrt_le_sqrt (le_trans (Internal.PieceAbsorb.cnormSq_curlGradOfSecondDeriv_le _)
          (mul_le_mul_of_nonneg_right (by norm_num) (Internal.PieceAbsorb.cnormSq_nonneg' _)))
    _ = 27 * secondDerivAmp (secondDerivField W) α σ y := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]; rfl
    _ ≤ 27 * (27 * (D / (1 + ‖y‖) ^ 3)) := by linarith

end Amplitudes

section Sups

theorem frameSpeedSup_nonneg (W : ℝ → Space → Space) (a : ℝ) (y : Space) : 0 ≤ frameSpeedSup W a y :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem vortSup_nonneg (W : ℝ → Space → Space) (y : Space) : 0 ≤ vortSup W y :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem vortGradSup_nonneg (W : ℝ → Space → Space) (y : Space) : 0 ≤ vortGradSup W y :=
  Real.iSup_nonneg fun _ => norm_nonneg _


theorem norm_curlVec_le (G : Space →L[ℝ] Space) : ‖curlVec G‖ ≤ 27 * ‖G‖ := by
  unfold curlVec
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ i : Fin 3, ‖(∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G (unitVector j) l) • unitVector i‖
      ≤ 9 * ‖G‖ := by
    intro i
    rw [norm_smul, norm_unit, mul_one, Real.norm_eq_abs]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hjl : ∀ j l : Fin 3, |alternatingSymbol i j l * G (unitVector j) l| ≤ ‖G‖ := by
      intro j l
      rw [abs_mul]
      have h1 := Internal.PieceAbsorb.alternatingSymbol_abs_le i j l
      have h2 : |G (unitVector j) l| ≤ ‖G‖ := by
        refine le_trans (abs_coord_le _ l) ?_
        refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
        rw [norm_unit, mul_one]
      calc |alternatingSymbol i j l| * |G (unitVector j) l| ≤ 1 * ‖G‖ :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = ‖G‖ := one_mul _
    calc ∑ j : Fin 3, |∑ l : Fin 3, alternatingSymbol i j l * G (unitVector j) l|
        ≤ ∑ j : Fin 3, ∑ l : Fin 3, |alternatingSymbol i j l * G (unitVector j) l| :=
          Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 3, ∑ _l : Fin 3, ‖G‖ := Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hjl j l
      _ = 9 * ‖G‖ := by simp [Finset.sum_const]; ring
  calc ∑ i : Fin 3, ‖(∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G (unitVector j) l) • unitVector i‖
      ≤ ∑ _i : Fin 3, 9 * ‖G‖ := Finset.sum_le_sum fun i _ => hterm i
    _ = 27 * ‖G‖ := by simp [Finset.sum_const]; ring

theorem norm_perp_le (x : Space) : ‖-(x 1) • unitVector 0 + x 0 • unitVector 1‖ ≤ 2 * ‖x‖ := by
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_smul, norm_smul, norm_unit, norm_unit, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_neg]
  linarith [abs_coord_le x 0, abs_coord_le x 1]

variable (W : ℝ → Space → Space) {D : ℝ}
  (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
include hD

theorem decay_const_nonneg : 0 ≤ D := by
  have := hD 0 0 0 (by norm_num)
  have h := le_trans (norm_nonneg _) this
  simpa using h

theorem frameSpeedSup_le (a : ℝ) (y : Space) :
    frameSpeedSup W a y ≤ D + (1 / 2 + 2 * |a|) * ‖y‖ := by
  have hD0 := decay_const_nonneg W hD
  refine Real.iSup_le (fun p => ?_) (by positivity)
  have hb : ‖W p.1 (axialRot p.2 y)‖ ≤ D := by
    have := hD p.1 (axialRot p.2 y) 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero, zero_add, pow_one] at this
    refine le_trans this (div_le_self hD0 ?_)
    linarith [norm_nonneg (axialRot p.2 y)]
  have hr := RotationInternal.axialRot_norm p.2 y
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hr]
  have hp := norm_perp_le (axialRot p.2 y)
  rw [hr] at hp
  have : |a| * ‖-(axialRot p.2 y 1) • unitVector 0 + axialRot p.2 y 0 • unitVector 1‖ ≤ |a| * (2 * ‖y‖) :=
    mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith [abs_nonneg a, norm_nonneg y]

theorem vortSup_le (y : Space) : vortSup W y ≤ 27 * (D / (1 + ‖y‖) ^ 2) := by
  have hD0 := decay_const_nonneg W hD
  refine Real.iSup_le (fun p => ?_) (by positivity)
  refine le_trans (norm_curlVec_le _) (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have := hD p.1 (axialRot p.2 y) 1 (by norm_num)
  rwa [norm_iteratedFDeriv_one, RotationInternal.axialRot_norm] at this

end Sups

theorem curlVec_add (G K : Space →L[ℝ] Space) : curlVec (G + K) = curlVec G + curlVec K := by
  unfold curlVec
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← add_smul]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [ContinuousLinearMap.add_apply, PiLp.add_apply]
  ring

theorem curlVec_smul (c : ℝ) (G : Space →L[ℝ] Space) : curlVec (c • G) = c • curlVec G := by
  unfold curlVec
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [ContinuousLinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul]
  ring

def curlLinear : (Space →L[ℝ] Space) →L[ℝ] Space :=
  LinearMap.mkContinuous
    { toFun := curlVec
      map_add' := curlVec_add
      map_smul' := curlVec_smul } 27 fun G => norm_curlVec_le G

theorem curlLinear_apply (G : Space →L[ℝ] Space) : curlLinear G = curlVec G := rfl

theorem vortGradSup_le (W : ℝ → Space → Space) {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (y : Space) :
    vortGradSup W y ≤ 27 * (D / (1 + ‖y‖) ^ 3) := by
  have hD0 := decay_const_nonneg W hD
  refine Real.iSup_le (fun p => ?_) (by positivity)
  have hWs : ContDiff ℝ 2 (W p.1) := by
    have : (W p.1) = (fun z : ℝ × Space => W z.1 z.2) ∘ (fun x : Space => (p.1, x)) := rfl
    rw [this]
    exact hW.comp (contDiff_const.prodMk contDiff_id)
  have hdiff : Differentiable ℝ (fderiv ℝ (W p.1)) :=
    (hWs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have e : (fun x => curlVec (fderiv ℝ (W p.1) x)) = (curlLinear ∘ fderiv ℝ (W p.1)) := rfl
  rw [e, (curlLinear.hasFDerivAt.comp _ (hdiff _).hasFDerivAt).fderiv]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  refine mul_le_mul (LinearMap.mkContinuous_norm_le _ (by norm_num) _) ?_ (norm_nonneg _) (by norm_num)
  have h2 := hD p.1 (axialRot p.2 y) 2 le_rfl
  have e2 : ‖iteratedFDeriv ℝ 1 (fderiv ℝ (W p.1)) (axialRot p.2 y)‖
      = ‖iteratedFDeriv ℝ (1 + 1) (W p.1) (axialRot p.2 y)‖ := norm_iteratedFDeriv_fderiv
  rw [norm_iteratedFDeriv_one] at e2
  rw [e2]
  simpa [RotationInternal.axialRot_norm] using h2

end Internal.SmoothPieceEps

end Coercive

end Breakdown
