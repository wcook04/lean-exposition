import Breakdown.Uniqueness.RegDefs

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem lintegral_mul_sq_le (a b : Space → ℝ≥0∞) (ha : Measurable a) (hb : Measurable b) (ξ : Space) :
    (∫⁻ η, a η * b (ξ - η)) ^ 2 ≤ (∫⁻ η, b η) * ∫⁻ η, a η ^ 2 * b (ξ - η) := by
  have hb' : Measurable fun η => b (ξ - η) := hb.comp (measurable_const.sub measurable_id)
  set s : Space → ℝ≥0∞ := fun η => b (ξ - η) ^ (1 / 2 : ℝ) with hs
  have hsm : Measurable s := hb'.pow_const _
  have key : ∀ η, a η * b (ξ - η) = (a η * s η) * s η := by
    intro η
    rw [mul_assoc, hs]
    simp only
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq volume (p := 2) (q := 2) Real.HolderConjugate.two_two
    ((ha.mul hsm).aemeasurable) hsm.aemeasurable
  have e1 : ∀ η, (a η * s η) ^ (2 : ℝ) = a η ^ 2 * b (ξ - η) := by
    intro η
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hs]
    simp only
    rw [← ENNReal.rpow_mul]
    norm_num
  have e2 : ∀ η, s η ^ (2 : ℝ) = b (ξ - η) := by
    intro η
    rw [hs]
    simp only
    rw [← ENNReal.rpow_mul]
    norm_num
  simp only [Pi.mul_apply, e1, e2] at h1
  have e3 : ∫⁻ η, b (ξ - η) = ∫⁻ η, b η := lintegral_sub_left_eq_self b ξ
  rw [e3] at h1
  simp_rw [key]
  calc (∫⁻ η, a η * s η * s η) ^ 2 ≤ ((∫⁻ η, a η ^ 2 * b (ξ - η)) ^ (1 / 2 : ℝ) * (∫⁻ η, b η) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ η, b η) * ∫⁻ η, a η ^ 2 * b (ξ - η) := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1/2:ℝ)), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num
        ring

private theorem productBound_sq (a b : Space → ℝ≥0∞) (ha : Measurable a) (hb : Measurable b) :
    ∫⁻ ξ, (∫⁻ η, a η * b (ξ - η)) ^ 2 ≤ (∫⁻ η, b η) ^ 2 * ∫⁻ η, a η ^ 2 := by
  calc ∫⁻ ξ, (∫⁻ η, a η * b (ξ - η)) ^ 2 ≤ ∫⁻ ξ, (∫⁻ η, b η) * ∫⁻ η, a η ^ 2 * b (ξ - η) :=
        lintegral_mono fun ξ => lintegral_mul_sq_le a b ha hb ξ
    _ = (∫⁻ η, b η) * ∫⁻ ξ, ∫⁻ η, a η ^ 2 * b (ξ - η) := lintegral_const_mul _ (Measurable.lintegral_prod_right' (f := fun p : Space × Space => a p.2 ^ 2 * b (p.1 - p.2)) ((ha.comp measurable_snd).pow_const 2 |>.mul (hb.comp (measurable_fst.sub measurable_snd))))
    _ = (∫⁻ η, b η) * ∫⁻ η, ∫⁻ ξ, a η ^ 2 * b (ξ - η) := by
        rw [lintegral_lintegral_swap]
        exact ((ha.comp measurable_snd).pow_const 2 |>.mul (hb.comp (measurable_fst.sub measurable_snd))).aemeasurable
    _ = (∫⁻ η, b η) * ∫⁻ η, a η ^ 2 * ∫⁻ ξ, b ξ := by
        congr 1
        refine lintegral_congr fun η => ?_
        rw [lintegral_const_mul (a η ^ 2) (f := fun ξ => b (ξ - η)) (hb.comp (measurable_id.sub measurable_const)), lintegral_sub_right_eq_self b η]
    _ = (∫⁻ η, b η) ^ 2 * ∫⁻ η, a η ^ 2 := by
        rw [lintegral_mul_const _ (ha.pow_const 2)]
        ring

private theorem norm_le_sum_components (v : CSpace) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  have h1 : ‖v‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg _) two_ne_zero).1 h1

private theorem enorm_le_sum_components (v : CSpace) : ‖v‖ₑ ≤ ∑ i, ‖v i‖ₑ := by
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_le_sum_components v)

private def gradDensity (g : Space → CSpace) (ζ : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * π * ‖ζ‖ * ‖g ζ‖)

private theorem enorm_term_le (f g : Space → CSpace) (i j : Fin 3) (η ζ : Space) :
    ‖f η j * (2 * (π : ℂ) * Complex.I * ((ζ j : ℝ) : ℂ) * g ζ i)‖ₑ ≤ ‖f η‖ₑ * gradDensity g ζ := by
  rw [gradDensity, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : ‖f η j‖ ≤ ‖f η‖ := PiLp.norm_apply_le _ _
  have h2 : ‖g ζ i‖ ≤ ‖g ζ‖ := PiLp.norm_apply_le _ _
  have h3 : |ζ j| ≤ ‖ζ‖ := by simpa using PiLp.norm_apply_le ζ j
  have e : ‖f η j * (2 * (π : ℂ) * Complex.I * ((ζ j : ℝ) : ℂ) * g ζ i)‖ = ‖f η j‖ * (2 * π * |ζ j| * ‖g ζ i‖) := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [e]
  have hp := Real.pi_pos
  gcongr

private theorem enorm_advectionBilin_le (f g : Space → CSpace) (ξ : Space) :
    ‖advectionBilin f g ξ‖ₑ ≤ 9 * ∫⁻ η, ‖f η‖ₑ * gradDensity g (ξ - η) := by
  calc ‖advectionBilin f g ξ‖ₑ ≤ ∑ i : Fin 3, ‖advectionBilin f g ξ i‖ₑ := enorm_le_sum_components _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∫⁻ η, ‖f η‖ₑ * gradDensity g (ξ - η) := by
      gcongr with i
      simp only [advectionBilin, PiLp.toLp_apply]
      refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      simp only [convC]
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun η => ?_)
      exact enorm_term_le f g i j η (ξ - η)
    _ = 9 * ∫⁻ η, ‖f η‖ₑ * gradDensity g (ξ - η) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
      ring

private def bracket (ξ : Space) : ℝ := Real.sqrt (1 + ‖ξ‖ ^ 2)

private theorem bracket_nonneg (ξ : Space) : 0 ≤ bracket ξ := Real.sqrt_nonneg _

private theorem bracket_sq (ξ : Space) : bracket ξ ^ 2 = 1 + ‖ξ‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem norm_le_bracket (ξ : Space) : ‖ξ‖ ≤ bracket ξ :=
  Real.le_sqrt_of_sq_le (by linarith)

private theorem bracket_add_le (x y : Space) : bracket (x + y) ≤ bracket x + bracket y := by
  have hx := bracket_sq x
  have hy := bracket_sq y
  have hxy := bracket_sq (x + y)
  have h1 := norm_le_bracket x
  have h2 := norm_le_bracket y
  have h3 := norm_add_le x y
  have h0x := bracket_nonneg x
  have h0y := bracket_nonneg y
  have h0 := bracket_nonneg (x + y)
  have n1 := norm_nonneg x
  have n2 := norm_nonneg y
  have n3 := norm_nonneg (x + y)
  have key : bracket (x + y) ^ 2 ≤ (bracket x + bracket y) ^ 2 := by
    rw [hxy]
    have : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ n3 h3 2
    nlinarith [mul_le_mul h1 h2 n2 h0x]
  exact (pow_le_pow_iff_left₀ h0 (by linarith) two_ne_zero).1 key

private theorem add_pow_le_two_pow (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (m : ℕ) :
    (u + v) ^ m ≤ 2 ^ m * (u ^ m + v ^ m) := by
  rcases le_total u v with h | h
  · calc (u + v) ^ m ≤ (2 * v) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * v ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (u ^ m + v ^ m) := by
        have := pow_nonneg hu m
        gcongr
        linarith
  · calc (u + v) ^ m ≤ (2 * u) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * u ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (u ^ m + v ^ m) := by
        have := pow_nonneg hv m
        gcongr
        linarith

private def sigmaW (m : ℕ) (ξ : Space) : ℝ≥0∞ := ENNReal.ofReal (bracket ξ ^ m)

private theorem sigmaW_le (m : ℕ) (ξ η : Space) :
    sigmaW m ξ ≤ 2 ^ m * (sigmaW m η + sigmaW m (ξ - η)) := by
  have h := bracket_add_le η (ξ - η)
  rw [add_sub_cancel] at h
  have h2 : bracket ξ ^ m ≤ 2 ^ m * (bracket η ^ m + bracket (ξ - η) ^ m) :=
    (pow_le_pow_left₀ (bracket_nonneg _) h m).trans
      (add_pow_le_two_pow _ _ (bracket_nonneg _) (bracket_nonneg _) m)
  have h3 := ENNReal.ofReal_le_ofReal h2
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (pow_nonneg (bracket_nonneg _) _)
    (pow_nonneg (bracket_nonneg _) _)] at h3
  have e2 : ENNReal.ofReal ((2 : ℝ) ^ m) = 2 ^ m := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    simp
  rw [e2] at h3
  exact h3

private theorem sigmaW_sq (m : ℕ) (ξ : Space) : sigmaW m ξ ^ 2 = ENNReal.ofReal (hsWeight m ξ) := by
  rw [sigmaW, ← ENNReal.ofReal_pow (pow_nonneg (bracket_nonneg _) _), hsWeight, ← pow_mul, mul_comm,
    pow_mul, bracket_sq]

private theorem sigmaW_grad_sq (m : ℕ) (g : Space → CSpace) (ζ : Space) :
    (sigmaW m ζ * gradDensity g ζ) ^ 2 ≤
      ENNReal.ofReal (4 * π ^ 2) * (ENNReal.ofReal (hsWeight (m + 1) ζ) * ‖g ζ‖ₑ ^ 2) := by
  rw [sigmaW, gradDensity, ← ofReal_norm, ← ENNReal.ofReal_mul (pow_nonneg (bracket_nonneg _) _),
    ← ENNReal.ofReal_pow (mul_nonneg (pow_nonneg (bracket_nonneg _) _) (by positivity)), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (by unfold hsWeight; positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hb : (bracket ζ ^ m) ^ 2 = (1 + ‖ζ‖ ^ 2) ^ m := by rw [← pow_mul, mul_comm, pow_mul, bracket_sq]
  have e : (bracket ζ ^ m * (2 * π * ‖ζ‖ * ‖g ζ‖)) ^ 2 = 4 * π ^ 2 * ((1 + ‖ζ‖ ^ 2) ^ m * ‖ζ‖ ^ 2 * ‖g ζ‖ ^ 2) := by
    rw [mul_pow, hb]; ring
  rw [e, hsWeight, pow_succ (1 + ‖ζ‖ ^ 2) m]
  have h1 : ‖ζ‖ ^ 2 ≤ 1 + ‖ζ‖ ^ 2 := by linarith
  have h2 : 0 ≤ (1 + ‖ζ‖ ^ 2) ^ m := by positivity
  have h3 : 0 ≤ ‖g ζ‖ ^ 2 := by positivity
  have h4 : 0 ≤ 4 * π ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h1 h2
  have := mul_le_mul_of_nonneg_right this h3
  exact mul_le_mul_of_nonneg_left this h4

private theorem lintegral_gradDensity (g : Space → CSpace) :
    ∫⁻ ζ, gradDensity g ζ = ENNReal.ofReal (2 * π) * gradFreqL1Norm g := by
  rw [gradFreqL1Norm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ζ => ?_
  rw [gradDensity, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    mul_assoc]

private theorem measurable_conv (a b : Space → ℝ≥0∞) (ha : Measurable a) (hb : Measurable b) :
    Measurable fun ξ => ∫⁻ η, a η * b (ξ - η) :=
  Measurable.lintegral_prod_right' (f := fun p : Space × Space => a p.2 * b (p.1 - p.2))
    ((ha.comp measurable_snd).mul (hb.comp (measurable_fst.sub measurable_snd)))

private theorem conv_comm (a b : Space → ℝ≥0∞) (ξ : Space) :
    ∫⁻ η, a η * b (ξ - η) = ∫⁻ η, b η * a (ξ - η) := by
  rw [← lintegral_sub_left_eq_self (fun η => b η * a (ξ - η)) ξ]
  simp only [sub_sub_cancel]
  exact lintegral_congr fun η => mul_comm _ _

private theorem sq_add_le_four (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2) := by
  have h : x + y ≤ 2 * max x y := by rw [two_mul]; exact add_le_add (le_max_left _ _) (le_max_right _ _)
  calc (x + y) ^ 2 ≤ (2 * max x y) ^ 2 := by gcongr
    _ = 4 * max x y ^ 2 := by rw [mul_pow]; norm_num
    _ ≤ 4 * (x ^ 2 + y ^ 2) := by
      gcongr
      rcases le_total x y with h | h
      · rw [max_eq_right h]; exact le_add_self
      · rw [max_eq_left h]; exact le_self_add


private theorem measurable_gradDensity (g : Space → CSpace) (hg : Measurable g) :
    Measurable (gradDensity g) := by
  unfold gradDensity
  fun_prop

private theorem measurable_sigmaW (m : ℕ) : Measurable (sigmaW m) := by
  unfold sigmaW bracket
  fun_prop

private theorem tame_measurable (m : ℕ) (f g : Space → CSpace) (hf : Measurable f) (hg : Measurable g) :
    hsNormSq m (advectionBilin f g) ≤ 324 * 4 ^ m * ENNReal.ofReal (4 * π ^ 2) *
      (freqL1Norm f ^ 2 * hsNormSq (m + 1) g + hsNormSq m f * gradFreqL1Norm g ^ 2) := by
  set F : Space → ℝ≥0∞ := fun η => ‖f η‖ₑ with hF
  set D := gradDensity g with hD
  set σ := sigmaW m with hσ
  have hFm : Measurable F := hf.enorm
  have hDm : Measurable D := measurable_gradDensity g hg
  have hσm : Measurable σ := measurable_sigmaW m
  set K1 : Space → ℝ≥0∞ := fun ξ => ∫⁻ η, (σ η * F η) * D (ξ - η) with hK1
  set K2 : Space → ℝ≥0∞ := fun ξ => ∫⁻ η, F η * (σ (ξ - η) * D (ξ - η)) with hK2
  have hK1m : Measurable K1 := measurable_conv _ _ (hσm.mul hFm) hDm
  have hK2m : Measurable K2 := measurable_conv F (fun ζ => σ ζ * D ζ) hFm (hσm.mul hDm)
  have step1 : ∀ ξ, ENNReal.ofReal (hsWeight m ξ) * ‖advectionBilin f g ξ‖ₑ ^ 2 ≤
      81 * 4 ^ m * 4 * (K1 ξ ^ 2 + K2 ξ ^ 2) := by
    intro ξ
    have a1 : σ ξ * ∫⁻ η, F η * D (ξ - η) ≤ 2 ^ m * (K1 ξ + K2 ξ) := by
      rw [← lintegral_const_mul' _ _ (by simp only [hσ, sigmaW]; exact ENNReal.ofReal_ne_top)]
      calc ∫⁻ η, σ ξ * (F η * D (ξ - η)) ≤ ∫⁻ η, 2 ^ m * ((σ η * F η) * D (ξ - η) + F η * (σ (ξ - η) * D (ξ - η))) := by
            refine lintegral_mono fun η => ?_
            calc σ ξ * (F η * D (ξ - η)) ≤ 2 ^ m * (σ η + σ (ξ - η)) * (F η * D (ξ - η)) := by
                  gcongr
                  exact sigmaW_le m ξ η
              _ = 2 ^ m * ((σ η * F η) * D (ξ - η) + F η * (σ (ξ - η) * D (ξ - η))) := by ring
        _ = 2 ^ m * (K1 ξ + K2 ξ) := by
            rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]
            congr 1
            exact lintegral_add_left ((hσm.mul hFm).mul (hDm.comp (measurable_const.sub measurable_id))) _
    have a2 : σ ξ * ‖advectionBilin f g ξ‖ₑ ≤ 9 * (2 ^ m * (K1 ξ + K2 ξ)) := by
      calc σ ξ * ‖advectionBilin f g ξ‖ₑ ≤ σ ξ * (9 * ∫⁻ η, F η * D (ξ - η)) := by
            gcongr
            exact enorm_advectionBilin_le f g ξ
        _ = 9 * (σ ξ * ∫⁻ η, F η * D (ξ - η)) := by ring
        _ ≤ 9 * (2 ^ m * (K1 ξ + K2 ξ)) := by gcongr
    calc ENNReal.ofReal (hsWeight m ξ) * ‖advectionBilin f g ξ‖ₑ ^ 2 = (σ ξ * ‖advectionBilin f g ξ‖ₑ) ^ 2 := by
          rw [mul_pow, hσ, sigmaW_sq]
      _ ≤ (9 * (2 ^ m * (K1 ξ + K2 ξ))) ^ 2 := by gcongr
      _ = 81 * 4 ^ m * (K1 ξ + K2 ξ) ^ 2 := by
          rw [mul_pow, mul_pow, ← pow_mul, mul_comm m 2, pow_mul]
          norm_num
          ring
      _ ≤ 81 * 4 ^ m * (4 * (K1 ξ ^ 2 + K2 ξ ^ 2)) := by gcongr; exact sq_add_le_four _ _
      _ = 81 * 4 ^ m * 4 * (K1 ξ ^ 2 + K2 ξ ^ 2) := by ring
  have step3 : ∫⁻ ξ, K1 ξ ^ 2 ≤ ENNReal.ofReal (4 * π ^ 2) * gradFreqL1Norm g ^ 2 * hsNormSq m f := by
    have := productBound_sq (fun η => σ η * F η) D (hσm.mul hFm) hDm
    have e1 : ∫⁻ η, (σ η * F η) ^ 2 = hsNormSq m f := by
      refine lintegral_congr fun η => ?_
      rw [mul_pow, hσ, sigmaW_sq]
    have e2 : (∫⁻ η, D η) ^ 2 = ENNReal.ofReal (4 * π ^ 2) * gradFreqL1Norm g ^ 2 := by
      rw [hD, lintegral_gradDensity, mul_pow, ← ENNReal.ofReal_pow (by positivity)]
      ring_nf
    rw [e1, e2] at this
    exact this
  have step4 : ∫⁻ ξ, K2 ξ ^ 2 ≤ freqL1Norm f ^ 2 * (ENNReal.ofReal (4 * π ^ 2) * hsNormSq (m + 1) g) := by
    have eK : ∀ ξ, K2 ξ = ∫⁻ η, (σ η * D η) * F (ξ - η) := fun ξ =>
      conv_comm F (fun ζ => σ ζ * D ζ) ξ
    simp_rw [eK]
    refine (productBound_sq (fun η => σ η * D η) F (hσm.mul hDm) hFm).trans ?_
    gcongr
    · exact le_rfl
    · rw [hsNormSq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_mono fun ζ => sigmaW_grad_sq m g ζ
  calc hsNormSq m (advectionBilin f g) ≤ ∫⁻ ξ, 81 * 4 ^ m * 4 * (K1 ξ ^ 2 + K2 ξ ^ 2) :=
        lintegral_mono step1
    _ = 81 * 4 ^ m * 4 * ((∫⁻ ξ, K1 ξ ^ 2) + ∫⁻ ξ, K2 ξ ^ 2) := by
        rw [lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top]), lintegral_add_left (hK1m.pow_const 2)]
    _ ≤ 81 * 4 ^ m * 4 * (ENNReal.ofReal (4 * π ^ 2) * gradFreqL1Norm g ^ 2 * hsNormSq m f +
          freqL1Norm f ^ 2 * (ENNReal.ofReal (4 * π ^ 2) * hsNormSq (m + 1) g)) := by
        gcongr
    _ = 324 * 4 ^ m * ENNReal.ofReal (4 * π ^ 2) *
          (freqL1Norm f ^ 2 * hsNormSq (m + 1) g + hsNormSq m f * gradFreqL1Norm g ^ 2) := by
        ring


private theorem convC_congr_ae {F F' G G' : Space → ℂ} (hF : F =ᵐ[volume] F') (hG : G =ᵐ[volume] G')
    (ξ : Space) : convC F G ξ = convC F' G' ξ := by
  unfold convC
  have hG' : (fun η => G (ξ - η)) =ᵐ[volume] fun η => G' (ξ - η) :=
    (Measure.measurePreserving_sub_left volume ξ).quasiMeasurePreserving.ae_eq_comp hG
  refine integral_congr_ae ?_
  filter_upwards [hF, hG'] with η h1 h2
  rw [h1, h2]

private theorem advectionBilin_congr_ae {f f' g g' : Space → CSpace} (hf : f =ᵐ[volume] f')
    (hg : g =ᵐ[volume] g') : advectionBilin f g = advectionBilin f' g' := by
  funext ξ
  unfold advectionBilin
  congr 1
  funext i
  refine Finset.sum_congr rfl fun j _ => convC_congr_ae ?_ ?_ ξ
  · filter_upwards [hf] with η h
    rw [h]
  · filter_upwards [hg] with η h
    rw [h]

private theorem hsNormSq_congr_ae (m : ℕ) {f f' : Space → CSpace} (hf : f =ᵐ[volume] f') :
    hsNormSq m f = hsNormSq m f' := by
  refine lintegral_congr_ae ?_
  filter_upwards [hf] with η h
  rw [h]

private theorem freqL1Norm_congr_ae {f f' : Space → CSpace} (hf : f =ᵐ[volume] f') :
    freqL1Norm f = freqL1Norm f' := by
  refine lintegral_congr_ae ?_
  filter_upwards [hf] with η h
  rw [h]

private theorem gradFreqL1Norm_congr_ae {f f' : Space → CSpace} (hf : f =ᵐ[volume] f') :
    gradFreqL1Norm f = gradFreqL1Norm f' := by
  refine lintegral_congr_ae ?_
  filter_upwards [hf] with η h
  rw [h]

theorem hsNormSq_advection_tame_bound (m : ℕ) : ∃ C : ℝ, ∀ f g : Space → CSpace,
    AEStronglyMeasurable f volume → AEStronglyMeasurable g volume →
      hsNormSq m (advectionBilin f g) ≤
        ENNReal.ofReal C * (freqL1Norm f ^ 2 * hsNormSq (m + 1) g + hsNormSq m f * gradFreqL1Norm g ^ 2) := by
  refine ⟨324 * 4 ^ m * (4 * π ^ 2), fun f g hf hg => ?_⟩
  have eC : ENNReal.ofReal (324 * 4 ^ m * (4 * π ^ 2)) = 324 * 4 ^ m * ENNReal.ofReal (4 * π ^ 2) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [eC, advectionBilin_congr_ae hf.ae_eq_mk hg.ae_eq_mk, hsNormSq_congr_ae m hf.ae_eq_mk,
    hsNormSq_congr_ae (m + 1) hg.ae_eq_mk, freqL1Norm_congr_ae hf.ae_eq_mk,
    gradFreqL1Norm_congr_ae hg.ae_eq_mk]
  exact tame_measurable m _ _ hf.stronglyMeasurable_mk.measurable hg.stronglyMeasurable_mk.measurable

end Breakdown.SmoothFlow
