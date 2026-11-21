import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegIdentifyAuxBilin
import Breakdown.Uniqueness.RegUniqueAux3

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem powerBilinPhys_of (α : ℝ) (hα : 1 < α) (h1 : Freq.FracBilinH1Formula α)
    (h2 : PowerSolenoidalStatement α) : PowerBilinPhysStatement α := by
  intro f hm hs hf τ hτ
  have hH1f := isH1Field_physField hm hs hf
  have hbd : ∃ C, ∀ x, ‖physField f x‖ ≤ C ∧ ‖fderiv ℝ (physField f) x‖ ≤ C :=
    ⟨max (freqL1Norm f).toReal (2 * π * (gradFreqL1Norm f).toReal), fun x =>
      ⟨(norm_physField_le hm (hf 3) x).trans (le_max_left _ _),
        (norm_fderiv_physField_le hm (hf 3) x).trans (le_max_right _ _)⟩⟩
  have hadv := advectionAt_physField_eq hm hs hf
  rw [h1 _ hH1f hbd τ hτ, hadv]
  have hL := h2.2.2.2 (advectionSymbol f) (memLp_one_advectionSymbol hm hs hf)
    (memLp_two_advectionSymbol hm hs hf) (advectionSymbol_neg hm hs hf) τ hτ
  have hn := Lp.coeFn_neg
    ((fracHeatSolenoidal α τ (toLpOrZero 2 (physField (advectionSymbol f))) : X) : L2C)
  filter_upwards [hL, hn] with ξ e1 e2
  have e3 : (((-fracHeatSolenoidal α τ (toLpOrZero 2 (physField (advectionSymbol f))) : X) : L2C) :
      Space → CSpace) ξ =
      -(((fracHeatSolenoidal α τ (toLpOrZero 2 (physField (advectionSymbol f))) : X) : L2C) :
        Space → CSpace) ξ := e2
  rw [e3, e1, nonlinSymbol, smul_neg]

private theorem phi_nonneg (α τ : ℝ) (ξ : Space) : 0 ≤ fracPhiFactor α τ ξ := by
  unfold fracPhiFactor
  positivity

private theorem le_exp_rpow {α y : ℝ} (hα : 1 < α) (hy : 0 ≤ y) :
    y ≤ Real.exp (y ^ (2 * α)) := by
  rcases le_total y 1 with h | h
  · exact h.trans (Real.one_le_exp (Real.rpow_nonneg hy _))
  · have h2 : y ≤ y ^ (2 * α) := by
      calc y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
        _ ≤ y ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    exact h2.trans (by linarith [Real.add_one_le_exp (y ^ (2 * α))])

private theorem phi_le_rpow {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    fracPhiFactor α τ ξ ≤ τ ^ (-(1 / (2 * α))) := by
  have hα0 : 0 < 2 * α := by linarith
  set c := τ ^ (1 / (2 * α)) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hτ _
  have hcp : c ^ (2 * α) = τ := by
    rw [hc, ← Real.rpow_mul hτ.le, one_div, inv_mul_cancel₀ hα0.ne', Real.rpow_one]
  set y := c * (2 * π * ‖ξ‖) with hy
  have hy0 : 0 ≤ y := by positivity
  have hyp : y ^ (2 * α) = τ * (2 * π * ‖ξ‖) ^ (2 * α) := by
    rw [hy, Real.mul_rpow hc0.le (by positivity), hcp]
  have hinv : τ ^ (-(1 / (2 * α))) = c⁻¹ := by rw [hc, Real.rpow_neg hτ.le]
  have key : fracPhiFactor α τ ξ = c⁻¹ * (y * Real.exp (-(y ^ (2 * α)))) := by
    rw [fracPhiFactor, hyp, hy, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul]
  have hb : y * Real.exp (-(y ^ (2 * α))) ≤ 1 := by
    have he : Real.exp (y ^ (2 * α)) * Real.exp (-(y ^ (2 * α))) = 1 := by
      rw [← Real.exp_add]
      simp
    have hp := Real.exp_pos (-(y ^ (2 * α)))
    have := le_exp_rpow hα hy0
    nlinarith
  rw [key, hinv]
  calc c⁻¹ * (y * Real.exp (-(y ^ (2 * α)))) ≤ c⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hc0.le)
    _ = c⁻¹ := mul_one _

private theorem phi_sq_le {α τ₀ τ : ℝ} (hα : 1 < α) (h0 : 0 < τ₀) (h : τ₀ ≤ τ) (ξ : Space) :
    fracPhiFactor α τ ξ ^ 2 ≤
      Real.exp (2 * τ₀) * τ₀⁻¹ * Real.exp (-(4 * π ^ 2 * τ₀ * ‖ξ‖ ^ 2)) := by
  have hφ : fracPhiFactor α τ ξ =
      (2 * π * ‖ξ‖) * Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))) := rfl
  have hxdef : 4 * π ^ 2 * τ₀ * ‖ξ‖ ^ 2 = τ₀ * (2 * π * ‖ξ‖) ^ 2 := by ring
  rw [hφ, hxdef]
  set y := 2 * π * ‖ξ‖ with hy
  have hy0 : 0 ≤ y := by positivity
  have hpow : y ^ 2 - 1 ≤ y ^ (2 * α) := by
    rcases le_total y 1 with h1 | h1
    · have : y ^ 2 ≤ 1 := by nlinarith
      have : 0 ≤ y ^ (2 * α) := Real.rpow_nonneg hy0 _
      linarith
    · have h3 : y ^ (2 : ℝ) ≤ y ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      rw [Real.rpow_two] at h3
      linarith
  have hr0 : 0 ≤ y ^ (2 * α) := Real.rpow_nonneg hy0 _
  have hmono : Real.exp (-(τ * y ^ (2 * α))) ≤ Real.exp (-(τ₀ * (y ^ 2 - 1))) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_left hpow h0.le, mul_le_mul_of_nonneg_right h hr0]
  set x := τ₀ * y ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hxe : x * Real.exp (-x) ≤ 1 := by
    have he : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      simp
    have h1 : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have hp : 0 < Real.exp (-x) := Real.exp_pos _
    nlinarith
  have hsq : (y * Real.exp (-(τ * y ^ (2 * α)))) ^ 2 ≤
      (y * Real.exp (-(τ₀ * (y ^ 2 - 1)))) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hy0 (Real.exp_pos _).le)
      (mul_le_mul_of_nonneg_left hmono hy0) 2
  have e : Real.exp (-(τ₀ * (y ^ 2 - 1))) ^ 2 =
      Real.exp (2 * τ₀) * (Real.exp (-x) * Real.exp (-x)) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hx]
    congr 1
    ring
  have e2 : (y * Real.exp (-(τ₀ * (y ^ 2 - 1)))) ^ 2 =
      Real.exp (2 * τ₀) * τ₀⁻¹ * (x * Real.exp (-x)) * Real.exp (-x) := by
    rw [mul_pow, e, hx]
    have := h0.ne'
    field_simp
  have hi : 0 ≤ Real.exp (2 * τ₀) * τ₀⁻¹ := by positivity
  have hp : 0 < Real.exp (-x) := Real.exp_pos _
  calc (y * Real.exp (-(τ * y ^ (2 * α)))) ^ 2 ≤ _ := hsq
    _ = _ := e2
    _ ≤ Real.exp (2 * τ₀) * τ₀⁻¹ * 1 * Real.exp (-x) := by gcongr
    _ = Real.exp (2 * τ₀) * τ₀⁻¹ * Real.exp (-x) := by ring

private theorem integrable_exp_neg_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun ξ : Space => Real.exp (-(a * ‖ξ‖ ^ 2))) volume := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Space) (b := (a : ℂ))
    (by simpa using ha) 0 0
  refine h.norm.congr (Eventually.of_forall fun ξ => ?_)
  have e : -(a : ℂ) * ((‖ξ‖ : ℝ) : ℂ) ^ 2 + 0 * ((inner ℝ (0 : Space) ξ : ℝ) : ℂ) =
      ((-(a * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
    push_cast
    ring
  simp only [e, Complex.norm_exp_ofReal]

private theorem hsNormSq_le_of_le {m n : ℕ} (h : m ≤ n) (f : Space → CSpace) :
    hsNormSq m f ≤ hsNormSq n f :=
  lintegral_mono fun ξ => by
    gcongr
    exact pow_le_pow_right₀ (le_add_of_nonneg_right (sq_nonneg _)) h

private theorem eLpNorm_two_eq_hs (g : Space → CSpace) :
    eLpNorm g 2 volume = hsNormSq 0 g ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, hsNormSq, hsWeight, pow_zero, ENNReal.ofReal_one, one_mul,
    ENNReal.rpow_two]

private theorem nonlin_pointwise_bound {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : IsHsCurve 3 F 0 T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc 0 T, ∀ ξ, ‖nonlinSymbol (F s) ξ‖ ≤ M := by
  obtain ⟨C, hC, hCb⟩ := hsCurve_bound hF
  have hCt : C ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC
  set K : ℝ≥0∞ := 2 * (ENNReal.ofReal (18 * π) * (C ^ (1 / 2 : ℝ) * C ^ (1 / 2 : ℝ))) with hK
  have hKt : K ≠ ⊤ := by
    rw [hK]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hCt hCt))
  refine ⟨K.toReal, ENNReal.toReal_nonneg, fun s hs ξ => ?_⟩
  have hm := (hF.1 s hs).1
  have e : ‖nonlinSymbol (F s) ξ‖ₑ ≤ K := by
    calc ‖nonlinSymbol (F s) ξ‖ₑ = ‖divFreeC ξ (advectionSymbol (F s) ξ)‖ₑ := by
          rw [nonlinSymbol, enorm_neg]
      _ ≤ 2 * ‖advectionSymbol (F s) ξ‖ₑ := enorm_divFreeC_le _ _
      _ ≤ 2 * (ENNReal.ofReal (18 * π) * convMass (F s) (F s) ξ) := by
          gcongr
          exact enorm_advectionBilin_le _ _ _
      _ ≤ K := by
          rw [hK]
          gcongr
          refine (convMass_le_hs hm hm ξ).trans ?_
          gcongr
          · exact (hsNormSq_zero_le_three _).trans (hCb s hs)
          · exact (homNormSq_one_le_three _).trans (hCb s hs)
  have h2 := (ENNReal.toReal_le_toReal enorm_ne_top hKt).2 e
  simpa using h2

private theorem nonlin_l2_bound {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : IsHsCurve 3 F 0 T) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ s ∈ Icc 0 T, eLpNorm (nonlinSymbol (F s)) 2 volume ≤ B := by
  obtain ⟨A, hA, hAb⟩ := hsCurve_bound hF
  obtain ⟨C₀, hC₀⟩ := hsNormSq_advectionBilin_le 0
  obtain ⟨C₁, hC₁⟩ := weightedFreqL1_le 1
  have hAt : A ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hA
  set W : ℝ≥0∞ := ENNReal.ofReal C₁ * A ^ (1 / 2 : ℝ) with hW
  have hWt : W ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAt
  set S : ℝ≥0∞ := ENNReal.ofReal C₀ * (W ^ 2 * A + A * W ^ 2) with hS
  have hSt : S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.pow_ne_top hWt) hA,
      ENNReal.mul_ne_top hA (ENNReal.pow_ne_top hWt)⟩)
  refine ⟨ENNReal.ofReal 2 * S ^ (1 / 2 : ℝ),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hSt),
    fun s hs => ?_⟩
  have hm := (hF.1 s hs).1
  have h3 : hsNormSq 3 (F s) ≤ A := hAb s hs
  have hw : freqL1Norm (F s) ≤ W :=
    (freqL1Norm_le_weighted _).trans ((hC₁ _).trans (by rw [hW]; gcongr))
  have hg : gradFreqL1Norm (F s) ≤ W :=
    (gradFreqL1Norm_le_weighted _).trans ((hC₁ _).trans (by rw [hW]; gcongr))
  have h1 : hsNormSq 1 (F s) ≤ A := (hsNormSq_le_of_le (by norm_num) _).trans h3
  have h0 : hsNormSq 0 (F s) ≤ A := (hsNormSq_zero_le_three _).trans h3
  have hadv : hsNormSq 0 (advectionSymbol (F s)) ≤ S :=
    (hC₀ (F s) (F s) hm hm).trans (by rw [hS]; gcongr)
  have hle : eLpNorm (nonlinSymbol (F s)) 2 volume ≤
      ENNReal.ofReal 2 * eLpNorm (advectionSymbol (F s)) 2 volume :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun ξ => by
      rw [nonlinSymbol, norm_neg]
      exact norm_divFreeC_le _ _) 2
  refine hle.trans ?_
  rw [eLpNorm_two_eq_hs]
  gcongr

private theorem sq_sum_le {a b M D : ℝ} (ha : a ^ 2 ≤ D) (hb : b ^ 2 ≤ D) :
    (a * M + b * M) ^ 2 ≤ 4 * M ^ 2 * D := by
  nlinarith [mul_le_mul_of_nonneg_left ha (sq_nonneg M),
    mul_le_mul_of_nonneg_left hb (sq_nonneg M), mul_nonneg (sq_nonneg M) (sq_nonneg (a - b))]

private theorem continuousOn_power_bilin {α : ℝ} (hα : 1 < α) (h1 : PowerBilinPhysStatement α)
    {T : ℝ} {F : ℝ → Space → CSpace} (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContinuousOn
      (fun s => fracBilinX α (t - s) (embedX (physField (F s))) (embedX (physField (F s))))
      (Ico 0 t) := by
  obtain ⟨M, hM0, hM⟩ := nonlin_pointwise_bound (hF 3)
  have hsub : Ico 0 t ⊆ Icc 0 T := fun s hs' => ⟨hs'.1, hs'.2.le.trans ht.2⟩
  have hrep : ∀ s ∈ Ico 0 t,
      ((fracBilinX α (t - s) (embedX (physField (F s))) (embedX (physField (F s))) : X) :
        Space → CSpace) =ᵐ[volume]
        fun ξ => ((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ := fun s hs' =>
    h1 (F s) ((hF 0).1 s (hsub hs')).1 (hs s (hsub hs'))
      (fun m => ((hF m).1 s (hsub hs')).2) (t - s) (sub_pos.2 hs'.2)
  intro s₀ hs₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ s ∈ Ico 0 t,
      ‖fracBilinX α (t - s) (embedX (physField (F s))) (embedX (physField (F s))) -
        fracBilinX α (t - s₀) (embedX (physField (F s₀))) (embedX (physField (F s₀)))‖ =
      ((∫⁻ ξ, ‖((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ -
        ((fracPhiFactor α (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ‖ₑ ^ (2 : ℝ)) ^
          (1 / 2 : ℝ)).toReal := by
    intro s hs'
    have e : ‖fracBilinX α (t - s) (embedX (physField (F s))) (embedX (physField (F s))) -
        fracBilinX α (t - s₀) (embedX (physField (F s₀))) (embedX (physField (F s₀)))‖ =
        ‖((fracBilinX α (t - s) (embedX (physField (F s))) (embedX (physField (F s))) : X) :
            L2C) -
          ((fracBilinX α (t - s₀) (embedX (physField (F s₀))) (embedX (physField (F s₀))) :
            X) : L2C)‖ :=
      rfl
    rw [e, Lp.norm_def,
      eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans ((hrep s hs').sub (hrep s₀ hs₀))),
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat]
    rfl
  have hτ₀ : 0 < (t - s₀) / 2 := by linarith [hs₀.2]
  have hlim : Tendsto (fun s => ∫⁻ ξ, ‖((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ -
      ((fracPhiFactor α (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ‖ₑ ^ (2 : ℝ))
      (𝓝[Ico 0 t] s₀) (𝓝 0) := by
    have key := tendsto_lintegral_filter_of_dominated_convergence' (μ := volume)
      (l := 𝓝[Ico 0 t] s₀)
      (F := fun s ξ => ‖((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ -
        ((fracPhiFactor α (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ‖ₑ ^ (2 : ℝ))
      (f := fun _ => 0)
      (fun ξ => ENNReal.ofReal (4 * M ^ 2 * (Real.exp (2 * ((t - s₀) / 2)) * ((t - s₀) / 2)⁻¹ *
        Real.exp (-(4 * π ^ 2 * ((t - s₀) / 2) * ‖ξ‖ ^ 2)))))
      ?_ ?_ ?_ ?_
    · simpa using key
    · filter_upwards [self_mem_nhdsWithin] with s hs'
      have e1 : AEStronglyMeasurable
          (fun ξ => ((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ) volume :=
        (Lp.aestronglyMeasurable _).congr (hrep s hs')
      have e2 : AEStronglyMeasurable
          (fun ξ => ((fracPhiFactor α (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ) volume :=
        (Lp.aestronglyMeasurable _).congr (hrep s₀ hs₀)
      exact (e1.sub e2).enorm.pow_const _
    · have hnear : Iio (s₀ + (t - s₀) / 2) ∈ 𝓝[Ico 0 t] s₀ :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
      filter_upwards [self_mem_nhdsWithin, hnear] with s hs' hs''
      refine Eventually.of_forall fun ξ => ?_
      have hτ1 : (t - s₀) / 2 ≤ t - s := by
        simp only [mem_Iio] at hs''
        linarith
      have hτ2 : (t - s₀) / 2 ≤ t - s₀ := by linarith
      have p1 := phi_sq_le hα hτ₀ hτ1 ξ
      have p2 := phi_sq_le hα hτ₀ hτ2 ξ
      have n1 := phi_nonneg α (t - s) ξ
      have n2 := phi_nonneg α (t - s₀) ξ
      have m1 := hM s (hsub hs') ξ
      have m2 := hM s₀ (hsub hs₀) ξ
      have hnrm : ‖((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ -
          ((fracPhiFactor α (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ‖ ≤
          fracPhiFactor α (t - s) ξ * M + fracPhiFactor α (t - s₀) ξ * M := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg n1]
          exact mul_le_mul_of_nonneg_left m1 n1
        · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg n2]
          exact mul_le_mul_of_nonneg_left m2 n2
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.rpow_two]
      have hn0 := norm_nonneg (((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ -
          ((fracPhiFactor α (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ)
      exact (pow_le_pow_left₀ hn0 hnrm 2).trans (sq_sum_le p1 p2)
    · refine (Integrable.lintegral_lt_top ?_).ne
      exact ((integrable_exp_neg_sq (mul_pos (by positivity) hτ₀)).const_mul
        (Real.exp (2 * ((t - s₀) / 2)) * ((t - s₀) / 2)⁻¹)).const_mul (4 * M ^ 2)
    · refine Eventually.of_forall fun ξ => ?_
      have hc : ContinuousWithinAt
          (fun s => ((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ)
          (Ico 0 t) s₀ := by
        have e1 : Continuous (fun s : ℝ => ((fracPhiFactor α (t - s) ξ : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp (continuous_const.mul (Real.continuous_exp.comp
            (((continuous_const.sub continuous_id).mul continuous_const).neg)))
        exact e1.continuousWithinAt.smul
          (((continuousOn_nonlinSymbol (hF 3) ξ).mono hsub) s₀ hs₀)
      have e2 : Tendsto (fun s => ((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ -
          ((fracPhiFactor α (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ)
          (𝓝[Ico 0 t] s₀) (𝓝 0) := by
        simpa using hc.tendsto.sub_const
          (((fracPhiFactor α (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ)
      have h3a := (continuous_enorm.tendsto (0 : CSpace)).comp e2
      rw [enorm_zero] at h3a
      have h3 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h3a
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
      exact h3
  have hlim2 : Tendsto (fun s => ((∫⁻ ξ, ‖((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) •
      nonlinSymbol (F s) ξ - ((fracPhiFactor α (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ‖ₑ ^
        (2 : ℝ)) ^ (1 / 2 : ℝ)).toReal) (𝓝[Ico 0 t] s₀) (𝓝 0) := by
    have e1 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hlim
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at e1
    have e2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp e1
    rw [ENNReal.toReal_zero] at e2
    exact e2
  refine hlim2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs'
  exact (hnorm s hs').symm

private theorem norm_power_bilin_le {α : ℝ} (hα : 1 < α) (h1 : PowerBilinPhysStatement α)
    {T : ℝ} {F : ℝ → Space → CSpace} (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) :
    ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ τ : ℝ, 0 < τ →
      ‖fracBilinX α τ (embedX (physField (F s))) (embedX (physField (F s)))‖ ≤
        C * τ ^ (-(1 / (2 * α))) := by
  obtain ⟨B, hBt, hBb⟩ := nonlin_l2_bound (hF 3)
  refine ⟨B.toReal, fun s hsT τ hτ => ?_⟩
  have hrep := h1 (F s) ((hF 0).1 s hsT).1 (hs s hsT) (fun m => ((hF m).1 s hsT).2) τ hτ
  have e : ‖fracBilinX α τ (embedX (physField (F s))) (embedX (physField (F s)))‖ =
      ‖((fracBilinX α τ (embedX (physField (F s))) (embedX (physField (F s))) : X) : L2C)‖ := rfl
  rw [e, Lp.norm_def, eLpNorm_congr_ae hrep]
  have hle : eLpNorm (fun ξ => ((fracPhiFactor α τ ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ) 2 volume ≤
      ENNReal.ofReal (τ ^ (-(1 / (2 * α)))) * eLpNorm (nonlinSymbol (F s)) 2 volume :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun ξ => by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (phi_nonneg α τ ξ)]
      exact mul_le_mul_of_nonneg_right (phi_le_rpow hα hτ ξ) (norm_nonneg _)) 2
  have hfin : ENNReal.ofReal (τ ^ (-(1 / (2 * α)))) * B ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBt
  calc (eLpNorm (fun ξ => ((fracPhiFactor α τ ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ) 2 volume).toReal
      ≤ (ENNReal.ofReal (τ ^ (-(1 / (2 * α)))) * B).toReal :=
        ENNReal.toReal_mono hfin (hle.trans (by gcongr; exact hBb s hsT))
    _ = B.toReal * τ ^ (-(1 / (2 * α))) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), mul_comm]

theorem powerBilinContinuous_of (α : ℝ) (hα : 1 < α) (h1 : PowerBilinPhysStatement α)
    (h2 : PowerSolenoidalStatement α) : PowerBilinContinuousStatement α := by
  intro T hT F hF hs
  exact ⟨fun t ht => continuousOn_power_bilin hα h1 hF hs ht, norm_power_bilin_le hα h1 hF hs⟩

end Breakdown.SmoothFlow
