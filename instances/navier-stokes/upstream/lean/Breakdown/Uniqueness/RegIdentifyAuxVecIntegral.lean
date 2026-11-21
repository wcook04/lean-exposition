import Breakdown.Uniqueness.RegIdentifyAuxBilin
import Breakdown.Uniqueness.RegUniqueAux3

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem phiFactor_nonneg' (τ : ℝ) (ξ : Space) : 0 ≤ phiFactor τ ξ := by
  unfold phiFactor
  positivity

private theorem phiFactor_le_rpow {τ : ℝ} (hτ : 0 < τ) (ξ : Space) :
    phiFactor τ ξ ≤ τ ^ (-(1 / 2 : ℝ)) := by
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  have hs' : Real.sqrt τ ≠ 0 := hs.ne'
  set y := 2 * π * Real.sqrt τ * ‖ξ‖ with hy
  have hy2 : y ^ 2 = 4 * π ^ 2 * τ * ‖ξ‖ ^ 2 := by
    rw [hy]
    have := Real.sq_sqrt hτ.le
    ring_nf
    rw [this]
    ring
  have hrp : τ ^ (-(1 / 2 : ℝ)) = (Real.sqrt τ)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hτ.le]
  have key : phiFactor τ ξ = (Real.sqrt τ)⁻¹ * (y * Real.exp (-(y ^ 2))) := by
    rw [phiFactor, ← hy2, ← mul_assoc]
    congr 1
    rw [hy]
    field_simp
  have h2 : y * Real.exp (-(y ^ 2)) ≤ 1 := by
    have he : Real.exp (y ^ 2) * Real.exp (-(y ^ 2)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hp : 0 < Real.exp (-(y ^ 2)) := Real.exp_pos _
    have h1 : y ≤ Real.exp (y ^ 2) := by
      have := Real.add_one_le_exp (y ^ 2)
      nlinarith [sq_nonneg (y - 1)]
    nlinarith
  rw [key, hrp]
  have hi : 0 ≤ (Real.sqrt τ)⁻¹ := inv_nonneg.2 hs.le
  calc (Real.sqrt τ)⁻¹ * (y * Real.exp (-(y ^ 2))) ≤ (Real.sqrt τ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h2 hi
    _ = (Real.sqrt τ)⁻¹ := mul_one _

private theorem phiFactor_sq_le {τ₀ τ : ℝ} (h0 : 0 < τ₀) (h : τ₀ ≤ τ) (ξ : Space) :
    phiFactor τ ξ ^ 2 ≤ τ₀⁻¹ * Real.exp (-(4 * π ^ 2 * τ₀ * ‖ξ‖ ^ 2)) := by
  have hmono : phiFactor τ ξ ≤ phiFactor τ₀ ξ := by
    unfold phiFactor
    have : 0 ≤ 2 * π * ‖ξ‖ := by positivity
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) this
    have : 0 ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 := by positivity
    nlinarith
  have hn : 0 ≤ phiFactor τ ξ := phiFactor_nonneg' τ ξ
  have hsq : phiFactor τ ξ ^ 2 ≤ phiFactor τ₀ ξ ^ 2 := pow_le_pow_left₀ hn hmono 2
  refine hsq.trans ?_
  set x := 4 * π ^ 2 * τ₀ * ‖ξ‖ ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hex : x * Real.exp (-x) ≤ 1 := by
    have he : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      simp
    have h1 : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have hp : 0 < Real.exp (-x) := Real.exp_pos _
    nlinarith
  have e : phiFactor τ₀ ξ ^ 2 = τ₀⁻¹ * (x * Real.exp (-x)) * Real.exp (-x) := by
    unfold phiFactor
    rw [← hx, hx]
    field_simp
    ring
  rw [e]
  have hi : 0 ≤ τ₀⁻¹ := inv_nonneg.2 h0.le
  have hp : 0 < Real.exp (-x) := Real.exp_pos _
  calc τ₀⁻¹ * (x * Real.exp (-x)) * Real.exp (-x) ≤ τ₀⁻¹ * 1 * Real.exp (-x) := by
        gcongr
    _ = τ₀⁻¹ * Real.exp (-x) := by ring

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

private theorem nonlinSymbol_bound {T : ℝ} {F : ℝ → Space → CSpace} (hF : IsHsCurve 3 F 0 T) :
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

private theorem eLpNorm_nonlinSymbol_bound {T : ℝ} {F : ℝ → Space → CSpace}
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

theorem continuousOn_bilinX_physField (hR : FieldOpRealized) (hB : BilinH1Formula)
    {T : ℝ} (hT : 0 < T) {F : ℝ → Space → CSpace} (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContinuousOn
      (fun s => bilinX (t - s) (embedX (physField (F s))) (embedX (physField (F s)))) (Ico 0 t) := by
  obtain ⟨M, hM0, hM⟩ := nonlinSymbol_bound (hF 3)
  have hsub : Ico 0 t ⊆ Icc 0 T := fun s hs' => ⟨hs'.1, hs'.2.le.trans ht.2⟩
  have hrep : ∀ s ∈ Ico 0 t,
      ((bilinX (t - s) (embedX (physField (F s))) (embedX (physField (F s))) : X) :
        Space → CSpace) =ᵐ[volume]
        fun ξ => ((phiFactor (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ := fun s hs' =>
    coe_bilinX_physField hR hB ((hF 0).1 s (hsub hs')).1 (hs s (hsub hs'))
      (fun m => ((hF m).1 s (hsub hs')).2) (sub_pos.2 hs'.2)
  intro s₀ hs₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ s ∈ Ico 0 t,
      ‖bilinX (t - s) (embedX (physField (F s))) (embedX (physField (F s))) -
        bilinX (t - s₀) (embedX (physField (F s₀))) (embedX (physField (F s₀)))‖ =
      ((∫⁻ ξ, ‖((phiFactor (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ -
        ((phiFactor (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)).toReal := by
    intro s hs'
    have e : ‖bilinX (t - s) (embedX (physField (F s))) (embedX (physField (F s))) -
        bilinX (t - s₀) (embedX (physField (F s₀))) (embedX (physField (F s₀)))‖ =
        ‖((bilinX (t - s) (embedX (physField (F s))) (embedX (physField (F s))) : X) : L2C) -
          ((bilinX (t - s₀) (embedX (physField (F s₀))) (embedX (physField (F s₀))) : X) : L2C)‖ :=
      rfl
    rw [e, Lp.norm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans ((hrep s hs').sub (hrep s₀ hs₀))),
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat]
    rfl
  have hτ₀ : 0 < (t - s₀) / 2 := by linarith [hs₀.2]
  have hlim : Tendsto (fun s => ∫⁻ ξ, ‖((phiFactor (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ -
      ((phiFactor (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ‖ₑ ^ (2 : ℝ)) (𝓝[Ico 0 t] s₀) (𝓝 0) := by
    have key := tendsto_lintegral_filter_of_dominated_convergence' (μ := volume)
      (l := 𝓝[Ico 0 t] s₀)
      (F := fun s ξ => ‖((phiFactor (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ -
        ((phiFactor (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ‖ₑ ^ (2 : ℝ)) (f := fun _ => 0)
      (fun ξ => ENNReal.ofReal (4 * M ^ 2 * (((t - s₀) / 2)⁻¹ *
        Real.exp (-(4 * π ^ 2 * ((t - s₀) / 2) * ‖ξ‖ ^ 2)))))
      ?_ ?_ ?_ ?_
    · simpa using key
    · filter_upwards [self_mem_nhdsWithin] with s hs'
      have h1 : AEStronglyMeasurable
          (fun ξ => ((phiFactor (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ) volume :=
        (Lp.aestronglyMeasurable _).congr (hrep s hs')
      have h2 : AEStronglyMeasurable
          (fun ξ => ((phiFactor (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ) volume :=
        (Lp.aestronglyMeasurable _).congr (hrep s₀ hs₀)
      exact (h1.sub h2).enorm.pow_const _
    · have hnear : Iio (s₀ + (t - s₀) / 2) ∈ 𝓝[Ico 0 t] s₀ :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
      filter_upwards [self_mem_nhdsWithin, hnear] with s hs' hs''
      refine Eventually.of_forall fun ξ => ?_
      have hτ1 : (t - s₀) / 2 ≤ t - s := by
        simp only [mem_Iio] at hs''
        linarith
      have hτ2 : (t - s₀) / 2 ≤ t - s₀ := by linarith
      have p1 := phiFactor_sq_le hτ₀ hτ1 ξ
      have p2 := phiFactor_sq_le hτ₀ hτ2 ξ
      have n1 := phiFactor_nonneg' (t - s) ξ
      have n2 := phiFactor_nonneg' (t - s₀) ξ
      have m1 := hM s (hsub hs') ξ
      have m2 := hM s₀ (hsub hs₀) ξ
      have hnrm : ‖((phiFactor (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ -
          ((phiFactor (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ‖ ≤
          phiFactor (t - s) ξ * M + phiFactor (t - s₀) ξ * M := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg n1]
          exact mul_le_mul_of_nonneg_left m1 n1
        · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg n2]
          exact mul_le_mul_of_nonneg_left m2 n2
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.rpow_two]
      have hn0 := norm_nonneg (((phiFactor (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ -
          ((phiFactor (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ)
      calc _ ≤ (phiFactor (t - s) ξ * M + phiFactor (t - s₀) ξ * M) ^ 2 :=
            pow_le_pow_left₀ hn0 hnrm 2
        _ ≤ _ := by
            nlinarith [mul_nonneg (sq_nonneg M) (sq_nonneg (phiFactor (t - s) ξ - phiFactor (t - s₀) ξ)),
              mul_le_mul_of_nonneg_left p1 (sq_nonneg M), mul_le_mul_of_nonneg_left p2 (sq_nonneg M)]
    · refine (Integrable.lintegral_lt_top ?_).ne
      exact ((integrable_exp_neg_sq (mul_pos (by positivity) hτ₀)).const_mul
        (((t - s₀) / 2)⁻¹)).const_mul (4 * M ^ 2)
    · refine Eventually.of_forall fun ξ => ?_
      have hc : ContinuousWithinAt
          (fun s => ((phiFactor (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ) (Ico 0 t) s₀ := by
        have h1 : Continuous (fun s : ℝ => ((phiFactor (t - s) ξ : ℝ) : ℂ)) := by
          unfold phiFactor
          fun_prop
        exact h1.continuousWithinAt.smul (((continuousOn_nonlinSymbol (hF 3) ξ).mono hsub) s₀ hs₀)
      have h2 : Tendsto (fun s => ((phiFactor (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ -
          ((phiFactor (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ) (𝓝[Ico 0 t] s₀) (𝓝 0) := by
        simpa using hc.tendsto.sub_const (((phiFactor (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ)
      have h3a := (continuous_enorm.tendsto (0 : CSpace)).comp h2
      rw [enorm_zero] at h3a
      have h3 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h3a
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
      exact h3
  have hlim2 : Tendsto (fun s => ((∫⁻ ξ, ‖((phiFactor (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ -
      ((phiFactor (t - s₀) ξ : ℝ) : ℂ) • nonlinSymbol (F s₀) ξ‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)).toReal)
      (𝓝[Ico 0 t] s₀) (𝓝 0) := by
    have h1 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hlim
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h1
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    rw [ENNReal.toReal_zero] at h2
    exact h2
  refine hlim2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs'
  exact (hnorm s hs').symm

theorem norm_bilinX_physField_le (hR : FieldOpRealized) (hB : BilinH1Formula)
    {T : ℝ} (hT : 0 < T) {F : ℝ → Space → CSpace} (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) :
    ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ τ : ℝ, 0 < τ →
      ‖bilinX τ (embedX (physField (F s))) (embedX (physField (F s)))‖ ≤ C * τ ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨B, hBt, hBb⟩ := eLpNorm_nonlinSymbol_bound (hF 3)
  refine ⟨B.toReal, fun s hsT τ hτ => ?_⟩
  have hrep := coe_bilinX_physField hR hB ((hF 0).1 s hsT).1 (hs s hsT)
    (fun m => ((hF m).1 s hsT).2) hτ
  have e : ‖bilinX τ (embedX (physField (F s))) (embedX (physField (F s)))‖ =
      ‖((bilinX τ (embedX (physField (F s))) (embedX (physField (F s))) : X) : L2C)‖ := rfl
  rw [e, Lp.norm_def, eLpNorm_congr_ae hrep]
  have hle : eLpNorm (fun ξ => ((phiFactor τ ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ) 2 volume ≤
      ENNReal.ofReal (τ ^ (-(1 / 2 : ℝ))) * eLpNorm (nonlinSymbol (F s)) 2 volume :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun ξ => by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (phiFactor_nonneg' τ ξ)]
      exact mul_le_mul_of_nonneg_right (phiFactor_le_rpow hτ ξ) (norm_nonneg _)) 2
  have hfin : ENNReal.ofReal (τ ^ (-(1 / 2 : ℝ))) * B ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBt
  calc (eLpNorm (fun ξ => ((phiFactor τ ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ) 2 volume).toReal
      ≤ (ENNReal.ofReal (τ ^ (-(1 / 2 : ℝ))) * B).toReal :=
        ENNReal.toReal_mono hfin (hle.trans (by gcongr; exact hBb s hsT))
    _ = B.toReal * τ ^ (-(1 / 2 : ℝ)) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), mul_comm]

end Breakdown.SmoothFlow
