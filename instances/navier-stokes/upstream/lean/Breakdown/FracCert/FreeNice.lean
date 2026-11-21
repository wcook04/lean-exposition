import Breakdown.FracCert.StFreeNiceParts
import Breakdown.Uniqueness.RegPhysAuxDeriv
import Breakdown.Uniqueness.RegEmbedAux
import Breakdown.Frac.OpExports
import Breakdown.Frac.NNiceField

open scoped ContDiff ENNReal FourierTransform SchwartzMap
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

private theorem profile_aesm {α : ℝ} {w : Space → Freq.CSpace} (hw : IsProfileSymbol α w) :
    AEStronglyMeasurable w volume := by
  have h1 : AEStronglyMeasurable w (volume.restrict ({0}ᶜ : Set Space)) :=
    hw.1.continuousOn.aestronglyMeasurable isClosed_singleton.isOpen_compl.measurableSet
  rwa [restrict_compl_singleton] at h1

private theorem profile_integrable_pow {α : ℝ} (hα : 1 < α) {w : Space → Freq.CSpace}
    (hw : IsProfileSymbol α w) (n : ℕ) (hn : n ≤ 2) : Integrable (fun ξ => ‖ξ‖ ^ n * ‖w ξ‖) := by
  obtain ⟨R, hR⟩ := hw.2.1
  obtain ⟨C, hC⟩ := hw.2.2.1 0
  have hmeas : AEStronglyMeasurable (fun ξ : Space => ‖ξ‖ ^ n * ‖w ξ‖) volume :=
    (continuous_norm.pow n).aestronglyMeasurable.mul (profile_aesm hw).norm
  have hae : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have hball : IntegrableOn (fun ξ : Space => ‖ξ‖ ^ n * ‖w ξ‖) (Metric.ball 0 (|R| + 1)) volume := by
    refine integrableOn_ball_of_norm_le_rpow (by simp) (α := 4 - 2 * α - n) (C := C) ?_ ?_ hmeas
    · have : (n : ℝ) ≤ 2 := by exact_mod_cast hn
      simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
      linarith
    · refine ae_restrict_of_ae (hae.mono fun ξ hξ => ?_)
      have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      have hb := hC ξ hξ
      rw [norm_iteratedFDeriv_zero] at hb
      rw [Real.norm_of_nonneg (by positivity)]
      calc ‖ξ‖ ^ n * ‖w ξ‖ ≤ ‖ξ‖ ^ n * (C * ‖ξ‖ ^ (2 * α - 4 - ((0 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = C * ‖ξ‖ ^ (-(4 - 2 * α - n)) := by
            rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hpos]
            congr 2
            push_cast
            ring
  refine hball.integrable_of_forall_notMem_eq_zero fun ξ hξ => ?_
  have hξR : R < ‖ξ‖ := by
    have : |R| + 1 ≤ ‖ξ‖ := by simpa [Metric.mem_ball, dist_zero_right, not_lt] using hξ
    linarith [le_abs_self R]
  simp [hR ξ hξR]

theorem contDiff_profileField {α : ℝ} (hα : 1 < α) {w : Space → Freq.CSpace} (hw : IsProfileSymbol α w) :
    ContDiff ℝ 2 (Freq.niceField w) := by
  have hpow : ∀ n : ℕ, (n : ℕ∞) ≤ (2 : ℕ∞) → Integrable (fun v : Space => ‖v‖ ^ n * ‖w v‖) :=
    fun n hn => profile_integrable_pow hα hw n (by exact_mod_cast hn)
  have hF : 𝓕⁻ w = VectorFourier.fourierIntegral 𝐞 volume
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ w :=
    funext fun y => SmoothFlow.Internal.freqTrInv_eq_integral w y
  have hcd := VectorFourier.contDiff_fourierIntegral (μ := volume)
    (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) (N := 2) hpow
  rw [← hF] at hcd
  exact Freq.realVec.contDiff.comp hcd

theorem divergence_profileField {α : ℝ} (hα : 1 < α) {w : Space → Freq.CSpace} (hw : IsProfileSymbol α w)
    (y : Space) :
    ∑ i : Fin 3, inner ℝ (fderiv ℝ (Freq.niceField w) y (unitVector i)) (unitVector i) = 0 := by
  have hi0 : Integrable w := by
    have := profile_integrable_pow hα hw 0 (by norm_num)
    simp only [pow_zero, one_mul] at this
    exact (integrable_norm_iff (profile_aesm hw)).1 this
  have hi1 : Integrable (fun v : Space => ‖v‖ * ‖w v‖) := by
    simpa using profile_integrable_pow hα hw 1 (by norm_num)
  have hd := (Freq.realVec.hasFDerivAt).comp y (SmoothFlow.Internal.hasFDerivAt_freqTrInv hi0 hi1 y)
  have hfd : ∀ h, fderiv ℝ (Freq.niceField w) y h =
      Freq.realVec (𝓕⁻ (fun ξ => (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ)) • w ξ) y) := by
    intro h
    have : Freq.niceField w = Freq.realVec ∘ 𝓕⁻ w := rfl
    rw [this, hd.fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [SmoothFlow.Internal.freqTrIntegral_smulRight_apply hi0 hi1]
  have hre : ∀ (z : Freq.CSpace) (i : Fin 3), Freq.realVec z i = (z i).re := fun z i => rfl
  simp_rw [hfd]
  simp_rw [SmoothFlow.Internal.inner_unitVector, hre]
  rw [← Complex.re_sum]
  have hint' : ∀ i : Fin 3, Integrable (fun ξ : Space => (2 * (π : ℂ) * Complex.I * ((ξ i : ℝ) : ℂ)) • w ξ) :=
    fun i => by
      simpa only [SmoothFlow.Internal.inner_unitVector] using
        SmoothFlow.Internal.integrable_symbol_smul hi0 hi1 (unitVector i)
  have hint : ∀ i : Fin 3, Integrable
      (fun ξ : Space => ((2 * (π : ℂ) * Complex.I * ((ξ i : ℝ) : ℂ)) • w ξ) i) :=
    fun i => (EuclideanSpace.proj (𝕜 := ℂ) i).integrable_comp (hint' i)
  have hc : ∀ i : Fin 3, 𝓕⁻ (fun ξ : Space => (2 * (π : ℂ) * Complex.I * ((ξ i : ℝ) : ℂ)) • w ξ) y i =
      𝓕⁻ (fun ξ : Space => ((2 * (π : ℂ) * Complex.I * ((ξ i : ℝ) : ℂ)) • w ξ) i) y :=
    fun i => SmoothFlow.Internal.freqTrInv_coord (hint' i) y i
  simp_rw [hc, SmoothFlow.Internal.freqTrInv_eq_integral]
  simp only [VectorFourier.fourierIntegral]
  rw [← integral_finsetSum _ (fun i _ => SmoothFlow.Internal.integrable_freqTr_integrand (hint i) y)]
  have hz : ∀ ξ : Space, ∑ i : Fin 3, ((2 * (π : ℂ) * Complex.I * ((ξ i : ℝ) : ℂ)) • w ξ) i = 0 := by
    intro ξ
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [show (∑ i : Fin 3, 2 * (π : ℂ) * Complex.I * ((ξ i : ℝ) : ℂ) * w ξ i) =
        2 * (π : ℂ) * Complex.I * ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * w ξ i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)]
    rw [hw.2.2.2.2 ξ, mul_zero]
  simp_rw [← Finset.smul_sum, hz, smul_zero, integral_zero, Complex.zero_re]

theorem profileSymbolSmooth : ProfileSymbolSmoothStatement :=
  fun _ hα _ _ hw => ⟨contDiff_profileField hα hw, divergence_profileField hα hw⟩


private theorem weak_of_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : Space → E} (hg : ContDiff ℝ 1 g) (φ : Space → ℝ) (hφ : IsTestScalar φ) (j : Fin 3) :
    ∫ y, fderiv ℝ φ y (unitVector j) • g y = -∫ y, φ y • fderiv ℝ g y (unitVector j) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (by exact_mod_cast le_top)
  have hcφ : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcg : Continuous (fun y => fderiv ℝ g y (unitVector j)) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsφ : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
    hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector j)
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume) (f := φ) (g := g)
    (v := unitVector j)
    ((hcφ.smul hg.continuous).integrable_of_hasCompactSupport (hsφ.smul_right))
    ((hφ1.continuous.smul hcg).integrable_of_hasCompactSupport (hφ.2.smul_right))
    ((hφ1.continuous.smul hg.continuous).integrable_of_hasCompactSupport (hφ.2.smul_right))
    (fun x _ => hφ1.differentiable one_ne_zero x) (fun x _ => hg.differentiable one_ne_zero x)
  rw [h, neg_neg]

private theorem second_apply {v : Space → Space} (hv : ContDiff ℝ 2 v) (i j : Fin 3) (y : Space) :
    fderiv ℝ (fun z => fderiv ℝ v z (unitVector i)) y (unitVector j) =
      fderiv ℝ (fun z => fderiv ℝ v z) y (unitVector j) (unitVector i) := by
  have hd : DifferentiableAt ℝ (fun z => fderiv ℝ v z) y :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) y
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp


private theorem integrable_of_rpow_bound {E : Type*} [NormedAddCommGroup E] {g : Space → E}
    (hm : AEStronglyMeasurable g volume) {R C β : ℝ} (hβ : -3 < β)
    (hR : ∀ ξ : Space, R < ‖ξ‖ → g ξ = 0) (hC : ∀ ξ : Space, ξ ≠ 0 → ‖g ξ‖ ≤ C * ‖ξ‖ ^ β) :
    Integrable g := by
  have hae : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have hball : IntegrableOn g (Metric.ball 0 (|R| + 1)) volume := by
    refine integrableOn_ball_of_norm_le_rpow (by simp) (α := -β) (C := C) ?_ ?_ hm
    · simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
      linarith
    · exact ae_restrict_of_ae (hae.mono fun ξ hξ => by rw [neg_neg]; exact hC ξ hξ)
  refine hball.integrable_of_forall_notMem_eq_zero fun ξ hξ => ?_
  have : |R| + 1 ≤ ‖ξ‖ := by simpa [Metric.mem_ball, dist_zero_right, not_lt] using hξ
  exact hR ξ (by linarith [le_abs_self R])

private theorem norm_mult_le (ξ h : Space) :
    ‖(2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ))‖ ≤ 2 * π * ‖h‖ * ‖ξ‖ := by
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs,
    abs_of_pos pi_pos, mul_one]
  have := abs_real_inner_le_norm ξ h
  nlinarith [pi_pos]

private theorem mult_bound {g : Space → Freq.CSpace} {C β : ℝ}
    (hC : ∀ ξ : Space, ξ ≠ 0 → ‖g ξ‖ ≤ C * ‖ξ‖ ^ β) (h : Space) :
    ∀ ξ : Space, ξ ≠ 0 → ‖(2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ)) • g ξ‖ ≤
      (2 * π * ‖h‖ * C) * ‖ξ‖ ^ (β + 1) := by
  intro ξ hξ
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  rw [norm_smul, Real.rpow_add hpos, Real.rpow_one]
  calc _ ≤ (2 * π * ‖h‖ * ‖ξ‖) * (C * ‖ξ‖ ^ β) :=
        mul_le_mul (norm_mult_le ξ h) (hC ξ hξ) (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem sq_bound {E : Type*} [NormedAddCommGroup E] {g : Space → E} {C β : ℝ}
    (hC : ∀ ξ : Space, ξ ≠ 0 → ‖g ξ‖ ≤ C * ‖ξ‖ ^ β) :
    ∀ ξ : Space, ξ ≠ 0 → ‖‖g ξ‖ ^ 2‖ ≤ C ^ 2 * ‖ξ‖ ^ (2 * β) := by
  intro ξ hξ
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  rw [Real.norm_of_nonneg (by positivity), mul_comm 2 β, Real.rpow_mul hpos.le, Real.rpow_two, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC ξ hξ) 2

private theorem mult_aesm {g : Space → Freq.CSpace} (hm : AEStronglyMeasurable g volume) (h : Space) :
    AEStronglyMeasurable (fun ξ : Space => (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ)) • g ξ) volume :=
  (Continuous.aestronglyMeasurable (continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)))).smul hm

private theorem fderiv_niceField_apply {g : Space → Freq.CSpace} (hi0 : Integrable g)
    (hi1 : Integrable (fun v : Space => ‖v‖ * ‖g v‖)) (y h : Space) :
    fderiv ℝ (Freq.niceField g) y h =
      Freq.niceField (fun ξ => (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ)) • g ξ) y := by
  have hd := (Freq.realVec.hasFDerivAt).comp y (SmoothFlow.Internal.hasFDerivAt_freqTrInv hi0 hi1 y)
  have : Freq.niceField g = Freq.realVec ∘ 𝓕⁻ g := rfl
  rw [this, hd.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [SmoothFlow.Internal.freqTrIntegral_smulRight_apply hi0 hi1]
  rfl

private theorem profile_facts {g : Space → Freq.CSpace} (hm : AEStronglyMeasurable g volume) {R C β : ℝ}
    (hβ : -3 / 2 < β) (hR : ∀ ξ : Space, R < ‖ξ‖ → g ξ = 0)
    (hC : ∀ ξ : Space, ξ ≠ 0 → ‖g ξ‖ ≤ C * ‖ξ‖ ^ β) :
    Integrable g ∧ MemLp g 2 volume ∧ MemLp (Freq.niceField g) 2 volume := by
  have h1 : Integrable g := integrable_of_rpow_bound hm (by linarith) hR hC
  have h2 : MemLp g 2 volume := (memLp_two_iff_integrable_sq_norm hm).2
    (integrable_of_rpow_bound (R := R) (hm.norm.pow 2) (by linarith) (fun ξ hξ => by simp [hR ξ hξ]) (sq_bound hC))
  exact ⟨h1, h2, SmoothFlow.Internal.RegEmbed.memLp_realVec_freqTrInv h1 h2⟩

private theorem moment_integrable {g : Space → Freq.CSpace} (hm : AEStronglyMeasurable g volume) {R C β : ℝ}
    (hβ : -4 < β) (hR : ∀ ξ : Space, R < ‖ξ‖ → g ξ = 0)
    (hC : ∀ ξ : Space, ξ ≠ 0 → ‖g ξ‖ ≤ C * ‖ξ‖ ^ β) : Integrable (fun v : Space => ‖v‖ * ‖g v‖) := by
  refine integrable_of_rpow_bound (β := β + 1) (C := C) (R := R)
    (continuous_norm.aestronglyMeasurable.mul hm.norm) (by linarith) (fun ξ hξ => by simp [hR ξ hξ])
    (fun ξ hξ => ?_)
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_add hpos, Real.rpow_one]
  calc ‖ξ‖ * ‖g ξ‖ ≤ ‖ξ‖ * (C * ‖ξ‖ ^ β) := mul_le_mul_of_nonneg_left (hC ξ hξ) hpos.le
    _ = _ := by ring

theorem energy_profileField {α : ℝ} (hα : 1 < α) (hα' : α < 5 / 4) {w : Space → Freq.CSpace}
    (hw : IsProfileSymbol α w) :
    Integrable (fun y => entrySq (fderiv ℝ (Freq.niceField w) y)) ∧
      Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun z => fderiv ℝ (Freq.niceField w) z) y (unitVector i) (unitVector j)‖ ^ 2) := by
  have hm := profile_aesm hw
  have hv := contDiff_profileField hα hw
  obtain ⟨R, hR⟩ := hw.2.1
  obtain ⟨C, hC0⟩ := hw.2.2.1 0
  have hC : ∀ ξ : Space, ξ ≠ 0 → ‖w ξ‖ ≤ C * ‖ξ‖ ^ (2 * α - 4) := fun ξ hξ => by
    have := hC0 ξ hξ
    rwa [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero] at this
  have hw0 : Integrable w := integrable_of_rpow_bound hm (by linarith) hR hC
  have hw1 := moment_integrable hm (by linarith) hR hC
  set c : Space → Space → ℂ := fun h ξ => 2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ) with hc
  have hRg : ∀ h ξ, R < ‖ξ‖ → c h ξ • w ξ = 0 := fun h ξ hξ => by simp [hR ξ hξ]
  have hCg := fun h => mult_bound hC h
  have hfirst : ∀ i : Fin 3, (fun y => fderiv ℝ (Freq.niceField w) y (unitVector i)) =
      Freq.niceField (fun ξ => c (unitVector i) ξ • w ξ) :=
    fun i => funext fun y => fderiv_niceField_apply hw0 hw1 y (unitVector i)
  refine ⟨?_, ?_⟩
  · have hfun : (fun y => entrySq (fderiv ℝ (Freq.niceField w) y)) =
        fun y => ∑ i : Fin 3, ‖Freq.niceField (fun ξ => c (unitVector i) ξ • w ξ) y‖ ^ 2 := by
      funext y
      simp only [entrySq]
      exact Finset.sum_congr rfl fun i _ => by rw [← hfirst i]
    rw [hfun]
    refine integrable_finsetSum _ fun i _ => ?_
    have hf := (profile_facts (mult_aesm hm (unitVector i)) (by linarith) (hRg (unitVector i))
      (hCg (unitVector i))).2.2
    exact (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  · refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    have hgj0 : Integrable (fun ξ => c (unitVector j) ξ • w ξ) :=
      integrable_of_rpow_bound (mult_aesm hm _) (by linarith) (hRg _) (hCg _)
    have hgj1 := moment_integrable (mult_aesm hm (unitVector j)) (by linarith) (hRg _) (hCg _)
    have heq : (fun y => ‖fderiv ℝ (fun z => fderiv ℝ (Freq.niceField w) z) y (unitVector i) (unitVector j)‖ ^ 2) =
        fun y => ‖Freq.niceField (fun ξ => c (unitVector i) ξ • (c (unitVector j) ξ • w ξ)) y‖ ^ 2 := by
      funext y
      rw [← second_apply hv j i y, hfirst j, fderiv_niceField_apply hgj0 hgj1 y (unitVector i)]
    rw [heq]
    have hRgg : ∀ ξ : Space, R < ‖ξ‖ → c (unitVector i) ξ • (c (unitVector j) ξ • w ξ) = 0 :=
      fun ξ hξ => by simp [hR ξ hξ]
    have hf := (profile_facts (mult_aesm (mult_aesm hm (unitVector j)) (unitVector i)) (by linarith) hRgg
      (mult_bound (hCg (unitVector j)) (unitVector i))).2.2
    exact (memLp_two_iff_integrable_sq_norm hf.1).1 hf

theorem profileSymbolEnergy : ProfileSymbolEnergyStatement :=
  fun _ hα hα' _ hw => energy_profileField hα hα' hw

private theorem pair_scalar {a b : Space → ℂ} (ha : Integrable a) (hb : Integrable b) :
    ∫ x, 𝓕⁻ a x * b x = ∫ ξ, a ξ * 𝓕⁻ b ξ := by
  have hflip : ((-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂).flip =
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ := by
    ext x y
    simp [real_inner_comm]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := 𝐞) (μ := volume) (ν := volume)
    (L := (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂) continuous_fourierChar
    (by apply (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).continuous₂ :
      Continuous (fun p : Space × Space =>
        (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ p.1 p.2)) ha hb
  rw [hflip] at h
  simp only [smul_eq_mul] at h
  simp_rw [SmoothFlow.Internal.freqTrInv_eq_integral]
  exact h

private theorem continuous_inverseTransform_of {a : Space → ℂ} (ha : Integrable a) : Continuous (𝓕⁻ a) := by
  have : 𝓕⁻ a = VectorFourier.fourierIntegral 𝐞 volume
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ a :=
    funext fun y => SmoothFlow.Internal.freqTrInv_eq_integral a y
  rw [this]
  exact VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by apply (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).continuous₂ :
      Continuous (fun p : Space × Space =>
        (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ p.1 p.2)) ha

private theorem norm_inverseTransform_le_of (a : Space → ℂ) (x : Space) : ‖𝓕⁻ a x‖ ≤ ∫ ξ, ‖a ξ‖ := by
  rw [SmoothFlow.Internal.freqTrInv_eq_integral]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

private theorem pair_vector {h : Space → Freq.CSpace} (hh : Integrable h) {f : Space → Space}
    (hf : Integrable f) :
    ∫ x, inner ℝ (Freq.niceField h x) (f x) =
      ∑ i : Fin 3, (∫ ξ, h ξ i * 𝓕⁻ (fun x => ((f x i : ℝ) : ℂ)) ξ).re := by
  have hhi : ∀ i : Fin 3, Integrable (fun ξ => h ξ i) :=
    fun i => (EuclideanSpace.proj (𝕜 := ℂ) i).integrable_comp hh
  have hfi : ∀ i : Fin 3, Integrable (fun x => ((f x i : ℝ) : ℂ)) :=
    fun i => ((EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hf).ofReal
  have hP : ∀ i : Fin 3, Integrable (fun x => 𝓕⁻ (fun ξ => h ξ i) x * ((f x i : ℝ) : ℂ)) := by
    intro i
    refine (hf.norm.const_mul (∫ ξ, ‖h ξ i‖)).mono'
      ((continuous_inverseTransform_of (hhi i)).aestronglyMeasurable.mul (hfi i).1)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (norm_inverseTransform_le_of _ x) (SmoothFlow.Internal.RegEmbed.abs_coord_le (f x) i)
      (abs_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  have hpt : ∀ x, inner ℝ (Freq.niceField h x) (f x) =
      ∑ i : Fin 3, (𝓕⁻ (fun ξ => h ξ i) x * ((f x i : ℝ) : ℂ)).re := by
    intro x
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_mul_ofReal, ← SmoothFlow.Internal.freqTrInv_coord hh x i]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [mul_comm]
    rfl
  simp_rw [hpt]
  have hPr : ∀ i : Fin 3, Integrable (fun x => (𝓕⁻ (fun ξ => h ξ i) x * ((f x i : ℝ) : ℂ)).re) :=
    fun i => (hP i).re
  rw [integral_finsetSum _ fun i _ => hPr i]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := integral_re (hP i)
  rw [pair_scalar (hhi i) (hfi i)] at this
  exact this

theorem power_profileField {α : ℝ} (hα : 1 < α) (hα' : α < 5 / 4) {w : Space → Freq.CSpace}
    (hw : IsProfileSymbol α w) :
    IsWeakFractionalPower α (Freq.niceField w) (Freq.niceField (fun ξ => freqPow (2 * α) ξ • w ξ)) := by
  have hm := profile_aesm hw
  obtain ⟨R, hR⟩ := hw.2.1
  obtain ⟨C, hC0⟩ := hw.2.2.1 0
  have hC : ∀ ξ : Space, ξ ≠ 0 → ‖w ξ‖ ≤ C * ‖ξ‖ ^ (2 * α - 4) := fun ξ hξ => by
    have := hC0 ξ hξ
    rwa [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero] at this
  have hw0 : Integrable w := integrable_of_rpow_bound hm (by linarith) hR hC
  have hk : Continuous (fun ξ : Space => freqPow (2 * α) ξ) := by
    unfold freqPow
    exact (continuous_const.mul continuous_norm).rpow_const (fun _ => Or.inr (by linarith))
  have hgm : AEStronglyMeasurable (fun ξ => freqPow (2 * α) ξ • w ξ) volume :=
    hk.aestronglyMeasurable.smul hm
  have hgR : ∀ ξ : Space, R < ‖ξ‖ → freqPow (2 * α) ξ • w ξ = 0 := fun ξ hξ => by simp [hR ξ hξ]
  have hgC : ∀ ξ : Space, ξ ≠ 0 →
      ‖freqPow (2 * α) ξ • w ξ‖ ≤ ((2 * π) ^ (2 * α) * C) * ‖ξ‖ ^ (4 * α - 4) := by
    intro ξ hξ
    have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hf0 : 0 ≤ freqPow (2 * α) ξ := by unfold freqPow; positivity
    rw [norm_smul, Real.norm_of_nonneg hf0]
    unfold freqPow
    rw [Real.mul_rpow (by positivity) hpos.le]
    calc (2 * π) ^ (2 * α) * ‖ξ‖ ^ (2 * α) * ‖w ξ‖ ≤
          (2 * π) ^ (2 * α) * ‖ξ‖ ^ (2 * α) * (C * ‖ξ‖ ^ (2 * α - 4)) :=
        mul_le_mul_of_nonneg_left (hC ξ hξ) (by positivity)
      _ = _ := by
        rw [show 4 * α - 4 = 2 * α + (2 * α - 4) by ring, Real.rpow_add hpos]
        ring
  obtain ⟨hg1, -, hgL2⟩ := profile_facts hgm (by linarith) hgR hgC
  refine ⟨hgL2, fun φ hφ => ?_⟩
  set φS : 𝓢(Space, Space) := hφ.2.toSchwartzMap hφ.1 with hφSdef
  have hφS : ⇑φS = φ := rfl
  have hφi : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2
  have hψi : Integrable (fractionalPowerAt α φ) := by
    have := FracInternal.NiceField.integrable_fracPower α hα (by linarith) φS
    rwa [hφS] at this
  rw [pair_vector hg1 hφi, pair_vector hw0 hψi]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have hsym := symbol α hα (by linarith) φS (-ξ)
  rw [hφS] at hsym
  have hcψ : Integrable (fun x => Freq.complexifyVec (fractionalPowerAt α φ x)) :=
    Freq.complexifyVec.integrable_comp hψi
  have hcφ : Integrable (fun x => Freq.complexifyVec (φ x)) := Freq.complexifyVec.integrable_comp hφi
  have e1 : 𝓕⁻ (fun x => ((fractionalPowerAt α φ x i : ℝ) : ℂ)) ξ =
      𝓕⁻ (fun x => Freq.complexifyVec (fractionalPowerAt α φ x)) ξ i :=
    (SmoothFlow.Internal.freqTrInv_coord hcψ ξ i).symm
  have e2 : 𝓕⁻ (fun x => ((φ x i : ℝ) : ℂ)) ξ = 𝓕⁻ (fun x => Freq.complexifyVec (φ x)) ξ i :=
    (SmoothFlow.Internal.freqTrInv_coord hcφ ξ i).symm
  beta_reduce
  rw [e1, e2, Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg, hsym]
  simp only [PiLp.smul_apply, smul_eq_mul, norm_neg, freqPow, Complex.real_smul]
  ring

theorem profileSymbolPower : ProfileSymbolPowerStatement :=
  fun _ hα hα' _ hw => power_profileField hα hα' hw

theorem profileSymbolRealize_of (hs : ProfileSymbolSmoothStatement) (h6 : ProfileSymbolSixStatement)
    (he : ProfileSymbolEnergyStatement) (hp : ProfileSymbolPowerStatement) : ProfileSymbolRealizeStatement := by
  intro α hα hα' m w hw hwc
  obtain ⟨hv, hdiv⟩ := hs α hα hα' w hw
  obtain ⟨hg2, hh2⟩ := he α hα hα' w hw
  have hf1 : ContDiff ℝ 1 (fun z => fderiv ℝ (Freq.niceField w) z) :=
    hv.fderiv_right (m := 1) (by norm_num)
  refine ⟨⟨hv.continuous.aestronglyMeasurable, (hf1.continuous).aestronglyMeasurable,
    (hf1.continuous_fderiv one_ne_zero).aestronglyMeasurable, h6 α hα hα' w hw, hg2, hh2, ?_, ?_,
    Filter.Eventually.of_forall hdiv, hwc⟩, hp α hα hα' w hw⟩
  · intro φ hφ j
    exact weak_of_contDiff (hv.of_le (by norm_num)) φ hφ j
  · intro φ hφ i j
    have hg : ContDiff ℝ 1 (fun z => fderiv ℝ (Freq.niceField w) z (unitVector i)) :=
      hf1.clm_apply contDiff_const
    rw [weak_of_contDiff hg φ hφ j]
    congr 1
    congr 1
    funext y
    rw [second_apply hv i j y]

theorem freeExistsNice_of (h1 : FreeSymbolExistsStatement) (h4 : ProfileSymbolSixStatement)
    (h3 : ProfileSymbolEquationStatement) : FreeExistsNiceStatement := by
  intro α hα hα' a m s hs hcl
  obtain ⟨w, hw, hwc, heq⟩ := h1 α hα hα' a m s hs hcl
  obtain ⟨hso, hpow⟩ := profileSymbolRealize_of profileSymbolSmooth h4 profileSymbolEnergy profileSymbolPower α hα hα' m w hw hwc
  obtain ⟨hdrift, hae⟩ := h3 α hα hα' a s w hs hw heq
  exact ⟨Freq.niceField w, fun y => fderiv ℝ (Freq.niceField w) y,
    fun y => fderiv ℝ (fun z => fderiv ℝ (Freq.niceField w) z) y,
    Freq.niceField (fun ξ => freqPow (2 * α) ξ • w ξ), hso, hpow, hdrift, hae⟩

end SteadyCert

end Breakdown
