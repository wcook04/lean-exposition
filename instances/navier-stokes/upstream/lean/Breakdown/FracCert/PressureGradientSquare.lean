import Breakdown.FracCert.WeakRegular

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow Breakdown.SteadyCert

namespace PressureGradientSquareInternal

theorem sq_lintegral_mul_le (a b : Space → ℝ≥0∞) (ha : AEMeasurable a) (hb : AEMeasurable b) :
    (∫⁻ η, a η * b η) ^ 2 ≤ (∫⁻ η, a η) * ∫⁻ η, a η * b η ^ 2 := by
  have hh : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hfa : AEMeasurable (fun η => a η ^ (1 / 2 : ℝ)) := ha.pow_const _
  have hga : AEMeasurable (fun η => a η ^ (1 / 2 : ℝ) * b η) := hfa.mul hb
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hfa hga
  have e1 : ∀ η, (a η ^ (1 / 2 : ℝ)) * (a η ^ (1 / 2 : ℝ) * b η) = a η * b η := by
    intro η
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hh hh]
    norm_num
  have e2 : ∀ η, (a η ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a η := by
    intro η
    rw [← ENNReal.rpow_mul]
    norm_num
  have e3 : ∀ η, (a η ^ (1 / 2 : ℝ) * b η) ^ (2 : ℝ) = a η * b η ^ 2 := by
    intro η
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), e2, ENNReal.rpow_two]
  simp only [Pi.mul_apply, e1, e2, e3] at H
  calc (∫⁻ η, a η * b η) ^ 2
      ≤ ((∫⁻ η, a η) ^ (1 / 2 : ℝ) * (∫⁻ η, a η * b η ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ η, a η) * ∫⁻ η, a η * b η ^ 2 := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

theorem lintegral_conv_sq_le (a b : Space → ℝ≥0∞) (ha : Measurable a) (hb : Measurable b) :
    ∫⁻ ξ, (∫⁻ η, a η * b (ξ - η)) ^ 2 ≤ (∫⁻ η, a η) ^ 2 * ∫⁻ ξ, b ξ ^ 2 := by
  have hJ : Measurable (Function.uncurry fun (ξ η : Space) => a η * b (ξ - η) ^ 2) :=
    (ha.comp measurable_snd).mul ((hb.comp (measurable_fst.sub measurable_snd)).pow_const 2)
  calc ∫⁻ ξ, (∫⁻ η, a η * b (ξ - η)) ^ 2
      ≤ ∫⁻ ξ, (∫⁻ η, a η) * ∫⁻ η, a η * b (ξ - η) ^ 2 :=
        lintegral_mono fun ξ => sq_lintegral_mul_le _ _ ha.aemeasurable
          (hb.comp (measurable_const.sub measurable_id)).aemeasurable
    _ = (∫⁻ η, a η) * ∫⁻ ξ, ∫⁻ η, a η * b (ξ - η) ^ 2 :=
        lintegral_const_mul _ hJ.lintegral_prod_right
    _ = (∫⁻ η, a η) * ∫⁻ η, ∫⁻ ξ, a η * b (ξ - η) ^ 2 := by
        rw [lintegral_lintegral_swap hJ.aemeasurable]
    _ = (∫⁻ η, a η) * ∫⁻ η, a η * ∫⁻ ξ, b ξ ^ 2 := by
        congr 1
        refine lintegral_congr fun η => ?_
        have hmeas : Measurable fun ξ : Space => b (ξ - η) ^ 2 :=
          (hb.comp (measurable_id.sub (measurable_const (a := η)))).pow_const 2
        rw [lintegral_const_mul _ hmeas]
        exact congrArg _ (lintegral_sub_right_eq_self (fun ξ => b ξ ^ 2) η)
    _ = (∫⁻ η, a η) ^ 2 * ∫⁻ ξ, b ξ ^ 2 := by
        rw [lintegral_mul_const _ ha, pow_two, mul_assoc]

theorem memLp_convC {p q : Space → ℂ} (hp : StronglyMeasurable p) (hq : StronglyMeasurable q)
    (hp1 : Integrable p) (hq2 : MemLp q 2) : MemLp (convC p q) 2 volume := by
  have hS : StronglyMeasurable (Function.uncurry fun (ξ η : Space) => p η * q (ξ - η)) :=
    (hp.comp_measurable measurable_snd).mul (hq.comp_measurable (measurable_fst.sub measurable_snd))
  have hm : StronglyMeasurable (convC p q) := hS.integral_prod_right
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  have hq' := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (μ := volume) (f := q) two_ne_zero
    ENNReal.ofNat_ne_top).1 hq2.2
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at hq' ⊢
  have hb := lintegral_conv_sq_le (fun η => ‖p η‖ₑ) (fun η => ‖q η‖ₑ) hp.measurable.enorm
    hq.measurable.enorm
  have hpt : ∫⁻ η, ‖p η‖ₑ < ⊤ := hp1.2
  calc ∫⁻ ξ, ‖convC p q ξ‖ₑ ^ 2
      ≤ ∫⁻ ξ, (∫⁻ η, ‖p η‖ₑ * ‖q (ξ - η)‖ₑ) ^ 2 := by
        refine lintegral_mono fun ξ => ?_
        gcongr
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        simp only [enorm_mul]
    _ ≤ (∫⁻ η, ‖p η‖ₑ) ^ 2 * ∫⁻ ξ, ‖q ξ‖ₑ ^ 2 := hb
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.pow_lt_top hpt) hq'

end PressureGradientSquareInternal

namespace PressureGradientSquareInternal

open WeakRegularInternal

theorem norm_le_sum_coord (z : CSpace) : ‖z‖ ≤ ∑ i, ‖z i‖ := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ i, ‖z i‖ ^ 2) ≤ √((∑ i, ‖z i‖) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _)
    _ = ∑ i, ‖z i‖ := Real.sqrt_sq (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem inner_freqVec_eq (ξ : Space) (A : CSpace) :
    ∑ i, ((ξ i : ℝ) : ℂ) * A i = inner ℂ (freqVec ξ) A := by
  simp [PiLp.inner_apply, freqVec, complexifyVec, mul_comm]

theorem norm_gradSymbol_le (A : CSpace) (ξ : Space) :
    ‖(2 * (π : ℂ) * Complex.I * (-(∑ i, ((ξ i : ℝ) : ℂ) * A i) /
      (2 * (π : ℂ) * Complex.I * (((‖ξ‖ ^ 2 : ℝ)) : ℂ)))) • freqVec ξ‖ ≤ ‖A‖ := by
  rcases eq_or_ne ξ 0 with h0 | h0
  · rw [norm_smul, Breakdown.SmoothFlow.Internal.norm_freqVec, h0, norm_zero, mul_zero]
    exact norm_nonneg _
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 h0
  have hc : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hr : (((‖ξ‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hn 2).ne'
  have hb : ‖∑ i, ((ξ i : ℝ) : ℂ) * A i‖ ≤ ‖ξ‖ * ‖A‖ := by
    rw [inner_freqVec_eq, ← Breakdown.SmoothFlow.Internal.norm_freqVec ξ]
    exact norm_inner_le_norm _ _
  set s := ∑ i, ((ξ i : ℝ) : ℂ) * A i
  have e : 2 * (π : ℂ) * Complex.I * (-s / (2 * (π : ℂ) * Complex.I * (((‖ξ‖ ^ 2 : ℝ)) : ℂ))) =
      -s / (((‖ξ‖ ^ 2 : ℝ)) : ℂ) := by
    field_simp
  rw [norm_smul, e, norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Breakdown.SmoothFlow.Internal.norm_freqVec, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hb hn.le]

end PressureGradientSquareInternal

open WeakRegularInternal PressureGradientSquareInternal in
theorem pressureGradientSquare (h1 : SymbolL1OfMomentsStatement) : PressureGradientSquareStatement := by
  intro U hM
  have hwm := (h1 U hM).1
  have hae := cleanSymbol_ae (goodSet_ae U)
  have hsol : IsSolenoidalSymbol (cleanSymbol (symbolX U)) :=
    fun ξ => ⟨cleanSymbol_div _ ξ, cleanSymbol_conjSym _ ξ⟩
  have hmf : AEStronglyMeasurable (cleanSymbol (symbolX U)) volume := (aesm_symbolX U).congr hae.symm
  have hW := memLp_pressureSymbol_single (memLp_clean U hwm) hsol
  have hM1 : homNormSq 1 (cleanSymbol (symbolX U)) < ⊤ := by
    rw [homNormSq, lintegral_congr_ae (by filter_upwards [hae] with ξ h; rw [h])]
    exact hM 1 le_rfl
  have M1 := memLp_of_homNormSq hmf 1 hM1
  have hI0 := moments_clean U hwm 0
  have hP : profilePressure U = physScalar (pressureSymbol (cleanSymbol (symbolX U))) := by
    rw [pressure_clean U]
    rfl
  set f := cleanSymbol (symbolX U) with hf
  set g := pressureSymbol f with hg
  have hsn : ∀ ξ, ‖g ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)‖ = ‖g ξ‖ := fun ξ => by
    rw [norm_smul]
    simp
  have hS0 := integrable_of_memLp_weight (hW 0)
  have hmS : AEStronglyMeasurable (fun ξ => g ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) volume :=
    hS0.aestronglyMeasurable
  have hmg : AEStronglyMeasurable g volume := by
    have h2 := (EuclideanSpace.proj (0 : Fin 3) : CSpace →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hmS
    refine h2.congr (ae_of_all _ fun ξ => ?_)
    simp
  have hg0 : Integrable g := hS0.norm.mono' hmg (ae_of_all _ fun ξ => (hsn ξ).ge)
  have hfv : Continuous freqVec := complexifyVec.continuous
  have hg1 : Integrable (fun ξ => g ξ • freqVec ξ) := by
    refine ⟨hmg.smul hfv.aestronglyMeasurable, ?_⟩
    have h2 := (memLp_weight_iff hmS).1 (hW 1)
    refine lt_of_le_of_lt (lintegral_mono fun ξ => ?_) h2
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_smul, Breakdown.SmoothFlow.Internal.norm_freqVec, hsn, pow_one]
    nlinarith [norm_nonneg (g ξ), norm_nonneg ξ]
  set G : Space → CSpace := fun ξ => (2 * (π : ℂ) * Complex.I * g ξ) • freqVec ξ with hG
  have hGI : Integrable G :=
    (hg1.smul (2 * (π : ℂ) * Complex.I)).congr
      (ae_of_all _ fun ξ => by simp only [hG, Pi.smul_apply, smul_smul])
  have hgrad : gradientAt (profilePressure U) = fun x => realVec (𝓕⁻ G x) := by
    funext x
    rw [hP]
    exact gradientAt_physScalar hg0 hg1 x
  set fm := hmf.mk f with hfmdef
  have hfm : StronglyMeasurable fm := hmf.stronglyMeasurable_mk
  have hfe : f =ᵐ[volume] fm := hmf.ae_eq_mk
  have hA : advectionSymbol f = advectionSymbol fm := advection_congr hfe
  have hproj : ∀ j : Fin 3, StronglyMeasurable (fun η => fm η j) := by
    intro j
    have h := (EuclideanSpace.proj j : CSpace →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hfm
    convert h using 1
    funext η
    simp
  have hfmI : Integrable fm :=
    hI0.mono' hfm.aestronglyMeasurable (by
      filter_upwards [hfe] with η hη
      rw [← hη, pow_zero, one_mul])
  have hc : ∀ i j : Fin 3, MemLp (convC (fun η => fm η j)
      (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * fm η i)) 2 volume := by
    intro i j
    have hq : StronglyMeasurable (fun η : Space => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * fm η i) :=
      (by fun_prop : Continuous fun η : Space => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ)).stronglyMeasurable.mul
        (hproj i)
    refine memLp_convC (hproj j) hq ?_ ?_
    · exact hfmI.norm.mono' (hproj j).aestronglyMeasurable
        (ae_of_all _ fun η => PiLp.norm_apply_le (fm η) j)
    · refine (M1.norm.const_mul (2 * π)).of_le hq.aestronglyMeasurable ?_
      filter_upwards [hfe] with η hη
      have e1 : ‖(2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * fm η i)‖ =
          2 * π * (‖η j‖ * ‖fm η i‖) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
          Complex.norm_ofNat, Real.norm_of_nonneg pi_pos.le]
        ring
      have e2 : ‖(2 * π * ‖(‖η‖ ^ 1 : ℝ) • f η‖ : ℝ)‖ = 2 * π * (‖η‖ * ‖fm η‖) := by
        rw [Real.norm_of_nonneg (by positivity), norm_smul, Real.norm_of_nonneg (by positivity), pow_one, hη]
      rw [e1, e2]
      gcongr
      · exact PiLp.norm_apply_le η j
      · exact PiLp.norm_apply_le (fm η) i
  have hsum : MemLp (fun ξ => ∑ i : Fin 3, ∑ j : Fin 3, ‖convC (fun η => fm η j)
      (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * fm η i) ξ‖) 2 volume :=
    memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => (hc i j).norm
  have hbound : ∀ ξ, ‖G ξ‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖convC (fun η => fm η j)
      (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * fm η i) ξ‖ := by
    intro ξ
    have hgξ : g ξ = -(∑ i, ((ξ i : ℝ) : ℂ) * advectionSymbol fm ξ i) /
        (2 * (π : ℂ) * Complex.I * (((‖ξ‖ ^ 2 : ℝ)) : ℂ)) := by
      rw [hg, pressureSymbol, hA]
    calc ‖G ξ‖ ≤ ‖advectionSymbol fm ξ‖ := by
          rw [hG]
          dsimp only
          rw [hgξ]
          exact norm_gradSymbol_le _ _
      _ ≤ ∑ i, ‖advectionSymbol fm ξ i‖ := norm_le_sum_coord _
      _ ≤ _ := Finset.sum_le_sum fun i _ => by
          simp only [advectionSymbol, advectionBilin, PiLp.toLp_apply]
          exact norm_sum_le _ _
  have hGL : MemLp G 2 volume :=
    hsum.of_le hGI.aestronglyMeasurable (ae_of_all _ fun ξ =>
      (hbound ξ).trans (le_of_eq (Real.norm_of_nonneg (by positivity)).symm))
  rw [hgrad]
  exact Breakdown.SmoothFlow.Internal.RegEmbed.memLp_realVec_freqTrInv hGI hGL

end Breakdown.FracCert
