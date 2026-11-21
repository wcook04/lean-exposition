import Breakdown.CertTorus.RegularStatements

open MeasureTheory Set Real Filter
open scoped ContDiff ENNReal Topology FourierTransform

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

namespace Internal.SymbolDilation

theorem finrank_space : Module.finrank ℝ Space = 3 := by simp

theorem homNormSq_eq_eLpNorm_sq (k : ℕ) (f : Space → CSpace) :
    homNormSq k f = eLpNorm (fun ξ => (‖ξ‖ ^ k : ℝ) • f ξ) 2 volume ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure Space))
    (f := fun ξ : Space => (‖ξ‖ ^ k : ℝ) • f ξ) (p := 2) two_ne_zero
  have e2 : ((2 : NNReal) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [e2] at h
  simp only [ENNReal.rpow_natCast, ENNReal.coe_ofNat] at h
  rw [h, homNormSq]
  refine lintegral_congr fun ξ => ?_
  rw [enorm_smul, Real.enorm_of_nonneg (by positivity), mul_pow, ← ENNReal.ofReal_pow (by positivity),
    ← pow_mul, mul_comm k 2]

theorem homNormSq_congr_ae (k : ℕ) {f g : Space → CSpace} (h : f =ᵐ[volume] g) :
    homNormSq k f = homNormSq k g := by
  refine lintegral_congr_ae ?_
  filter_upwards [h] with ξ e
  rw [e]

theorem homNormSq_comp_smul (k : ℕ) (f : Space → CSpace) {c : ℝ} (hc : 0 < c) :
    homNormSq k (fun ξ => c • f (c • ξ)) =
      ENNReal.ofReal (c ^ 2 * ((c ^ (2 * k))⁻¹ * (c ^ 3)⁻¹)) * homNormSq k f := by
  set F : Space → ℝ≥0∞ := fun η => ENNReal.ofReal (‖η‖ ^ (2 * k)) * ‖f η‖ₑ ^ 2 with hF
  have hpt : ∀ ξ : Space, ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * ‖c • f (c • ξ)‖ₑ ^ 2 =
      ENNReal.ofReal (c ^ 2 * (c ^ (2 * k))⁻¹) * F (c • ξ) := by
    intro ξ
    have hs : ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * ENNReal.ofReal c ^ 2 =
        ENNReal.ofReal (c ^ 2 * (c ^ (2 * k))⁻¹) * ENNReal.ofReal (‖c • ξ‖ ^ (2 * k)) := by
      rw [← ENNReal.ofReal_pow hc.le, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [norm_smul, Real.norm_of_nonneg hc.le, mul_pow]
      field_simp
    simp only [hF]
    rw [enorm_smul, Real.enorm_of_nonneg hc.le, mul_pow, ← mul_assoc, hs, mul_assoc]
  have hmap : ∫⁻ ξ, F (c • ξ) = ENNReal.ofReal (c ^ 3)⁻¹ * ∫⁻ η, F η := by
    have e := lintegral_map_equiv F (MeasurableEquiv.smul₀ c hc.ne' : Space ≃ᵐ Space) (μ := volume)
    have e' : (⇑(MeasurableEquiv.smul₀ c hc.ne' : Space ≃ᵐ Space)) = fun ξ : Space => c • ξ := rfl
    rw [e', Measure.map_addHaar_smul volume hc.ne', lintegral_smul_measure, finrank_space,
      abs_of_pos (by positivity)] at e
    rw [← e, smul_eq_mul]
  unfold homNormSq
  rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmap, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem symX_dilX_ae {μ : ℝ} (hμ : 0 < μ) (x : X) :
    symX (dilX μ x) =ᵐ[volume] fun ξ => (Real.sqrt μ)⁻¹ • symX x ((Real.sqrt μ)⁻¹ • ξ) := by
  have h := dilation_holds.2.2.2.2 μ hμ x
  have hr := Breakdown.Freq.Internal.DilationCont.scaleOp_realized fieldOpRealized_holds
    (inv_ne_zero (Real.sqrt_pos.2 hμ).ne') (x : L2C)
  unfold symX
  rw [h]
  exact hr

theorem lerayC_smul_vec (ξ : Space) (r : ℝ) (z : CSpace) : divFreeC ξ (r • z) = r • divFreeC ξ z := by
  ext i
  simp [divFreeC, freqVec, complexifyVec, Complex.real_smul]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_sub]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem lerayC_smul_freq (ξ : Space) {c : ℝ} (hc : 0 < c) (z : CSpace) :
    divFreeC (c • ξ) z = divFreeC ξ z := by
  rcases eq_or_ne ξ 0 with h | h
  · simp [h]
  have hn : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  ext i
  simp [divFreeC, freqVec, complexifyVec, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  simp only [mul_assoc (c : ℂ), ← Finset.mul_sum]
  field_simp

theorem velSymbol_dilX_ae {μ : ℝ} (hμ : 0 < μ) (x : X) :
    velSymbol (dilX μ x) =ᵐ[volume]
      fun ξ => ((Real.sqrt μ)⁻¹ ^ 2) • velSymbol x ((Real.sqrt μ)⁻¹ • ξ) := by
  set c := (Real.sqrt μ)⁻¹ with hc_def
  have hc : 0 < c := inv_pos.2 (Real.sqrt_pos.2 hμ)
  have h1 := symX_dilX_ae hμ x
  have h2 := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h1, h2] with ξ e1 e2
  simp only [Function.comp_apply] at e2
  simp only [velSymbol]
  rw [e1, e2, smul_neg, map_smul, ← smul_add, smul_comm (1 / 2 : ℝ) c, lerayC_smul_vec,
    lerayC_smul_freq ξ hc, smul_smul, smul_smul]
  congr 1
  rw [norm_smul, Real.norm_of_nonneg hc.le]
  rcases eq_or_ne ‖ξ‖ 0 with h | h
  · simp [h]
  · field_simp

theorem fourierInv_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Space → E) {c : ℝ} (hc : 0 < c) (y : Space) :
    𝓕⁻ (fun ξ => f (c • ξ)) y = (c ^ 3)⁻¹ • 𝓕⁻ f (c⁻¹ • y) := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  have key := Measure.integral_comp_smul (volume : Measure Space)
    (fun η : Space => Real.fourierChar (inner ℝ η (c⁻¹ • y)) • f η) c
  rw [finrank_space, abs_of_pos (by positivity)] at key
  rw [← key]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only [real_inner_smul_left, real_inner_smul_right, inv_mul_cancel_left₀ hc.ne']

theorem fourierInv_real_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (r : ℝ) (f : Space → E) (y : Space) :
    𝓕⁻ (fun ξ => r • f ξ) y = r • 𝓕⁻ f y := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq, ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only
  rw [Circle.smul_def, Circle.smul_def, ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul,
    mul_comm]

theorem advectionSymbol_scale {f f' : Space → CSpace} {c : ℝ} (hc : 0 < c)
    (hf : f =ᵐ[volume] fun ξ => (c ^ 2) • f' (c • ξ)) (ξ : Space) :
    advectionSymbol f ξ = advectionSymbol f' (c • ξ) := by
  unfold advectionSymbol advectionBilin
  congr 1
  funext i
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [convC]
  have h2 := (Measure.measurePreserving_sub_left (volume : Measure Space) ξ).quasiMeasurePreserving.ae_eq_comp hf
  have key := Measure.integral_comp_smul (volume : Measure Space)
    (fun η : Space => f' η j * (2 * (π : ℂ) * Complex.I * (((c • ξ - η) j : ℝ) : ℂ) * f' (c • ξ - η) i)) c
  rw [finrank_space, abs_of_pos (by positivity)] at key
  have e : ∫ η, f η j * (2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * f (ξ - η) i) =
      ∫ η, ((c ^ 3 : ℝ) : ℂ) * (f' (c • η) j *
        (2 * (π : ℂ) * Complex.I * (((c • ξ - c • η) j : ℝ) : ℂ) * f' (c • ξ - c • η) i)) := by
    refine integral_congr_ae ?_
    filter_upwards [hf, h2] with η e1 e2
    simp only [Function.comp_apply] at e2
    rw [e1, e2, smul_sub]
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  rw [e, integral_const_mul, key, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (by positivity), Complex.ofReal_one, one_mul]

theorem pressureSymbol_scale {f f' : Space → CSpace} {c : ℝ} (hc : 0 < c)
    (hf : f =ᵐ[volume] fun ξ => (c ^ 2) • f' (c • ξ)) (ξ : Space) :
    pressureSymbol f ξ = c • pressureSymbol f' (c • ξ) := by
  unfold pressureSymbol
  rw [advectionSymbol_scale hc hf ξ, Complex.real_smul]
  simp only [PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_of_nonneg hc.le]
  rcases eq_or_ne ‖ξ‖ 0 with h | h
  · simp [h]
  · push_cast
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hn : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
    field_simp
    rw [Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem homSob_dilX (k : ℕ) {μ : ℝ} (hμ : 0 < μ) (x : X) :
    homSob k (dilX μ x) = ENNReal.ofReal (μ ^ ((k : ℝ) + 1 / 2)) * homSob k x := by
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  unfold homSob
  rw [homNormSq_congr_ae k (symX_dilX_ae hμ x), homNormSq_comp_smul k _ (inv_pos.2 hs)]
  congr 2
  rw [Real.rpow_add hμ, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  set s := Real.sqrt μ with hs_def
  rw [show μ = s ^ 2 from (Real.sq_sqrt hμ.le).symm]
  simp only [inv_pow, inv_inv]
  field_simp
  ring

theorem symX_sub_ae (a b : X) :
    symX (a - b) =ᵐ[volume] fun ξ => symX a ξ - symX b ξ :=
  Lp.coeFn_sub (a : L2C) (b : L2C)

theorem tendsto_homSob_dilX (k : ℕ) {μ : ℝ} (hμ : 0 < μ) (x : X) (hx : homSob k x ≠ ⊤) :
    Tendsto (fun ν => homSob k (dilX ν x - dilX μ x)) (𝓝 μ) (𝓝 0) := by
  have hm : AEStronglyMeasurable (symX x) volume := Lp.aestronglyMeasurable _
  have hmem : MemLp (fun ξ => (‖ξ‖ ^ k : ℝ) • symX x ξ) 2 volume := by
    refine ⟨(by fun_prop : Continuous fun ξ : Space => ‖ξ‖ ^ k).aestronglyMeasurable.smul hm, ?_⟩
    unfold homSob at hx
    rw [homNormSq_eq_eLpNorm_sq] at hx
    exact lt_top_iff_ne_top.2 fun h => hx (by rw [h]; simp)
  obtain ⟨G, hG⟩ : ∃ G : L2C, G = hmem.toLp _ := ⟨_, rfl⟩
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ → L2C, Φ = fun ν =>
    (Real.sqrt ν ^ k) • Breakdown.Freq.Internal.DilationCont.scaleOp (Real.sqrt ν)⁻¹ G := ⟨_, rfl⟩
  have hΦ : ∀ ν, 0 < ν → (fun ξ => (‖ξ‖ ^ k : ℝ) • symX (dilX ν x) ξ) =ᵐ[volume] Φ ν := by
    intro ν hν
    have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
    have hc : 0 < (Real.sqrt ν)⁻¹ := inv_pos.2 hs
    have a1 := symX_dilX_ae hν x
    have a2 := Breakdown.Freq.Internal.DilationCont.scaleOp_realized fieldOpRealized_holds hc.ne' G
    have a3 := (Measure.quasiMeasurePreserving_smul (volume : Measure Space) hc.ne').ae_eq_comp
      (hmem.coeFn_toLp)
    have a4 := Lp.coeFn_smul (Real.sqrt ν ^ k)
      (Breakdown.Freq.Internal.DilationCont.scaleOp (Real.sqrt ν)⁻¹ G)
    filter_upwards [a1, a2, a3, a4] with ξ e1 e2 e3 e4
    simp only [Function.comp_apply] at e3
    rw [← hG] at e3
    rw [hΦdef, e4, Pi.smul_apply, e2, e3, e1, smul_smul, smul_smul, smul_smul]
    congr 1
    rw [norm_smul, Real.norm_of_nonneg hc.le, mul_pow]
    field_simp
    rw [mul_assoc, ← mul_pow, mul_one_div_cancel hs.ne', one_pow, mul_one]
  have hcont : Tendsto Φ (𝓝 μ) (𝓝 (Φ μ)) := by
    have hsq : ContinuousAt (fun ν : ℝ => (Real.sqrt ν)⁻¹) μ :=
      Real.continuous_sqrt.continuousAt.inv₀ (Real.sqrt_pos.2 hμ).ne'
    have h1 := (Breakdown.Freq.Internal.DilationCont.tendsto_scaleOp fieldOpRealized_holds
      (inv_pos.2 (Real.sqrt_pos.2 hμ)) G).comp hsq
    have h2 : Tendsto (fun ν : ℝ => Real.sqrt ν ^ k) (𝓝 μ) (𝓝 (Real.sqrt μ ^ k)) :=
      (Real.continuous_sqrt.pow k).tendsto μ
    rw [hΦdef]
    exact h2.smul h1
  have heq : (fun ν => eLpNorm (⇑(Φ ν) - ⇑(Φ μ)) 2 volume ^ 2) =ᶠ[𝓝 μ]
      fun ν => homSob k (dilX ν x - dilX μ x) := by
    filter_upwards [Ioi_mem_nhds hμ] with ν hν
    have hsub := symX_sub_ae (dilX ν x) (dilX μ x)
    have hae : (⇑(Φ ν) - ⇑(Φ μ) : Space → CSpace) =ᵐ[volume]
        fun ξ => (‖ξ‖ ^ k : ℝ) • symX (dilX ν x - dilX μ x) ξ := by
      filter_upwards [hsub, hΦ ν hν, hΦ μ hμ] with ξ e0 e1 e2
      beta_reduce at e1 e2
      rw [Pi.sub_apply, e0, smul_sub]
      exact congrArg₂ (fun a b => a - b) e1.symm e2.symm
    rw [show homSob k (dilX ν x - dilX μ x) = homNormSq k (symX (dilX ν x - dilX μ x)) from rfl,
      homNormSq_eq_eLpNorm_sq, eLpNorm_congr_ae hae]
  refine Tendsto.congr' heq ?_
  have h0 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' Φ (Φ μ)).1 hcont
  have h3 := ((ENNReal.continuous_pow 2).tendsto 0).comp h0
  rw [show (0 : ℝ≥0∞) ^ 2 = 0 by norm_num] at h3
  exact h3

theorem physField_dilX {μ : ℝ} (hμ : 0 < μ) (x : X) (y : Space) :
    physField (velSymbol (dilX μ x)) y =
      Real.sqrt μ • physField (velSymbol x) (Real.sqrt μ • y) := by
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hc : 0 < (Real.sqrt μ)⁻¹ := inv_pos.2 hs
  unfold physField
  rw [Real.fourierInv_congr_ae (velSymbol_dilX_ae hμ x), fourierInv_real_smul,
    fourierInv_comp_smul _ hc, inv_inv, smul_smul, map_smul]
  congr 1
  field_simp

theorem physScalar_dilX {μ : ℝ} (hμ : 0 < μ) (x : X) (y : Space) :
    physScalar (pressureSymbol (velSymbol (dilX μ x))) y =
      μ * physScalar (pressureSymbol (velSymbol x)) (Real.sqrt μ • y) := by
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hc : 0 < (Real.sqrt μ)⁻¹ := inv_pos.2 hs
  have hp : pressureSymbol (velSymbol (dilX μ x)) =
      fun ξ => (Real.sqrt μ)⁻¹ • pressureSymbol (velSymbol x) ((Real.sqrt μ)⁻¹ • ξ) :=
    funext (pressureSymbol_scale hc (velSymbol_dilX_ae hμ x))
  unfold physScalar
  rw [hp, fourierInv_real_smul, fourierInv_comp_smul _ hc, inv_inv, smul_smul, Complex.smul_re]
  congr 1
  set s := Real.sqrt μ with hs_def
  rw [show μ = s ^ 2 from (Real.sq_sqrt hμ.le).symm]
  field_simp

end Internal.SymbolDilation

open Internal.SymbolDilation in
theorem dilateSymbol_holds : DilateSymbol := by
  intro μ hμ x
  refine ⟨fun k => homSob_dilX k hμ x, fun k => ?_, fun _ y => physField_dilX hμ x y,
    fun _ y => physScalar_dilX hμ x y⟩
  by_cases h : homSob k x = ⊤
  · exact Or.inr h
  · exact Or.inl (tendsto_homSob_dilX k hμ x h)

end Breakdown.FarField
