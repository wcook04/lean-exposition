import Breakdown.Frac.StRealize
import Breakdown.Frac.OpExports
import Breakdown.Frac.NNiceEmbed
import Breakdown.FreqTr.NiceApprox

open MeasureTheory Set Real Metric
open scoped ENNReal ContDiff SchwartzMap FourierTransform

noncomputable section

namespace Breakdown.FracInternal.NiceField

open Freq Freq.Internal.NiceApprox Freq.FracInternal.NiceEmbed

def symbolS {m : Space → CSpace} (hm : IsNiceSymbol m) : 𝓢(Space, CSpace) :=
  hm.2.1.toSchwartzMap hm.1

theorem symbolS_coe {m : Space → CSpace} (hm : IsNiceSymbol m) : ⇑(symbolS hm) = m := rfl

def fieldS {m : Space → CSpace} (hm : IsNiceSymbol m) : 𝓢(Space, Space) :=
  SchwartzMap.postcompCLM realVec (𝓕⁻ (symbolS hm))

theorem fieldS_coe {m : Space → CSpace} (hm : IsNiceSymbol m) : ⇑(fieldS hm) = niceField m := by
  funext x
  rw [fieldS, SchwartzMap.postcompCLM_apply, SchwartzMap.fourierInv_coe]
  rfl

theorem complexify_fieldS {m : Space → CSpace} (hm : IsNiceSymbol m) (x : Space) :
    complexifyVec (fieldS hm x) = (𝓕⁻ (symbolS hm)) x := by
  rw [fieldS, SchwartzMap.postcompCLM_apply]
  exact complexify_realVec_of_conj (freqTrInv_conj _ hm.2.2.2.1 x)

theorem transform_fieldS {m : Space → CSpace} (hm : IsNiceSymbol m) :
    𝓕 (fun x => complexifyVec (fieldS hm x)) = m := by
  have e : (fun x => complexifyVec (fieldS hm x)) = ⇑(𝓕⁻ (symbolS hm) : 𝓢(Space, CSpace)) :=
    funext (complexify_fieldS hm)
  rw [e, ← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  rfl

theorem eq_niceField_of_transform {f : Space → Space} (hc : Continuous f) (hi : Integrable f)
    {n : Space → CSpace} (hn : IsNiceSymbol n) (hF : 𝓕 (fun x => complexifyVec (f x)) = n) :
    f = niceField n := by
  have hint : Integrable (𝓕 (fun x => complexifyVec (f x))) := by
    rw [hF, ← symbolS_coe hn]
    exact (symbolS hn).integrable
  have h : 𝓕⁻ (𝓕 (fun x => complexifyVec (f x))) = fun x => complexifyVec (f x) :=
    Continuous.fourierInv_fourier_eq (complexifyVec.continuous.comp hc)
      (complexifyVec.integrable_comp hi) hint
  funext x
  have hx := congrFun h x
  rw [hF] at hx
  rw [niceField, hx]
  exact (realVec_complexifyVec_eq (f x)).symm

theorem kernel_smul_norm (α : ℝ) (v z : Space) :
    ‖‖z‖ ^ (-(3 + 2 * α)) • v‖ = ‖z‖ ^ (-(3 + 2 * α)) * ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

theorem integrable_fracPower (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) (G : 𝓢(Space, Space)) :
    Integrable (fractionalPowerAt α G) := by
  have h := remainderProductIntegrable α hα hα2 G
  have hK : Measurable (fun p : Space × Space => ‖p.2‖ ^ (-(3 + 2 * α))) :=
    (measurable_norm.comp measurable_snd).pow_const _
  have hF : Integrable
      (fun p : Space × Space => ‖p.2‖ ^ (-(3 + 2 * α)) • secondOrderRemainder G p.1 p.2)
      (volume.prod volume) :=
    h.mono' (hK.aestronglyMeasurable.smul (continuous_remainder G).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => (kernel_smul_norm α _ _).le)
  exact hF.integral_prod_left.smul ((fractionalNormalizer α)⁻¹)

theorem remainder_far_bound (f : Space → Space) (x z : Space) (hz : 1 ≤ ‖z‖) :
    ‖secondOrderRemainder f x z‖ ≤
      ‖f (x + z)‖ + (‖f x‖ + ‖fderiv ℝ f x‖ + ‖iteratedFDeriv ℝ 2 f x‖) * ‖z‖ ^ 2 := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have h1 : ‖z‖ ≤ ‖z‖ ^ 2 := by nlinarith
  have h2 : (1 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith
  have hD : ‖fderiv ℝ f x z‖ ≤ ‖fderiv ℝ f x‖ * ‖z‖ := (fderiv ℝ f x).le_opNorm z
  have hD2 : ‖iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ‖z‖ ^ 2 := by
    have := (iteratedFDeriv ℝ 2 f x).le_opNorm ![z, z]
    simpa [Fin.prod_univ_two, sq] using this
  have hs : ‖(1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 f x ![z, z]‖ := by
    rw [norm_smul]
    have := norm_nonneg (iteratedFDeriv ℝ 2 f x ![z, z])
    norm_num
    nlinarith
  unfold secondOrderRemainder
  have n1 := norm_sub_le (f (x + z) - f x - fderiv ℝ f x z)
    ((1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z])
  have n2 := norm_sub_le (f (x + z) - f x) (fderiv ℝ f x z)
  have n3 := norm_sub_le (f (x + z)) (f x)
  have p1 : ‖f x‖ ≤ ‖f x‖ * ‖z‖ ^ 2 := le_mul_of_one_le_right (norm_nonneg _) h2
  have p2 : ‖fderiv ℝ f x‖ * ‖z‖ ≤ ‖fderiv ℝ f x‖ * ‖z‖ ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  nlinarith

theorem continuous_fracPower (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) (G : 𝓢(Space, Space)) :
    Continuous (fractionalPowerAt α G) := by
  have hb : ∀ n y, ‖iteratedFDeriv ℝ n G y‖ ≤ SchwartzMap.seminorm ℝ 0 n G :=
    fun n y => SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ G n y
  have b0 : ∀ y, ‖G y‖ ≤ SchwartzMap.seminorm ℝ 0 0 G := fun y => by
    have := hb 0 y
    rwa [norm_iteratedFDeriv_zero] at this
  have b1 : ∀ y, ‖fderiv ℝ G y‖ ≤ SchwartzMap.seminorm ℝ 0 1 G := fun y => by
    rw [← norm_iteratedFDeriv_one]
    exact hb 1 y
  have hS0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 G := (norm_nonneg _).trans (b0 0)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = SchwartzMap.seminorm ℝ 0 3 G := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * SchwartzMap.seminorm ℝ 0 0 G + SchwartzMap.seminorm ℝ 0 1 G +
    SchwartzMap.seminorm ℝ 0 2 G := ⟨_, rfl⟩
  have hK : Measurable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α))) := measurable_norm.pow_const _
  obtain ⟨bound, hbound⟩ : ∃ f : Space → ℝ,
      f = (ball (0 : Space) 1).indicator (fun z => A * ‖z‖ ^ (-(2 * α))) +
        (ball (0 : Space) 1)ᶜ.indicator (fun z => B * ‖z‖ ^ (-(1 + 2 * α))) := ⟨_, rfl⟩
  have hbi : Integrable bound := by
    rw [hbound]
    refine Integrable.add ?_ ?_
    · have h1 : IntegrableOn (fun z : Space => A * ‖z‖ ^ (-(2 * α))) (ball (0 : Space) 1) :=
        (integrableOn_ball_norm_rpow (s := -(2 * α)) (by linarith)).const_mul A
      exact h1.integrable_indicator measurableSet_ball
    · have h1 : IntegrableOn (fun z : Space => B * ‖z‖ ^ (-(1 + 2 * α))) (ball (0 : Space) 1)ᶜ :=
        (integrableOn_compl_ball_norm_rpow (s := -(1 + 2 * α)) (by linarith)).const_mul B
      exact h1.integrable_indicator measurableSet_ball.compl
  have hcont : ∀ z : Space,
      Continuous (fun x => ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder G x z) := fun z => by
    have h1 : Continuous (fun x => secondOrderRemainder G x z) := by
      have d1 : Continuous (fun x => fderiv ℝ G x) := (G.smooth 1).continuous_fderiv (by simp)
      have d2 : Continuous (fun x => iteratedFDeriv ℝ 2 G x) :=
        (G.smooth 2).continuous_iteratedFDeriv le_rfl
      unfold secondOrderRemainder
      fun_prop
    exact h1.const_smul (‖z‖ ^ (-(3 + 2 * α)))
  have hmeas : ∀ x : Space, AEStronglyMeasurable
      (fun z => ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder G x z) volume := fun x => by
    have h1 : Continuous (fun z => secondOrderRemainder G x z) := by
      unfold secondOrderRemainder
      fun_prop
    exact hK.aestronglyMeasurable.smul h1.aestronglyMeasurable
  have hbd : ∀ x z : Space, ‖‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder G x z‖ ≤ bound z := by
    intro x z
    rw [kernel_smul_norm]
    by_cases hz : z ∈ ball (0 : Space) 1
    · have hz' : z ∉ (ball (0 : Space) 1)ᶜ := fun h => h hz
      simp only [hbound, Pi.add_apply, Set.indicator_of_mem hz, Set.indicator_of_notMem hz', add_zero]
      have hR := remainderBound G (G.smooth 3) x z A (fun y _ => hA ▸ hb 3 y)
      rcases eq_or_ne z 0 with rfl | hz0
      · rw [norm_zero, Real.zero_rpow (by linarith : -(3 + 2 * α) ≠ 0),
          Real.zero_rpow (by linarith : -(2 * α) ≠ 0)]
        simp
      · have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
        calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder G x z‖
            ≤ ‖z‖ ^ (-(3 + 2 * α)) * (A * ‖z‖ ^ 3) :=
              mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg hpos.le _)
          _ = A * ‖z‖ ^ (-(2 * α)) := by
              rw [show -(2 * α) = -(3 + 2 * α) + ((3 : ℕ) : ℝ) by push_cast; ring,
                Real.rpow_add hpos, Real.rpow_natCast]
              ring
    · have hz' : z ∈ (ball (0 : Space) 1)ᶜ := hz
      simp only [hbound, Pi.add_apply, Set.indicator_of_mem hz', Set.indicator_of_notMem hz, zero_add]
      have hz1 : 1 ≤ ‖z‖ := by simpa using hz
      have hpos : 0 < ‖z‖ := by linarith
      have h2 : (1 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith
      have hf := remainder_far_bound G x z hz1
      have e1 : (‖G x‖ + ‖fderiv ℝ G x‖ + ‖iteratedFDeriv ℝ 2 G x‖) * ‖z‖ ^ 2 ≤
          (SchwartzMap.seminorm ℝ 0 0 G + SchwartzMap.seminorm ℝ 0 1 G +
            SchwartzMap.seminorm ℝ 0 2 G) * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [b0 x, b1 x, hb 2 x]) (by positivity)
      have e2 : SchwartzMap.seminorm ℝ 0 0 G ≤ SchwartzMap.seminorm ℝ 0 0 G * ‖z‖ ^ 2 :=
        le_mul_of_one_le_right hS0 h2
      have hfar : ‖secondOrderRemainder G x z‖ ≤ B * ‖z‖ ^ 2 := by
        rw [hB]
        nlinarith [b0 (x + z)]
      calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder G x z‖
          ≤ ‖z‖ ^ (-(3 + 2 * α)) * (B * ‖z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hfar (Real.rpow_nonneg hpos.le _)
        _ = B * ‖z‖ ^ (-(1 + 2 * α)) := by
            rw [show -(1 + 2 * α) = -(3 + 2 * α) + ((2 : ℕ) : ℝ) by push_cast; ring,
              Real.rpow_add hpos, Real.rpow_natCast]
            ring
  have hc := continuous_of_dominated hmeas (fun x => Filter.Eventually.of_forall (hbd x)) hbi
    (Filter.Eventually.of_forall hcont)
  exact hc.const_smul ((fractionalNormalizer α)⁻¹)

theorem transform_clm_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : CSpace →L[ℂ] F) (f : 𝓢(Space, CSpace)) (ξ : Space) :
    𝓕 (fun x => L (f x)) ξ = L (𝓕 (⇑f) ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have hi : Integrable (fun v : Space => 𝐞 (-inner ℝ v ξ) • f v) volume :=
    (Real.fourierIntegral_convergent_iff ξ).2 f.integrable
  rw [← L.integral_comp_comm hi]
  congr 1
  funext v
  rw [Circle.smul_def, Circle.smul_def, map_smul]

theorem divergence_fieldS {m : Space → CSpace} (hm : IsNiceSymbol m) (y : Space) :
    divergenceAt (fieldS hm) y = 0 := by
  set Ac : 𝓢(Space, CSpace) := 𝓕⁻ (symbolS hm) with hAc
  have hG : ⇑(fieldS hm) = fun x => realVec (Ac x) :=
    funext fun x => SchwartzMap.postcompCLM_apply _ _ _
  set S : 𝓢(Space, ℂ) := ∑ j : Fin 3, SchwartzMap.postcompCLM (EuclideanSpace.proj j : CSpace →L[ℂ] ℂ)
    (LineDeriv.lineDerivOp (unitVector j) Ac) with hSdef
  have hSy : ∀ x, S x = ∑ j : Fin 3, (pd (unitVector j) ⇑Ac x) j := by
    intro x
    simp only [hSdef, Fin.sum_univ_three, add_apply, SchwartzMap.postcompCLM_apply]
    rfl
  have hF : ∀ ξ, (𝓕 S) ξ = 0 := by
    intro ξ
    have hj : ∀ j : Fin 3, (𝓕 (SchwartzMap.postcompCLM (EuclideanSpace.proj j : CSpace →L[ℂ] ℂ)
        (LineDeriv.lineDerivOp (unitVector j) Ac))) ξ =
        (2 * π * Complex.I) * (((ξ j : ℝ) : ℂ) * m ξ j) := by
      intro j
      rw [SchwartzMap.fourier_coe]
      have e : ⇑(SchwartzMap.postcompCLM (EuclideanSpace.proj j : CSpace →L[ℂ] ℂ)
          (LineDeriv.lineDerivOp (unitVector j) Ac)) =
          fun x => (EuclideanSpace.proj j : CSpace →L[ℂ] ℂ)
            ((LineDeriv.lineDerivOp (unitVector j) Ac) x) :=
        funext fun x => SchwartzMap.postcompCLM_apply _ _ _
      rw [e, transform_clm_apply, ← SchwartzMap.fourier_coe, freqTr_lineDeriv_apply, hAc,
        FourierTransform.fourier_fourierInv_eq, symbolS_coe]
      simp [Complex.real_smul]
    rw [← SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ)]
    simp only [hSdef, Fin.sum_univ_three, map_add, add_apply,
      SchwartzMap.fourierTransformCLM_apply, hj]
    have hd := hm.2.2.2.2 ξ
    rw [Fin.sum_univ_three] at hd
    linear_combination (2 * π * Complex.I) * hd
  have hS0 : S y = 0 := by
    have hinv : (𝓕⁻ (𝓕 S : 𝓢(Space, ℂ)) : 𝓢(Space, ℂ)) = S := FourierTransform.fourierInv_fourier_eq S
    rw [← hinv, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
    simp only [hF, smul_zero, integral_zero]
  rw [divergence_eq_sum, hG]
  have hp : ∀ j : Fin 3, pd (unitVector j) (fun x => realVec (Ac x)) y =
      realVec (pd (unitVector j) ⇑Ac y) := fun j =>
    congrFun (pd_clm realVec Ac.differentiable _) y
  simp only [hp]
  have e : ∑ j : Fin 3, (realVec (pd (unitVector j) ⇑Ac y)) j = (S y).re := by
    rw [hSy, Complex.re_sum]
    rfl
  rw [e, hS0, Complex.zero_re]

end Breakdown.FracInternal.NiceField

namespace Breakdown.Freq

open Breakdown.FracInternal.NiceField Freq.FracInternal.NiceEmbed Freq.Internal.NiceApprox

theorem fracPower_niceField (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) (m : Space → CSpace)
    (hm : IsNiceSymbol m) :
    fractionalPowerAt α (niceField m) =
      niceField (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • m ξ) := by
  rw [← fieldS_coe hm]
  refine eq_niceField_of_transform (continuous_fracPower α hα hα2 (fieldS hm))
    (integrable_fracPower α hα hα2 (fieldS hm)) (isNiceSymbol_frac α hm) ?_
  funext ξ
  rw [symbol α hα hα2 (fieldS hm) ξ, transform_fieldS hm, Complex.coe_smul]

theorem niceFieldProps (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) : NiceFieldProps α := by
  rintro φ ⟨m, hm, rfl⟩
  refine ⟨⟨fieldS hm, fieldS_coe hm⟩, ?_, ⟨_, isNiceSymbol_traceSecondDeriv hm, negTraceSecondDeriv_niceField hm⟩,
    ⟨_, isNiceSymbol_frac α hm, fracPower_niceField α hα hα2 m hm⟩, ?_⟩
  · rw [← fieldS_coe hm]
    refine isDecayField_rapid _ (divergence_fieldS hm)
  · rw [negTraceSecondDeriv_niceField hm, fracPower_niceField α hα hα2 _ (isNiceSymbol_traceSecondDeriv hm),
      fracPower_niceField α hα hα2 m hm, negTraceSecondDeriv_niceField (isNiceSymbol_frac α hm)]
    congr 1
    funext ξ
    rw [smul_smul, smul_smul, mul_comm]

end Breakdown.Freq
