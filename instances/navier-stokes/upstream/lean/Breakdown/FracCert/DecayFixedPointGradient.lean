import Breakdown.FracCert.DecayFixedPointParts
import Breakdown.FracCert.WeakRegular
import Breakdown.FracCert.WeakSymbolL1
import Breakdown.Uniqueness.RegPhysAuxProductPart2
import Breakdown.Uniqueness.RegPhysAuxDeriv
import Breakdown.FreqTr.NiceApprox

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform SchwartzMap ComplexConjugate

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

namespace DecayGradientInternal

theorem pair_scalar {a b : Space → ℂ} (ha : Integrable a) (hb : Integrable b) :
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

theorem continuous_inverseTransform_of {a : Space → ℂ} (ha : Integrable a) : Continuous (𝓕⁻ a) := by
  have : 𝓕⁻ a = VectorFourier.fourierIntegral 𝐞 volume
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ a :=
    funext fun y => SmoothFlow.Internal.freqTrInv_eq_integral a y
  rw [this]
  exact VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by apply (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).continuous₂ :
      Continuous (fun p : Space × Space =>
        (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ p.1 p.2)) ha

theorem norm_inverseTransform_le_of (a : Space → ℂ) (x : Space) : ‖𝓕⁻ a x‖ ≤ ∫ ξ, ‖a ξ‖ := by
  rw [SmoothFlow.Internal.freqTrInv_eq_integral]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

end DecayGradientInternal

open DecayGradientInternal in
theorem profileGradientFree : ProfileGradientFreeStatement := by
  intro U hM q hqh hqs hqc _ hqf
  obtain ⟨c, hc⟩ := hqf
  have hw := WeakRegularInternal.moments_clean U (symbolL1OfMoments U hM).1
  set h := WeakRegularInternal.cleanSymbol (symbolX U) with hdef
  have hmeas : AEStronglyMeasurable h volume :=
    (WeakRegularInternal.aesm_symbolX U).congr
      (WeakRegularInternal.cleanSymbol_ae (WeakRegularInternal.goodSet_ae U)).symm
  have hI : Integrable h := by
    have h0 := hw 0
    simp only [pow_zero, one_mul] at h0
    exact (integrable_norm_iff hmeas).1 h0
  have hdiv := WeakRegularInternal.cleanSymbol_div (symbolX U)
  let M := hqc.toSchwartzMap hqs
  have hMq : ⇑M = q := rfl
  have hreal : ∀ y, conjVec ((𝓕⁻ M) y) = (𝓕⁻ M) y :=
    Internal.NiceApprox.freqTrInv_conj M (fun ξ => hqh ξ)
  have eq' : physField q = fun y => realVec ((𝓕⁻ M) y) := WeakRegularInternal.physField_of_rapid M rfl
  show ∫ y, inner ℝ (physField (symbolX U) y) (physField q y) = 0
  rw [← WeakRegularInternal.physField_clean U, eq']
  have hMi : Integrable q := by rw [← hMq]; exact M.integrable
  have hqi : ∀ i : Fin 3, Integrable (fun ξ => q ξ i) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℂ) i).integrable_comp hMi
  have hhi : ∀ i : Fin 3, Integrable (fun ξ => h ξ i) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℂ) i).integrable_comp hI
  have eB : ∀ y i, ((𝓕⁻ M) y) i = 𝓕⁻ (fun ξ => q ξ i) y := fun y i => by
    rw [SchwartzMap.fourierInv_coe, hMq]
    exact SmoothFlow.Internal.ConvProduct.freqTrInv_apply_eq hMi y i
  have eA : ∀ y i, (𝓕⁻ h y) i = 𝓕⁻ (fun ξ => h ξ i) y := fun y i =>
    SmoothFlow.Internal.ConvProduct.freqTrInv_apply_eq hI y i
  have hBi : ∀ i : Fin 3, Integrable (fun y => 𝓕⁻ (fun ξ => q ξ i) y) := fun i => by
    have := (EuclideanSpace.proj (𝕜 := ℂ) i).integrable_comp ((𝓕⁻ M).integrable (μ := volume))
    refine this.congr (ae_of_all _ fun y => ?_)
    exact eB y i
  have hpt : ∀ y, inner ℝ (physField h y) (realVec ((𝓕⁻ M) y)) =
      (∑ i : Fin 3, 𝓕⁻ (fun ξ => h ξ i) y * 𝓕⁻ (fun ξ => q ξ i) y).re := by
    intro y
    rw [physField, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have him : (((𝓕⁻ M) y) i).im = 0 := by
      have e : star (((𝓕⁻ M) y) i) = ((𝓕⁻ M) y) i := congrArg (fun w : CSpace => w i) (hreal y)
      exact Complex.conj_eq_iff_im.1 e
    rw [← eA, ← eB, Complex.mul_re, him, mul_zero, sub_zero]
    have er : ∀ z : CSpace, realVec z i = (z i).re := fun z => rfl
    rw [er, er, RCLike.inner_apply, conj_trivial, mul_comm]
  refine (integral_congr_ae (ae_of_all _ fun y => hpt y)).trans ?_
  have hAB : ∀ i : Fin 3, Integrable (fun y => 𝓕⁻ (fun ξ => h ξ i) y * 𝓕⁻ (fun ξ => q ξ i) y) := by
    intro i
    exact (hBi i).bdd_mul (c := ∫ ξ, ‖h ξ i‖) (continuous_inverseTransform_of (hhi i)).aestronglyMeasurable
      (ae_of_all _ fun y => norm_inverseTransform_le_of _ y)
  show ∫ y, RCLike.re (∑ i : Fin 3, 𝓕⁻ (fun ξ => h ξ i) y * 𝓕⁻ (fun ξ => q ξ i) y) = 0
  rw [integral_re (integrable_finsetSum _ fun i _ => hAB i), integral_finsetSum _ fun i _ => hAB i]
  have hinv : ∀ (i : Fin 3) (ξ : Space), 𝓕⁻ (𝓕⁻ (fun ζ => q ζ i)) ξ = q (-ξ) i := by
    intro i ξ
    rw [Real.fourierInv_eq_fourier_neg]
    have hcont : Continuous (fun ζ => q ζ i) := (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp hqs.continuous
    have hFi : Integrable (𝓕 (fun ζ => q ζ i)) := by
      refine ((hBi i).comp_neg).congr (ae_of_all _ fun x => ?_)
      show 𝓕⁻ (fun ζ => q ζ i) (-x) = 𝓕 (fun ζ => q ζ i) x
      rw [Real.fourierInv_eq_fourier_neg, neg_neg]
    exact congrFun (hcont.fourier_fourierInv_eq (hqi i) hFi) (-ξ)
  have hpair : ∀ i : Fin 3, ∫ y, 𝓕⁻ (fun ξ => h ξ i) y * 𝓕⁻ (fun ξ => q ξ i) y =
      ∫ ξ, h ξ i * q (-ξ) i := by
    intro i
    rw [pair_scalar (hhi i) (hBi i)]
    simp_rw [hinv]
  simp_rw [hpair]
  obtain ⟨Cq, hCq⟩ : ∃ C, ∀ ξ, ‖q (-ξ)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hqs.continuous.bounded_above_of_compact_support hqc
    exact ⟨C, fun ξ => hC (-ξ)⟩
  have hHQ : ∀ i : Fin 3, Integrable (fun ξ => h ξ i * q (-ξ) i) := by
    intro i
    refine (hhi i).mul_bdd (c := Cq) ?_ (ae_of_all _ fun ξ => (PiLp.norm_apply_le _ _).trans (hCq ξ))
    exact ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp (hqs.continuous.comp continuous_neg)).aestronglyMeasurable
  rw [← integral_finsetSum _ fun i _ => hHQ i]
  have hz : ∀ ξ, ∑ i : Fin 3, h ξ i * q (-ξ) i = 0 := by
    intro ξ
    have e : ∀ i : Fin 3, h ξ i * q (-ξ) i = -(c (-ξ) * (((ξ i : ℝ) : ℂ) * h ξ i)) := by
      intro i
      rw [hc]
      simp [freqVec, complexifyVec]
      ring
    simp_rw [e]
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hdiv ξ, mul_zero, neg_zero]
  simp_rw [hz]
  simp

end Breakdown.FracCert
