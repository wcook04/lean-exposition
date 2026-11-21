import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

open FourierTransform SchwartzMap

private theorem integral_smul_freqTrL2_eq (g : Space → CSpace) (h1 : MemLp g 1 volume) (h2 : MemLp g 2 volume)
    (θ : 𝓢(Space, ℂ)) :
    ∫ x, θ x • (freqTrL2 (toLpOrZero 2 g) : Space → CSpace) x = ∫ x, θ x • 𝓕 g x := by
  have e1 : (toLpOrZero 2 g) = h2.toLp g := by simp [toLpOrZero, h2]
  have key := congrArg (fun T : 𝓢'(Space, CSpace) => T θ)
    (Lp.fourier_toTemperedDistribution_eq (toLpOrZero 2 g))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at key
  change _ = ∫ x, θ x • ((freqTrL2 (toLpOrZero 2 g) : L2C) : Space → CSpace) x at key
  rw [← key, e1]
  have hae := h2.coeFn_toLp
  refine (integral_congr_ae (g := fun x => (𝓕 θ) x • g x) (hae.mono fun x hx => by simp only [hx])).trans ?_
  rw [fourier_coe]
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ Space) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner θ.integrable (memLp_one_iff_integrable.mp h1)
  simp only [flip_innerₗ] at this
  exact this

private theorem integral_smul_freqTrL2_symm_eq (g : Space → CSpace) (h1 : MemLp g 1 volume) (h2 : MemLp g 2 volume)
    (θ : 𝓢(Space, ℂ)) :
    ∫ x, θ x • (freqTrL2.symm (toLpOrZero 2 g) : Space → CSpace) x = ∫ x, θ x • 𝓕⁻ g x := by
  have e1 : (toLpOrZero 2 g) = h2.toLp g := by simp [toLpOrZero, h2]
  have key := congrArg (fun T : 𝓢'(Space, CSpace) => T θ)
    (Lp.fourierInv_toTemperedDistribution_eq (toLpOrZero 2 g))
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at key
  change _ = ∫ x, θ x • ((freqTrL2.symm (toLpOrZero 2 g) : L2C) : Space → CSpace) x at key
  rw [← key, e1]
  have hae := h2.coeFn_toLp
  refine (integral_congr_ae (g := fun x => (𝓕⁻ θ) x • g x) (hae.mono fun x hx => by simp only [hx])).trans ?_
  rw [fourierInv_coe]
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ Space) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner.neg θ.integrable (memLp_one_iff_integrable.mp h1)
  have hfl : (-innerₗ Space : Space →ₗ[ℝ] Space →ₗ[ℝ] ℝ).flip = -innerₗ Space := by
    ext x y
    simp [real_inner_comm]
  rw [hfl] at this
  exact this

private theorem freqTrL2_ae_eq (g : Space → CSpace) (h1 : MemLp g 1 volume) (h2 : MemLp g 2 volume) :
    (freqTrL2 (toLpOrZero 2 g) : Space → CSpace) =ᵐ[volume] 𝓕 g := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp _).locallyIntegrable (by norm_num)
  · exact (VectorFourier.fourierIntegral_continuous (L := innerₗ Space) (μ := volume)
      Real.continuous_fourierChar continuous_inner (memLp_one_iff_integrable.mp h1)).locallyIntegrable
  · intro φ hφ hφc
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
    have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
    have := integral_smul_freqTrL2_eq g h1 h2 (hg₁.toSchwartzMap hg₂)
    simpa [Complex.coe_smul] using this

private theorem freqTrL2_symm_ae_eq (g : Space → CSpace) (h1 : MemLp g 1 volume)
    (h2 : MemLp g 2 volume) :
    (freqTrL2.symm (toLpOrZero 2 g) : Space → CSpace) =ᵐ[volume] 𝓕⁻ g := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp _).locallyIntegrable (by norm_num)
  · exact (VectorFourier.fourierIntegral_continuous (L := -innerₗ Space) (μ := volume)
      Real.continuous_fourierChar continuous_inner.neg (memLp_one_iff_integrable.mp h1)).locallyIntegrable
  · intro φ hφ hφc
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
    have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
    have := integral_smul_freqTrL2_symm_eq g h1 h2 (hg₁.toSchwartzMap hg₂)
    simpa [Complex.coe_smul] using this

theorem freqTrL1L2 :
    FreqTrL1L2 ∧ FreqTrInvL1L2 :=
  ⟨freqTrL2_ae_eq, freqTrL2_symm_ae_eq⟩

end Breakdown.Freq
