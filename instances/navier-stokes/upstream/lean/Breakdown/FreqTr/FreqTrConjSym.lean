import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform RealInnerProductSpace

noncomputable section

namespace Breakdown.Freq

namespace Internal.FreqTrConjSym

theorem conjVec_freqTr_neg (f : Space → Space) (hf : Integrable f) (ξ : Space) :
    conjVec (𝓕 (fun x => complexifyVec (f x)) (-ξ)) = 𝓕 (fun x => complexifyVec (f x)) ξ := by
  have hi : Integrable (fun v : Space => 𝐞 (-⟪v, -ξ⟫) • complexifyVec (f v)) := by
    rw [Real.fourierIntegral_convergent_iff]
    exact complexifyVec.integrable_comp hf
  rw [Real.fourier_eq, Real.fourier_eq, ← conjVec.integral_comp_comm hi]
  congr 1
  ext v i
  simp [conjVec, complexifyVec, Circle.smul_def, Real.fourierChar_apply]
  left
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  exact Or.inl (map_ofNat _ 2)

theorem reflConj_ae (h1 : FieldOpRealized) (f : L2C) :
    (reflConj f : Space → CSpace) =ᵐ[volume] fun ξ => conjVec (f (-ξ)) :=
  h1 (ContinuousLinearEquiv.neg ℝ) (fun _ => conjVec) ‖conjVec‖ aestronglyMeasurable_const
    (fun _ => le_rfl) f

theorem complexify_toLp (φ : SchwartzMap Space Space) :
    complexify (φ.toLp 2) = (SchwartzMap.postcompCLM (𝕜 := ℝ) complexifyVec φ).toLp 2 := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec (φ.toLp 2),
    φ.coeFn_toLp 2 volume, (SchwartzMap.postcompCLM (𝕜 := ℝ) complexifyVec φ).coeFn_toLp 2 volume]
    with x hx1 hx2 hx3
  rw [complexify, hx1, hx3, hx2, SchwartzMap.postcompCLM_apply]

theorem freqTrR_toLp (ψ : SchwartzMap Space CSpace) : freqTrR (ψ.toLp 2) = (𝓕 ψ).toLp 2 :=
  SchwartzMap.toLp_fourier_eq ψ

theorem reflConj_freqTr_rapid (h1 : FieldOpRealized) (φ : SchwartzMap Space Space) :
    reflConj (freqTrR (complexify (φ.toLp 2))) = freqTrR (complexify (φ.toLp 2)) := by
  rw [complexify_toLp, freqTrR_toLp]
  set ψ := SchwartzMap.postcompCLM (𝕜 := ℝ) complexifyVec φ
  apply Lp.ext
  have hneg : (((𝓕 ψ).toLp 2 : L2C) : Space → CSpace) ∘ (fun ξ => -ξ) =ᵐ[volume]
      ((𝓕 ψ : SchwartzMap Space CSpace) : Space → CSpace) ∘ (fun ξ => -ξ) :=
    ((𝓕 ψ).coeFn_toLp 2 volume).comp_tendsto
      (Measure.measurePreserving_neg volume).quasiMeasurePreserving.tendsto_ae
  filter_upwards [reflConj_ae h1 ((𝓕 ψ).toLp 2), hneg, (𝓕 ψ).coeFn_toLp 2 volume] with ξ ha hb hc
  rw [ha, hc]
  simp only [Function.comp] at hb
  rw [hb, SchwartzMap.fourier_coe]
  have hψ : (ψ : Space → CSpace) = fun x => complexifyVec (φ x) :=
    funext fun x => SchwartzMap.postcompCLM_apply _ _ _
  rw [hψ]
  exact conjVec_freqTr_neg φ (φ.integrable) ξ

end Internal.FreqTrConjSym

theorem freqTrConjSym (h1 : FieldOpRealized) :
    FreqTrConjSym := by
  intro g
  have hd := SchwartzMap.denseRange_toLpCLM (E := Space) (F := Space) (p := 2) (μ := volume)
    ENNReal.ofNat_ne_top
  have heq := hd.equalizer (g := fun g => reflConj (freqTrR (complexify g)))
    (h := fun g => freqTrR (complexify g)) (reflConj.comp (freqTrR.comp complexify)).continuous
    (freqTrR.comp complexify).continuous
    (funext fun φ => Internal.FreqTrConjSym.reflConj_freqTr_rapid h1 φ)
  exact congrFun heq g

end Breakdown.Freq
