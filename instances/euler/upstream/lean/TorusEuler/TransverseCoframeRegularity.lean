import TorusEuler.LocalizedAmplitudeComparison

/-! Smoothness of the fixed transverse coframes. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.LocalizedAmplitude

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Restriction of the forward coframe to the fixed launch plane is smooth. -/
theorem contDiffOn_coframeLift (k : Vec3) {F : P → Vec3 →L[ℝ] Vec3}
    {S : Set P} {n : ℕ∞ω} (hF : ContDiffOn ℝ n F S) :
    ContDiffOn ℝ n (fun q => coframeLift k (F q)) S :=
  hF.clm_comp (contDiffOn_const (c := (transversePlane k).subtypeL))

/-- The projected inverse coframe is smooth wherever the transported covector is nonzero. -/
theorem contDiffOn_coframePullback (k : Vec3) {G : P → Vec3 →L[ℝ] Vec3}
    {S : Set P} {n : ℕ∞ω} (hG : ContDiffOn ℝ n G S)
    (hκ₀ : ∀ q ∈ S, (G q).adjoint k ≠ 0) :
    ContDiffOn ℝ n (fun q => coframePullback k (G q)) S := by
  let κ (q : P) := (G q).adjoint k
  let adj : (Vec3 →L[ℝ] Vec3) ≃ₗᵢ[ℝ] (Vec3 →L[ℝ] Vec3) := ContinuousLinearMap.adjoint
  have hκ : ContDiffOn ℝ n κ S :=
    (adj.contDiff.comp_contDiffOn hG).clm_apply contDiffOn_const
  let L : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ := innerSL ℝ
  have hInner : ContDiffOn ℝ n (fun q => L (κ q)) S := L.contDiff.comp_contDiffOn hκ
  have hRank : ContDiffOn ℝ n (fun q => InnerProductSpace.rankOne ℝ (κ q) (κ q)) S :=
    (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := Vec3) (F := Vec3)).contDiff.comp_contDiffOn
      (hInner.prodMk hκ)
  have hNormSq : ContDiffOn ℝ n (fun q => ‖κ q‖ ^ 2) S := hκ.norm_sq ℝ
  have hInv : ContDiffOn ℝ n (fun q => (‖κ q‖ ^ 2)⁻¹) S :=
    hNormSq.inv fun q hq => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hκ₀ q hq))
  have hProj : ContDiffOn ℝ n (fun q => oscillatoryTransverseProjection (κ q)) S :=
    contDiffOn_const.sub (hInv.smul hRank)
  exact (contDiffOn_const (c := (transversePlane k).orthogonalProjectionOnto)).clm_comp
    (hG.clm_comp hProj)

end TorusEuler.LocalizedAmplitude
