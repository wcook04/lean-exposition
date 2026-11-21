import TorusEuler.Piola
import TorusEuler.ResidualGradient
import TorusEuler.TransportedPhase

/-! The Eulerian momentum of the profile expansion evaluated on the transported graph. -/

open ContinuousLinearMap Set
open scoped InnerProductSpace

namespace TorusEuler

/-- The spatial pressure gradient on the transported graph is the label
gradient pushed by the coframe plus the fast phase derivative. -/
theorem hasGradientAt_transportedPressure {t : ℝ} {x k : Vec3}
    {A : Velocity} {p : ℝ → Vec3 → ℝ → ℝ} {Ax : Vec3 →L[ℝ] Vec3} {pa : Vec3} {ps : ℝ}
    (hA : HasFDerivAt (A t) Ax x)
    (hp : HasFDerivAt (fun q : Vec3 × ℝ => p t q.1 q.2)
      ((innerSL ℝ pa).coprod (toSpanSingleton ℝ ps)) (A t x, ⟪k, A t x⟫_ℝ)) :
    HasGradientAt (transportedProfile A k p t) (Ax.adjoint pa + ps • Ax.adjoint k) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (hasFDerivAt_transportedProfile hA hp).congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp [ContinuousLinearMap.adjoint_inner_left, mul_comm]

/-- The Eulerian residual of the sum is the parent residual plus the four
terms of the profile momentum equation. This uses within-slab time
derivatives at both ends. -/
theorem momentumResidual_transportedHierarchy
    {I : Set ℝ} {t : ℝ} {x k At : Vec3} {Ax : Vec3 →L[ℝ] Vec3}
    {U A : Velocity} {p : Pressure} {W : ℝ → Vec3 → ℝ → Vec3}
    {Q : ℝ → Vec3 → ℝ → ℝ} {Ut Wt Ws Qa : Vec3} {Wa : Vec3 →L[ℝ] Vec3}
    {Qs : ℝ}
    (ht : t ∈ I) (hI : UniqueDiffWithinAt ℝ I t)
    (hA : HasFDerivWithinAt (Function.uncurry A) ((toSpanSingleton ℝ At).coprod Ax)
      (I ×ˢ univ) (t, x))
    (htransport : At + Ax (U t x) = 0)
    (hUt : HasDerivWithinAt (fun r => U r x) Ut I t)
    (hUx : DifferentiableAt ℝ (U t) x) (hp : DifferentiableAt ℝ (p t) x)
    (hW : HasFDerivWithinAt (fun q : ℝ × Vec3 × ℝ => W q.1 q.2.1 q.2.2)
      ((toSpanSingleton ℝ Wt).coprod (Wa.coprod (toSpanSingleton ℝ Ws)))
      (I ×ˢ univ) (t, A t x, ⟪k, A t x⟫_ℝ))
    (hQ : HasFDerivAt (fun q : Vec3 × ℝ => Q t q.1 q.2)
      ((innerSL ℝ Qa).coprod (toSpanSingleton ℝ Qs)) (A t x, ⟪k, A t x⟫_ℝ)) :
    let w := transportedProfile A k W t x
    let Dw := Wa.comp Ax + (innerSL ℝ (Ax.adjoint k)).smulRight Ws
    momentumResidual I (U + transportedProfile A k W) (p + transportedProfile A k Q) t x =
      Wt + fderiv ℝ (U t) x w + Dw w + (Ax.adjoint Qa + Qs • Ax.adjoint k) +
        momentumResidual I U p t x := by
  let w := transportedProfile A k W t x
  let Dw := Wa.comp Ax + (innerSL ℝ (Ax.adjoint k)).smulRight Ws
  obtain ⟨hWx, hMaterial⟩ := transportedProfile_chainRule ht hI hA hW htransport
  have hAx : HasFDerivAt (A t) Ax x := by
    have h := hA.comp_hasFDerivAt x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
      (Filter.Eventually.of_forall fun y => mem_prod.mpr ⟨ht, mem_univ y⟩)
    have hd : ((toSpanSingleton ℝ At).coprod Ax).comp (inr ℝ ℝ Vec3) = Ax := by
      apply ContinuousLinearMap.ext
      intro v
      simp
    rw [hd] at h
    exact h
  have hWt :=
    (hasFDerivWithinAt_transportedProfile hA hW).comp_hasDerivWithinAt t
      ((hasDerivWithinAt_id t I).prodMk (hasDerivWithinAt_const t I x))
      (fun _ hr => mem_prod.mpr ⟨hr, mem_univ x⟩)
  change HasDerivWithinAt (fun r => transportedProfile A k W r x) _ I t at hWt
  have hdt :
      derivWithin (fun r => U r x + transportedProfile A k W r x) I t =
        derivWithin (fun r => U r x) I t + derivWithin (fun r => transportedProfile A k W r x) I t := by
    exact derivWithin_fun_add hUt.differentiableWithinAt hWt.differentiableWithinAt
  have hdx : fderiv ℝ (fun y => U t y + transportedProfile A k W t y) x =
      fderiv ℝ (U t) x + Dw :=
    (hUx.hasFDerivAt.add hWx).fderiv
  have hGrad := hasGradientAt_transportedPressure hAx hQ
  have hGradAdd : HasGradientAt (fun y => p t y + transportedProfile A k Q t y)
      (gradient (p t) x + (Ax.adjoint Qa + Qs • Ax.adjoint k)) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    refine (hp.hasGradientAt.hasFDerivAt.add hGrad.hasFDerivAt).congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro v
    simp
  have hMaterial' :
      derivWithin (fun r => transportedProfile A k W r x) I t + Dw (U t x) = Wt := by
    rwa [hWx.fderiv] at hMaterial
  change derivWithin (fun r => U r x + transportedProfile A k W r x) I t +
    fderiv ℝ (fun y => U t y + transportedProfile A k W t y) x (U t x + w) +
    gradient (fun y => p t y + transportedProfile A k Q t y) x =
    Wt + fderiv ℝ (U t) x w + Dw w + (Ax.adjoint Qa + Qs • Ax.adjoint k) +
      momentumResidual I U p t x
  rw [hdt, hdx, hGradAdd.gradient, ← hMaterial']
  simp only [momentumResidual, materialAcceleration, add_apply, map_add]
  abel

/-- The graph divergence is the trace of the coframe label derivative plus
the fast covector contracted with the phase derivative. -/
theorem divergence_transportedHierarchy {t : ℝ} {x k : Vec3} {A : Velocity}
    {W : ℝ → Vec3 → ℝ → Vec3} {Ax Wa : Vec3 →L[ℝ] Vec3} {Ws : Vec3}
    (hA : HasFDerivAt (A t) Ax x)
    (hW : HasFDerivAt (fun q : Vec3 × ℝ => W t q.1 q.2)
      (Wa.coprod (toSpanSingleton ℝ Ws)) (A t x, ⟪k, A t x⟫_ℝ)) :
    divergence (transportedProfile A k W t) x =
      LinearMap.trace ℝ Vec3 (Wa.comp Ax).toLinearMap + ⟪Ax.adjoint k, Ws⟫_ℝ := by
  rw [divergence_eq_trace_fderiv, (hasFDerivAt_transportedProfile hA hW).fderiv]
  change LinearMap.trace ℝ Vec3 ((Wa.comp Ax).toLinearMap +
    (innerSL ℝ (Ax.adjoint k)).toLinearMap.smulRight Ws) = _
  rw [map_add, LinearMap.trace_smulRight]
  rfl

end TorusEuler
