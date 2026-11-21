import TorusEuler.Statement
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The profile graph and chain rules on the lifted label cell in §3. -/

open ContinuousLinearMap Filter Set
open scoped InnerProductSpace Topology

namespace TorusEuler

variable {E : Type*}

/-- Evaluate a profile at the inverse label and the transported real phase. -/
noncomputable def transportedProfile (A : Velocity) (k : Vec3) (f : ℝ → Vec3 → ℝ → E)
    (t : ℝ) (x : Vec3) : E :=
  f t (A t x) ⟪k, A t x⟫_ℝ

theorem transportedProfile_on_trajectory {A X : Velocity} {t : ℝ} {a : Vec3}
    (k : Vec3) (f : ℝ → Vec3 → ℝ → E) (h : A t (X t a) = a) :
    transportedProfile A k f t (X t a) = f t a ⟪k, a⟫_ℝ := by
  simp only [transportedProfile, h]

/-- The transported phase gradient is the transpose of the inverse label derivative applied
to the initial wave vector. -/
theorem hasGradientAt_transportedPhase {A : Velocity} {t : ℝ} {x k : Vec3}
    {Ax : Vec3 →L[ℝ] Vec3} (hA : HasFDerivAt (A t) Ax x) :
    HasGradientAt (fun y => ⟪k, A t y⟫_ℝ) (Ax.adjoint k) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  change HasFDerivAt _ (innerSL ℝ (Ax.adjoint k)) x
  rw [← innerSL_apply_comp]
  exact (innerSL ℝ k).hasFDerivAt.comp x hA

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The spatial chain rule in (3.1) at fixed time. The first term differentiates in
the label and the second differentiates in the phase. -/
theorem hasFDerivAt_transportedProfile {t : ℝ} {x k : Vec3}
    {A : Velocity} {f : ℝ → Vec3 → ℝ → E} {Ax : Vec3 →L[ℝ] Vec3}
    {fs : E} {fa : Vec3 →L[ℝ] E}
    (hA : HasFDerivAt (A t) Ax x)
    (hf : HasFDerivAt (fun p : Vec3 × ℝ => f t p.1 p.2)
      (fa.coprod (toSpanSingleton ℝ fs)) (A t x, ⟪k, A t x⟫_ℝ)) :
    HasFDerivAt (transportedProfile A k f t)
      (fa.comp Ax + (innerSL ℝ (Ax.adjoint k)).smulRight fs) x := by
  have hphase := (hasGradientAt_transportedPhase hA (k := k)).hasFDerivAt
  have h := hf.comp x (hA.prodMk hphase)
  have hsplit : (fa.coprod (toSpanSingleton ℝ fs)).comp
      (Ax.prod (innerSL ℝ (Ax.adjoint k))) =
      fa.comp Ax + (innerSL ℝ (Ax.adjoint k)).smulRight fs := by
    ext v
    simp
  exact hsplit ▸ h

/-- Joint derivative of the graph evaluation on a time slab. -/
theorem hasFDerivWithinAt_transportedProfile {I : Set ℝ} {t : ℝ} {x k : Vec3}
    {A : Velocity} {f : ℝ → Vec3 → ℝ → E} {dA : (ℝ × Vec3) →L[ℝ] Vec3}
    {df : (ℝ × Vec3 × ℝ) →L[ℝ] E}
    (hA : HasFDerivWithinAt (Function.uncurry A) dA (I ×ˢ univ) (t, x))
    (hf : HasFDerivWithinAt (fun p : ℝ × Vec3 × ℝ => f p.1 p.2.1 p.2.2)
      df (I ×ˢ univ) (t, A t x, ⟪k, A t x⟫_ℝ)) :
    HasFDerivWithinAt (Function.uncurry (transportedProfile A k f))
      (df.comp ((fst ℝ ℝ Vec3).prod (dA.prod ((innerSL ℝ k).comp dA))))
      (I ×ˢ univ) (t, x) := by
  have hphase := (innerSL ℝ k).hasFDerivAt.comp_hasFDerivWithinAt (t, x) hA
  have hgraph := hasFDerivWithinAt_fst.prodMk (hA.prodMk hphase)
  exact hf.comp (t, x) hgraph (fun p hp => mem_prod.mpr ⟨hp.1, mem_univ _⟩)

/-- The spatial and material chain rules of (3.1). `At + Ax u = 0` is the inverse
label transport equation. The time derivative is taken within the time interval. -/
theorem transportedProfile_chainRule {I : Set ℝ} {t : ℝ} {x k u At : Vec3}
    {A : Velocity} {f : ℝ → Vec3 → ℝ → E} {Ax : Vec3 →L[ℝ] Vec3}
    {ft fs : E} {fa : Vec3 →L[ℝ] E}
    (ht : t ∈ I) (hI : UniqueDiffWithinAt ℝ I t)
    (hA : HasFDerivWithinAt (Function.uncurry A) ((toSpanSingleton ℝ At).coprod Ax)
      (I ×ˢ univ) (t, x))
    (hf : HasFDerivWithinAt (fun p : ℝ × Vec3 × ℝ => f p.1 p.2.1 p.2.2)
      ((toSpanSingleton ℝ ft).coprod (fa.coprod (toSpanSingleton ℝ fs)))
      (I ×ˢ univ) (t, A t x, ⟪k, A t x⟫_ℝ))
    (htransport : At + Ax u = 0) :
    HasFDerivAt (transportedProfile A k f t)
      (fa.comp Ax + (innerSL ℝ (Ax.adjoint k)).smulRight fs) x ∧
    derivWithin (fun r => transportedProfile A k f r x) I t +
      fderiv ℝ (transportedProfile A k f t) x u = ft := by
  let dA := (toSpanSingleton ℝ At).coprod Ax
  let df := (toSpanSingleton ℝ ft).coprod (fa.coprod (toSpanSingleton ℝ fs))
  let dg := df.comp ((fst ℝ ℝ Vec3).prod (dA.prod ((innerSL ℝ k).comp dA)))
  have hg := hasFDerivWithinAt_transportedProfile hA hf
  change HasFDerivWithinAt (Function.uncurry (transportedProfile A k f)) dg _ _ at hg
  have hx := hg.comp_hasFDerivAt x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
    (Eventually.of_forall fun y => mem_prod.mpr ⟨ht, mem_univ y⟩)
  have hDx : dg.comp (inr ℝ ℝ Vec3) =
      fa.comp Ax + (innerSL ℝ (Ax.adjoint k)).smulRight fs := by
    ext v
    simp [dg, dA, df, ContinuousLinearMap.adjoint_inner_left]
  have hx' : HasFDerivAt (transportedProfile A k f t)
      (fa.comp Ax + (innerSL ℝ (Ax.adjoint k)).smulRight fs) x := by
    exact hDx ▸ hx
  have ht' := hg.comp_hasDerivWithinAt t
    ((hasDerivWithinAt_id t I).prodMk (hasDerivWithinAt_const t I x))
    (fun _ hr => mem_prod.mpr ⟨hr, mem_univ x⟩)
  change HasDerivWithinAt (fun r => transportedProfile A k f r x) (dg (1, 0)) I t at ht'
  have hsum : dg (1, 0) + dg (0, u) = ft := by
    rw [← map_add]
    change dg (1 + 0, 0 + u) = ft
    simp [dg, dA, df, htransport]
  refine ⟨hx', ?_⟩
  rw [ht'.derivWithin hI, hx'.fderiv, ← hDx]
  exact hsum

/-- Differentiating the local identity `A(t, X(t,a)) = a` gives transport of the
inverse label along the parent trajectory, including at a time-slab endpoint. -/
theorem inverseLabel_materialDerivative_eq_zero {I : Set ℝ} {A X : Velocity}
    {t : ℝ} {a u At : Vec3} {Ax : Vec3 →L[ℝ] Vec3}
    (ht : t ∈ I) (hI : UniqueDiffWithinAt ℝ I t)
    (hA : HasFDerivWithinAt (Function.uncurry A) ((toSpanSingleton ℝ At).coprod Ax)
      (I ×ˢ univ) (t, X t a))
    (hX : HasDerivWithinAt (fun r => X r a) u I t)
    (hInv : (fun r => A r (X r a)) =ᶠ[𝓝[I] t] fun _ => a) :
    At + Ax u = 0 := by
  have h := hA.comp_hasDerivWithinAt t ((hasDerivWithinAt_id t I).prodMk hX)
    (fun r hr => mem_prod.mpr ⟨hr, mem_univ (X r a)⟩)
  have hc := (hasDerivWithinAt_const t I a).congr_of_eventuallyEq_of_mem hInv ht
  simpa using (h.derivWithin hI).symm.trans (hc.derivWithin hI)

/-- The spatial derivative of a local inverse label map equals the inverse of the
flow derivative at the corresponding label. -/
theorem inverseLabel_spatialDerivative_eq {A X : Velocity} {t : ℝ} {a : Vec3}
    {Ax : Vec3 →L[ℝ] Vec3} {F : Vec3 ≃L[ℝ] Vec3}
    (hA : HasFDerivAt (A t) Ax (X t a))
    (hX : HasFDerivAt (X t) (F : Vec3 →L[ℝ] Vec3) a)
    (hInv : (A t ∘ X t) =ᶠ[𝓝 a] id) :
    Ax = (F.symm : Vec3 →L[ℝ] Vec3) := by
  have h := (hasFDerivAt_id (𝕜 := ℝ) a).congr_of_eventuallyEq hInv
  have hcomp := (hA.comp a hX).fderiv.symm.trans h.fderiv
  apply ContinuousLinearMap.ext
  intro v
  simpa using congrArg (fun L : Vec3 →L[ℝ] Vec3 => L (F.symm v)) hcomp

/-- The inverse-transpose wave vector satisfies the covector equation preceding (3.2)
when the deformation satisfies the forward variational equation along the label. -/
theorem hasDerivWithinAt_transportedWaveVector {I : Set ℝ} {t : ℝ} {k : Vec3}
    {F : ℝ → Vec3 ≃L[ℝ] Vec3} {M : Vec3 →L[ℝ] Vec3}
    (hF : HasDerivWithinAt (fun r => (F r : Vec3 →L[ℝ] Vec3))
      (M.comp (F t : Vec3 →L[ℝ] Vec3)) I t) :
    HasDerivWithinAt (fun r => (F r).symm.toContinuousLinearMap.adjoint k)
      (-(M.adjoint ((F t).symm.toContinuousLinearMap.adjoint k))) I t := by
  have hInverse := (hasFDerivAt_ringInverse (𝕜 := ℝ) (F t).toUnit).comp_hasDerivWithinAt t hF
  have hinv_eq : (fun r => (F r).symm.toContinuousLinearMap) =
      Ring.inverse ∘ (fun r => (F r : Vec3 →L[ℝ] Vec3)) := by
    funext r
    exact (Ring.inverse_unit (F r).toUnit).symm
  rw [← hinv_eq] at hInverse
  let B := (F t).symm.toContinuousLinearMap
  have hB : HasDerivWithinAt (fun r => (F r).symm.toContinuousLinearMap)
      (-(B.comp M)) I t := by
    refine hInverse.congr_deriv ?_
    simp only [neg_apply, mulLeftRight_apply, ContinuousLinearMap.mul_def]
    change -(B.comp (M.comp (F t : Vec3 →L[ℝ] Vec3))).comp B = -(B.comp M)
    apply ContinuousLinearMap.ext
    intro v
    simp [B]
  let adj : (Vec3 →L[ℝ] Vec3) →L[ℝ] (Vec3 →L[ℝ] Vec3) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toLinearIsometry.toContinuousLinearMap
  let C := (ContinuousLinearMap.apply ℝ Vec3 k).comp adj
  refine (C.hasFDerivAt.comp_hasDerivWithinAt t hB).congr_deriv ?_
  change (-(B.comp M)).adjoint k = -(M.adjoint (B.adjoint k))
  simp [ContinuousLinearMap.adjoint_comp]

end TorusEuler
