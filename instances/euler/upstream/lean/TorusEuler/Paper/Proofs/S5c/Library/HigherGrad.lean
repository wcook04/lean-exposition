import TorusEuler.Paper.Proofs.S5c.Library.FlowGeom
import TorusEuler.Paper.Proofs.S5c.Library.Inactive
import TorusEuler.HierarchyConcreteMean

/-!
# Glue for (5.52) of Lemma 5.9: the gradient of a readout and the pressure slope

* `gradient_graphRead_eq`: the chain rule (3.1) for a scalar profile,
  `∇_x f^♮ = (𝐝f + κ∂_s f)^♮` (`sections/08_exact_wave.tex:211-218`);
* `phaseGrad_transverse_eq`: for a solution of the transverse equation (5.15) with source `F`,
  the transverse equation (5.16) gives `κ∂_s𝗉 = P_κ(F - 2MV)` (`:211-217`), read from the
  library ODE solve (`exists_transverseResult`, field `pressure_slope`) through the uniqueness of
  transverse solutions (`Bridge.TransverseSolution.unique`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile InnerProductSpace

noncomputable section

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
  {D lam : ℝ}

/-- The chain rule (3.1) for the gradient of the readout of a scalar profile:
`∇_x f^♮ = (𝐝 f + κ ∂_s f)^♮`. -/
theorem gradient_graphRead_eq (d : ParentGeometry hT U X k) (hP : S5.Parent T U X pU D lam)
    (f : HierarchyTwistedProfile T k ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    gradient (graphRead (fun t => X t 0) f t) =
      graphRead (fun t => X t 0) ((S5.ops d).labelGrad f + (S5.ops d).phaseGrad f) t := by
  funext x
  let F : Vec3 × ℝ → ℝ := fun z => f.val.val.val (t, z.1, z.2)
  have hF : ContDiff ℝ ∞ F := HierarchySmoothProfile.contDiff_labelPhase_slice f.val.val ht
  have hY : ContDiff ℝ ∞ (X t 0) := contDiff_slice (inverseFlow_smooth hT hP) ht
  set a := X t 0 x with ha
  set s := ⟪k, a⟫_ℝ with hs
  let DY := fderiv ℝ (X t 0) x
  have hYd : HasFDerivAt (X t 0) DY x := ((hY.differentiable (by simp)) x).hasFDerivAt
  have hΦ : HasFDerivAt (fun y => ((X t 0 y, ⟪k, X t 0 y⟫_ℝ) : Vec3 × ℝ))
      (DY.prod ((innerSL ℝ k).comp DY)) x :=
    hYd.prodMk ((innerSL ℝ k).hasFDerivAt.comp x hYd)
  have hFd : HasFDerivAt F (fderiv ℝ F (a, s)) (a, s) :=
    ((hF.differentiable (by simp)) _).hasFDerivAt
  have hcomp := hFd.comp x hΦ
  have hgrad : gradient (graphRead (fun t => X t 0) f t) x =
      (toDual ℝ Vec3).symm ((fderiv ℝ F (a, s)).comp (DY.prod ((innerSL ℝ k).comp DY))) := by
    exact congrArg (toDual ℝ Vec3).symm hcomp.fderiv
  rw [hgrad]
  -- the two terms of the right side at `(t, a, s)`
  have hp : ((t, a, s) : HierarchyProfilePoint) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hval : graphRead (fun t => X t 0) ((S5.ops d).labelGrad f + (S5.ops d).phaseGrad f) t x =
      ((S5.ops d).labelGrad f).val.val.val (t, a, s) +
        ((S5.ops d).phaseGrad f).val.val.val (t, a, s) := rfl
  rw [hval, Bridge.ops_phaseGrad_eval d f hp]
  have hlab : ((S5.ops d).labelGrad f).val.val.val (t, a, s) =
      (d.inverse.val.val.val (t, a, s)).adjoint (gradient (fun y => f.val.val.val (t, y, s)) a) :=
    HierarchySmoothProfile.labelGradient_eq_adjoint_gradient hT d.inverse.val.val f.val.val ht a s
  rw [hlab, d.inverse_value (t, a, s) hp]
  change _ = (fderiv ℝ (X t 0) (X 0 t a)).adjoint _ + _
  rw [ha, inverseFlow_right hT hP ht x]
  refine ext_inner_right ℝ fun w => ?_
  rw [toDual_symm_apply, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    real_inner_smul_left]
  -- the partial derivatives of `F`
  have hlabel : HasFDerivAt (fun y => f.val.val.val (t, y, s))
      ((fderiv ℝ F (a, s)).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ)) a := by
    have hi : HasFDerivAt (fun y : Vec3 => ((y, s) : Vec3 × ℝ)) (ContinuousLinearMap.inl ℝ Vec3 ℝ) a :=
      (hasFDerivAt_id a).prodMk (hasFDerivAt_const s a)
    exact hFd.comp a hi
  have hphase : HasDerivAt (fun r => f.val.val.val (t, a, r)) (fderiv ℝ F (a, s) (0, 1)) s := by
    have hi : HasDerivAt (fun r : ℝ => ((a, r) : Vec3 × ℝ)) ((0 : Vec3), (1 : ℝ)) s :=
      (hasDerivAt_const s a).prodMk (hasDerivAt_id s)
    exact hFd.comp_hasDerivAt s hi
  rw [hlabel.hasGradientAt.gradient, hphase.deriv, toDual_symm_apply]
  have hκ : ⟪S5.waveVector X k t a, w⟫_ℝ = ⟪k, DY w⟫_ℝ := by
    rw [ha]
    exact (inner_carrier_fderiv_inverseFlow hT hP ht x w).symm
  rw [hκ]
  have hsplit : ((DY w, ⟪k, DY w⟫_ℝ) : Vec3 × ℝ) = (DY w, 0) + ⟪k, DY w⟫_ℝ • ((0 : Vec3), (1 : ℝ)) := by
    ext <;> simp
  change fderiv ℝ F (a, s) (DY w, ⟪k, DY w⟫_ℝ) = _
  rw [hsplit, map_add, map_smul, smul_eq_mul]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inl_apply]
  ring

/-- The transverse equation (5.16): `κ∂_s𝗉 = P_κ(F - 2MV)` for a solution `(V, 𝗉)` of (5.15) with
source `F` of zero phase mean, with `P_κ = |κ|⁻²κ⊗κ`. -/
theorem phaseGrad_transverse_eq (d : ParentGeometry hT U X k) {F V : HierarchyTwistedProfile T k Vec3}
    {q : HierarchyTwistedProfile T k ℝ} (h : S5.TransverseSolution d F V q)
    (hF0 : (S5.ops d).average F = 0) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    ((S5.ops d).phaseGrad q).val.val.val (t, a, s) =
      ((‖S5.waveVector X k t a‖ ^ 2)⁻¹ •
        InnerProductSpace.rankOne ℝ (S5.waveVector X k t a) (S5.waveVector X k t a))
        (F.val.val.val (t, a, s) - (2 : ℝ) • S5.strainField U X t a (V.val.val.val (t, a, s))) := by
  obtain ⟨r⟩ := exists_transverseResult hT d.inverse d.strain d.covector d.oscillation F hF0
  have hr : S5.TransverseSolution d F r.output.V r.output.p := by
    refine ⟨r.momentum, fun t ht a s => ?_, r.output.average_V, r.velocity_initial,
      r.pressure_mean⟩
    have h := r.transverse t ht a s
    rw [d.covector_value (t, a, s) ⟨ht, mem_univ _⟩] at h
    exact h
  obtain ⟨hV, hq⟩ := Bridge.TransverseSolution.unique d h hr
  have hp : ((t, a, s) : HierarchyProfilePoint) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hp0 : ((t, a, 0) : HierarchyProfilePoint) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  rw [Bridge.ops_phaseGrad_eval d q hp, hq, hV]
  change deriv (fun z => r.output.p.val.val.val (t, a, z)) s • _ = _
  rw [(r.pressure_slope t ht a s).deriv, d.strain_value _ hp0, d.covector_value _ hp0]
  change oscillatoryPressureSlope (S5.strainField U X t a) (S5.waveVector X k t a)
    (F.val.val.val (t, a, s)) (r.output.V.val.val.val (t, a, s)) • S5.waveVector X k t a = _
  simp only [oscillatoryPressureSlope, smul_apply, rankOne_apply,
    inner_sub_right, real_inner_smul_right, smul_smul]
  congr 1
  ring

end

end TorusEuler.Paper.Lib.S5c
