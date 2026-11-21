import TorusEuler.Paper.Proofs.S5c.Library.HigherGrad
import TorusEuler.Paper.Proofs.S5c.Library.CoefNorms
import TorusEuler.HierarchyHigherPressure

/-!
# Glue for (5.52) of Lemma 5.9: the gradient profile as products of coefficients and fields

On a time set `A ⊆ [0,T]`, in the language of Lemma D.1 (`Bridge.slices A f`):

* `slices_labelGrad_eq`: `𝐝q = Gᵀ∇_a q = ∑_j (∂_{a_j} q) Gᵀe_j`, with `G = (D_aX)⁻¹`, a sum of
  products `labelB j (G, ∂_{a_j} q)` of a phase-independent coefficient and a label derivative;
* `slices_phaseGrad_eq`: for a transverse solution, `κ∂_s𝗉 = P_κ(F - 2MV)` is the product
  `idB (P_κ, F + negB (M, V))`.

`adjL` (`A ↦ Aᵀ`) is a copy of the S5a glue `Lib.S5a.adjL` (`Proofs/S5a/Library/Budget.lean:48`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile InnerProductSpace AppendixD

noncomputable section

/-- The transpose `A ↦ Aᵀ` as a continuous linear map (copy of `Lib.S5a.adjL`). -/
def adjL : (Vec3 →L[ℝ] Vec3) →L[ℝ] (Vec3 →L[ℝ] Vec3) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A.adjoint
      map_add' := fun A B => map_add _ A B
      map_smul' := fun c A => by
        simp [ContinuousLinearMap.adjoint.map_smulₛₗ] }

/-- The transpose of `A` is `adjL A` (simp form of `adjL`). -/
@[simp] theorem adjL_apply (A : Vec3 →L[ℝ] Vec3) : adjL A = A.adjoint := rfl

/-- The adjoint-type map `adjL` has operator norm at most one. -/
theorem norm_adjL_le : ‖adjL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => by
    rw [adjL_apply, ContinuousLinearMap.adjoint.norm_map, one_mul]

/-- `labelB j (A, r) = r Aᵀe_j`. -/
def labelB (j : Fin 3) : (Vec3 →L[ℝ] Vec3) →L[ℝ] ℝ →L[ℝ] Vec3 :=
  (ContinuousLinearMap.lsmul ℝ ℝ).flip.comp
    ((ContinuousLinearMap.apply ℝ Vec3 (coordinateDirection j)).comp adjL)

/-- Evaluation formula for the bilinear label map `labelB j`. -/
theorem labelB_apply (j : Fin 3) (A : Vec3 →L[ℝ] Vec3) (r : ℝ) :
    labelB j A r = r • A.adjoint (coordinateDirection j) := rfl

/-- The bilinear label map `labelB j` has norm at most one. -/
theorem norm_labelB_le (j : Fin 3) : ‖labelB j‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Vec3 →L[ℝ] Vec3).flip‖ ≤ 1 := by
    rw [ContinuousLinearMap.opNorm_flip]
    exact ContinuousLinearMap.opNorm_lsmul_le
  have h2 : ‖(ContinuousLinearMap.apply ℝ Vec3 (coordinateDirection j)).comp adjL‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h3 : ‖ContinuousLinearMap.apply ℝ Vec3 (coordinateDirection j)‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => ?_
      rw [ContinuousLinearMap.apply_apply, one_mul]
      refine (A.le_opNorm _).trans ?_
      simp [coordinateDirection]
    simpa using mul_le_mul h3 norm_adjL_le (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
  simpa using mul_le_mul h1 h2 (ContinuousLinearMap.opNorm_nonneg _) zero_le_one

/-- The identity of `𝓛(ℝ³)`, as the bilinear map `(A, v) ↦ A v`. -/
abbrev idB : (Vec3 →L[ℝ] Vec3) →L[ℝ] Vec3 →L[ℝ] Vec3 := ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3)

/-- `negB (A, v) = -(A v + A v) = -2 A v`. -/
abbrev negB : (Vec3 →L[ℝ] Vec3) →L[ℝ] Vec3 →L[ℝ] Vec3 := -(idB + idB)

/-- The identity bilinear map `idB` has norm at most one. -/
theorem norm_idB_le : ‖idB‖ ≤ 1 := ContinuousLinearMap.norm_id_le

/-- The bilinear map `negB` has norm at most two. -/
theorem norm_negB_le : ‖negB‖ ≤ 2 := by
  show ‖-(idB + idB)‖ ≤ 2
  refine (norm_neg (idB + idB)).le.trans ?_
  have := norm_idB_le
  linarith [norm_add_le idB idB]

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
  {D lam : ℝ}

/-- `𝐝q = ∑_j (∂_{a_j} q) Gᵀe_j` on a time set `A ⊆ [0,T]`, with `G = (D_aX)⁻¹`. -/
theorem slices_labelGrad_eq (d : ParentGeometry hT U X k) {A : Set ℝ} (hA : A ⊆ Icc 0 T)
    (f : HierarchyTwistedProfile T k ℝ) (t : A) (x : Vec3 × ℝ) :
    Bridge.slices A ((S5.ops d).labelGrad f) t x =
      ∑ j : Fin 3, labelB j (fderiv ℝ (X t.1 0) (X 0 t.1 x.1))
        (labelPartial j (Bridge.slices A f) t x) := by
  have ht : (t : ℝ) ∈ Icc 0 T := hA t.2
  have hp : (((t : ℝ), x.1, x.2) : HierarchyProfilePoint) ∈ hierarchyProfileSlab T :=
    ⟨ht, mem_univ _⟩
  change ((S5.ops d).labelGrad f).val.val.val ((t : ℝ), x.1, x.2) = _
  have hlab : ((S5.ops d).labelGrad f).val.val.val ((t : ℝ), x.1, x.2) =
      (d.inverse.val.val.val ((t : ℝ), x.1, x.2)).adjoint
        (gradient (fun y => f.val.val.val ((t : ℝ), y, x.2)) x.1) :=
    HierarchySmoothProfile.labelGradient_eq_adjoint_gradient hT d.inverse.val.val f.val.val ht x.1 x.2
  rw [hlab, d.inverse_value _ hp]
  let F : Vec3 × ℝ → ℝ := fun z => f.val.val.val ((t : ℝ), z.1, z.2)
  have hF : ContDiff ℝ ∞ F := HierarchySmoothProfile.contDiff_labelPhase_slice f.val.val ht
  have hFd : HasFDerivAt F (fderiv ℝ F x) x := ((hF.differentiable (by simp)) x).hasFDerivAt
  have hi : HasFDerivAt (fun y : Vec3 => ((y, x.2) : Vec3 × ℝ)) (ContinuousLinearMap.inl ℝ Vec3 ℝ) x.1 :=
    (hasFDerivAt_id x.1).prodMk (hasFDerivAt_const x.2 x.1)
  have hFd' : HasFDerivAt F (fderiv ℝ F x) (x.1, x.2) := hFd
  have hg0 := hFd'.comp x.1 hi
  have hg : HasFDerivAt (fun y => f.val.val.val ((t : ℝ), y, x.2))
      ((fderiv ℝ F x).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ)) x.1 := hg0
  rw [hg.hasGradientAt.gradient]
  have hpart (j : Fin 3) : labelPartial j (Bridge.slices A f) t x =
      fderiv ℝ F x (coordinateDirection j, 0) := rfl
  simp only [hpart, labelB_apply]
  set G := fderiv ℝ (X (t : ℝ) 0) (X 0 (t : ℝ) x.1)
  set g := (toDual ℝ Vec3).symm ((fderiv ℝ F x).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ))
  have hgexp : g = ∑ j : Fin 3, fderiv ℝ F x (coordinateDirection j, 0) • coordinateDirection j := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr g]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordinateDirection]
    congr 1
    have h1 : g j = ⟪g, EuclideanSpace.single j (1 : ℝ)⟫_ℝ := by
      rw [EuclideanSpace.inner_single_right]
      simp
    rw [h1, toDual_symm_apply]
    rfl
  rw [hgexp, map_sum]
  simp only [map_smul]

/-- `κ∂_s𝗉 = P_κ(F - 2MV)` for a transverse solution, as the product `idB (P_κ, F + negB (M, V))`
on a time set `A ⊆ [0,T]`. -/
theorem slices_phaseGrad_eq (d : ParentGeometry hT U X k) {A : Set ℝ} (hA : A ⊆ Icc 0 T)
    {F V : HierarchyTwistedProfile T k Vec3} {q : HierarchyTwistedProfile T k ℝ}
    (h : S5.TransverseSolution d F V q) (hF0 : (S5.ops d).average F = 0) (t : A) (x : Vec3 × ℝ) :
    Bridge.slices A ((S5.ops d).phaseGrad q) t x =
      idB (hierarchyLongitudinalProjection (S5.waveVector X k t.1 x.1))
        (Bridge.slices A F t x + negB (S5.strainField U X t.1 x.1) (Bridge.slices A V t x)) := by
  have ht : (t : ℝ) ∈ Icc 0 T := hA t.2
  change ((S5.ops d).phaseGrad q).val.val.val ((t : ℝ), x.1, x.2) = _
  rw [phaseGrad_transverse_eq d h hF0 ht x.1 x.2]
  simp only [hierarchyLongitudinalProjection, idB, negB, ContinuousLinearMap.id_apply,
    smul_apply, neg_apply, add_apply]
  have heq : Bridge.slices A F t x + -(S5.strainField U X t x.1 (Bridge.slices A V t x) +
      S5.strainField U X t x.1 (Bridge.slices A V t x)) =
      F.val.val.val ((t : ℝ), x.1, x.2) - (2 : ℝ) • S5.strainField U X t x.1
        (V.val.val.val ((t : ℝ), x.1, x.2)) := by
    rw [two_smul, sub_eq_add_neg]
    rfl
  rw [heq]

end

end TorusEuler.Paper.Lib.S5c
