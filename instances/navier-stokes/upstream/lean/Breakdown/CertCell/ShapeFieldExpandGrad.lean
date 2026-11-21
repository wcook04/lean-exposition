import Breakdown.CertCell.ShapeKeyRotation
import Breakdown.CertCell.ShapeKeyTime
import Breakdown.CertCell.ShapeModeOrthogonal
import Breakdown.Cert.CoerciveRotation

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

namespace GradExpand

def spaceRot (φ : ℝ) : Space →L[ℝ] Space :=
  (Coercive.RotationInternal.axialRotEquiv φ).toContinuousLinearEquiv.toContinuousLinearMap

theorem spaceRot_apply (φ : ℝ) (y : Space) : spaceRot φ y = axialRot φ y := rfl

def twistVec (θ φ : ℝ) (w : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => Complex.exp ((θ : ℂ) * Complex.I) * rotateVec φ w i

def twistMap (θ φ : ℝ) : (Fin 3 → ℂ) →L[ℝ] (Fin 3 → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := twistVec θ φ
      map_add' := fun x z => by
        funext i
        fin_cases i <;> simp [twistVec, rotateVec] <;> ring
      map_smul' := fun c x => by
        funext i
        fin_cases i <;> simp [twistVec, rotateVec] <;> ring }

theorem twistMap_apply (θ φ : ℝ) (w : Fin 3 → ℂ) : twistMap θ φ w = twistVec θ φ w := rfl

def harmonicAngle (m : ℕ) (κ : FieldKey) (τ φ : ℝ) : ℝ :=
  2 * Real.pi * ((labelHarmonic m κ.label).1 : ℝ) * τ + ((labelHarmonic m κ.label).2 : ℝ) * φ

theorem key_shift_rot (P : ShapeParams) (D : TimeFieldData) (hD : IsTimeFieldData D) {κ : FieldKey}
    (hκ : κ ∈ D.keys) (σ τ φ : ℝ) (x : Space) :
    keyVector P κ (D.amp κ) (σ + τ) (axialRot φ x) =
      twistVec (harmonicAngle P.azimuthOrder κ τ φ) φ (keyVector P κ (D.amp κ) σ x) := by
  rw [keyRotation P D κ (σ + τ) φ x hD hκ, keyTimeShift_holds P κ (D.amp κ) σ τ x]
  have hx : Complex.exp (((harmonicAngle P.azimuthOrder κ τ φ : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((((labelAzimuth P.azimuthOrder κ.label : ℝ) * φ : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * τ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [harmonicAngle, labelHarmonic]
    push_cast
    ring
  funext i
  simp only [twistVec, hx]
  fin_cases i <;> simp [rotateVec] <;> ring

theorem key_fderiv_shift_rot (P : ShapeParams) (D : TimeFieldData) (hD : IsTimeFieldData D) {κ : FieldKey}
    (hκ : κ ∈ D.keys) (σ τ φ : ℝ) (y v : Space)
    (hf : Differentiable ℝ (keyVector P κ (D.amp κ) (σ + τ)))
    (hg : Differentiable ℝ (keyVector P κ (D.amp κ) σ)) :
    fderiv ℝ (keyVector P κ (D.amp κ) (σ + τ)) (axialRot φ y) (axialRot φ v) =
      twistVec (harmonicAngle P.azimuthOrder κ τ φ) φ (fderiv ℝ (keyVector P κ (D.amp κ) σ) y v) := by
  set θ := harmonicAngle P.azimuthOrder κ τ φ
  have h1 : HasFDerivAt (fun x => keyVector P κ (D.amp κ) (σ + τ) (spaceRot φ x))
      ((fderiv ℝ (keyVector P κ (D.amp κ) (σ + τ)) (spaceRot φ y)).comp (spaceRot φ)) y :=
    (hf (spaceRot φ y)).hasFDerivAt.comp y (spaceRot φ).hasFDerivAt
  have h2 : HasFDerivAt (fun x => twistMap θ φ (keyVector P κ (D.amp κ) σ x))
      ((twistMap θ φ).comp (fderiv ℝ (keyVector P κ (D.amp κ) σ) y)) y :=
    (twistMap θ φ).hasFDerivAt.comp y (hg y).hasFDerivAt
  have heq : (fun x => keyVector P κ (D.amp κ) (σ + τ) (spaceRot φ x)) =
      fun x => twistMap θ φ (keyVector P κ (D.amp κ) σ x) := by
    funext x
    rw [spaceRot_apply, twistMap_apply]
    exact key_shift_rot P D hD hκ σ τ φ x
  rw [heq] at h1
  have h3 := congrArg (fun L : Space →L[ℝ] (Fin 3 → ℂ) => L v) (h1.unique h2)
  simpa [spaceRot_apply, twistMap_apply] using h3

theorem realPartVec_apply (v : Fin 3 → ℂ) (i : Fin 3) : realPartVec v i = (v i).re := by
  simp [realPartVec]

theorem unrot_realPart (θ φ : ℝ) (w : Fin 3 → ℂ) (i : Fin 3) :
    axialRot (-φ) (realPartVec (twistVec θ φ w)) i = (Complex.exp ((θ : ℂ) * Complex.I) * w i).re := by
  have h1 := Real.cos_sq_add_sin_sq φ
  fin_cases i
  · show axialRot (-φ) (realPartVec (twistVec θ φ w)) 0 = (Complex.exp ((θ : ℂ) * Complex.I) * w 0).re
    rw [rot_apply_zero, realPartVec_apply, realPartVec_apply]
    simp [twistVec, rotateVec, Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    linear_combination (Real.cos θ * (w 0).re - Real.sin θ * (w 0).im) * h1
  · show axialRot (-φ) (realPartVec (twistVec θ φ w)) 1 = (Complex.exp ((θ : ℂ) * Complex.I) * w 1).re
    rw [rot_apply_one, realPartVec_apply, realPartVec_apply]
    simp [twistVec, rotateVec, Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    linear_combination (Real.cos θ * (w 1).re - Real.sin θ * (w 1).im) * h1
  · show axialRot (-φ) (realPartVec (twistVec θ φ w)) 2 = (Complex.exp ((θ : ℂ) * Complex.I) * w 2).re
    rw [rot_apply_two, realPartVec_apply]
    simp [twistVec, rotateVec]

theorem unrot_realPart_sum {α : Type*} (s : Finset α) (θ : α → ℝ) (φ : ℝ) (w : α → Fin 3 → ℂ) (i : Fin 3) :
    axialRot (-φ) (realPartVec (∑ a ∈ s, twistVec (θ a) φ (w a))) i =
      ∑ a ∈ s, (Complex.exp ((θ a : ℂ) * Complex.I) * w a i).re := by
  rw [map_sum, ← spaceRot_apply, map_sum]
  simp only [spaceRot_apply]
  rw [show (∑ a ∈ s, axialRot (-φ) (realPartVec (twistVec (θ a) φ (w a)))) i =
      ∑ a ∈ s, axialRot (-φ) (realPartVec (twistVec (θ a) φ (w a))) i by simp]
  exact Finset.sum_congr rfl fun a _ => unrot_realPart (θ a) φ (w a) i

theorem fderiv_shapeField (P : ShapeParams) (D : TimeFieldData) (s : ℝ)
    (hdiff : ∀ κ ∈ D.keys, Differentiable ℝ (keyVector P κ (D.amp κ) s)) (z v : Space) :
    fderiv ℝ (shapeInfoField P D s) z v = realPartVec (∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) s) z v) := by
  have hsum := HasFDerivAt.sum (u := D.keys) fun κ hκ => (hdiff κ hκ z).hasFDerivAt
  have h := realPartVec.hasFDerivAt.comp z hsum
  have hW : shapeInfoField P D s = realPartVec ∘ (∑ κ ∈ D.keys, keyVector P κ (D.amp κ) s) := by
    funext y
    simp only [shapeInfoField, complexField, Function.comp_apply, Finset.sum_apply]
  rw [hW, h.fderiv]
  simp

theorem span_of_waves {α : Type*} (S : Finset (ℤ × ℤ)) (hSy : ∀ β ∈ S, -β ∈ S) (K : Finset α)
    (ν : α → ℤ × ℤ) (hK : ∀ a ∈ K, ν a ∈ S) (w : α → ℂ) :
    ∑ ξ ∈ S, (∑ a ∈ K, ((if ξ = ν a then w a / 2 else 0) +
      (if ξ = -ν a then starRingEnd ℂ (w a) / 2 else 0))).re = ∑ a ∈ K, (w a).re := by
  rw [← Complex.re_sum, Finset.sum_comm, Complex.re_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' S (ν a), Finset.sum_ite_eq' S (-ν a),
    if_pos (hK a ha), if_pos (hSy _ (hK a ha))]
  simp

end GradExpand

end Internal

open Internal.GradExpand in
theorem fieldSpan_of_keys (P : ShapeParams) (D : TimeFieldData) (S : Finset (ℤ × ℤ)) (hD : IsTimeFieldData D)
    (hS : harmonicsOf P.azimuthOrder D ⊆ S) (hSy : ∀ β ∈ S, -β ∈ S) :
    ∀ σ y i, shapeInfoField P D σ y i = ∑ β ∈ S, (modeVel β (shapeInfoField P D) σ y i).re := by
  intro σ y i
  have hK : ∀ κ ∈ D.keys, labelHarmonic P.azimuthOrder κ.label ∈ S :=
    fun κ hκ => hS (Finset.mem_image_of_mem _ hκ)
  have hv : ∀ (τ φ : ℝ) (l : Fin 3), axialRot (-φ) (shapeInfoField P D (σ + τ) (axialRot φ y)) l =
      ∑ κ ∈ D.keys, (Complex.exp (((2 * Real.pi * (((labelHarmonic P.azimuthOrder κ.label).1) : ℝ) * τ +
        (((labelHarmonic P.azimuthOrder κ.label).2) : ℝ) * φ : ℝ) : ℂ) * Complex.I) *
          keyVector P κ (D.amp κ) σ y l).re := by
    intro τ φ l
    have hsum : complexField P D (σ + τ) (axialRot φ y) =
        ∑ κ ∈ D.keys, twistVec (harmonicAngle P.azimuthOrder κ τ φ) φ (keyVector P κ (D.amp κ) σ y) := by
      simp only [complexField]
      exact Finset.sum_congr rfl fun κ hκ => key_shift_rot P D hD hκ σ τ φ y
    simp only [shapeInfoField]
    rw [hsum, unrot_realPart_sum]
    rfl
  have hmode := fun ξ => modeVel_of_waveSum D.keys (fun κ => labelHarmonic P.azimuthOrder κ.label)
    (fun κ => keyVector P κ (D.amp κ) σ y) (shapeInfoField P D) σ y hv ξ
  simp_rw [hmode]
  rw [span_of_waves S hSy D.keys _ hK (fun κ => keyVector P κ (D.amp κ) σ y i)]
  simp only [shapeInfoField, complexField, realPartVec_apply, Finset.sum_apply, Complex.re_sum]

open Internal.GradExpand in
theorem gradientSpan_of_keyDiff (P : ShapeParams) (D : TimeFieldData) (S : Finset (ℤ × ℤ)) (hD : IsTimeFieldData D)
    (hdiff : ∀ κ ∈ D.keys, ∀ s, Differentiable ℝ (keyVector P κ (D.amp κ) s))
    (hS : harmonicsOf P.azimuthOrder D ⊆ S) (hSy : ∀ β ∈ S, -β ∈ S) :
    ∀ σ y i j, fderiv ℝ (shapeInfoField P D σ) y (unitVector j) i =
      ∑ β ∈ S, (modeGrad β (gradField (shapeInfoField P D)) σ y (i, j)).re := by
  intro σ y i j
  have hK : ∀ κ ∈ D.keys, labelHarmonic P.azimuthOrder κ.label ∈ S :=
    fun κ hκ => hS (Finset.mem_image_of_mem _ hκ)
  have hG : ∀ (τ φ : ℝ) (ij : Fin 3 × Fin 3),
      axialRot (-φ) (gradField (shapeInfoField P D) (σ + τ) (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1 =
      ∑ κ ∈ D.keys, (Complex.exp (((2 * Real.pi * (((labelHarmonic P.azimuthOrder κ.label).1) : ℝ) * τ +
        (((labelHarmonic P.azimuthOrder κ.label).2) : ℝ) * φ : ℝ) : ℂ) * Complex.I) *
          fderiv ℝ (keyVector P κ (D.amp κ) σ) y (unitVector ij.2) ij.1).re := by
    intro τ φ ij
    simp only [gradField]
    rw [fderiv_shapeField P D (σ + τ) (fun κ hκ => hdiff κ hκ (σ + τ))]
    have hsum : (∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) (σ + τ)) (axialRot φ y)
        (axialRot φ (unitVector ij.2))) = ∑ κ ∈ D.keys, twistVec (harmonicAngle P.azimuthOrder κ τ φ) φ
          (fderiv ℝ (keyVector P κ (D.amp κ) σ) y (unitVector ij.2)) :=
      Finset.sum_congr rfl fun κ hκ => key_fderiv_shift_rot P D hD hκ σ τ φ y _
        (hdiff κ hκ (σ + τ)) (hdiff κ hκ σ)
    rw [hsum, unrot_realPart_sum]
    rfl
  have hmode := fun ξ => modeGrad_of_waveSum D.keys (fun κ => labelHarmonic P.azimuthOrder κ.label)
    (fun κ ij => fderiv ℝ (keyVector P κ (D.amp κ) σ) y (unitVector ij.2) ij.1)
    (gradField (shapeInfoField P D)) σ y hG ξ
  simp_rw [hmode]
  rw [span_of_waves S hSy D.keys _ hK (fun κ => fderiv ℝ (keyVector P κ (D.amp κ) σ) y (unitVector j) i),
    fderiv_shapeField P D σ (fun κ hκ => hdiff κ hκ σ)]
  simp only [realPartVec_apply, Finset.sum_apply, Complex.re_sum]

theorem gradientSpan_of_keySmooth (h1 : TypeOneKeySmooth) (h2 : TypeTwoKeySmooth) (P : ShapeParams)
    (D : TimeFieldData) (S : Finset (ℤ × ℤ)) (hP : IsShapeParams P) (hD : IsTimeFieldData D)
    (hS : harmonicsOf P.azimuthOrder D ⊆ S) (hSy : ∀ β ∈ S, -β ∈ S) :
    ∀ σ y i j, fderiv ℝ (shapeInfoField P D σ) y (unitVector j) i =
      ∑ β ∈ S, (modeGrad β (gradField (shapeInfoField P D)) σ y (i, j)).re := by
  refine gradientSpan_of_keyDiff P D S hD (fun κ hκ s => ?_) hS hSy
  by_cases h : κ.label.1 = 0
  · exact (h2 P D κ s hP hD hκ h).smooth.differentiable (by simp)
  · exact (h1 P D κ s hP hD hκ h).smooth.differentiable (by simp)

end GivenShape

end CertCell

end Breakdown
