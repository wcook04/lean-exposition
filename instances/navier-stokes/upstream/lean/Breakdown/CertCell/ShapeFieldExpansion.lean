import Breakdown.CertCell.ShapeFieldSecondDerivFlip
import Breakdown.CertCell.ShapeKeyRotation
import Breakdown.CertCell.ShapeKeyTime
import Breakdown.CertCell.ShapeModeOrthogonal
import Breakdown.Cert.CoerciveRotation

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

namespace SecondDerivExpand

def phaseRotVec (θ φ : ℝ) (w : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => Complex.exp ((θ : ℂ) * Complex.I) * rotateVec φ w i

theorem phaseRotVec_inv (θ φ : ℝ) (w : Fin 3 → ℂ) : phaseRotVec (-θ) (-φ) (phaseRotVec θ φ w) = w := by
  have hE : Complex.exp (-((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have h1 := Complex.cos_sq_add_sin_sq (φ : ℂ)
  funext i
  fin_cases i <;> simp [phaseRotVec, rotateVec, Real.cos_neg, Real.sin_neg]
  · linear_combination (Complex.cos (φ : ℂ) ^ 2 + Complex.sin (φ : ℂ) ^ 2) * w 0 * hE + w 0 * h1
  · linear_combination (Complex.cos (φ : ℂ) ^ 2 + Complex.sin (φ : ℂ) ^ 2) * w 1 * hE + w 1 * h1
  · linear_combination w 2 * hE

def phaseRotEquiv (θ φ : ℝ) : (Fin 3 → ℂ) ≃L[ℝ] (Fin 3 → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := phaseRotVec θ φ
      invFun := phaseRotVec (-θ) (-φ)
      map_add' := fun x z => by
        funext i
        fin_cases i <;> simp [phaseRotVec, rotateVec] <;> ring
      map_smul' := fun c x => by
        funext i
        fin_cases i <;> simp [phaseRotVec, rotateVec] <;> ring
      left_inv := fun x => phaseRotVec_inv θ φ x
      right_inv := fun x => by
        have h := phaseRotVec_inv (-θ) (-φ) x
        simp only [neg_neg] at h
        exact h }

theorem phaseRotEquiv_apply (θ φ : ℝ) (w : Fin 3 → ℂ) : phaseRotEquiv θ φ w = phaseRotVec θ φ w := rfl

def rotEquiv (φ : ℝ) : Space ≃L[ℝ] Space := (Coercive.RotationInternal.axialRotEquiv φ).toContinuousLinearEquiv

theorem rotEquiv_apply (φ : ℝ) (y : Space) : rotEquiv φ y = axialRot φ y := rfl

def keyAngle (m : ℕ) (κ : FieldKey) (τ φ : ℝ) : ℝ :=
  2 * Real.pi * ((labelHarmonic m κ.label).1 : ℝ) * τ + ((labelHarmonic m κ.label).2 : ℝ) * φ

theorem keyVector_shift_rot (P : ShapeParams) (D : TimeFieldData) (hD : IsTimeFieldData D) {κ : FieldKey}
    (hκ : κ ∈ D.keys) (σ τ φ : ℝ) (x : Space) :
    keyVector P κ (D.amp κ) (σ + τ) (rotEquiv φ x) =
      phaseRotEquiv (keyAngle P.azimuthOrder κ τ φ) φ (keyVector P κ (D.amp κ) σ x) := by
  rw [rotEquiv_apply, keyRotation P D κ (σ + τ) φ x hD hκ, keyTimeShift_holds P κ (D.amp κ) σ τ x,
    phaseRotEquiv_apply]
  have hx : Complex.exp (((keyAngle P.azimuthOrder κ τ φ : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((((labelAzimuth P.azimuthOrder κ.label : ℝ) * φ : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * τ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [keyAngle, labelHarmonic]
    push_cast
    ring
  funext i
  simp only [phaseRotVec, hx]
  fin_cases i <;> simp [rotateVec] <;> ring

theorem keySecondDeriv_shift_rot (P : ShapeParams) (D : TimeFieldData) (hD : IsTimeFieldData D) {κ : FieldKey}
    (hκ : κ ∈ D.keys) (σ τ φ : ℝ) (y a b : Space) :
    keyHess P κ (D.amp κ) (σ + τ) (axialRot φ y) (axialRot φ a) (axialRot φ b) =
      phaseRotVec (keyAngle P.azimuthOrder κ τ φ) φ (keyHess P κ (D.amp κ) σ y a b) :=
  SecondDerivFlip.secondDeriv_of_equiv_conj (rotEquiv φ) (phaseRotEquiv (keyAngle P.azimuthOrder κ τ φ) φ) _ _
    (keyVector_shift_rot P D hD hκ σ τ φ) y a b

theorem realPartVec_apply (v : Fin 3 → ℂ) (i : Fin 3) : realPartVec v i = (v i).re := by
  simp [realPartVec]

theorem rot_realPart (θ φ : ℝ) (w : Fin 3 → ℂ) (i : Fin 3) :
    axialRot (-φ) (realPartVec (phaseRotVec θ φ w)) i = (Complex.exp ((θ : ℂ) * Complex.I) * w i).re := by
  have h1 := Real.cos_sq_add_sin_sq φ
  fin_cases i
  · show axialRot (-φ) (realPartVec (phaseRotVec θ φ w)) 0 = (Complex.exp ((θ : ℂ) * Complex.I) * w 0).re
    rw [rot_apply_zero, realPartVec_apply, realPartVec_apply]
    simp [phaseRotVec, rotateVec, Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    linear_combination (Real.cos θ * (w 0).re - Real.sin θ * (w 0).im) * h1
  · show axialRot (-φ) (realPartVec (phaseRotVec θ φ w)) 1 = (Complex.exp ((θ : ℂ) * Complex.I) * w 1).re
    rw [rot_apply_one, realPartVec_apply, realPartVec_apply]
    simp [phaseRotVec, rotateVec, Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    linear_combination (Real.cos θ * (w 1).re - Real.sin θ * (w 1).im) * h1
  · show axialRot (-φ) (realPartVec (phaseRotVec θ φ w)) 2 = (Complex.exp ((θ : ℂ) * Complex.I) * w 2).re
    rw [rot_apply_two, realPartVec_apply]
    simp [phaseRotVec, rotateVec]

theorem shapeSecondDeriv_apply (P : ShapeParams) (D : TimeFieldData) (σ : ℝ) (y a b : Space) :
    shapeHess P D σ y a b = ∑ κ ∈ D.keys, realPartVec (keyHess P κ (D.amp κ) σ y a b) := by
  simp [shapeHess]

theorem space_sum_apply {α : Type*} (s : Finset α) (v : α → Space) (i : Fin 3) :
    (∑ a ∈ s, v a) i = ∑ a ∈ s, v a i := by
  simp

theorem axialRot_sum {α : Type*} (φ : ℝ) (s : Finset α) (v : α → Space) :
    axialRot φ (∑ a ∈ s, v a) = ∑ a ∈ s, axialRot φ (v a) := by
  simp only [← rotEquiv_apply, map_sum]

theorem re_half_add_conj_half (w : ℂ) : (w / 2).re + (starRingEnd ℂ w / 2).re = w.re := by
  simp

theorem secondDeriv_integrand (P : ShapeParams) (D : TimeFieldData) (hD : IsTimeFieldData D) (σ : ℝ) (y : Space)
    (τ φ : ℝ) (ijl : Fin 3 × Fin 3 × Fin 3) :
    axialRot (-φ) (shapeHess P D (σ + τ) (axialRot φ y) (axialRot φ (unitVector ijl.2.1))
      (axialRot φ (unitVector ijl.2.2))) ijl.1 = ∑ κ ∈ D.keys,
      (Complex.exp (((2 * Real.pi * (((labelHarmonic P.azimuthOrder κ.label).1) : ℝ) * τ +
        (((labelHarmonic P.azimuthOrder κ.label).2) : ℝ) * φ : ℝ) : ℂ) * Complex.I) *
        keyHess P κ (D.amp κ) σ y (unitVector ijl.2.1) (unitVector ijl.2.2) ijl.1).re := by
  rw [shapeSecondDeriv_apply, axialRot_sum, space_sum_apply]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  rw [keySecondDeriv_shift_rot P D hD hκ, rot_realPart]
  rfl

theorem secondDerivSpan (P : ShapeParams) (D : TimeFieldData) (S : Finset (ℤ × ℤ)) (hD : IsTimeFieldData D)
    (hS : harmonicsOf P.azimuthOrder D ⊆ S) (hSy : ∀ β ∈ S, -β ∈ S) (σ : ℝ) (y : Space) (i j l : Fin 3) :
    shapeHess P D σ y (unitVector j) (unitVector l) i =
      ∑ β ∈ S, (modeSecondDeriv β (shapeHess P D) σ y (i, j, l)).re := by
  have hM : ∀ β, modeSecondDeriv β (shapeHess P D) σ y (i, j, l) = ∑ κ ∈ D.keys,
      ((if β = labelHarmonic P.azimuthOrder κ.label then
          keyHess P κ (D.amp κ) σ y (unitVector j) (unitVector l) i / 2 else 0) +
        (if β = -labelHarmonic P.azimuthOrder κ.label then
          starRingEnd ℂ (keyHess P κ (D.amp κ) σ y (unitVector j) (unitVector l) i) / 2 else 0)) :=
    fun β => congrFun (modeSecondDeriv_of_waveSum D.keys (fun κ => labelHarmonic P.azimuthOrder κ.label)
      (fun κ ijl => keyHess P κ (D.amp κ) σ y (unitVector ijl.2.1) (unitVector ijl.2.2) ijl.1)
      (shapeHess P D) σ y (secondDeriv_integrand P D hD σ y) β) (i, j, l)
  simp only [hM, Complex.re_sum]
  rw [Finset.sum_comm, shapeSecondDeriv_apply, space_sum_apply]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  have hν : labelHarmonic P.azimuthOrder κ.label ∈ S := hS (Finset.mem_image_of_mem _ hκ)
  have hν' := hSy _ hν
  simp only [Complex.add_re, Finset.sum_add_distrib, apply_ite Complex.re, Complex.zero_re,
    Finset.sum_ite_eq', if_pos hν, if_pos hν', realPartVec_apply]
  exact (re_half_add_conj_half _).symm

end SecondDerivExpand

end Internal

theorem fieldHarmonicExpansion_of_spans
    (hF : ∀ (P : ShapeParams) (D : TimeFieldData) (S : Finset (ℤ × ℤ)), IsShapeParams P → IsTimeFieldData D →
      harmonicsOf P.azimuthOrder D ⊆ S → (∀ β ∈ S, -β ∈ S) →
        (∀ σ y i, shapeInfoField P D σ y i = ∑ β ∈ S, (modeVel β (shapeInfoField P D) σ y i).re) ∧
        ∀ σ y i j, fderiv ℝ (shapeInfoField P D σ) y (unitVector j) i =
          ∑ β ∈ S, (modeGrad β (gradField (shapeInfoField P D)) σ y (i, j)).re) :
    FieldHarmonicExpansion := by
  intro P D S hP hD hS hSy
  obtain ⟨hf, hg⟩ := hF P D S hP hD hS hSy
  exact ⟨hSy, hf, hg, fun σ y i j l => Internal.SecondDerivExpand.secondDerivSpan P D S hD hS hSy σ y i j l⟩

theorem secondDerivSpan_of_keys (P : ShapeParams) (D : TimeFieldData) (S : Finset (ℤ × ℤ)) (hD : IsTimeFieldData D)
    (hS : harmonicsOf P.azimuthOrder D ⊆ S) (hSy : ∀ β ∈ S, -β ∈ S) :
    ∀ σ y i j l, shapeHess P D σ y (unitVector j) (unitVector l) i =
      ∑ β ∈ S, (modeSecondDeriv β (shapeHess P D) σ y (i, j, l)).re :=
  fun σ y i j l => Internal.SecondDerivExpand.secondDerivSpan P D S hD hS hSy σ y i j l

end GivenShape

end CertCell

end Breakdown
