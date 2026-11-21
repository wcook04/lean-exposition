import Breakdown.CertCell.AssemblyPotentialModelTorusMean

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open CellCert.CellAnalysis Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation
  Coercive.StretchInternal

def ModelFieldFrameStatement : Prop :=
  ∀ (M : CellMesh) (F : CellMatField M.count) (m : ℕ) (K : Fin M.count), IsCellMesh M →
    F.IsConjugateClosed M.box →
    ∀ᵐ p ∂(volume.restrict (M.box K).rect), ∀ τ φ : ℝ, ∀ a b : Fin 3,
      ((fibGrad (F.field M.box m) (planePoint p) τ φ a b : ℝ) : ℂ)
        = ∑ α ∈ F.labels K, labelPhase m α τ φ * F.planeValue M.box K α a b p

def StrainFrameStatement : Prop :=
  ∀ (A : Space →L[ℝ] Space) (φ : ℝ) (a b : Fin 3),
    axialRot (-φ) (((1 / 2 : ℝ) • (A + ContinuousLinearMap.adjoint A)) (axialRot φ (unitVector b))) a
      = (axialRot (-φ) (A (axialRot φ (unitVector b))) a + axialRot (-φ) (A (axialRot φ (unitVector a))) b) / 2

def VorticityGradFrameStatement : Prop :=
  ∀ (B : Space →L[ℝ] Space →L[ℝ] Space), (∀ u w, B u w = B w u) → ∀ (φ : ℝ) (j l : Fin 3),
    axialRot (-φ) (CoerciveWeak.vortGradMap B (axialRot φ (unitVector l))) j
      = curlGradReal (fun i j' l' => axialRot (-φ) (B (axialRot φ (unitVector j')) (axialRot φ (unitVector l'))) i) j l

def RotatedBoundStatement : Prop :=
  ∀ (A : Space →L[ℝ] Space) (φ : ℝ) (u : Fin 3 → ℂ),
    cnormSq (fun a => ∑ b : Fin 3, ((axialRot (-φ) (A (axialRot φ (unitVector b))) a : ℝ) : ℂ) * u b)
      ≤ ‖A‖ ^ 2 * cnormSq u

def OrbitSolidStatement : Prop :=
  ∀ (K : CellBox) (p : ℝ × ℝ) (φ : ℝ), IsCellBox K → p ∈ K.rect → axialRot φ (planePoint p) ∈ K.solid

def GradSectionStatement : Prop :=
  ∀ (F : ℝ → Space → (Space →L[ℝ] Space)), AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume →
    ∀ K : CellBox, IsCellBox K →
      (∀ᵐ p ∂(volume.restrict K.rect), ∀ a b : Fin 3,
        AEStronglyMeasurable (fun z : ℝ × ℝ => fibGrad F (planePoint p) z.1 z.2 a b) boxMeasure) ∧
      ∀ (m : ℕ) (ι : ℤ × ℤ) (ab : Fin 3 × Fin 3),
        AEStronglyMeasurable (fun p => labelGrad m ι F p ab) (volume.restrict K.rect)

def SecondDerivSectionStatement : Prop :=
  ∀ (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)), AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume →
    ∀ K : CellBox, IsCellBox K →
      (∀ᵐ p ∂(volume.restrict K.rect), ∀ a b c : Fin 3,
        AEStronglyMeasurable (fun z : ℝ × ℝ => frameSecondDeriv H (planePoint p) z.1 z.2 a b c) boxMeasure) ∧
      ∀ (m : ℕ) (ι : ℤ × ℤ) (abc : Fin 3 × Fin 3 × Fin 3),
        AEStronglyMeasurable (fun p => labelHess m ι H p abc) (volume.restrict K.rect)

def GivenExpansionStatement : Prop :=
  ∀ (S : Finset (ℤ × ℤ)) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (B : ℝ),
    Bridge.IsHarmonicExpansion S W HW → CoerciveWeak.IsWeakSecondDerivState W HW B → ∀ K : CellBox, IsCellBox K →
      (∀ (y : Space) (τ φ : ℝ) (a b : Fin 3),
        ((fibGrad (gradField W) y τ φ a b : ℝ) : ℂ) = ∑ β ∈ S, phase β τ φ * modeGrad β (gradField W) 0 y (a, b)) ∧
      ∀ᵐ p ∂(volume.restrict K.rect), ∀ (τ φ : ℝ) (a b c : Fin 3),
        ((frameSecondDeriv HW (planePoint p) τ φ a b c : ℝ) : ℂ)
          = ∑ β ∈ S, phase β τ φ * modeSecondDeriv β HW 0 (planePoint p) (a, b, c)

structure FrameFacts : Prop where
  model_field : ModelFieldFrameStatement
  strain : StrainFrameStatement
  vorticity_grad : VorticityGradFrameStatement
  rotated_bound : RotatedBoundStatement
  orbit_solid : OrbitSolidStatement
  grad_section : GradSectionStatement
  secondDeriv_section : SecondDerivSectionStatement
  given_expansion : GivenExpansionStatement

end Internal

end Assembly

end CertCell

end Breakdown
