import Breakdown.CertCell.ShapeKeyFlip

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

namespace SecondDerivFlip

def flipPointEquiv : Space ≃L[ℝ] Space :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := flipPoint
      invFun := flipPoint
      map_add' := fun x z => by
        ext i
        fin_cases i <;> simp [(flipPoint_coords _).1, (flipPoint_coords _).2.1, (flipPoint_coords _).2.2] <;> ring
      map_smul' := fun c x => by
        ext i
        fin_cases i <;> simp [(flipPoint_coords _).1, (flipPoint_coords _).2.1, (flipPoint_coords _).2.2]
      left_inv := fun x => by
        ext i
        fin_cases i <;> simp [(flipPoint_coords _).1, (flipPoint_coords _).2.1, (flipPoint_coords _).2.2]
      right_inv := fun x => by
        ext i
        fin_cases i <;> simp [(flipPoint_coords _).1, (flipPoint_coords _).2.1, (flipPoint_coords _).2.2] }

theorem flipPointEquiv_apply (y : Space) : flipPointEquiv y = flipPoint y := rfl

def flipVecEquiv : (Fin 3 → ℂ) ≃L[ℝ] (Fin 3 → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := flipVec
      invFun := flipVec
      map_add' := fun x z => by
        ext i
        fin_cases i <;> simp [flipVec] <;> ring
      map_smul' := fun c x => by
        ext i
        fin_cases i <;> simp [flipVec]
      left_inv := fun x => by
        ext i
        fin_cases i <;> simp [flipVec]
      right_inv := fun x => by
        ext i
        fin_cases i <;> simp [flipVec] }

theorem flipVecEquiv_apply (w : Fin 3 → ℂ) : flipVecEquiv w = flipVec w := rfl

theorem realPartVec_flipVec (w : Fin 3 → ℂ) : realPartVec (flipVec w) = flipPoint (realPartVec w) := by
  ext i
  fin_cases i <;> simp [realPartVec, flipVec, (flipPoint_coords _).1, (flipPoint_coords _).2.1,
    (flipPoint_coords _).2.2]

theorem secondDeriv_of_equiv_conj {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : Space ≃L[ℝ] Space) (V : W ≃L[ℝ] W) (f g : Space → W) (h : ∀ x, f (F x) = V (g x))
    (y a b : Space) : fderiv ℝ (fderiv ℝ f) (F y) (F a) (F b) = V (fderiv ℝ (fderiv ℝ g) y a b) := by
  have hf : f = ((V : W → W) ∘ g) ∘ (F.symm : Space → Space) := by
    funext z
    simpa using h (F.symm z)
  have hd : fderiv ℝ f = (F.arrowCongr V : (Space →L[ℝ] W) → (Space →L[ℝ] W)) ∘ fderiv ℝ g ∘
      (F.symm : Space → Space) := by
    funext z
    rw [hf, F.symm.comp_right_fderiv, V.comp_fderiv]
    ext v
    simp
  rw [hd, ← Function.comp_assoc, F.symm.comp_right_fderiv, (F.arrowCongr V).comp_fderiv]
  simp

theorem keySecondDeriv_flip (hK : KeyFlip) (P : ShapeParams) (D : TimeFieldData) (hD : IsTimeFieldData D)
    {κ : FieldKey} (hκ : κ ∈ D.keys) (σ : ℝ) (y a b : Space) :
    keyHess P κ (D.amp κ) σ (flipPoint y) (flipPoint a) (flipPoint b) =
      flipVec (keyHess P κ.flipKey (D.amp κ.flipKey) σ y a b) := by
  have hκ' : κ.flipKey ∈ D.keys := (hD.keys_flip κ).1 hκ
  have hkk : κ.flipKey.flipKey = κ := by
    obtain ⟨l, p⟩ := κ
    simp [FieldKey.flipKey, labelFlip]
  have h : ∀ x, keyVector P κ (D.amp κ) σ (flipPointEquiv x) =
      flipVecEquiv (keyVector P κ.flipKey (D.amp κ.flipKey) σ x) := by
    intro x
    have := hK P D κ.flipKey σ x hD hκ'
    rw [hkk] at this
    exact this
  exact secondDeriv_of_equiv_conj flipPointEquiv flipVecEquiv _ _ h y a b

end SecondDerivFlip

end Internal

open Internal Internal.SecondDerivFlip in
theorem fieldSecondDerivFlip_of_keyFlip (hK : KeyFlip) : FieldHessFlip := by
  intro P D _ hD σ y a b
  have hkk : ∀ κ : FieldKey, κ.flipKey.flipKey = κ := by
    intro κ
    obtain ⟨l, p⟩ := κ
    simp [FieldKey.flipKey, labelFlip]
  unfold shapeHess
  simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]
  rw [Finset.sum_congr rfl (fun κ hκ => by rw [keySecondDeriv_flip hK P D hD hκ σ y a b, realPartVec_flipVec])]
  rw [← flipPointEquiv_apply, map_sum]
  simp only [flipPointEquiv_apply]
  exact Finset.sum_nbij' FieldKey.flipKey FieldKey.flipKey (fun κ hκ => (hD.keys_flip κ).1 hκ)
    (fun κ hκ => (hD.keys_flip κ).1 hκ) (fun κ _ => hkk κ) (fun κ _ => hkk κ) (fun κ _ => rfl)

theorem fieldSecondDerivFlip_holds : FieldHessFlip :=
  fieldSecondDerivFlip_of_keyFlip keyFlip_holds

end GivenShape

end CertCell

end Breakdown
