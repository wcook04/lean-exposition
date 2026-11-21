import Breakdown.CertCell.BridgeStatements

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

private lemma flipPoint_coord (y : Space) (i : Fin 3) : flipPoint y i = frameSign i * y i := by
  fin_cases i <;> simp [flipPoint, frameSign, unitVector]

private lemma frameSign_zero : frameSign 0 = 1 := by simp [frameSign]

private lemma frameSign_one : frameSign 1 = -1 := by simp [frameSign]

private lemma frameSign_two : frameSign 2 = -1 := by simp [frameSign]

private lemma frameSign_mul_self (a : Fin 3) : frameSign a * frameSign a = 1 := by
  unfold frameSign
  split_ifs <;> norm_num

private lemma flipPoint_unitVector (j : Fin 3) : unitVector j = frameSign j • flipPoint (unitVector j) := by
  ext i
  rw [PiLp.smul_apply, flipPoint_coord, smul_eq_mul, ← mul_assoc]
  fin_cases j <;> fin_cases i <;> simp [unitVector, frameSign_zero, frameSign_one, frameSign_two]

private lemma sign_symbol_pair (i j l : Fin 3) :
    alternatingSymbol i j l * (frameSign j * frameSign l) = frameSign i * alternatingSymbol i j l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol, frameSign]

private def flipMap : Space →L[ℝ] Space :=
  (EuclideanSpace.proj (0 : Fin 3)).smulRight (unitVector 0)
    - (EuclideanSpace.proj (1 : Fin 3)).smulRight (unitVector 1)
    - (EuclideanSpace.proj (2 : Fin 3)).smulRight (unitVector 2)

private lemma flipMap_apply (y : Space) : flipMap y = flipPoint y := by
  simp [flipMap, flipPoint]

private lemma fderiv_flip (W : Space → Space) (hW : Differentiable ℝ W)
    (hF : ∀ y, W (flipPoint y) = flipPoint (W y)) (y a : Space) :
    fderiv ℝ W (flipPoint y) (flipPoint a) = flipPoint (fderiv ℝ W y a) := by
  have hc : W ∘ flipMap = flipMap ∘ W := by
    funext x
    simp only [Function.comp_apply, flipMap_apply, hF]
  have h1 : fderiv ℝ (W ∘ flipMap) y = (fderiv ℝ W (flipMap y)).comp flipMap := by
    rw [fderiv_comp y (hW _) flipMap.differentiableAt, flipMap.fderiv]
  have h2 : fderiv ℝ (flipMap ∘ W) y = flipMap.comp (fderiv ℝ W y) := by
    rw [fderiv_comp y flipMap.differentiableAt (hW _), flipMap.fderiv]
  have h3 := congrArg (fun L => L a) (h1.symm.trans ((congrArg (fun f => fderiv ℝ f y) hc).trans h2))
  simpa only [ContinuousLinearMap.comp_apply, flipMap_apply] using h3

private lemma map_unit_flip (A B : Space →L[ℝ] Space) (h : ∀ a, A (flipPoint a) = flipPoint (B a))
    (j i : Fin 3) : A (unitVector j) i = frameSign i * frameSign j * B (unitVector j) i := by
  rw [flipPoint_unitVector j, A.map_smul, h, PiLp.smul_apply, smul_eq_mul, flipPoint_coord, ← flipPoint_unitVector]
  ring

private lemma bilin_unit_flip (A B : Space →L[ℝ] Space →L[ℝ] Space)
    (h : ∀ a b, A (flipPoint a) (flipPoint b) = flipPoint (B a b)) (m a b : Fin 3) :
    A (unitVector m) (unitVector a) b
      = frameSign m * frameSign a * frameSign b * B (unitVector m) (unitVector a) b := by
  rw [flipPoint_unitVector m, flipPoint_unitVector a, A.map_smul, ContinuousLinearMap.smul_apply,
    (A (flipPoint (unitVector m))).map_smul, h, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
    flipPoint_coord, ← flipPoint_unitVector, ← flipPoint_unitVector]
  ring

private lemma curlVec_coord (A : Space →L[ℝ] Space) (i : Fin 3) :
    curlVec A i = ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * A (unitVector j) l := by
  fin_cases i <;> simp [curlVec, unitVector, Fin.sum_univ_three]

private lemma curlVec_flip (A B : Space →L[ℝ] Space) (h : ∀ a, A (flipPoint a) = flipPoint (B a)) (i : Fin 3) :
    curlVec A i = frameSign i * curlVec B i := by
  rw [curlVec_coord, curlVec_coord, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_unit_flip A B h]
  have := sign_symbol_pair i j l
  linear_combination (B (unitVector j) l) * this

private lemma vortGrad_flip (A B : Space →L[ℝ] Space →L[ℝ] Space)
    (h : ∀ a b, A (flipPoint a) (flipPoint b) = flipPoint (B a b)) (j m : Fin 3) :
    vortGrad A j m = frameSign j * frameSign m * vortGrad B j m := by
  unfold vortGrad
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [bilin_unit_flip A B h]
  have := sign_symbol_pair j a b
  linear_combination (frameSign m * B (unitVector m) (unitVector a) b) * this

theorem stretchFlip : StretchFlipHolds := by
  intro W HW hM hW v G σ y hv hG
  have hD : ∀ j i, fderiv ℝ (W σ) (flipPoint y) (unitVector j) i
      = frameSign i * frameSign j * fderiv ℝ (W σ) y (unitVector j) i :=
    map_unit_flip _ _ (fderiv_flip (W σ) (hW σ) (hM.field_flip σ) y)
  have hC : ∀ i, curlVec (G σ (flipPoint y)) i = frameSign i * curlVec (G σ y) i :=
    curlVec_flip _ _ hG
  have hGc : ∀ j i, G σ (flipPoint y) (unitVector j) i = frameSign i * frameSign j * G σ y (unitVector j) i :=
    map_unit_flip _ _ hG
  have hV : ∀ m, v σ (flipPoint y) m = frameSign m * v σ y m := fun m => by
    rw [hv, flipPoint_coord]
  have hH : ∀ j m, vortGrad (HW σ (flipPoint y)) j m = frameSign j * frameSign m * vortGrad (HW σ y) j m :=
    vortGrad_flip _ _ (hM.hessian_flip σ y)
  unfold CoerciveWeak.stretchFormWith
  simp only [hD, hC, hGc, hV, hH]
  simp only [Fin.sum_univ_three]
  simp only [frameSign_zero, frameSign_one, frameSign_two]
  norm_num [alternatingSymbol]
  ring

end Bridge

end CertCell

end Breakdown
