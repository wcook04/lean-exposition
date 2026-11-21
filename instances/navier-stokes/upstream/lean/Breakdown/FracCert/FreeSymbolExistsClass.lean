import Breakdown.FracCert.FreeSymbolExistsEquation
import Breakdown.Frac.NNiceField

open scoped ContDiff ENNReal FourierTransform
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace FreeSymbolClassInternal

open FreeSymbolEquationInternal

theorem transform_clm (L : Freq.CSpace ≃L[ℂ] Freq.CSpace) (f : Space → Freq.CSpace) (ξ : Space) :
    𝓕 (fun x => L (f x)) ξ = L (𝓕 f ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq, ← L.integral_comp_comm]
  congr 1
  funext v
  rw [Circle.smul_def, Circle.smul_def, L.map_smul]

theorem inverseTransform_clm (L : Freq.CSpace ≃L[ℂ] Freq.CSpace) (f : Space → Freq.CSpace) (ξ : Space) :
    𝓕⁻ (fun x => L (f x)) ξ = L (𝓕⁻ f ξ) := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq, ← L.integral_comp_comm]
  congr 1
  funext v
  rw [Circle.smul_def, Circle.smul_def, L.map_smul]

structure Compatible (T : Space ≃ₗᵢ[ℝ] Space) (TC : Freq.CSpace ≃L[ℂ] Freq.CSpace) : Prop where
  rot : ∀ θ y, T (axialRotationFormula θ y) = axialRotationFormula θ (T y)
  rotC : ∀ θ z, TC (axialRotationC θ z) = axialRotationC θ (TC z)
  re : ∀ z, Freq.realVec (TC z) = T (Freq.realVec z)
  cx : ∀ y, Freq.complexifyVec (T y) = TC (Freq.complexifyVec y)

theorem symbol_equiv {T : Space ≃ₗᵢ[ℝ] Space} {TC : Freq.CSpace ≃L[ℂ] Freq.CSpace} (hT : Compatible T TC)
    {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s)
    (hN : ∀ y, Freq.niceField s (T y) = T (Freq.niceField s y)) (ξ : Space) : s (T ξ) = TC (s ξ) := by
  have hF := FracInternal.NiceField.transform_fieldS hs
  rw [FracInternal.NiceField.fieldS_coe] at hF
  rw [← hF, ← Real.fourier_comp_linearIsometry]
  have e : ((fun x => Freq.complexifyVec (Freq.niceField s x)) ∘ T) =
      fun x => TC (Freq.complexifyVec (Freq.niceField s x)) := by
    funext x
    simp only [Function.comp_apply, hN, hT.cx]
  rw [e, transform_clm]

theorem solution_equiv {T : Space ≃ₗᵢ[ℝ] Space} {TC : Freq.CSpace ≃L[ℂ] Freq.CSpace} (hT : Compatible T TC)
    (α a : ℝ) {s : Space → Freq.CSpace} (hsT : ∀ η, s (T η) = TC (s η)) (ξ : Space) :
    freeSolution α a s (T ξ) = TC (freeSolution α a s ξ) := by
  unfold freeSolution
  rw [← TC.integral_comp_comm]
  congr 1
  funext τ
  have hw : freeWeight α τ (T ξ) = freeWeight α τ ξ := by simp [freeWeight, freqPow]
  rw [hw, ← hT.rot, ← T.map_smul, hsT, ← hT.rotC]
  exact ((TC : Freq.CSpace →L[ℂ] Freq.CSpace).map_smul_of_tower _ _).symm

theorem field_equiv {T : Space ≃ₗᵢ[ℝ] Space} {TC : Freq.CSpace ≃L[ℂ] Freq.CSpace} (hT : Compatible T TC)
    {w : Space → Freq.CSpace} (hwT : ∀ ξ, w (T ξ) = TC (w ξ)) (y : Space) :
    Freq.niceField w (T y) = T (Freq.niceField w y) := by
  unfold Freq.niceField
  rw [← Real.fourierInv_comp_linearIsometry]
  have e : (w ∘ T) = fun x => TC (w x) := funext hwT
  rw [e, inverseTransform_clm, hT.re]

def rotLin (θ : ℝ) : Space →ₗ[ℝ] Space where
  toFun := axialRotationFormula θ
  map_add' x y := by ext i; fin_cases i <;> simp [axialRotationFormula] <;> ring
  map_smul' c x := rot_smul' θ c x

def rotIso (θ : ℝ) : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv ⟨rotLin θ, FreeSymbolSmoothInternal.rot_norm' θ⟩ rfl

def mirrorLin : Space →ₗ[ℝ] Space where
  toFun := mirror
  map_add' x y := by ext i; fin_cases i <;> simp [mirror] <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp [mirror]

theorem mirror_norm (y : Space) : ‖mirror y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, mirror]

def mirrorIso : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv ⟨mirrorLin, mirror_norm⟩ rfl

def rotCLE (θ : ℝ) : Freq.CSpace ≃L[ℂ] Freq.CSpace :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := axialRotationC θ
      invFun := axialRotationC (-θ)
      map_add' := fun x y => by ext i; fin_cases i <;> simp [axialRotationC] <;> ring
      map_smul' := fun c x => by ext i; fin_cases i <;> simp [axialRotationC] <;> ring
      left_inv := fun z => by simp only [rotC_rotC, neg_add_cancel, rotC_zero']
      right_inv := fun z => by simp only [rotC_rotC, add_neg_cancel, rotC_zero'] }

def mirrorC (z : Freq.CSpace) : Freq.CSpace :=
  EuclideanSpace.single 0 (z 0) + EuclideanSpace.single 1 (z 1) + EuclideanSpace.single 2 (-(z 2))

def mirrorCLE : Freq.CSpace ≃L[ℂ] Freq.CSpace :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := mirrorC
      invFun := mirrorC
      map_add' := fun x y => by ext i; fin_cases i <;> simp [mirrorC] <;> ring
      map_smul' := fun c x => by ext i; fin_cases i <;> simp [mirrorC]
      left_inv := fun z => by ext i; fin_cases i <;> simp [mirrorC]
      right_inv := fun z => by ext i; fin_cases i <;> simp [mirrorC] }

theorem turn_compatible (m : ℕ) :
    Compatible (rotIso (2 * Real.pi / m)) (rotCLE (2 * Real.pi / m)) where
  rot θ y := by
    change axialRotationFormula (2 * Real.pi / m) (axialRotationFormula θ y) =
      axialRotationFormula θ (axialRotationFormula (2 * Real.pi / m) y)
    rw [rot_rot, rot_rot, add_comm]
  rotC θ z := by
    change axialRotationC (2 * Real.pi / m) (axialRotationC θ z) =
      axialRotationC θ (axialRotationC (2 * Real.pi / m) z)
    rw [rotC_rotC, rotC_rotC, add_comm]
  re z := by
    change Freq.realVec (axialRotationC (2 * Real.pi / m) z) = axialRotationFormula (2 * Real.pi / m) (Freq.realVec z)
    ext i
    fin_cases i <;> simp [Freq.realVec, axialRotationC, axialRotationFormula, -Complex.ofReal_cos,
      -Complex.ofReal_sin]
  cx y := by
    change Freq.complexifyVec (axialRotationFormula (2 * Real.pi / m) y) =
      axialRotationC (2 * Real.pi / m) (Freq.complexifyVec y)
    ext i
    fin_cases i <;> simp [Freq.complexifyVec, axialRotationC, axialRotationFormula, -Complex.ofReal_cos,
      -Complex.ofReal_sin]

theorem mirror_compatible : Compatible mirrorIso mirrorCLE where
  rot θ y := by
    change mirror (axialRotationFormula θ y) = axialRotationFormula θ (mirror y)
    ext i
    fin_cases i <;> simp [mirror, axialRotationFormula]
  rotC θ z := by
    change mirrorC (axialRotationC θ z) = axialRotationC θ (mirrorC z)
    ext i
    fin_cases i <;> simp [mirrorC, axialRotationC]
  re z := by
    change Freq.realVec (mirrorC z) = mirror (Freq.realVec z)
    ext i
    fin_cases i <;> simp [Freq.realVec, mirrorC, mirror]
  cx y := by
    change Freq.complexifyVec (mirror y) = mirrorC (Freq.complexifyVec y)
    ext i
    fin_cases i <;> simp [Freq.complexifyVec, mirrorC, mirror]

theorem solution_class {α a : ℝ} {m : ℕ} {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s)
    (hcls : IsClassField m (Freq.niceField s)) : IsClassField m (Freq.niceField (freeSolution α a s)) := by
  obtain ⟨h1, h2⟩ := hcls
  have hNc : Continuous (Freq.niceField s) := by
    rw [← FracInternal.NiceField.fieldS_coe hs]
    exact (FracInternal.NiceField.fieldS hs).continuous
  have e1 : ∀ y, Freq.niceField s (rotIso (2 * Real.pi / m) y) =
      rotIso (2 * Real.pi / m) (Freq.niceField s y) := by
    have h := (Continuous.ae_eq_iff_eq volume (hNc.comp (rotIso (2 * Real.pi / m)).continuous)
      ((rotIso (2 * Real.pi / m)).continuous.comp hNc)).1 h1
    exact fun y => congrFun h y
  have e2 : ∀ y, Freq.niceField s (mirrorIso y) =
      mirrorIso (Freq.niceField s y) := by
    have h := (Continuous.ae_eq_iff_eq volume (hNc.comp mirrorIso.continuous)
      (mirrorIso.continuous.comp hNc)).1 h2
    exact fun y => congrFun h y
  refine ⟨Filter.Eventually.of_forall fun y => ?_, Filter.Eventually.of_forall fun y => ?_⟩
  · exact field_equiv (turn_compatible m)
      (solution_equiv (turn_compatible m) α a (symbol_equiv (turn_compatible m) hs e1)) y
  · exact field_equiv mirror_compatible
      (solution_equiv mirror_compatible α a (symbol_equiv mirror_compatible hs e2)) y

end FreeSymbolClassInternal

theorem freeSolutionClass : FreeSolutionClassStatement := fun _ _ _ _ _ _ hs hcls =>
  FreeSymbolClassInternal.solution_class hs hcls

end SteadyCert

end Breakdown
