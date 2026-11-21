import Breakdown.FracCert.StWeak
import Breakdown.Frac.NNiceField

open MeasureTheory Set Real
open scoped ENNReal ContDiff SchwartzMap FourierTransform

noncomputable section


namespace Breakdown.FracInternal.NiceDrift

open Freq Breakdown.FracInternal.NiceField

def turnC : CSpace →L[ℂ] CSpace :=
  (EuclideanSpace.proj 1 : CSpace →L[ℂ] ℂ).smulRight (-(EuclideanSpace.single 0 1 : CSpace)) +
    (EuclideanSpace.proj 0 : CSpace →L[ℂ] ℂ).smulRight (EuclideanSpace.single 1 1 : CSpace)

theorem turnC_0 (z : CSpace) : turnC z 0 = -z 1 := by simp [turnC]
theorem turnC_1 (z : CSpace) : turnC z 1 = z 0 := by simp [turnC]
theorem turnC_2 (z : CSpace) : turnC z 2 = 0 := by simp [turnC]

theorem realVec_turnC (z : CSpace) : realVec (turnC z) = axialTurn (realVec z) := by
  ext i
  fin_cases i <;> simp [turnC, axialTurn, realVec]

theorem conjVec_turnC (z : CSpace) : conjVec (turnC z) = turnC (conjVec z) := by
  ext i
  fin_cases i <;> simp [turnC, conjVec]

theorem invTransform_postcomp (L : CSpace →L[ℂ] CSpace) (f : 𝓢(Space, CSpace)) (x : Space) :
    (𝓕⁻ (SchwartzMap.postcompCLM L f)) x = L ((𝓕⁻ f) x) := by
  have e1 : ∀ g : 𝓢(Space, CSpace), (𝓕⁻ g) x = (𝓕 g) (-x) := fun g => by
    rw [SchwartzMap.fourierInv_apply_eq]
    rfl
  rw [e1, e1, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have e2 : ⇑(SchwartzMap.postcompCLM L f) = fun v => L (f v) :=
    funext fun v => SchwartzMap.postcompCLM_apply _ _ _
  rw [e2, transform_clm_apply]

theorem temperate (j : Fin 3) : (fun x : Space => inner ℝ x (unitVector j)).HasTemperateGrowth :=
  ((innerSL ℝ).flip (unitVector j)).hasTemperateGrowth

def coordMul (j : Fin 3) (S : 𝓢(Space, CSpace)) : 𝓢(Space, CSpace) :=
  SchwartzMap.smulLeftCLM CSpace (fun x : Space => inner ℝ x (unitVector j)) S

theorem coordMul_apply (j : Fin 3) (S : 𝓢(Space, CSpace)) (ξ : Space) :
    coordMul j S ξ = inner ℝ ξ (unitVector j) • S ξ :=
  SchwartzMap.smulLeftCLM_apply_apply (temperate j) S ξ

theorem inner_unit (y : Space) (j : Fin 3) : inner ℝ y (unitVector j) = y j := by
  simp [unitVector, EuclideanSpace.inner_single_right]

theorem mul_lineDeriv (S : 𝓢(Space, CSpace)) (j k : Fin 3) (y : Space) :
    (𝓕⁻ (LineDeriv.lineDerivOp (unitVector k) (coordMul j S))) y =
      -((y k) • (LineDeriv.lineDerivOp (unitVector j) (𝓕⁻ S)) y) := by
  rw [SchwartzMap.lineDerivOp_fourierInv_eq, SchwartzMap.fourierInv_lineDerivOp_eq,
    FourierTransform.fourierInv_smul, smul_apply, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply (temperate k), inner_unit]
  rw [coordMul, neg_smul, smul_comm (2 * (π : ℂ) * Complex.I)]

end Breakdown.FracInternal.NiceDrift

namespace Breakdown.FracInternal.NiceDrift

open Freq Breakdown.FracInternal.NiceField

theorem fderiv_realVec (A : 𝓢(Space, CSpace)) (y v : Space) :
    fderiv ℝ (fun x => realVec (A x)) y v = realVec (LineDeriv.lineDerivOp v A y) := by
  have h : HasFDerivAt (fun x => realVec (A x)) (realVec.comp (fderiv ℝ A y)) y :=
    realVec.hasFDerivAt.comp y (A.differentiableAt.hasFDerivAt)
  rw [h.fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

theorem vec_expand (y : Space) : y = ∑ j : Fin 3, y j • unitVector j := by
  ext i
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem turn_expand (y : Space) :
    axialTurn y = (-(y 1)) • unitVector 0 + (y 0) • unitVector 1 := by
  ext i
  fin_cases i <;> simp [unitVector, axialTurn]

theorem lineDeriv_self (A : 𝓢(Space, CSpace)) (y : Space) :
    LineDeriv.lineDerivOp y A y = ∑ j : Fin 3, y j • LineDeriv.lineDerivOp (unitVector j) A y := by
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  calc fderiv ℝ A y y = fderiv ℝ A y (∑ j : Fin 3, y j • unitVector j) := by rw [← vec_expand y]
    _ = _ := by simp [map_sum, map_smul]

theorem lineDeriv_turn (A : 𝓢(Space, CSpace)) (y : Space) :
    LineDeriv.lineDerivOp (axialTurn y) A y =
      (-(y 1)) • LineDeriv.lineDerivOp (unitVector 0) A y +
        (y 0) • LineDeriv.lineDerivOp (unitVector 1) A y := by
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [turn_expand, map_add, map_smul, map_smul]

def invTransformCLM : 𝓢(Space, CSpace) →L[ℂ] 𝓢(Space, CSpace) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := Space))) ∘L
    (SchwartzMap.fourierTransformCLM ℂ)

theorem invTransform_eq (f : 𝓢(Space, CSpace)) : 𝓕⁻ f = invTransformCLM f := rfl

def driftS (α a : ℝ) (S : 𝓢(Space, CSpace)) : 𝓢(Space, CSpace) :=
  (1 - 4 * (1 / (2 * α))) • S +
    (1 / (2 * α)) • ∑ j : Fin 3, LineDeriv.lineDerivOp (unitVector j) (coordMul j S) -
    a • (LineDeriv.lineDerivOp (unitVector 1) (coordMul 0 S) -
      LineDeriv.lineDerivOp (unitVector 0) (coordMul 1 S) - SchwartzMap.postcompCLM turnC S)

theorem invTransform_driftS (α a : ℝ) (S : 𝓢(Space, CSpace)) (y : Space) :
    (𝓕⁻ (driftS α a S)) y = (1 - 4 * (1 / (2 * α))) • (𝓕⁻ S) y -
      (1 / (2 * α)) • ∑ j : Fin 3, y j • (LineDeriv.lineDerivOp (unitVector j) (𝓕⁻ S) : 𝓢(Space, CSpace)) y -
      a • ((-(y 1)) • (LineDeriv.lineDerivOp (unitVector 0) (𝓕⁻ S) : 𝓢(Space, CSpace)) y +
        (y 0) • (LineDeriv.lineDerivOp (unitVector 1) (𝓕⁻ S) : 𝓢(Space, CSpace)) y - turnC ((𝓕⁻ S) y)) := by
  rw [invTransform_eq]
  simp only [driftS, Fin.sum_univ_three, map_add, map_sub, ContinuousLinearMap.map_smul_of_tower, add_apply, sub_apply,
    smul_apply]
  simp only [← invTransform_eq, mul_lineDeriv, invTransform_postcomp]
  module

theorem drift_eq (α a : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) :
    FracCert.driftAdjoint α a (niceField m) = niceField ⇑(driftS α a (symbolS hm)) := by
  funext y
  have hφ : niceField m = fun x => realVec ((𝓕⁻ (symbolS hm)) x) := by
    funext x
    rw [SchwartzMap.fourierInv_coe, symbolS_coe]
    rfl
  have hT : niceField ⇑(driftS α a (symbolS hm)) y = realVec ((𝓕⁻ (driftS α a (symbolS hm))) y) := by
    rw [SchwartzMap.fourierInv_coe]
    rfl
  rw [hT, invTransform_driftS, FracCert.driftAdjoint, hφ, fderiv_realVec, fderiv_realVec,
    lineDeriv_self, lineDeriv_turn]
  simp only [map_sub, map_add, map_smul, map_sum, realVec_turnC]

end Breakdown.FracInternal.NiceDrift

namespace Breakdown.FracInternal.NiceDrift

open Freq Breakdown.FracInternal.NiceField

theorem lineDeriv_coordMul (S : 𝓢(Space, CSpace)) (j k : Fin 3) (ξ : Space) :
    (LineDeriv.lineDerivOp (unitVector k) (coordMul j S) : 𝓢(Space, CSpace)) ξ =
      (ξ j) • fderiv ℝ S ξ (unitVector k) + (inner ℝ (unitVector k) (unitVector j)) • S ξ := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have e : ⇑(coordMul j S) = ⇑((innerSL ℝ).flip (unitVector j)) • ⇑S :=
    funext fun x => by rw [coordMul_apply]; rfl
  have hd := (((innerSL ℝ).flip (unitVector j)).hasFDerivAt (x := ξ)).smul
    (S.differentiableAt (x := ξ)).hasFDerivAt
  rw [e, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply]
  rw [innerSL_apply_apply, innerSL_apply_apply, inner_unit]

def driftSym (α a : ℝ) (m : Space → CSpace) (ξ : Space) : CSpace :=
  (1 - 4 * (1 / (2 * α))) • m ξ +
    (1 / (2 * α)) • ∑ j : Fin 3, ((ξ j) • fderiv ℝ m ξ (unitVector j) + m ξ) -
    a • ((ξ 0) • fderiv ℝ m ξ (unitVector 1) - (ξ 1) • fderiv ℝ m ξ (unitVector 0) - turnC (m ξ))

theorem driftS_apply (α a : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) :
    ⇑(driftS α a (symbolS hm)) = driftSym α a m := by
  funext ξ
  simp only [driftS, add_apply, sub_apply, smul_apply, Fin.sum_univ_three, lineDeriv_coordMul,
    SchwartzMap.postcompCLM_apply, symbolS_coe, inner_unit]
  simp [unitVector, driftSym, Fin.sum_univ_three]

theorem driftSym_zero (α a : ℝ) {m : Space → CSpace} {ξ : Space} (hev : m =ᶠ[nhds ξ] 0) :
    driftSym α a m ξ = 0 := by
  have h0 : m ξ = 0 := hev.eq_of_nhds
  have h1 : fderiv ℝ m ξ = 0 := by
    rw [hev.fderiv_eq]
    simp
  simp [driftSym, h0, h1]

theorem fderiv_neg_conj {m : Space → CSpace} (hm : IsNiceSymbol m) (ξ v : Space) :
    fderiv ℝ m (-ξ) v = -conjVec (fderiv ℝ m ξ v) := by
  have hd : Differentiable ℝ m := hm.1.differentiable (by simp)
  have h1 : HasFDerivAt (fun x => m (-x)) ((fderiv ℝ m (-ξ)).comp (-ContinuousLinearMap.id ℝ Space)) ξ :=
    (hd (-ξ)).hasFDerivAt.comp ξ ((-ContinuousLinearMap.id ℝ Space).hasFDerivAt)
  have h2 : HasFDerivAt (fun x => conjVec (m x)) (conjVec.comp (fderiv ℝ m ξ)) ξ :=
    conjVec.hasFDerivAt.comp ξ (hd ξ).hasFDerivAt
  have e : (fun x => m (-x)) = fun x => conjVec (m x) := funext hm.2.2.2.1
  rw [e] at h1
  have h3 := congrArg (fun L : Space →L[ℝ] CSpace => L (-v)) (h1.unique h2)
  simpa using h3

theorem driftSym_conj (α a : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) (ξ : Space) :
    driftSym α a m (-ξ) = conjVec (driftSym α a m ξ) := by
  simp only [driftSym, fderiv_neg_conj hm, hm.2.2.2.1, map_add, map_sub, map_smul, map_sum,
    conjVec_turnC]
  simp only [PiLp.neg_apply, neg_smul_neg]

theorem div_deriv {m : Space → CSpace} (hm : IsNiceSymbol m) (ξ v : Space) :
    ∑ i : Fin 3, (((v i : ℝ) : ℂ) * m ξ i + ((ξ i : ℝ) : ℂ) * fderiv ℝ m ξ v i) = 0 := by
  have hd : Differentiable ℝ m := hm.1.differentiable (by simp)
  have hc : ∀ i : Fin 3, HasFDerivAt (fun x : Space => ((x i : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ)) ξ := fun i =>
    (Complex.ofRealCLM.comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ)).hasFDerivAt
  have hm' : ∀ i : Fin 3, HasFDerivAt (fun x => m x i)
      (((EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).restrictScalars ℝ).comp (fderiv ℝ m ξ)) ξ := fun i =>
    ((EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp ξ (hd ξ).hasFDerivAt
  have hF := HasFDerivAt.sum (u := Finset.univ) (fun i _ => (hc i).mul (hm' i))
  have e : (∑ i : Fin 3, (fun x : Space => ((x i : ℝ) : ℂ)) * fun x => m x i) = fun _ => 0 := by
    funext x
    rw [Finset.sum_apply]
    exact hm.2.2.2.2 x
  rw [e] at hF
  have h3 := congrArg (fun L : Space →L[ℝ] ℂ => L v) (hF.unique (hasFDerivAt_const 0 ξ))
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    ContinuousLinearMap.zero_apply] at h3
  rw [← h3]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  ring

theorem driftSym_div (α a : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) (ξ : Space) :
    ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * driftSym α a m ξ i = 0 := by
  have hH := hm.2.2.2.2 ξ
  have h0 := div_deriv hm ξ (unitVector 0)
  have h1 := div_deriv hm ξ (unitVector 1)
  have h2 := div_deriv hm ξ (unitVector 2)
  simp only [Fin.sum_univ_three] at hH h0 h1 h2 ⊢
  simp [unitVector] at h0 h1 h2
  simp [driftSym, Fin.sum_univ_three, turnC_0, turnC_1, turnC_2, Complex.real_smul, unitVector]
  linear_combination (1 - 4 * (1 / (2 * (α : ℂ))) + 2 * (1 / (2 * (α : ℂ)))) * hH +
    (1 / (2 * (α : ℂ))) * (((ξ 0 : ℝ) : ℂ) * h0 + ((ξ 1 : ℝ) : ℂ) * h1 + ((ξ 2 : ℝ) : ℂ) * h2) -
    (a : ℂ) * (((ξ 0 : ℝ) : ℂ) * h1 - ((ξ 1 : ℝ) : ℂ) * h0)

end Breakdown.FracInternal.NiceDrift

namespace Breakdown.FracCert

open Freq Breakdown.FracInternal.NiceField Breakdown.FracInternal.NiceDrift

theorem niceDriftClosed : NiceDriftClosedStatement := by
  rintro α a - φ ⟨m, hm, rfl⟩
  refine ⟨_, ?_, drift_eq α a hm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (driftS α a (symbolS hm)).smooth ⊤
  · rw [driftS_apply α a hm]
    exact HasCompactSupport.intro' hm.2.1 (isClosed_tsupport m) fun ξ hξ =>
      driftSym_zero α a (notMem_tsupport_iff_eventuallyEq.1 hξ)
  · rw [driftS_apply α a hm]
    obtain ⟨r, hr, hz⟩ := hm.2.2.1
    refine ⟨r, hr, fun ξ hξ => driftSym_zero α a ?_⟩
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hξ] with y hy
    exact hz y hy
  · rw [driftS_apply α a hm]
    exact driftSym_conj α a hm
  · rw [driftS_apply α a hm]
    exact driftSym_div α a hm

end Breakdown.FracCert
