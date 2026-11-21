import Breakdown.Frac.StSymbol

open MeasureTheory Real LineDeriv FourierTransform SchwartzMap
open scoped RealInnerProductSpace

noncomputable section

namespace Breakdown

namespace FracInternal.RemainderTransform

def lift (φ : 𝓢(Space, Space)) : 𝓢(Space, Freq.CSpace) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Freq.complexifyVec φ

theorem lift_apply (φ : 𝓢(Space, Space)) (x : Space) :
    lift φ x = Freq.complexifyVec (φ x) := rfl

theorem coe_lift (φ : 𝓢(Space, Space)) : (⇑(lift φ)) = Freq.complexifyVec ∘ ⇑φ := rfl

theorem fderiv_lift (φ : 𝓢(Space, Space)) (x z : Space) :
    fderiv ℝ (lift φ) x z = Freq.complexifyVec (fderiv ℝ φ x z) := by
  rw [coe_lift, ((Freq.complexifyVec.hasFDerivAt).comp x (φ.differentiableAt.hasFDerivAt)).fderiv]
  rfl

theorem iteratedFDeriv_lift (φ : 𝓢(Space, Space)) (x z : Space) :
    iteratedFDeriv ℝ 2 (lift φ) x ![z, z] =
      Freq.complexifyVec (iteratedFDeriv ℝ 2 φ x ![z, z]) := by
  rw [coe_lift, Freq.complexifyVec.iteratedFDeriv_comp_left (f := ⇑φ) (φ.smooth ⊤).contDiffAt
    (WithTop.coe_le_coe.2 le_top)]
  rfl

theorem second_eq (S : 𝓢(Space, Freq.CSpace)) (x z : Space) :
    (∂_{z} (∂_{z} S)) x = iteratedFDeriv ℝ 2 S x ![z, z] := by
  rw [← iteratedLineDerivOp_eq_iteratedFDeriv]
  simp [iteratedLineDerivOp_succ_left]

theorem pointwise (φ : 𝓢(Space, Space)) (x z : Space) :
    Freq.complexifyVec (secondOrderRemainder φ x z) =
      lift φ (x + z) - (lift φ + ∂_{z} (lift φ) + (1 / 2 : ℝ) • ∂_{z} (∂_{z} (lift φ))) x := by
  rw [_root_.add_apply, _root_.add_apply, _root_.smul_apply, second_eq,
    iteratedFDeriv_lift, lineDerivOp_apply_eq_fderiv, fderiv_lift, lift_apply, lift_apply]
  simp only [secondOrderRemainder, map_sub, map_smul]
  abel

theorem transform_translate (S : 𝓢(Space, Freq.CSpace)) (z ξ : Space) :
    𝓕 (fun x => S (x + z)) ξ = 𝐞 (⟪z, ξ⟫) • 𝓕 (⇑S) ξ := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ Space) (⇑S) z) ξ
  exact h

theorem transform_deriv_apply (S : 𝓢(Space, Freq.CSpace)) (z ξ : Space) :
    𝓕 (⇑(∂_{z} S : 𝓢(Space, Freq.CSpace))) ξ = (2 * π * Complex.I) • (⟪ξ, z⟫ • 𝓕 (⇑S) ξ) := by
  have : (inner ℝ · z).HasTemperateGrowth := ((innerSL ℝ).flip z).hasTemperateGrowth
  rw [← fourier_coe, fourier_lineDerivOp_eq, _root_.smul_apply, smulLeftCLM_apply_apply this,
    fourier_coe]

theorem transform_lincomb (S : 𝓢(Space, Freq.CSpace)) (z ξ : Space) :
    𝓕 (⇑(S + ∂_{z} S + (1 / 2 : ℝ) • ∂_{z} (∂_{z} S))) ξ =
      𝓕 (⇑S) ξ + (2 * π * Complex.I) • (⟪ξ, z⟫ • 𝓕 (⇑S) ξ) +
        (1 / 2 : ℝ) • ((2 * π * Complex.I) • (⟪ξ, z⟫ • ((2 * π * Complex.I) • (⟪ξ, z⟫ • 𝓕 (⇑S) ξ)))) := by
  rw [← fourier_coe, FourierAdd.fourier_add, FourierAdd.fourier_add, FourierSMul.fourier_smul]
  simp only [_root_.add_apply, _root_.smul_apply, fourier_coe, transform_deriv_apply]

theorem scalar_identity (ξ z : Space) (v : Freq.CSpace) :
    𝐞 (⟪z, ξ⟫) • v - (v + (2 * π * Complex.I) • (⟪ξ, z⟫ • v) +
      (1 / 2 : ℝ) • ((2 * π * Complex.I) • (⟪ξ, z⟫ • ((2 * π * Complex.I) • (⟪ξ, z⟫ • v))))) =
    phaseRemainder ξ z • v := by
  have hc : 𝐞 (⟪z, ξ⟫) • v - (v + (2 * π * Complex.I) • (⟪ξ, z⟫ • v) +
      (1 / 2 : ℝ) • ((2 * π * Complex.I) • (⟪ξ, z⟫ • ((2 * π * Complex.I) • (⟪ξ, z⟫ • v))))) =
      ((𝐞 (⟪z, ξ⟫) : ℂ) - 1 - (2 * π * Complex.I) * (⟪ξ, z⟫ : ℂ) -
        (1 / 2 : ℂ) * ((2 * π * Complex.I) * (⟪ξ, z⟫ : ℂ)) ^ 2) • v := by
    rw [Circle.smul_def]
    simp only [← Complex.coe_smul, smul_smul]
    push_cast
    module
  rw [hc]
  congr 1
  rw [Real.fourierChar_apply]
  unfold phaseRemainder
  rw [real_inner_comm ξ z]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

end FracInternal.RemainderTransform

open FracInternal.RemainderTransform in
theorem remainderTransform : RemainderTransformStatement := by
  intro φ z ξ
  have hf : (fun x => Freq.complexifyVec (secondOrderRemainder φ x z)) =
      fun x => lift φ (x + z) -
        (lift φ + ∂_{z} (lift φ) + (1 / 2 : ℝ) • ∂_{z} (∂_{z} (lift φ))) x :=
    funext fun x => pointwise φ x z
  have h1 : Integrable (fun x => lift φ (x + z)) := (lift φ).integrable.comp_add_right z
  have h2 : Integrable
      ⇑(lift φ + ∂_{z} (lift φ) + (1 / 2 : ℝ) • ∂_{z} (∂_{z} (lift φ)) : 𝓢(Space, Freq.CSpace)) :=
    SchwartzMap.integrable _
  have hS : (fun x => Freq.complexifyVec (φ x)) = ⇑(lift φ) := rfl
  rw [hf, hS, Real.fourier_eq]
  simp_rw [smul_sub]
  rw [integral_sub ((Real.fourierIntegral_convergent_iff ξ).2 h1)
    ((Real.fourierIntegral_convergent_iff ξ).2 h2), ← Real.fourier_eq, ← Real.fourier_eq,
    transform_translate, transform_lincomb, scalar_identity]

end Breakdown
