import Breakdown.CertCell.MeanStretchModeSum

open scoped ComplexConjugate
open Filter Topology Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace Sharp

open Bridge Bridge.Internal.MeanStretch Coercive.StretchInternal

def slotRe (x : Slot → ℂ) : Slot → ℂ := fun k => (((x k).re : ℝ) : ℂ)

def slotIm (x : Slot → ℂ) : Slot → ℂ := fun k => (((x k).im : ℝ) : ℂ)

theorem pairForm_conj_split (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ) (x : Slot → ℂ) :
    pairForm gW hW x (fun k => conj (x k)) + pairForm gW hW (fun k => conj (x k)) x
      = 2 * (pairForm gW hW (slotRe x) (slotRe x) + pairForm gW hW (slotIm x) (slotIm x)) := by
  have hx0 : x = slotRe x + Complex.I • slotIm x := by
    funext k
    simp only [slotRe, slotIm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im (x k)).symm
  have hc : (fun k => conj (x k)) = slotRe x - Complex.I • slotIm x := by
    funext k
    simp only [slotRe, slotIm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    apply Complex.ext <;> simp
  have e1 : pairForm gW hW x (fun k => conj (x k)) = pairLinear gW hW x (fun k => conj (x k)) := rfl
  have e2 : pairForm gW hW (fun k => conj (x k)) x = pairLinear gW hW (fun k => conj (x k)) x := rfl
  have e3 : pairForm gW hW (slotRe x) (slotRe x) = pairLinear gW hW (slotRe x) (slotRe x) := rfl
  have e4 : pairForm gW hW (slotIm x) (slotIm x) = pairLinear gW hW (slotIm x) (slotIm x) := rfl
  rw [e1, e2, e3, e4, hc]
  generalize slotRe x = r at hx0 ⊢
  generalize slotIm x = t at hx0 ⊢
  rw [hx0]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem realForm_lower (wg : Fin 3 → Fin 3 → ℝ) (wh : Fin 3 → Fin 3 → Fin 3 → ℝ) (lam K : ℝ)
    (hS : ∀ u : Fin 3 → ℝ, ∑ a : Fin 3, ∑ b : Fin 3, u a * ((wg a b + wg b a) / 2) * u b ≤ lam * ∑ a : Fin 3, u a ^ 2)
    (htr : curlGradReal wh 0 0 + curlGradReal wh 1 1 + curlGradReal wh 2 2 = 0) (hK0 : 0 ≤ K)
    (hK : ∀ x : Fin 3 → ℝ, ∑ j : Fin 3, matVec (curlGradReal wh) x j ^ 2 ≤ K ^ 2 * ∑ m : Fin 3, x m ^ 2)
    (u : Fin 3 → ℝ) (s : Fin 3 → Fin 3 → ℝ) :
    -(lam * ∑ i : Fin 3, curlMat s i ^ 2
        + Real.sqrt (7 / 2) * K * Real.sqrt (∑ m : Fin 3, u m ^ 2) * Real.sqrt (∑ l : Fin 3, ∑ j : Fin 3, s l j ^ 2))
      ≤ realForm wg (curlGradReal wh) u s := by
  unfold realForm
  have h1 := hS (curlMat s)
  have e1 : ∑ i : Fin 3, ∑ j : Fin 3, curlMat s i * ((wg i j + wg j i) / 2) * curlMat s j
      = ∑ a : Fin 3, ∑ b : Fin 3, curlMat s a * ((wg a b + wg b a) / 2) * curlMat s b := rfl
  set nv := ∑ m : Fin 3, u m ^ 2 with hnv
  set ns := ∑ l : Fin 3, ∑ j : Fin 3, s l j ^ 2 with hns
  have hnv0 : 0 ≤ nv := Finset.sum_nonneg fun m _ => sq_nonneg (u m)
  have hns0 : 0 ≤ ns := Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun j _ => sq_nonneg (s l j)
  have hB : bilin (curlGradReal wh) u s ^ 2 ≤ (7 / 2 : ℝ) * K ^ 2 * nv * ns := by
    rw [bilin_eq_sum]
    refine (sum_sq_prod_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (kernel_sq_le (curlGradReal wh) u htr hK) hns0
  have hB' : |bilin (curlGradReal wh) u s| ≤ Real.sqrt (7 / 2) * K * Real.sqrt nv * Real.sqrt ns := by
    have := Real.abs_le_sqrt hB
    refine this.trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      Real.sqrt_sq hK0]
  have hB'' := neg_abs_le (bilin (curlGradReal wh) u s)
  linarith

theorem sqrt_cross_le (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt a * Real.sqrt b + Real.sqrt c * Real.sqrt d ≤ Real.sqrt (a + c) * Real.sqrt (b + d) := by
  rw [← Real.sqrt_mul (show 0 ≤ a + c by positivity) (b + d)]
  have hA := Real.sq_sqrt ha
  have hB := Real.sq_sqrt hb
  have hC := Real.sq_sqrt hc
  have hD := Real.sq_sqrt hd
  apply Real.le_sqrt_of_sq_le
  have : (a + c) * (b + d) - (Real.sqrt a * Real.sqrt b + Real.sqrt c * Real.sqrt d) ^ 2
      = (Real.sqrt a * Real.sqrt d - Real.sqrt c * Real.sqrt b) ^ 2 := by
    nlinarith [hA, hB, hC, hD]
  nlinarith [sq_nonneg (Real.sqrt a * Real.sqrt d - Real.sqrt c * Real.sqrt b)]

def slotVelRe (x : Slot → ℂ) : Fin 3 → ℝ := fun i => (x (Sum.inl i)).re

def slotVelIm (x : Slot → ℂ) : Fin 3 → ℝ := fun i => (x (Sum.inl i)).im

def slotGradRe (x : Slot → ℂ) : Fin 3 → Fin 3 → ℝ := fun i j => (x (Sum.inr (i, j))).re

def slotGradIm (x : Slot → ℂ) : Fin 3 → Fin 3 → ℝ := fun i j => (x (Sum.inr (i, j))).im

theorem slotRe_eq (x : Slot → ℂ) : slotRe x = fun k => ((slotOf (slotVelRe x) (slotGradRe x) k : ℝ) : ℂ) := by
  funext k
  rcases k with i | ⟨i, j⟩ <;> rfl

theorem slotIm_eq (x : Slot → ℂ) : slotIm x = fun k => ((slotOf (slotVelIm x) (slotGradIm x) k : ℝ) : ℂ) := by
  funext k
  rcases k with i | ⟨i, j⟩ <;> rfl

theorem curl_norm_sq (x : Slot → ℂ) (i : Fin 3) :
    ‖curlOfGrad (fun ij => x (Sum.inr ij)) i‖ ^ 2 = curlMat (slotGradRe x) i ^ 2 + curlMat (slotGradIm x) i ^ 2 := by
  have hre : (curlOfGrad (fun ij => x (Sum.inr ij)) i).re = curlMat (slotGradRe x) i := by
    simp [curlOfGrad, curlMat, slotGradRe, Complex.re_sum]
  have him : (curlOfGrad (fun ij => x (Sum.inr ij)) i).im = curlMat (slotGradIm x) i := by
    simp [curlOfGrad, curlMat, slotGradIm, Complex.im_sum]
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  ring

theorem vel_norm_sq (x : Slot → ℂ) :
    ∑ i : Fin 3, ‖x (Sum.inl i)‖ ^ 2 = ∑ m : Fin 3, slotVelRe x m ^ 2 + ∑ m : Fin 3, slotVelIm x m ^ 2 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [slotVelRe, slotVelIm]
  ring

theorem grad_norm_sq (x : Slot → ℂ) :
    ∑ l : Fin 3, ∑ j : Fin 3, ‖x (Sum.inr (l, j))‖ ^ 2
      = ∑ l : Fin 3, ∑ j : Fin 3, slotGradRe x l j ^ 2 + ∑ l : Fin 3, ∑ j : Fin 3, slotGradIm x l j ^ 2 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [slotGradRe, slotGradIm]
  ring

theorem triple_lower (wg : Fin 3 → Fin 3 → ℝ) (wh : Fin 3 → Fin 3 → Fin 3 → ℝ) (lam K : ℝ)
    (hS : ∀ u : Fin 3 → ℝ, ∑ a : Fin 3, ∑ b : Fin 3, u a * ((wg a b + wg b a) / 2) * u b ≤ lam * ∑ a : Fin 3, u a ^ 2)
    (htr : curlGradReal wh 0 0 + curlGradReal wh 1 1 + curlGradReal wh 2 2 = 0) (hK0 : 0 ≤ K)
    (hK : ∀ x : Fin 3 → ℝ, ∑ j : Fin 3, matVec (curlGradReal wh) x j ^ 2 ≤ K ^ 2 * ∑ m : Fin 3, x m ^ 2)
    (x : Slot → ℂ) :
    -(lam * ∑ i : Fin 3, ‖curlOfGrad (fun ij => x (Sum.inr ij)) i‖ ^ 2
        + Real.sqrt (7 / 2) * K * Real.sqrt (∑ i : Fin 3, ‖x (Sum.inl i)‖ ^ 2)
          * Real.sqrt (∑ l : Fin 3, ∑ j : Fin 3, ‖x (Sum.inr (l, j))‖ ^ 2))
      ≤ ((pairForm (fun ij => ((wg ij.1 ij.2 : ℝ) : ℂ)) (fun ijl => ((wh ijl.1 ijl.2.1 ijl.2.2 : ℝ) : ℂ))
            x (fun k => conj (x k))
          + pairForm (fun ij => ((wg ij.1 ij.2 : ℝ) : ℂ)) (fun ijl => ((wh ijl.1 ijl.2.1 ijl.2.2 : ℝ) : ℂ))
            (fun k => conj (x k)) x) / 2).re := by
  rw [pairForm_conj_split, slotRe_eq, slotIm_eq, pairForm_ofReal, pairForm_ofReal]
  have e : ((2 * (((realForm wg (curlGradReal wh) (slotVelRe x) (slotGradRe x) : ℝ) : ℂ)
      + ((realForm wg (curlGradReal wh) (slotVelIm x) (slotGradIm x) : ℝ) : ℂ))) / 2).re
      = realForm wg (curlGradReal wh) (slotVelRe x) (slotGradRe x)
        + realForm wg (curlGradReal wh) (slotVelIm x) (slotGradIm x) := by
    simp
  rw [e]
  have h1 := realForm_lower wg wh lam K hS htr hK0 hK (slotVelRe x) (slotGradRe x)
  have h2 := realForm_lower wg wh lam K hS htr hK0 hK (slotVelIm x) (slotGradIm x)
  have hc : ∑ i : Fin 3, ‖curlOfGrad (fun ij => x (Sum.inr ij)) i‖ ^ 2
      = ∑ i : Fin 3, curlMat (slotGradRe x) i ^ 2 + ∑ i : Fin 3, curlMat (slotGradIm x) i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => curl_norm_sq x i
  rw [hc, vel_norm_sq, grad_norm_sq]
  have hx := sqrt_cross_le (∑ m : Fin 3, slotVelRe x m ^ 2) (∑ l : Fin 3, ∑ j : Fin 3, slotGradRe x l j ^ 2)
    (∑ m : Fin 3, slotVelIm x m ^ 2) (∑ l : Fin 3, ∑ j : Fin 3, slotGradIm x l j ^ 2)
    (by positivity) (by positivity) (by positivity) (by positivity)
  have hk : 0 ≤ Real.sqrt (7 / 2) * K := by positivity
  have hx' := mul_le_mul_of_nonneg_left hx hk
  nlinarith [hx', h1, h2]

open Coercive.RotationInternal in
theorem rot_inner (φ : ℝ) (a b : Space) : inner ℝ (axialRot φ a) (axialRot φ b) = inner ℝ a b :=
  (axialRotEquiv φ).inner_map_map a b

theorem frame_quad_eq (A : Space →L[ℝ] Space) (φ : ℝ) (w : Fin 3 → ℝ) :
    ∑ a : Fin 3, ∑ c : Fin 3, w a * axialRot (-φ) (A (axialRot φ (unitVector c))) a * w c
      = inner ℝ (axialRot φ (∑ k : Fin 3, w k • unitVector k)) (A (axialRot φ (∑ k : Fin 3, w k • unitVector k))) := by
  set A' : Space →L[ℝ] Space := (rotCLM (-φ)).comp (A.comp (rotCLM φ)) with hA'
  have h1 := symPartForm_coord A' w
  have h2 : ∀ i j, A' (unitVector j) i = axialRot (-φ) (A (axialRot φ (unitVector j))) i := by
    intro i j; rfl
  simp only [h2] at h1
  rw [← h1]
  unfold symPartForm
  have h3 : A' (∑ k : Fin 3, w k • unitVector k)
      = axialRot (-φ) (A (axialRot φ (∑ k : Fin 3, w k • unitVector k))) := rfl
  rw [h3, ← rot_inner φ, Coercive.RotationInternal.axialRot_self_neg]

theorem strain_frame (A : Space →L[ℝ] Space) (φ lam : ℝ)
    (hW : ∀ u : Space, inner ℝ u (A u) ≤ lam * ‖u‖ ^ 2) (w : Fin 3 → ℝ) :
    ∑ a : Fin 3, ∑ b : Fin 3, w a * ((axialRot (-φ) (A (axialRot φ (unitVector b))) a
        + axialRot (-φ) (A (axialRot φ (unitVector a))) b) / 2) * w b
      ≤ lam * ∑ a : Fin 3, w a ^ 2 := by
  set F : Fin 3 → Fin 3 → ℝ := fun a b => axialRot (-φ) (A (axialRot φ (unitVector b))) a with hF
  have hsym : ∑ a : Fin 3, ∑ b : Fin 3, w a * ((F a b + F b a) / 2) * w b = ∑ a : Fin 3, ∑ b : Fin 3, w a * F a b * w b := by
    have e : ∑ a : Fin 3, ∑ b : Fin 3, w a * F b a * w b = ∑ a : Fin 3, ∑ b : Fin 3, w a * F a b * w b := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    have : ∑ a : Fin 3, ∑ b : Fin 3, w a * ((F a b + F b a) / 2) * w b
        = (∑ a : Fin 3, ∑ b : Fin 3, w a * F a b * w b + ∑ a : Fin 3, ∑ b : Fin 3, w a * F b a * w b) / 2 := by
      simp only [Fin.sum_univ_three]
      ring
    rw [this, e]; ring
  rw [hsym]
  have hq := frame_quad_eq A φ w
  simp only [hF]
  rw [hq]
  refine (hW _).trans (le_of_eq ?_)
  rw [Coercive.RotationInternal.axialRot_norm, norm_sq_coord]

theorem frameUnit_eq (φ : ℝ) (b : Fin 3) : frameUnit φ b = axialRot φ (unitVector b) := by
  fin_cases b <;> ext i <;> fin_cases i <;>
    simp [frameUnit, CellCert.CellAnalysis.radialUnit, CellCert.CellAnalysis.angularUnit,
      CellCert.CellAnalysis.axialUnit, axialRot, unitVector]

theorem inner_unitVector (a b : Fin 3) : inner ℝ (unitVector a) (unitVector b) = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> simp [unitVector, PiLp.inner_apply, Fin.sum_univ_three]

theorem frameMap_rot_unit (φ : ℝ) (x0 : Fin 3 → Fin 3 → ℝ) (m j : Fin 3) :
    axialRot (-φ) (CellMatField.frameMap φ x0 (axialRot φ (unitVector m))) j = x0 j m := by
  have e1 : CellMatField.frameMap φ x0 (axialRot φ (unitVector m)) = ∑ a : Fin 3, x0 a m • axialRot φ (unitVector a) := by
    unfold CellMatField.frameMap
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, frameUnit_eq, rot_inner, inner_unitVector]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [smul_smul]
  rw [e1]
  have e2 : axialRot (-φ) (∑ a : Fin 3, x0 a m • axialRot φ (unitVector a)) = ∑ a : Fin 3, x0 a m • unitVector a := by
    rw [← rotCLM_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, rotCLM_apply, Coercive.RotationInternal.axialRot_neg_self]
  rw [e2]
  simp [unitVector, Fin.sum_univ_three]
  fin_cases j <;> simp

theorem wave_frame (B : Space →L[ℝ] Space) (φ K : ℝ) (x0 : Fin 3 → Fin 3 → ℝ) (hK0 : 0 ≤ K)
    (hB : ∀ u : Space, ‖B u - CellMatField.frameMap φ x0 u‖ ≤ K * ‖u‖) (x : Fin 3 → ℝ) :
    ∑ j : Fin 3, matVec (fun a c => axialRot (-φ) (B (axialRot φ (unitVector c))) a - x0 a c) x j ^ 2
      ≤ K ^ 2 * ∑ m : Fin 3, x m ^ 2 := by
  set C : Space →L[ℝ] Space := B - CellMatField.frameMap φ x0 with hC
  set A' : Space →L[ℝ] Space := (rotCLM (-φ)).comp (C.comp (rotCLM φ)) with hA'
  have hA'e : (fun j m => A' (unitVector m) j) = fun a c => axialRot (-φ) (B (axialRot φ (unitVector c))) a - x0 a c := by
    funext j m
    simp only [hA', hC, ContinuousLinearMap.comp_apply, rotCLM_apply, ContinuousLinearMap.sub_apply]
    rw [← rotCLM_apply (-φ), map_sub, rotCLM_apply, rotCLM_apply, PiLp.sub_apply, frameMap_rot_unit]
  have hnorm : ‖A'‖ ≤ K := by
    refine ContinuousLinearMap.opNorm_le_bound _ hK0 fun u => ?_
    simp only [hA', ContinuousLinearMap.comp_apply, rotCLM_apply, Coercive.RotationInternal.axialRot_norm]
    have := hB (axialRot φ u)
    rw [Coercive.RotationInternal.axialRot_norm] at this
    simpa [hC] using this
  have h := matVec_le_opNorm A' x
  rw [hA'e] at h
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun m _ => sq_nonneg (x m))
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

end Sharp

end Internal

end Assembly

end CertCell

end Breakdown
