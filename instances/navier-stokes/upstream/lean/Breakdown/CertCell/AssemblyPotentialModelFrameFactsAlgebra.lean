import Breakdown.CertCell.AssemblyPotentialModelFrame

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open CellCert.CellAnalysis Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation
  Coercive.StretchInternal Coercive.RotationInternal


private theorem rot_coord_inner (φ : ℝ) (z : Space) (a : Fin 3) :
    axialRot (-φ) z a = inner ℝ (axialRot φ (unitVector a)) z := by
  rw [rotNeg_apply, col_expand, sum_inner]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [real_inner_smul_left, unitVector, EuclideanSpace.inner_single_left]
  simp

theorem strainFrame : StrainFrameStatement := by
  intro A φ a b
  simp only [rot_coord_inner]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, inner_smul_right, inner_add_right,
    ContinuousLinearMap.adjoint_inner_right,
    real_inner_comm (axialRot φ (unitVector b)) (A (axialRot φ (unitVector a)))]
  ring

private theorem rm_orth (φ : ℝ) (j k : Fin 3) :
    ∑ a : Fin 3, rm φ a j * rm φ a k = if j = k then 1 else 0 := by
  have h := Real.sin_sq_add_cos_sq φ
  fin_cases j <;> fin_cases k <;> simp [rm_eq, Fin.sum_univ_three] <;> nlinarith

theorem vorticityGradFrame : VorticityGradFrameStatement := by
  intro B _ φ j l
  set C := curlGradReal (fun a b c =>
    axialRot (-φ) (B (axialRot φ (unitVector b)) (axialRot φ (unitVector c))) a) with hC
  have hv : ∀ a : Fin 3, CoerciveWeak.vortGradMap B (axialRot φ (unitVector l)) a
      = ∑ m : Fin 3, rm φ m l * conjM φ C a m := by
    intro a
    simp only [CoerciveWeak.vortGradMap, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, coord_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have e1 : inner ℝ (unitVector m) (axialRot φ (unitVector l)) = rm φ m l := by
      rw [unitVector, EuclideanSpace.inner_single_left]
      simp [rm]
    rw [e1]
    congr 1
    simp only [vortGrad_conj φ B, ← hC]
    rw [Fin.sum_univ_three]
    fin_cases a <;> simp [unitVector]
  have hexp : axialRot (-φ) (CoerciveWeak.vortGradMap B (axialRot φ (unitVector l))) j = ∑ a' : Fin 3, ∑ c : Fin 3,
      (∑ a : Fin 3, rm φ a j * rm φ a a') * (∑ m : Fin 3, rm φ m l * rm φ m c) * C a' c := by
    simp only [rotNeg_apply, hv, conjM, Fin.sum_univ_three]
    ring
  rw [hexp]
  simp only [rm_orth, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

private theorem rotated_real (A : Space →L[ℝ] Space) (φ : ℝ) (x : Fin 3 → ℝ) :
    ∑ a : Fin 3, (∑ b : Fin 3, axialRot (-φ) (A (axialRot φ (unitVector b))) a * x b) ^ 2
      ≤ ‖A‖ ^ 2 * ∑ b : Fin 3, x b ^ 2 := by
  set X : Space := ∑ b : Fin 3, x b • unitVector b with hX
  have hXc : ∀ b, X b = x b := by
    intro b
    rw [hX, coord_sum]
    fin_cases b <;> simp [unitVector]
  have hV : ∀ a, ∑ b : Fin 3, axialRot (-φ) (A (axialRot φ (unitVector b))) a * x b
      = axialRot (-φ) (A (axialRot φ X)) a := by
    intro a
    rw [hX, axialRot_sum_smul, map_sum]
    simp only [map_smul, axialRot_sum_smul, coord_sum]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hn : ∀ v : Space, ‖v‖ ^ 2 = ∑ a : Fin 3, v a ^ 2 := by
    intro v
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  simp only [hV]
  rw [← hn, ← funext hXc, ← hn, axialRot_norm]
  have h1 : ‖A (axialRot φ X)‖ ≤ ‖A‖ * ‖X‖ := by
    refine (A.le_opNorm _).trans ?_
    rw [axialRot_norm]
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

theorem rotatedBound : RotatedBoundStatement := by
  intro A φ u
  set M : Fin 3 → Fin 3 → ℝ := fun a b => axialRot (-φ) (A (axialRot φ (unitVector b))) a with hM
  have hre := rotated_real A φ (fun b => (u b).re)
  have him := rotated_real A φ (fun b => (u b).im)
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hl : cnormSq (fun a => ∑ b : Fin 3, ((M a b : ℝ) : ℂ) * u b)
      = ∑ a : Fin 3, (∑ b : Fin 3, M a b * (u b).re) ^ 2 + ∑ a : Fin 3, (∑ b : Fin 3, M a b * (u b).im) ^ 2 := by
    simp only [cnormSq, hsq, Complex.re_sum, Complex.im_sum, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    rw [Finset.sum_add_distrib]
  have hr : cnormSq u = ∑ b : Fin 3, (u b).re ^ 2 + ∑ b : Fin 3, (u b).im ^ 2 := by
    simp only [cnormSq, hsq]
    rw [Finset.sum_add_distrib]
  show cnormSq (fun a => ∑ b : Fin 3, ((M a b : ℝ) : ℂ) * u b) ≤ ‖A‖ ^ 2 * cnormSq u
  rw [hl, hr, mul_add]
  exact add_le_add hre him

private theorem rot_plane_coords (φ : ℝ) (p : ℝ × ℝ) :
    axialRot φ (planePoint p) 0 = Real.cos φ * p.1 ∧ axialRot φ (planePoint p) 1 = Real.sin φ * p.1 ∧
      axialRot φ (planePoint p) 2 = p.2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [axialRot, planePoint, cylPoint, unitVector]

theorem orbitSolid : OrbitSolidStatement := by
  intro K p φ hK hp
  obtain ⟨c0, c1, c2⟩ := rot_plane_coords φ p
  obtain ⟨⟨hr1, hr2⟩, hz1, hz2⟩ := hp
  have hp1 : 0 ≤ p.1 := hK.r_order.1.trans hr1
  have hp2 : 0 ≤ p.2 := hK.z_order.1.trans hz1
  have hrad : Real.sqrt (axialRot φ (planePoint p) 0 ^ 2 + axialRot φ (planePoint p) 1 ^ 2) = p.1 := by
    rw [c0, c1, show (Real.cos φ * p.1) ^ 2 + (Real.sin φ * p.1) ^ 2 = p.1 ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq φ], Real.sqrt_sq hp1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show K.r₁ ≤ Real.sqrt _
    rw [hrad]; exact hr1
  · show Real.sqrt _ ≤ K.r₂
    rw [hrad]; exact hr2
  · show K.z₁ ≤ |axialRot φ (planePoint p) 2|
    rw [c2, abs_of_nonneg hp2]; exact hz1
  · show |axialRot φ (planePoint p) 2| ≤ K.z₂
    rw [c2, abs_of_nonneg hp2]; exact hz2

end Internal
end Assembly
end CertCell
end Breakdown
