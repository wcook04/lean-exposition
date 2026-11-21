import Breakdown.CertTorus.RegularStatements

open MeasureTheory Set Real Filter
open scoped ContDiff ENNReal Topology FourierTransform

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

namespace Internal.RotateSymbol

theorem apply_coord (R : Space ≃ₗᵢ[ℝ] Space) (v : Space) (i : Fin 3) :
    R v i = ∑ j : Fin 3, R (unitVector j) i * v j := by
  have hv : v = ∑ j : Fin 3, v j • unitVector j := by
    ext i
    simp only [unitVector, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, PiLp.single_apply]
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb.symm]) (by simp)]
    simp
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, mul_comm]

theorem rotC_apply (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) (i : Fin 3) :
    rotC R z i = ∑ j : Fin 3, ((R (unitVector j) i : ℝ) : ℂ) * z j := rfl

theorem rotC_complex_smul (R : Space ≃ₗᵢ[ℝ] Space) (c : ℂ) (z : CSpace) :
    rotC R (c • z) = c • rotC R z := by
  ext i
  simp only [rotC_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem rotC_comp (R S : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) :
    rotC R (rotC S z) = rotC (S.trans R) z := by
  ext i
  simp only [rotC_apply, LinearIsometryEquiv.trans_apply]
  simp_rw [apply_coord R (S (unitVector _)) i, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem rotC_refl (z : CSpace) : rotC (LinearIsometryEquiv.refl ℝ Space) z = z := by
  ext i
  simp only [rotC_apply, unitVector]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb.symm]) (by simp)]
  simp

theorem rotC_symm_rotC (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) : rotC R.symm (rotC R z) = z := by
  rw [rotC_comp, LinearIsometryEquiv.self_trans_symm, rotC_refl]

theorem realVec_rotC (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) :
    realVec (rotC R z) = R (realVec z) := by
  ext i
  rw [apply_coord R (realVec z) i]
  simp [realVec, rotC_apply, Complex.re_sum]

theorem conjVec_rotC (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) :
    conjVec (rotC R z) = rotC R (conjVec z) := by
  ext i
  simp [conjVec, rotC_apply, map_sum]

theorem complexifyVec_map (R : Space ≃ₗᵢ[ℝ] Space) (v : Space) :
    complexifyVec (R v) = rotC R (complexifyVec v) := by
  ext i
  show ((R v i : ℝ) : ℂ) = ∑ j : Fin 3, ((R (unitVector j) i : ℝ) : ℂ) * ((v j : ℝ) : ℂ)
  rw [apply_coord R v i]
  push_cast
  rfl

def imVec (z : CSpace) : Space := WithLp.toLp 2 (fun i => (z i).im)

theorem re_rotC (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) (i : Fin 3) :
    (rotC R z i).re = R (realVec z) i := by
  rw [apply_coord R (realVec z) i]
  simp [realVec, rotC_apply, Complex.re_sum]

theorem im_rotC (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) (i : Fin 3) :
    (rotC R z i).im = R (imVec z) i := by
  rw [apply_coord R (imVec z) i]
  simp [imVec, rotC_apply, Complex.im_sum]

theorem normSq_split (z : CSpace) : ‖z‖ ^ 2 = ‖realVec z‖ ^ 2 + ‖imVec z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [realVec, imVec, Real.norm_eq_abs, sq_abs]
  ring

theorem norm_rotC (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) : ‖rotC R z‖ = ‖z‖ := by
  have h1 : realVec (rotC R z) = R (realVec z) := by
    ext i
    rw [← re_rotC]
    simp [realVec]
  have h2 : imVec (rotC R z) = R (imVec z) := by
    ext i
    rw [← im_rotC]
    simp [imVec]
  have h : ‖rotC R z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [normSq_split, normSq_split z, h1, h2, LinearIsometryEquiv.norm_map,
      LinearIsometryEquiv.norm_map]
  rw [← Real.sqrt_sq (norm_nonneg (rotC R z)), h, Real.sqrt_sq (norm_nonneg z)]

theorem enorm_rotC (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) : ‖rotC R z‖ₑ = ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_rotC]

def rotCIsom (R : Space ≃ₗᵢ[ℝ] Space) : CSpace →ₗᵢ[ℝ] CSpace where
  toLinearMap := (rotC R : CSpace →ₗ[ℝ] CSpace)
  norm_map' := norm_rotC R

theorem rotCIsom_apply (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) : rotCIsom R z = rotC R z := rfl

theorem inner_coord (R : Space ≃ₗᵢ[ℝ] Space) (η : Space) (j : Fin 3) :
    ∑ i : Fin 3, R η i * R (unitVector j) i = η j := by
  have h := R.inner_map_map η (unitVector j)
  simp only [unitVector] at h ⊢
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_single_right] at h
  simp only [dotProduct, star_trivial, one_mul, conj_trivial] at h
  rw [← h]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dot_rotC (R : Space ≃ₗᵢ[ℝ] Space) (η : Space) (w : CSpace) :
    ∑ i : Fin 3, ((R η i : ℝ) : ℂ) * rotC R w i = ∑ j : Fin 3, ((η j : ℝ) : ℂ) * w j := by
  simp only [rotC_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← inner_coord R η j]
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem lerayC_rotC (R : Space ≃ₗᵢ[ℝ] Space) (η : Space) (w : CSpace) :
    divFreeC (R η) (rotC R w) = rotC R (divFreeC η w) := by
  unfold divFreeC
  rw [map_sub, rotC_complex_smul, dot_rotC, LinearIsometryEquiv.norm_map, freqVec, freqVec,
    complexifyVec_map]

theorem symX_rotX_ae (R : Space ≃ₗᵢ[ℝ] Space) (x : X) :
    symX (rotX R x) =ᵐ[volume] fun ξ => rotC R (symX x (R.symm ξ)) := by
  unfold symX
  rw [(rotation_holds R).1 x]
  exact fieldOpRealized_holds R.symm.toContinuousLinearEquiv (fun _ => rotC R) ‖rotC R‖
    aestronglyMeasurable_const (fun _ => le_rfl) (x : L2C)

theorem velSymbol_rotX_ae (R : Space ≃ₗᵢ[ℝ] Space) (x : X) :
    velSymbol (rotX R x) =ᵐ[volume] fun ξ => rotC R (velSymbol x (R.symm ξ)) := by
  have h1 := symX_rotX_ae R x
  have h2 : (fun ξ => symX (rotX R x) (-ξ)) =ᵐ[volume]
      fun ξ => rotC R (symX x (R.symm (-ξ))) :=
    (LinearIsometryEquiv.neg ℝ (E := Space)).measurePreserving.quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h1, h2] with ξ ha hb
  unfold velSymbol
  rw [ha, hb, map_neg, conjVec_rotC, ← map_add, ← map_smul]
  have hξ : ξ = R (R.symm ξ) := (R.apply_symm_apply ξ).symm
  conv_lhs => rw [hξ]
  rw [lerayC_rotC, ← map_smul, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.apply_symm_apply]

theorem measurePreserving_weight (R : Space ≃ₗᵢ[ℝ] Space) (k : ℕ) :
    MeasurePreserving R.symm (weightL1Measure k) (weightL1Measure k) := by
  refine ⟨R.symm.continuous.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply R.symm.continuous.measurable hs]
  simp only [weightL1Measure]
  have h := R.symm.measurePreserving.setLIntegral_comp_preimage_emb
    R.symm.toHomeomorph.measurableEmbedding (fun a => ENNReal.ofReal ((1 + ‖a‖) ^ k)) s
  simp only [LinearIsometryEquiv.norm_map] at h
  rw [withDensity_apply _ (R.symm.continuous.measurable hs), withDensity_apply _ hs, h]

theorem weight_transfer (R : Space ≃ₗᵢ[ℝ] Space) (k : ℕ) {f f' : Space → CSpace}
    (hf : MemLp f 1 (weightL1Measure k))
    (hae : f' =ᵐ[volume] fun ξ => rotC R (f (R.symm ξ))) :
    MemLp f' 1 (weightL1Measure k) ∧
      eLpNorm f' 1 (weightL1Measure k) = eLpNorm f 1 (weightL1Measure k) := by
  have hae' : f' =ᵐ[weightL1Measure k] fun ξ => rotC R (f (R.symm ξ)) :=
    (withDensity_absolutelyContinuous _ _).ae_le hae
  have hc : MemLp (f ∘ R.symm) 1 (weightL1Measure k) :=
    hf.comp_measurePreserving (measurePreserving_weight R k)
  have hr : MemLp (fun ξ => rotC R (f (R.symm ξ))) 1 (weightL1Measure k) :=
    (rotC R).comp_memLp' hc
  refine ⟨hr.ae_eq hae'.symm, ?_⟩
  have hn : eLpNorm (fun ξ => rotC R (f (R.symm ξ))) 1 (weightL1Measure k) =
      eLpNorm (f ∘ R.symm) 1 (weightL1Measure k) :=
    eLpNorm_congr_norm_ae (ae_of_all _ fun ξ => norm_rotC R _)
  rw [eLpNorm_congr_ae hae', hn]
  exact eLpNorm_comp_measurePreserving hf.1 (measurePreserving_weight R k)

theorem velSymbol_rotX_ae_inv (R : Space ≃ₗᵢ[ℝ] Space) (x : X) :
    velSymbol x =ᵐ[volume] fun ξ => rotC R.symm (velSymbol (rotX R x) (R.symm.symm ξ)) := by
  have h := R.measurePreserving.quasiMeasurePreserving.ae_eq_comp (velSymbol_rotX_ae R x)
  filter_upwards [h] with ξ hξ
  simp only [Function.comp_apply, LinearIsometryEquiv.symm_symm] at hξ ⊢
  rw [hξ, LinearIsometryEquiv.symm_apply_apply, rotC_symm_rotC]

theorem homSob_rotX (R : Space ≃ₗᵢ[ℝ] Space) (x : X) (k : ℕ) :
    homSob k (rotX R x) = homSob k x := by
  unfold homSob homNormSq
  rw [lintegral_congr_ae ((symX_rotX_ae R x).mono fun ξ hξ => by rw [hξ])]
  have h := R.symm.measurePreserving.lintegral_comp_emb R.symm.toHomeomorph.measurableEmbedding
    (fun η => ENNReal.ofReal (‖η‖ ^ (2 * k)) * ‖symX x η‖ₑ ^ 2)
  rw [← h]
  refine lintegral_congr fun ξ => ?_
  simp only [enorm_rotC, LinearIsometryEquiv.norm_map]

theorem weightNorm_rotX (R : Space ≃ₗᵢ[ℝ] Space) (x : X) (k : ℕ) :
    ‖toWeightL1 k (velSymbol (rotX R x))‖ = ‖toWeightL1 k (velSymbol x)‖ := by
  unfold toWeightL1
  by_cases hf : MemLp (velSymbol x) 1 (weightL1Measure k)
  · obtain ⟨hf', he⟩ := weight_transfer R k hf (velSymbol_rotX_ae R x)
    rw [dif_pos hf', dif_pos hf, Lp.norm_toLp, Lp.norm_toLp, he]
  · have hf' : ¬ MemLp (velSymbol (rotX R x)) 1 (weightL1Measure k) := fun h =>
      hf (weight_transfer R.symm k h (velSymbol_rotX_ae_inv R x)).1
    rw [dif_neg hf', dif_neg hf]

theorem physField_rotX (R : Space ≃ₗᵢ[ℝ] Space) (x : X) (y : Space) :
    physField (velSymbol (rotX R x)) y = R (physField (velSymbol x) (R.symm y)) := by
  unfold physField
  have h1 : 𝓕⁻ (velSymbol (rotX R x)) y =
      𝓕⁻ (fun ξ => rotC R (velSymbol x (R.symm ξ))) y := by
    simp only [Real.fourierInv_eq]
    exact integral_congr_ae ((velSymbol_rotX_ae R x).mono fun v hv => by simp only [hv])
  have h2 : 𝓕⁻ (fun ξ => rotC R (velSymbol x (R.symm ξ))) y =
      rotC R (𝓕⁻ (velSymbol x ∘ R.symm) y) := by
    simp only [Real.fourierInv_eq, Function.comp_apply]
    rw [← rotCIsom_apply, ← LinearIsometry.integral_comp_comm]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [rotCIsom_apply, Circle.smul_def, rotC_complex_smul]
  rw [h1, h2, Real.fourierInv_comp_linearIsometry, realVec_rotC]

end Internal.RotateSymbol

open Internal.RotateSymbol in
theorem rotateSymbol_holds : RotateSymbol := fun R x =>
  ⟨fun k => homSob_rotX R x k, fun k => weightNorm_rotX R x k, fun y => physField_rotX R x y⟩

end Breakdown.FarField
