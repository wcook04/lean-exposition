import Breakdown.CertCell.TailSquareTransfer
import Breakdown.CertCell.ModeRotationNorms
import Breakdown.Cert.CoerciveFrequencySeminormTransportModes
import Breakdown.Cert.ExtendedCoerciveMain
import Breakdown.Cert.SigmaProfileOfHeld
import Breakdown.Cert.CoerciveSmoothBase

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

namespace Internal.SquareModes

open Coercive (reVec imVec reMat imMat rotC rotCMat)
open Internal.SquareTransfer

theorem reVec_coord (x : Fin 3 → ℂ) (i : Fin 3) : reVec x i = (x i).re := by
  fin_cases i <;> simp [reVec, unitVector, Fin.sum_univ_three]

theorem imVec_coord (x : Fin 3 → ℂ) (i : Fin 3) : imVec x i = (x i).im := by
  fin_cases i <;> simp [imVec, unitVector, Fin.sum_univ_three]

theorem reMat_coord (g : Fin 3 × Fin 3 → ℂ) (x : Space) (i : Fin 3) :
    reMat g x i = ∑ j : Fin 3, (g (i, j)).re * x j := by
  fin_cases i <;> simp [reMat, unitVector, EuclideanSpace.inner_single_left, Fin.sum_univ_three] <;> ring

theorem imMat_coord (g : Fin 3 × Fin 3 → ℂ) (x : Space) (i : Fin 3) :
    imMat g x i = ∑ j : Fin 3, (g (i, j)).im * x j := by
  fin_cases i <;> simp [imMat, unitVector, EuclideanSpace.inner_single_left, Fin.sum_univ_three] <;> ring

theorem cnormSq_eq_re_im (x : Fin 3 → ℂ) : cnormSq x = ‖reVec x‖ ^ 2 + ‖imVec x‖ ^ 2 := by
  rw [norm_sq_coord, norm_sq_coord]
  simp only [reVec_coord, imVec_coord, cnormSq, Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem reVec_unphase (α : ℝ) (x : Fin 3 → ℂ) :
    reVec x = Real.cos α • reVec (fun i => Complex.exp ((α : ℂ) * Complex.I) * x i) +
      Real.sin α • imVec (fun i => Complex.exp ((α : ℂ) * Complex.I) * x i) := by
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, reVec_coord, imVec_coord, Complex.mul_re,
    Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  linear_combination (-(x i).re) * Real.sin_sq_add_cos_sq α

theorem imVec_unphase (α : ℝ) (x : Fin 3 → ℂ) :
    imVec x = (-Real.sin α) • reVec (fun i => Complex.exp ((α : ℂ) * Complex.I) * x i) +
      Real.cos α • imVec (fun i => Complex.exp ((α : ℂ) * Complex.I) * x i) := by
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, reVec_coord, imVec_coord, Complex.mul_re,
    Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  linear_combination (-(x i).im) * Real.sin_sq_add_cos_sq α

theorem reMat_unphase (α : ℝ) (g : Fin 3 × Fin 3 → ℂ) :
    reMat g = Real.cos α • reMat (fun ij => Complex.exp ((α : ℂ) * Complex.I) * g ij) +
      Real.sin α • imMat (fun ij => Complex.exp ((α : ℂ) * Complex.I) * g ij) := by
  ext x i
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, reMat_coord, imMat_coord, Complex.mul_re, Complex.mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Fin.sum_univ_three]
  linear_combination (-((g (i, 0)).re * x 0 + (g (i, 1)).re * x 1 + (g (i, 2)).re * x 2)) *
    Real.sin_sq_add_cos_sq α

theorem imMat_unphase (α : ℝ) (g : Fin 3 × Fin 3 → ℂ) :
    imMat g = (-Real.sin α) • reMat (fun ij => Complex.exp ((α : ℂ) * Complex.I) * g ij) +
      Real.cos α • imMat (fun ij => Complex.exp ((α : ℂ) * Complex.I) * g ij) := by
  ext x i
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, reMat_coord, imMat_coord, Complex.mul_re, Complex.mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Fin.sum_univ_three]
  linear_combination (-((g (i, 0)).im * x 0 + (g (i, 1)).im * x 1 + (g (i, 2)).im * x 2)) *
    Real.sin_sq_add_cos_sq α

theorem reVec_rotC (ψ : ℝ) (x : Fin 3 → ℂ) : reVec (rotC ψ x) = axialRot ψ (reVec x) := by
  ext i
  rw [reVec_coord, Coercive.Internal.ModeRotation.axialRot_apply ψ (reVec x) i]
  simp only [rotC, Complex.re_sum, Complex.re_ofReal_mul, reVec_coord]

theorem imVec_rotC (ψ : ℝ) (x : Fin 3 → ℂ) : imVec (rotC ψ x) = axialRot ψ (imVec x) := by
  ext i
  rw [imVec_coord, Coercive.Internal.ModeRotation.axialRot_apply ψ (imVec x) i]
  simp only [rotC, Complex.im_sum, Complex.im_ofReal_mul, imVec_coord]

theorem rotC_const_mul (ψ : ℝ) (c : ℂ) (x : Fin 3 → ℂ) :
    rotC ψ (fun i => c * x i) = fun i => c * rotC ψ x i := by
  funext i
  simp only [rotC, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem rotCMat_const_mul (ψ : ℝ) (c : ℂ) (g : Fin 3 × Fin 3 → ℂ) :
    rotCMat ψ (fun ij => c * g ij) = fun ij => c * rotCMat ψ g ij := by
  funext ij
  simp only [rotCMat, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem rotC_add (ψ θ : ℝ) (x : Fin 3 → ℂ) : rotC (ψ + θ) x = rotC ψ (rotC θ x) := by
  funext i
  fin_cases i <;>
    simp [rotC, axialRot, unitVector, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring

theorem rotCMat_add (ψ θ : ℝ) (g : Fin 3 × Fin 3 → ℂ) : rotCMat (ψ + θ) g = rotCMat ψ (rotCMat θ g) := by
  funext ij
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;>
    simp [rotCMat, axialRot, unitVector, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring

def frameFlip (x : Fin 3 → ℂ) : Fin 3 → ℂ := fun a => (frameSign a : ℂ) * x a

theorem frameFlip_frameFlip (x : Fin 3 → ℂ) : frameFlip (frameFlip x) = x := by
  funext a
  fin_cases a <;> simp [frameFlip, frameSign]

theorem rotC_frameFlip (θ : ℝ) (x : Fin 3 → ℂ) : rotC (-θ) (frameFlip x) = frameFlip (rotC θ x) := by
  funext i
  fin_cases i
  · simp [rotC, frameFlip, frameSign, axialRot, unitVector, Fin.sum_univ_three]
  · simp [rotC, frameFlip, frameSign, axialRot, unitVector, Fin.sum_univ_three]
    ring
  · simp [rotC, frameFlip, frameSign, axialRot, unitVector, Fin.sum_univ_three]

theorem reVec_frameFlip (x : Fin 3 → ℂ) : reVec (frameFlip x) = flipPoint (reVec x) := by
  ext i
  fin_cases i <;> simp [reVec_coord, frameFlip, frameSign, flipPoint, unitVector]

theorem imVec_frameFlip (x : Fin 3 → ℂ) : imVec (frameFlip x) = flipPoint (imVec x) := by
  ext i
  fin_cases i <;> simp [imVec_coord, frameFlip, frameSign, flipPoint, unitVector]

theorem ae_snd {Q : Space → Prop} (h : ∀ᵐ z : ℝ × Space, Q z.2) : ∀ᵐ y, Q y := by
  have h' : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure Space)), Q z.2 := h
  obtain ⟨σ, hσ⟩ := (Measure.ae_ae_of_ae_prod h').exists
  exact hσ

theorem ae_ne_snd : ∀ᵐ p : ℝ × ℝ, p.2 ≠ 0 := by
  have e : {p : ℝ × ℝ | ¬p.2 ≠ 0} = univ ×ˢ {0} := by
    ext p
    simp
  rw [ae_iff, e, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

theorem weak_smul {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} (h : IsWeakGradient f g)
    (c : ℝ) : IsWeakGradient (fun y => c • f y) (fun y => c • g y) := by
  refine ⟨h.1.smul c, h.2.1.smul c, fun φ hφ i => ?_⟩
  have e1 : (fun y => φ y • (c • g y) (unitVector i)) =
      fun y => c • (φ y • g y (unitVector i)) := by
    funext y
    rw [FunLike.coe_smul, Pi.smul_apply, smul_comm]
  have e2 : (fun y => fderiv ℝ φ y (unitVector i) • c • f y) =
      fun y => c • (fderiv ℝ φ y (unitVector i) • f y) := by
    funext y
    rw [smul_comm]
  rw [e1, e2, integral_smul, integral_smul, h.2.2 φ hφ i, smul_neg]

theorem weak_comb {f₁ f₂ : Space → Space} {g₁ g₂ : Space → (Space →L[ℝ] Space)}
    (h₁ : IsWeakGradient f₁ g₁) (h₂ : IsWeakGradient f₂ g₂) (a b : ℝ) :
    IsWeakGradient (fun y => a • f₁ y + b • f₂ y) (fun y => a • g₁ y + b • g₂ y) :=
  Cert.Internal.SigmaProfileOfHeld.isWeakGradient_add (weak_smul h₁ a) (weak_smul h₂ b)

theorem good_vel {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ξ : ℤ × ℤ} (hξ : ξ.2 = 0) :
    ∀ᵐ y, ∀ ψ, modeVel ξ v 0 (axialRot ψ y) = rotC ψ (modeVel ξ v 0 y) := by
  have hloc := (Coercive.perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv).1
  have hz := Coercive.Internal.ModeRotation.ae_integrable_orbit Coercive.axialRotationHolds_proof hloc
  refine ae_snd ?_
  filter_upwards [hz] with z hz ψ
  have h := Coercive.Internal.ModeRotation.modeVel_rotation_of Coercive.axialRotationHolds_proof ξ ψ hz
  rw [Coercive.FrequencySeminorm.Internal.modeVel_shift ξ hv.periodic_velocity z.1 (axialRot ψ z.2),
    Coercive.FrequencySeminorm.Internal.modeVel_shift ξ hv.periodic_velocity z.1 z.2,
    rotC_const_mul] at h
  funext i
  have hi := congrFun h i
  simp only [hξ, Int.cast_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul] at hi
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) hi

theorem good_grad {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ξ : ℤ × ℤ} (hξ : ξ.2 = 0) :
    ∀ᵐ y, ∀ ψ, modeGrad ξ G 0 (axialRot ψ y) = rotCMat ψ (modeGrad ξ G 0 y) := by
  have hloc := (Coercive.perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv).2.1
  have hz := Coercive.Internal.ModeRotation.ae_integrable_orbit Coercive.axialRotationHolds_proof hloc
  refine ae_snd ?_
  filter_upwards [hz] with z hz ψ
  have h := Coercive.Internal.ModeRotation.modeGrad_rotation_of Coercive.axialRotationHolds_proof ξ ψ hz
  rw [Coercive.FrequencySeminorm.Internal.modeGrad_shift ξ hv.periodic_gradient z.1 (axialRot ψ z.2),
    Coercive.FrequencySeminorm.Internal.modeGrad_shift ξ hv.periodic_gradient z.1 z.2,
    rotCMat_const_mul] at h
  funext ij
  have hi := congrFun h ij
  simp only [hξ, Int.cast_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul] at hi
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) hi

theorem good_rot {U : Space → Fin 3 → ℂ} {y : Space} (hy : ∀ ψ, U (axialRot ψ y) = rotC ψ (U y))
    (θ : ℝ) : ∀ ψ, U (axialRot ψ (axialRot θ y)) = rotC ψ (U (axialRot θ y)) := by
  intro ψ
  rw [← Coercive.axialRotationHolds_proof.2.1, hy, hy, rotC_add]

theorem flip_ae {U : Space → Fin 3 → ℂ} (hgood : ∀ᵐ y, ∀ ψ, U (axialRot ψ y) = rotC ψ (U y))
    (hflip : ∀ᵐ p ∂(volume.restrict halfPlane),
      U (planePoint (p.1, -p.2)) = frameFlip (U (planePoint p))) :
    ∀ᵐ y, U (flipPoint y) = frameFlip (U y) := by
  have hA : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hQ : MeasurableSet halfPlane := measurableSet_Ioi.prod measurableSet_Ioi
  have hGA := ae_planePoint_of_ae hgood fun θ y hy => good_rot hy θ
  have hρ : MeasurePreserving (Prod.map (id : ℝ → ℝ) (fun t : ℝ => -t))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (MeasurePreserving.id _).prod (Measure.measurePreserving_neg _)
  have hGA' : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ univ)),
      ∀ ψ, U (axialRot ψ (planePoint (p.1, -p.2))) = rotC ψ (U (planePoint (p.1, -p.2))) := by
    have h1 := (ae_restrict_iff' hA).1 hGA
    have h2 := hρ.quasiMeasurePreserving.ae h1
    rw [ae_restrict_iff' hA]
    filter_upwards [h2] with p hp hpA
    exact hp ⟨hpA.1, mem_univ _⟩
  have hF1 := (ae_restrict_iff' hQ).1 hflip
  have hF2 := hρ.quasiMeasurePreserving.ae hF1
  have hall : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ univ)),
      (∀ ψ, U (axialRot ψ (planePoint p)) = rotC ψ (U (planePoint p))) ∧
      (∀ ψ, U (axialRot ψ (planePoint (p.1, -p.2))) = rotC ψ (U (planePoint (p.1, -p.2)))) ∧
      U (planePoint (p.1, -p.2)) = frameFlip (U (planePoint p)) := by
    filter_upwards [hGA, hGA', ae_restrict_of_ae hF1, ae_restrict_of_ae hF2, ae_restrict_of_ae ae_ne_snd,
      ae_restrict_mem hA] with p h1 h2 h3 h4 h5 h6
    refine ⟨h1, h2, ?_⟩
    rcases lt_or_gt_of_ne h5 with hneg | hpos
    · have h7 := h4 ⟨h6.1, neg_pos.2 hneg⟩
      simp only [Prod.map_fst, Prod.map_snd, id, neg_neg, Prod.mk.eta] at h7
      rw [h7, frameFlip_frameFlip]
      rfl
    · exact h3 ⟨h6.1, hpos⟩
  filter_upwards [ae_pointPlane hall] with y hy
  obtain ⟨h1, h2, h4⟩ := hy
  have hy0 : axialRot (pointAngle y) (planePoint (pointPlane y)) = y := rot_pointAngle y
  have hfy : axialRot (-pointAngle y) (planePoint ((pointPlane y).1, -(pointPlane y).2)) = flipPoint y := by
    rw [Internal.FlipDecay.rot_plane_flip, neg_neg, hy0]
  rw [← hfy, h2, h4, rotC_frameFlip, ← h1, hy0]

theorem cnormSq_phase {β : Type*} [Fintype β] (α : ℝ) (x : β → ℂ) :
    cnormSq (fun i => Complex.exp ((α : ℂ) * Complex.I) * x i) = cnormSq x := by
  simp only [cnormSq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem matSq_nonneg' (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem reVec_sq_le (x : Fin 3 → ℂ) : ‖reVec x‖ ^ 2 ≤ cnormSq x := by
  rw [cnormSq_eq_re_im]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem imVec_sq_le (x : Fin 3 → ℂ) : ‖imVec x‖ ^ 2 ≤ cnormSq x := by
  rw [cnormSq_eq_re_im]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem sixth_le {f : Space → Space} {u : Space → Fin 3 → ℂ} (hf : ∀ y, ‖f y‖ ^ 2 ≤ cnormSq (u y))
    (h : ∫⁻ y, ENNReal.ofReal (cnormSq (u y) ^ 3) < ⊤) : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_) h
  calc ‖f y‖ ^ 6 = (‖f y‖ ^ 2) ^ 3 := by ring
    _ ≤ cnormSq (u y) ^ 3 := pow_le_pow_left₀ (sq_nonneg _) (hf y) 3

theorem modeGrad_finite {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (ξ : ℤ × ℤ) :
    ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ξ G 0 y)) < ⊤ := by
  have hpar := CoerciveWeak.modeSquareSumHolds_closed.2.1 G hv.measurable_gradient hv.periodic_gradient
    hv.gradient_finite
  have hle := ENNReal.le_tsum (f := fun ι : ℤ × ℤ =>
    ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ι G σ y))) ξ
  have hσ : ∀ σ : ℝ, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ξ G σ y)) =
      ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ξ G 0 y)) := by
    intro σ
    refine lintegral_congr fun y => ?_
    rw [Coercive.FrequencySeminorm.Internal.modeGrad_shift ξ hv.periodic_gradient σ y, cnormSq_phase]
  have hconst : ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ξ G σ y)) =
      ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ξ G 0 y)) := by
    simp_rw [hσ]
    rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
  rw [← hconst]
  refine lt_of_le_of_lt hle ?_
  rw [← hpar]
  exact hv.gradient_finite

theorem matSq_lintegral_finite {u : Space → Fin 3 × Fin 3 → ℂ} (h : ∫⁻ y, ENNReal.ofReal (cnormSq (u y)) < ⊤)
    (f : (Fin 3 × Fin 3 → ℂ) → (Space →L[ℝ] Space)) (hf : ∀ x, matSq (f x) ≤ cnormSq x) :
    ∫⁻ y, ENNReal.ofReal (matSq (f (u y))) < ⊤ :=
  lt_of_le_of_lt (lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hf (u y))) h

theorem labelHarmonic_flip {mm : ℕ} {ι : ℤ × ℤ} (h : labelAzimuth mm ι = 0) :
    labelHarmonic mm (labelFlip ι) = labelHarmonic mm ι := by
  simp only [labelAzimuth] at h
  simp only [labelHarmonic, labelFlip, labelTime, labelAzimuth, Prod.mk.injEq]
  constructor
  · ring
  · rw [neg_mul, h, neg_zero]

theorem cancel_two_pi {a b : ℝ≥0∞}
    (h : ENNReal.ofReal 2 * (ENNReal.ofReal (2 * Real.pi) * a) ≤ ENNReal.ofReal (2 * Real.pi) * b) :
    ENNReal.ofReal 2 * a ≤ b := by
  rw [mul_left_comm] at h
  exact (ENNReal.mul_le_mul_iff_right (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top).1 h

theorem norm_planePoint_sq (p : ℝ × ℝ) : ‖planePoint p‖ ^ 2 = planeRadius p ^ 2 := by
  rw [norm_sq_coord, planePoint_zero, planePoint_one, planePoint_two, planeRadius,
    Real.sq_sqrt (by positivity)]
  ring

end Internal.SquareModes

open Coercive (reVec imVec reMat imMat) in
open Internal.SquareModes Internal.SquareTransfer in
theorem modeSquareInverseSquare_of (hW : SquareExteriorSpaceWeakStatement) : ModeSquareInverseSquare := by
  intro R hR Γ P v G H g hv _ mm ι hazi hfe
  have hξ : (labelHarmonic mm ι).2 = 0 := hazi
  obtain ⟨σ, hσ⟩ := ((CoerciveWeak.modeDerivativeHolds_closed Γ P v G H g hv (labelHarmonic mm ι)).1).exists
  have hUσ : ∀ y, modeVel (labelHarmonic mm ι) v σ y = fun i =>
      Complex.exp (((2 * Real.pi * (labelHarmonic mm ι).1 * σ : ℝ) : ℂ) * Complex.I) *
        modeVel (labelHarmonic mm ι) v 0 y i :=
    fun y => Coercive.FrequencySeminorm.Internal.modeVel_shift _ hv.periodic_velocity σ y
  have hMσ : ∀ y, modeGrad (labelHarmonic mm ι) G σ y = fun ij =>
      Complex.exp (((2 * Real.pi * (labelHarmonic mm ι).1 * σ : ℝ) : ℂ) * Complex.I) *
        modeGrad (labelHarmonic mm ι) G 0 y ij :=
    fun y => Coercive.FrequencySeminorm.Internal.modeGrad_shift _ hv.periodic_gradient σ y
  set α : ℝ := 2 * Real.pi * (labelHarmonic mm ι).1 * σ with hα
  have hre : IsWeakGradient (fun y => reVec (modeVel (labelHarmonic mm ι) v 0 y))
      (fun y => reMat (modeGrad (labelHarmonic mm ι) G 0 y)) := by
    have e1 : (fun y => reVec (modeVel (labelHarmonic mm ι) v 0 y)) = fun y =>
        Real.cos α • reVec (modeVel (labelHarmonic mm ι) v σ y) +
          Real.sin α • imVec (modeVel (labelHarmonic mm ι) v σ y) := by
      funext y
      rw [hUσ]
      exact reVec_unphase α _
    have e2 : (fun y => reMat (modeGrad (labelHarmonic mm ι) G 0 y)) = fun y =>
        Real.cos α • reMat (modeGrad (labelHarmonic mm ι) G σ y) +
          Real.sin α • imMat (modeGrad (labelHarmonic mm ι) G σ y) := by
      funext y
      rw [hMσ]
      exact reMat_unphase α _
    rw [e1, e2]
    exact weak_comb hσ.1 hσ.2 _ _
  have him : IsWeakGradient (fun y => imVec (modeVel (labelHarmonic mm ι) v 0 y))
      (fun y => imMat (modeGrad (labelHarmonic mm ι) G 0 y)) := by
    have e1 : (fun y => imVec (modeVel (labelHarmonic mm ι) v 0 y)) = fun y =>
        (-Real.sin α) • reVec (modeVel (labelHarmonic mm ι) v σ y) +
          Real.cos α • imVec (modeVel (labelHarmonic mm ι) v σ y) := by
      funext y
      rw [hUσ]
      exact imVec_unphase α _
    have e2 : (fun y => imMat (modeGrad (labelHarmonic mm ι) G 0 y)) = fun y =>
        (-Real.sin α) • reMat (modeGrad (labelHarmonic mm ι) G σ y) +
          Real.cos α • imMat (modeGrad (labelHarmonic mm ι) G σ y) := by
      funext y
      rw [hMσ]
      exact imMat_unphase α _
    rw [e1, e2]
    exact weak_comb hσ.1 hσ.2 _ _
  have h6 := modeVelSixthFinite Γ P v G H g hv (labelHarmonic mm ι)
  have hMfin := modeGrad_finite hv (labelHarmonic mm ι)
  have hgV := good_vel hv hξ
  have hgM := good_grad hv hξ
  have hfe' : ∀ᵐ p ∂(volume.restrict halfPlane),
      modeVel (labelHarmonic mm ι) v 0 (planePoint (p.1, -p.2)) =
        frameFlip (modeVel (labelHarmonic mm ι) v 0 (planePoint p)) := by
    filter_upwards [hfe] with p hp
    have e := hp
    simp only [labelVel, labelHarmonic_flip hazi] at e
    exact e
  have hfl := flip_ae hgV hfe'
  have hWr := hW R hR _ _ hre (sixth_le (fun y => reVec_sq_le _) h6)
    (matSq_lintegral_finite hMfin reMat fun x => by
      rw [← Coercive.SmoothBaseInternal.matNorm_re_im]
      exact le_add_of_nonneg_right (matSq_nonneg' _))
    (fun ψ => hgV.mono fun y hy => by simp only [hy ψ, reVec_rotC])
    (hfl.mono fun y hy => by simp only [hy, reVec_frameFlip])
  have hWi := hW R hR _ _ him (sixth_le (fun y => imVec_sq_le _) h6)
    (matSq_lintegral_finite hMfin imMat fun x => by
      rw [← Coercive.SmoothBaseInternal.matNorm_re_im]
      exact le_add_of_nonneg_left (matSq_nonneg' _))
    (fun ψ => hgV.mono fun y hy => by simp only [hy ψ, imVec_rotC])
    (hfl.mono fun y hy => by simp only [hy, imVec_frameFlip])
  have hr2 : AEMeasurable (fun y => ‖reVec (modeVel (labelHarmonic mm ι) v 0 y)‖ ^ 2) :=
    hre.1.aestronglyMeasurable.norm.aemeasurable.pow_const 2
  have hi2 : AEMeasurable (fun y => ‖imVec (modeVel (labelHarmonic mm ι) v 0 y)‖ ^ 2) :=
    him.1.aestronglyMeasurable.norm.aemeasurable.pow_const 2
  have hn2 : AEMeasurable (fun y : Space => ‖y‖ ^ 2) := (measurable_norm.pow_const 2).aemeasurable
  have hfr : AEMeasurable (fun y => matSq (reMat (modeGrad (labelHarmonic mm ι) G 0 y))) :=
    (continuous_matSq_map.comp_aestronglyMeasurable hre.2.1.aestronglyMeasurable).aemeasurable
  have hfi : AEMeasurable (fun y => matSq (imMat (modeGrad (labelHarmonic mm ι) G 0 y))) :=
    (continuous_matSq_map.comp_aestronglyMeasurable him.2.1.aestronglyMeasurable).aemeasurable
  have hm1 : AEMeasurable (fun y =>
      ENNReal.ofReal (‖reVec (modeVel (labelHarmonic mm ι) v 0 y)‖ ^ 2 / ‖y‖ ^ 2)) :=
    (hr2.div hn2).ennreal_ofReal
  have hF1 : AEMeasurable (fun y => ENNReal.ofReal
      ((‖reVec (modeVel (labelHarmonic mm ι) v 0 y)‖ ^ 2 +
        ‖imVec (modeVel (labelHarmonic mm ι) v 0 y)‖ ^ 2) / ‖y‖ ^ 2)) :=
    ((hr2.add hi2).div hn2).ennreal_ofReal
  have hm3 : AEMeasurable (fun y =>
      ENNReal.ofReal (matSq (reMat (modeGrad (labelHarmonic mm ι) G 0 y)))) :=
    hfr.ennreal_ofReal
  have hF2 : AEMeasurable (fun y => ENNReal.ofReal
      (matSq (reMat (modeGrad (labelHarmonic mm ι) G 0 y)) +
        matSq (imMat (modeGrad (labelHarmonic mm ι) G 0 y)))) :=
    (hfr.add hfi).ennreal_ofReal
  have eL : ∫⁻ y in spaceSquareExterior R, ENNReal.ofReal
      ((‖reVec (modeVel (labelHarmonic mm ι) v 0 y)‖ ^ 2 +
        ‖imVec (modeVel (labelHarmonic mm ι) v 0 y)‖ ^ 2) / ‖y‖ ^ 2) =
      (∫⁻ y in spaceSquareExterior R,
        ENNReal.ofReal (‖reVec (modeVel (labelHarmonic mm ι) v 0 y)‖ ^ 2 / ‖y‖ ^ 2)) +
      ∫⁻ y in spaceSquareExterior R,
        ENNReal.ofReal (‖imVec (modeVel (labelHarmonic mm ι) v 0 y)‖ ^ 2 / ‖y‖ ^ 2) := by
    rw [← lintegral_add_left' hm1.restrict]
    refine lintegral_congr fun y => ?_
    rw [add_div, ENNReal.ofReal_add (by positivity) (by positivity)]
  have eR : ∫⁻ y in spaceSquareExterior R, ENNReal.ofReal
      (matSq (reMat (modeGrad (labelHarmonic mm ι) G 0 y)) +
        matSq (imMat (modeGrad (labelHarmonic mm ι) G 0 y))) =
      (∫⁻ y in spaceSquareExterior R,
        ENNReal.ofReal (matSq (reMat (modeGrad (labelHarmonic mm ι) G 0 y)))) +
      ∫⁻ y in spaceSquareExterior R,
        ENNReal.ofReal (matSq (imMat (modeGrad (labelHarmonic mm ι) G 0 y))) := by
    rw [← lintegral_add_left' hm3.restrict]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_add (matSq_nonneg' _) (matSq_nonneg' _)]
  have h3 : ENNReal.ofReal 2 * ∫⁻ y in spaceSquareExterior R, ENNReal.ofReal
      ((‖reVec (modeVel (labelHarmonic mm ι) v 0 y)‖ ^ 2 +
        ‖imVec (modeVel (labelHarmonic mm ι) v 0 y)‖ ^ 2) / ‖y‖ ^ 2) ≤
      ∫⁻ y in spaceSquareExterior R, ENNReal.ofReal
      (matSq (reMat (modeGrad (labelHarmonic mm ι) G 0 y)) +
        matSq (imMat (modeGrad (labelHarmonic mm ι) G 0 y))) := by
    rw [eL, eR, mul_add]
    exact add_le_add hWr hWi
  rw [lintegral_spaceSquare_ae hF1
      (by
        filter_upwards [hgV] with y hy θ
        simp only [hy θ, reVec_rotC, imVec_rotC, Coercive.RotationInternal.axialRot_norm]) R,
    lintegral_spaceSquare_ae hF2
      (by
        filter_upwards [hgM] with y hy θ
        simp only [Coercive.SmoothBaseInternal.matNorm_re_im, hy θ,
          Internal.AngularPlane.cnormSq_rotCMat]) R] at h3
  have h4 := cancel_two_pi h3
  have hPm := measurableSet_planeSquare R
  calc ENNReal.ofReal 2 * ∫⁻ p in planeSquareExterior R,
        ENNReal.ofReal (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2 * p.1)
      = ENNReal.ofReal 2 * ∫⁻ p in planeSquareExterior R, ENNReal.ofReal p.1 * ENNReal.ofReal
          ((‖reVec (modeVel (labelHarmonic mm ι) v 0 (planePoint p))‖ ^ 2 +
            ‖imVec (modeVel (labelHarmonic mm ι) v 0 (planePoint p))‖ ^ 2) / ‖planePoint p‖ ^ 2) := by
        congr 1
        refine setLIntegral_congr_fun hPm fun p hp => ?_
        rw [← ENNReal.ofReal_mul hp.1.1.le, ← cnormSq_eq_re_im, norm_planePoint_sq]
        congr 1
        simp only [labelVel]
        ring
    _ ≤ ∫⁻ p in planeSquareExterior R, ENNReal.ofReal p.1 * ENNReal.ofReal
          (matSq (reMat (modeGrad (labelHarmonic mm ι) G 0 (planePoint p))) +
            matSq (imMat (modeGrad (labelHarmonic mm ι) G 0 (planePoint p)))) := h4
    _ = ∫⁻ p in planeSquareExterior R, ENNReal.ofReal (cnormSq (labelGrad mm ι G p) * p.1) := by
        refine setLIntegral_congr_fun hPm fun p hp => ?_
        rw [Coercive.SmoothBaseInternal.matNorm_re_im, ← ENNReal.ofReal_mul hp.1.1.le, mul_comm]
        rfl

theorem modeSquareInverseSquare_of_smooth (h : SquareExteriorSmoothStatement) :
    ModeSquareInverseSquare :=
  modeSquareInverseSquare_of (squareExteriorSpaceWeak_of (squareExteriorSpaceSmooth_of h))

end TailBand

end CertCell

end Breakdown
