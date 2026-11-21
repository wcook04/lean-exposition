import Breakdown.CertCell.InstancePairStatements
import Breakdown.CertCell.PinHalfPlane
import Breakdown.CertCell.HalfPlaneReduction
import Breakdown.CertCell.ModeFlip
import Breakdown.CertCell.ModeTermFlip
import Breakdown.FracCell.RowTurnPair

open scoped ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace InstancePair

namespace Internal.ByPartsModes

open Instance
open Coercive.Internal.ModeRotation (expFactor modeAverage_eq expFactor_add_period)
open TailBand.Internal.FlipDecay (rot_neg_flip axialRot_add_period axialRot_neg_add_period)
open Bridge.Internal.PinHalf (flip_rot rot_unit_flip rot_smul_apply)
open Bridge.Internal.ModeFlip (flipPoint_apply frameSign_mul_self integral_neg_of_periodic expFactor_flip
  flipPoint_unitVector)

theorem expFactor_flipLabel (ξ : ℤ × ℤ) (τ φ : ℝ) : expFactor (flipLabel ξ) τ φ = expFactor ξ τ (-φ) := by
  have h := expFactor_flip ξ τ (-φ)
  rwa [neg_neg] at h

theorem modeGrad_flip_pair {B B' : ℝ → Space → (Space →L[ℝ] Space)}
    (hB : ∀ σ y a, B σ (flipPoint y) (flipPoint a) = flipPoint (B' σ y a)) (ξ : ℤ × ℤ) (σ : ℝ) (y : Space)
    (a c : Fin 3) :
    modeGrad (flipLabel ξ) B σ (flipPoint y) (a, c) =
      ((frameSign a * frameSign c : ℝ) : ℂ) * modeGrad ξ B' σ y (a, c) := by
  set g : ℝ → ℝ → ℂ := fun τ φ => expFactor ξ τ φ *
    ((axialRot (-φ) (B' (σ + τ) (axialRot φ y) (axialRot φ (unitVector c))) a : ℝ) : ℂ) with hg
  have hper : ∀ τ, Function.Periodic (g τ) (2 * Real.pi) := by
    intro τ φ
    simp only [hg, expFactor_add_period, axialRot_add_period, axialRot_neg_add_period]
  have hpt : ∀ τ φ, expFactor (flipLabel ξ) τ φ *
      ((axialRot (-φ) (B (σ + τ) (axialRot φ (flipPoint y)) (axialRot φ (unitVector c))) a : ℝ) : ℂ) =
      ((frameSign a * frameSign c : ℝ) : ℂ) * g τ (-φ) := by
    intro τ φ
    rw [expFactor_flipLabel, flip_rot, rot_unit_flip φ c, map_smul, hB, rot_smul_apply, rot_neg_flip]
    simp only [hg, neg_neg]
    push_cast
    ring
  have hin : ∀ τ, (∫ φ in (0 : ℝ)..(2 * Real.pi), expFactor (flipLabel ξ) τ φ *
      ((axialRot (-φ) (B (σ + τ) (axialRot φ (flipPoint y)) (axialRot φ (unitVector c))) a : ℝ) : ℂ)) =
      ((frameSign a * frameSign c : ℝ) : ℂ) * ∫ φ in (0 : ℝ)..(2 * Real.pi), g τ φ := by
    intro τ
    rw [intervalIntegral.integral_congr fun φ _ => hpt τ φ, intervalIntegral.integral_const_mul,
      integral_neg_of_periodic _ (hper τ)]
  simp only [modeGrad, modeAverage_eq]
  rw [intervalIntegral.integral_congr fun τ _ => hin τ, intervalIntegral.integral_const_mul]
  ring

theorem modeVel_flip_pair {v v' : ℝ → Space → Space} (hv : ∀ σ y, v σ (flipPoint y) = flipPoint (v' σ y))
    (ξ : ℤ × ℤ) (σ : ℝ) (y : Space) (a : Fin 3) :
    modeVel (flipLabel ξ) v σ (flipPoint y) a = (frameSign a : ℂ) * modeVel ξ v' σ y a := by
  set g : ℝ → ℝ → ℂ := fun τ φ => expFactor ξ τ φ *
    ((axialRot (-φ) (v' (σ + τ) (axialRot φ y)) a : ℝ) : ℂ) with hg
  have hper : ∀ τ, Function.Periodic (g τ) (2 * Real.pi) := by
    intro τ φ
    simp only [hg, expFactor_add_period, axialRot_add_period, axialRot_neg_add_period]
  have hpt : ∀ τ φ, expFactor (flipLabel ξ) τ φ *
      ((axialRot (-φ) (v (σ + τ) (axialRot φ (flipPoint y))) a : ℝ) : ℂ) = (frameSign a : ℂ) * g τ (-φ) := by
    intro τ φ
    rw [expFactor_flipLabel, flip_rot, hv, rot_neg_flip]
    simp only [hg, neg_neg]
    push_cast
    ring
  have hin : ∀ τ, (∫ φ in (0 : ℝ)..(2 * Real.pi), expFactor (flipLabel ξ) τ φ *
      ((axialRot (-φ) (v (σ + τ) (axialRot φ (flipPoint y))) a : ℝ) : ℂ)) =
      (frameSign a : ℂ) * ∫ φ in (0 : ℝ)..(2 * Real.pi), g τ φ := by
    intro τ
    rw [intervalIntegral.integral_congr fun φ _ => hpt τ φ, intervalIntegral.integral_const_mul,
      integral_neg_of_periodic _ (hper τ)]
  simp only [modeVel, modeAverage_eq]
  rw [intervalIntegral.integral_congr fun τ _ => hin τ, intervalIntegral.integral_const_mul]
  ring


abbrev flipEquiv : Space ≃ₗᵢ[ℝ] Space := Bridge.Internal.ModeTermFlip.flipIsometryEquiv

abbrev flipCLM : Space →L[ℝ] Space := (flipEquiv.toContinuousLinearEquiv : Space →L[ℝ] Space)

theorem flipEquiv_apply (y : Space) : flipEquiv y = flipPoint y := rfl

theorem flipCLM_apply (y : Space) : flipCLM y = flipPoint y := rfl

theorem flipPoint_flipPoint (y : Space) : flipPoint (flipPoint y) = y :=
  Bridge.Internal.HalfPlaneReduction.flipPoint_flipPoint y

theorem norm_flipPoint (y : Space) : ‖flipPoint y‖ = ‖y‖ := flipEquiv.norm_map y

def flippedField (b : ℝ → Space → Space) : ℝ → Space → Space := fun σ y => flipPoint (b σ (flipPoint y))

theorem flippedField_flip (b : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    b σ (flipPoint y) = flipPoint (flippedField b σ y) := by
  simp only [flippedField, flipPoint_flipPoint]

theorem gradField_flipped (b : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    gradField (flippedField b) σ y = flipCLM.comp ((gradField b σ (flipPoint y)).comp flipCLM) := by
  have e : flippedField b σ = (flipEquiv.toContinuousLinearEquiv) ∘ ((b σ) ∘ flipEquiv.toContinuousLinearEquiv) :=
    rfl
  unfold gradField
  rw [e, ContinuousLinearEquiv.comp_fderiv, ContinuousLinearEquiv.comp_right_fderiv]
  rfl

theorem gradField_flip_rel (b : ℝ → Space → Space) (σ : ℝ) (y a : Space) :
    gradField b σ (flipPoint y) (flipPoint a) = flipPoint (gradField (flippedField b) σ y a) := by
  rw [gradField_flipped]
  simp only [ContinuousLinearMap.comp_apply, flipCLM_apply, flipPoint_flipPoint]

theorem abs_frameSign (a : Fin 3) : |frameSign a| = 1 := by
  unfold frameSign
  split_ifs <;> norm_num

theorem entrySquareSum_flip (A : Space →L[ℝ] Space) : matSq (flipCLM.comp (A.comp flipCLM)) = matSq A := by
  unfold matSq
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.comp_apply, flipCLM_apply, flipPoint_unitVector, map_smul, norm_flipPoint,
    norm_smul, Real.norm_eq_abs, abs_frameSign, one_mul]

theorem lintegral_flip (h : Space → ℝ≥0∞) : ∫⁻ y, h (flipPoint y) = ∫⁻ y, h y :=
  flipEquiv.measurePreserving.lintegral_comp_emb flipEquiv.toHomeomorph.measurableEmbedding h

theorem measurePreserving_flipSnd :
    MeasurePreserving (fun z : ℝ × Space => (z.1, flipPoint z.2)) volume volume :=
  (MeasurePreserving.id (volume : Measure ℝ)).prod flipEquiv.measurePreserving

theorem labelHarmonic_labelFlip (m : ℕ) (ι : ℤ × ℤ) :
    labelHarmonic m (labelFlip ι) = flipLabel (labelHarmonic m ι) := by
  simp only [labelHarmonic, labelTime, labelAzimuth, labelFlip, flipLabel, Prod.mk.injEq]
  constructor <;> ring

theorem flipLabel_flipLabel (ξ : ℤ × ℤ) : flipLabel (flipLabel ξ) = ξ := by
  simp [flipLabel]

theorem flipLabel_neg (ξ : ℤ × ℤ) : flipLabel (-ξ) = -flipLabel ξ := by
  simp [flipLabel]

theorem pointPlane_flip (y : Space) : (pointPlane (flipPoint y)).1 = (pointPlane y).1 := by
  simp only [pointPlane, flipPoint_apply, frameSign]
  norm_num


theorem frameSign_ne_zero (a : Fin 3) : (frameSign a : ℂ) ≠ 0 := by
  unfold frameSign
  split_ifs <;> norm_num

theorem flipped_shape {m : ℕ} {S : Finset (ℤ × ℤ)} {b : ℝ → Space → Space} (hb : ActuatorShapeFacts m S b) :
    ActuatorShapeFacts m (S.image labelFlip) (flippedField b) where
  measurable :=
    flipEquiv.continuous.comp_aestronglyMeasurable (hb.measurable.comp_measurePreserving measurePreserving_flipSnd)
  periodic := fun σ y => by simp only [flippedField, hb.periodic σ]
  bounded_support := by
    obtain ⟨B, R, h⟩ := hb.bounded_support
    refine ⟨B, R, fun σ y => ⟨?_, fun hy => ?_⟩⟩
    · rw [flippedField, norm_flipPoint]
      exact (h σ _).1
    · rw [flippedField, (h σ _).2 (by rwa [norm_flipPoint]), ← flipEquiv_apply, map_zero]
  square_finite := by
    have e : ∀ σ, ∫⁻ y, ENNReal.ofReal (‖flippedField b σ y‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (‖b σ y‖ ^ 2) := by
      intro σ
      simp only [flippedField, norm_flipPoint]
      exact lintegral_flip (fun y => ENNReal.ofReal (‖b σ y‖ ^ 2))
    unfold periodLIntegral
    simp_rw [e]
    exact hb.square_finite
  gradient_measurable := by
    have hc : Continuous (fun A : Space →L[ℝ] Space => flipCLM.comp (A.comp flipCLM)) :=
      continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
    have h := hc.comp_aestronglyMeasurable (hb.gradient_measurable.comp_measurePreserving measurePreserving_flipSnd)
    refine h.congr (Eventually.of_forall fun z => ?_)
    exact (gradField_flipped b z.1 z.2).symm
  gradient_periodic := fun σ y => by rw [gradField_flipped, gradField_flipped, hb.gradient_periodic]
  gradient_finite := by
    have e : ∀ σ, ∫⁻ y, ENNReal.ofReal (matSq (gradField (flippedField b) σ y)) =
        ∫⁻ y, ENNReal.ofReal (matSq (gradField b σ y)) := by
      intro σ
      simp only [gradField_flipped, entrySquareSum_flip]
      exact lintegral_flip (fun y => ENNReal.ofReal (matSq (gradField b σ y)))
    unfold periodLIntegral
    simp_rw [e]
    exact hb.gradient_finite
  weak_gradient := by
    intro σ
    have h := Bridge.Internal.ModeFlip.weakGradient_flip flipEquiv flipEquiv_apply (hb.weak_gradient σ) 1
      (by norm_num)
    simp only [one_smul] at h
    have e : gradField (flippedField b) σ = fun y => flipCLM.comp ((gradField b σ (flipEquiv y)).comp flipCLM) :=
      funext (gradField_flipped b σ)
    rw [e]
    exact h
  modes_in := by
    intro ξ σ y hy hne
    have hrel := modeVel_flip_pair (v := b) (v' := flippedField b) (flippedField_flip b) ξ σ y
    have hne' : modeVel (flipLabel ξ) b σ (flipPoint y) ≠ 0 := by
      intro h0
      apply hne
      funext a
      have h1 := hrel a
      rw [h0] at h1
      have h2 : (frameSign a : ℂ) * modeVel ξ (flippedField b) σ y a = 0 := by
        rw [← h1]
        rfl
      exact (mul_eq_zero.1 h2).resolve_left (frameSign_ne_zero a)
    obtain ⟨ι, hι, hιe⟩ := hb.modes_in (flipLabel ξ) σ (flipPoint y) (by rwa [pointPlane_flip]) hne'
    refine ⟨labelFlip ι, Finset.mem_image_of_mem _ hι, ?_⟩
    rw [labelHarmonic_labelFlip]
    rcases hιe with h | h
    · left
      rw [h, flipLabel_flipLabel]
    · right
      rw [h, flipLabel_neg, flipLabel_flipLabel]
  invariant := by
    set θ : ℝ := Real.pi / m with hθ
    have hT : MeasurePreserving (fun z : ℝ × Space => (z.1 + 1 / 2, axialRot (-θ) (flipPoint z.2))) volume volume :=
      (measurePreserving_add_right volume (1 / 2 : ℝ)).prod
        ((Coercive.RotationInternal.axialRotEquiv (-θ)).measurePreserving.comp flipEquiv.measurePreserving)
    filter_upwards [hT.quasiMeasurePreserving.ae hb.invariant, hb.invariant] with z h1 h2
    obtain ⟨σ, y⟩ := z
    constructor
    · have e1 : σ + 1 / 2 + 1 / 2 = σ + 1 := by ring
      have h3 := h1.1
      simp only at h3
      rw [e1, hb.periodic, Coercive.RotationInternal.axialRot_self_neg] at h3
      simp only [flippedField]
      rw [Bridge.Internal.HalfPlaneReduction.flipPoint_axialRot θ y, h3,
        Bridge.Internal.HalfPlaneReduction.flipPoint_axialRot, Coercive.RotationInternal.axialRot_self_neg]
    · simp only [flippedField, flipPoint_flipPoint]
      rw [h2.2]


open Bridge.Internal.PinHalf (pairDensity goodSet goodSet_rot ae_goodSet aesm_pairDensity_zero
  locallyIntegrable_of_squareSum measurableSet_halfPlane) in
theorem modeGrad_gradField_ae_zero (hgm : ActuatorGradientModes) {m : ℕ} (hm : 0 < m) {S : Finset (ℤ × ℤ)}
    {b : ℝ → Space → Space} (hb : ActuatorShapeFacts m S b) {ξ : ℤ × ℤ}
    (hξ : ∀ ι ∈ S, labelHarmonic m ι ≠ ξ ∧ labelHarmonic m ι ≠ -ξ) (σ : ℝ) :
    ∀ᵐ y, modeGrad ξ (gradField b) σ y = 0 := by
  set B := gradField b with hBdef
  set B' := gradField (flippedField b) with hB'def
  have h1 := hgm m S b hm hb ξ hξ
  have h2 := hgm m (S.image labelFlip) (flippedField b) hm (flipped_shape hb) (flipLabel ξ) (by
    intro ι hι
    obtain ⟨ι₀, hι₀, rfl⟩ := Finset.mem_image.1 hι
    rw [labelHarmonic_labelFlip, ← flipLabel_neg]
    exact ⟨fun h => (hξ ι₀ hι₀).1 (by simpa [flipLabel_flipLabel] using congrArg flipLabel h),
      fun h => (hξ ι₀ hι₀).2 (by simpa [flipLabel_flipLabel] using congrArg flipLabel h)⟩)
  have hpair : ∀ y, modeGrad (flipLabel ξ) B' 0 y = 0 → modeGrad ξ B 0 (flipPoint y) = 0 := by
    intro y h0
    funext ab
    obtain ⟨a, c⟩ := ab
    have h := modeGrad_flip_pair (B := B) (B' := B') (gradField_flip_rel b) (flipLabel ξ) 0 y a c
    rw [flipLabel_flipLabel, h0] at h
    rw [h]
    simp
  have hpd : ∀ y, modeGrad ξ B 0 y = 0 → pairDensity ξ B B 0 y = 0 := by
    intro y h0
    simp [pairDensity, cdotMat, h0]
  have hli := locallyIntegrable_of_squareSum hb.gradient_measurable hb.gradient_periodic hb.gradient_finite
  have hS := ae_goodSet hb.gradient_periodic hb.gradient_periodic hli hli
  have hmeas : AEMeasurable (fun y => ENNReal.ofReal (pairDensity ξ B B 0 y)) volume :=
    (aesm_pairDensity_zero hb.gradient_measurable hb.gradient_measurable hb.gradient_periodic
      hb.gradient_periodic ξ).aemeasurable.ennreal_ofReal
  have hint := Bridge.Internal.HalfPlaneReduction.meridian_lintegral
    (fun y => ENNReal.ofReal (pairDensity ξ B B 0 y)) hmeas (goodSet B B) (goodSet_rot B B) hS (ae_iff.1 hS)
    (fun φ y hy => by simp only [hy ξ φ])
  rw [Bridge.Internal.HalfPlaneReduction.meridian_split
    (fun p => ENNReal.ofReal (pairDensity ξ B B 0 (planePoint p)) * ENNReal.ofReal p.1)] at hint
  have z1 : ∫⁻ p in halfPlane, ENNReal.ofReal (pairDensity ξ B B 0 (planePoint p)) * ENNReal.ofReal p.1 = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [(ae_restrict_iff' measurableSet_halfPlane).2 h1] with p hp
    simp [hpd _ hp]
  have z2 : ∫⁻ p in halfPlane, ENNReal.ofReal (pairDensity ξ B B 0 (planePoint (p.1, -p.2))) *
      ENNReal.ofReal (p.1, -p.2).1 = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [(ae_restrict_iff' measurableSet_halfPlane).2 h2] with p hp
    rw [Bridge.Internal.HalfPlaneReduction.planePoint_neg_height, hpd _ (hpair _ hp)]
    simp
  rw [z1, z2, add_zero, mul_zero] at hint
  have hae := (lintegral_eq_zero_iff' hmeas).1 hint
  filter_upwards [hae] with y hy
  have hle : pairDensity ξ B B 0 y ≤ 0 := ENNReal.ofReal_eq_zero.1 hy
  have hsum : pairDensity ξ B B 0 y = ∑ ab, ‖modeGrad ξ B 0 y ab‖ ^ 2 := by
    simp only [pairDensity, cdotMat, Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hsum] at hle
  have hz : ∀ ab, modeGrad ξ B 0 y ab = 0 := by
    intro ab
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1
      (le_antisymm hle (Finset.sum_nonneg fun i _ => by positivity)) ab (Finset.mem_univ ab)
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0)
  rw [Coercive.FrequencySeminorm.Internal.modeGrad_shift ξ hb.gradient_periodic σ y]
  funext ab
  rw [show modeGrad ξ (gradField b) 0 y ab = 0 from hz ab, mul_zero]
  rfl

end Internal.ByPartsModes

end InstancePair

end CertCell

end Breakdown
