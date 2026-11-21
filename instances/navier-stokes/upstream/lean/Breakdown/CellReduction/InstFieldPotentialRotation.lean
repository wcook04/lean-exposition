import Breakdown.CellReduction.InstanceStatements
import Breakdown.CertCell.CellLayerClosed
import Breakdown.Cert.CoerciveRotation

open scoped ContDiff RealInnerProductSpace Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal

namespace FieldPot

open Coercive.RotationInternal

def keysAt (D : TimeFieldData) (k : ℕ) : TimeFieldData :=
  ⟨D.keys.filter (fun κ => κ.label.1.natAbs = k), D.amp⟩

theorem mem_keysAt {D : TimeFieldData} {k : ℕ} {κ : FieldKey} :
    κ ∈ (keysAt D k).keys ↔ κ ∈ D.keys ∧ κ.label.1.natAbs = k := Finset.mem_filter

theorem keysAt_valid {D : TimeFieldData} (hD : IsTimeFieldData D) (k : ℕ) :
    IsTimeFieldData (keysAt D k) := by
  have hn : ∀ κ : FieldKey, κ.negKey.label.1.natAbs = κ.label.1.natAbs := by
    intro κ
    simp [FieldKey.negKey]
  have hf : ∀ κ : FieldKey, κ.flipKey.label.1.natAbs = κ.label.1.natAbs := by
    intro κ
    simp [FieldKey.flipKey, labelFlip]
  have h1 : ∀ κ, κ ∈ (keysAt D k).keys → κ ∈ D.keys := fun κ hκ => (mem_keysAt.1 hκ).1
  exact
    { keys_neg := fun κ => by rw [mem_keysAt, mem_keysAt, hn, hD.keys_neg κ]
      keys_flip := fun κ => by rw [mem_keysAt, mem_keysAt, hf, hD.keys_flip κ]
      neg_radial := fun κ hκ => hD.neg_radial κ (h1 κ hκ)
      neg_polar := fun κ hκ => hD.neg_polar κ (h1 κ hκ)
      neg_stream := fun κ hκ => hD.neg_stream κ (h1 κ hκ)
      neg_swirl := fun κ hκ => hD.neg_swirl κ (h1 κ hκ)
      neg_axisCoef := fun κ hκ => hD.neg_axisCoef κ (h1 κ hκ)
      neg_orders := fun κ hκ => hD.neg_orders κ (h1 κ hκ)
      flip_radial := fun κ hκ => hD.flip_radial κ (h1 κ hκ)
      flip_polar := fun κ hκ => hD.flip_polar κ (h1 κ hκ)
      flip_orders := fun κ hκ => hD.flip_orders κ (h1 κ hκ)
      stream_odd := fun κ hκ => hD.stream_odd κ (h1 κ hκ)
      swirl_odd := fun κ hκ => hD.swirl_odd κ (h1 κ hκ)
      radial_class := fun κ hκ => hD.radial_class κ (h1 κ hκ)
      polar_class := fun κ hκ => hD.polar_class κ (h1 κ hκ)
      lowOrder_ge := fun κ hκ => hD.lowOrder_ge κ (h1 κ hκ)
      stream_class := fun κ hκ => hD.stream_class κ (h1 κ hκ)
      swirl_class := fun κ hκ => hD.swirl_class κ (h1 κ hκ)
      stream_origin := fun κ hκ => hD.stream_origin κ (h1 κ hκ)
      swirl_origin := fun κ hκ => hD.swirl_origin κ (h1 κ hκ)
      highOrder_pos := fun κ hκ => hD.highOrder_pos κ (h1 κ hκ) }

theorem shapeField_fiber (P : ShapeParams) (D : TimeFieldData) (σ : ℝ) (y : Space) :
    shapeInfoField P D σ y = ∑ k ∈ D.keys.image (fun κ => κ.label.1.natAbs), shapeInfoField P (keysAt D k) σ y := by
  simp only [shapeInfoField, complexField, ← map_sum]
  congr 1
  exact (Finset.sum_fiberwise_of_maps_to (fun κ hκ => Finset.mem_image_of_mem _ hκ) _).symm

def rotL (φ : ℝ) : Space →L[ℝ] Space := ((axialRotEquiv φ).toContinuousLinearEquiv : Space →L[ℝ] Space)

theorem rotL_apply (φ : ℝ) (y : Space) : rotL φ y = axialRot φ y := rfl

theorem rotL_norm_le (φ : ℝ) : ‖rotL φ‖ ≤ 1 :=
  (axialRotEquiv φ).toLinearIsometry.norm_toContinuousLinearMap_le

def turnVec (w : Space) : Space := (-(w 1)) • unitVector 0 + (w 0) • unitVector 1

theorem unit_apply (i j : Fin 3) : unitVector i j = if j = i then 1 else 0 := by
  simp [unitVector]

theorem realPart_rotate (φ : ℝ) (w : Fin 3 → ℂ) : realPartVec (rotateVec φ w) = axialRot φ (realPartVec w) := by
  apply space_ext
  · simp [realPartVec, rotateVec, axialRot_apply_zero, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  · simp [realPartVec, rotateVec, axialRot_apply_one, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  · simp [realPartVec, rotateVec, axialRot_apply_two]

theorem rotate_smul (φ : ℝ) (c : ℂ) (w : Fin 3 → ℂ) : rotateVec φ (c • w) = c • rotateVec φ w := by
  ext i
  fin_cases i <;> simp [rotateVec] <;> ring

theorem hasDerivAt_rot {V : ℝ → Space} {V' : Space} {u : ℝ} (h : HasDerivAt V V' u) :
    HasDerivAt (fun v => axialRot v (V v)) (axialRot u V' + turnVec (axialRot u (V u))) u := by
  have hc : ∀ i : Fin 3, HasDerivAt (fun v => V v i) (V' i) u := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt u h
  have h0 := (((Real.hasDerivAt_cos u).mul (hc 0)).sub ((Real.hasDerivAt_sin u).mul (hc 1))).smul_const
    (unitVector 0)
  have h1 := (((Real.hasDerivAt_sin u).mul (hc 0)).add ((Real.hasDerivAt_cos u).mul (hc 1))).smul_const
    (unitVector 1)
  have h2 := (hc 2).smul_const (unitVector 2)
  refine HasDerivAt.congr_deriv ((h0.add h1).add h2) ?_
  apply space_ext
  · simp [turnVec, axialRot_apply_zero, axialRot_apply_one, unit_apply]
    ring
  · simp [turnVec, axialRot_apply_zero, axialRot_apply_one, unit_apply]
    ring
  · simp [turnVec, axialRot_apply_two, unit_apply]

theorem field_rot {P : ShapeParams} {D : TimeFieldData} (hD : IsTimeFieldData D) (σ v : ℝ) (y : Space) :
    shapeInfoField P D σ (axialRot v y) = axialRot v (realPartVec (∑ κ ∈ D.keys,
      Complex.exp ((((labelAzimuth P.azimuthOrder κ.label : ℝ) * v : ℝ) : ℂ) * Complex.I) •
        keyVector P κ (D.amp κ) σ y)) := by
  have hrot := shapeParts_closed.key_rotation
  have hsum : ∀ w : FieldKey → Space, axialRot v (∑ κ ∈ D.keys, w κ) = ∑ κ ∈ D.keys, axialRot v (w κ) := by
    intro w
    simp only [← rotL_apply, map_sum]
  simp only [shapeInfoField, complexField, map_sum, hsum]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  rw [hrot P D κ σ v y hD hκ, ← realPart_rotate, rotate_smul]
  rfl

def rotShift (M : ℝ) : ℝ := -(Real.pi / (2 * M))

def axisPot (M : ℝ) (F : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  (1 / M) • axialRot (-rotShift M) (F σ (axialRot (rotShift M) y))

def phaseSum (P : ShapeParams) (D : TimeFieldData) (M σ : ℝ) (y : Space) (u : ℝ) : Space :=
  (1 / M) • realPartVec (∑ κ ∈ D.keys,
    Complex.exp ((((labelAzimuth P.azimuthOrder κ.label : ℝ) * (rotShift M + u) : ℝ) : ℂ) * Complex.I) •
      keyVector P κ (D.amp κ) σ y)

theorem axialRot_smul (φ c : ℝ) (w : Space) : axialRot φ (c • w) = c • axialRot φ w := by
  rw [← rotL_apply, map_smul, rotL_apply]

theorem axisPot_rot {P : ShapeParams} {D : TimeFieldData} (hD : IsTimeFieldData D) (M σ u : ℝ) (y : Space) :
    axisPot M (shapeInfoField P D) σ (axialRot u y) = axialRot u (phaseSum P D M σ y u) := by
  rw [axisPot, ← axialRot_add, field_rot hD, ← axialRot_add, phaseSum, axialRot_smul]
  congr 2
  ring

theorem axisPot_eq {P : ShapeParams} {D : TimeFieldData} (hD : IsTimeFieldData D) (M σ : ℝ) (y : Space) :
    axisPot M (shapeInfoField P D) σ y = phaseSum P D M σ y 0 := by
  have h := axisPot_rot (P := P) hD M σ 0 y
  rwa [axialRot_zero, axialRot_zero] at h

theorem hasDerivAt_phase (a b u : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (((a * (b + v) : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((a * (b + u) : ℝ) : ℂ) * Complex.I) * ((a : ℂ) * Complex.I)) u := by
  have h1 : HasDerivAt (fun v : ℝ => a * (b + v)) a u := by
    simpa using ((hasDerivAt_id u).const_add b).const_mul a
  have h2 := (h1.ofReal_comp.mul_const Complex.I).cexp
  simpa using h2

theorem hasDerivAt_phaseSum (P : ShapeParams) (D : TimeFieldData) (M σ : ℝ) (y : Space) (u : ℝ) :
    HasDerivAt (phaseSum P D M σ y)
      ((1 / M) • realPartVec (∑ κ ∈ D.keys,
        (Complex.exp ((((labelAzimuth P.azimuthOrder κ.label : ℝ) * (rotShift M + u) : ℝ) : ℂ) * Complex.I) *
          (((labelAzimuth P.azimuthOrder κ.label : ℝ) : ℂ) * Complex.I)) • keyVector P κ (D.amp κ) σ y)) u := by
  have hs := HasDerivAt.fun_sum (u := D.keys) (fun κ _ =>
    (hasDerivAt_phase (labelAzimuth P.azimuthOrder κ.label : ℝ) (rotShift M) u).smul_const
      (keyVector P κ (D.amp κ) σ y))
  exact (realPartVec.hasFDerivAt.comp_hasDerivAt u hs).const_smul (1 / M)

theorem phase_at_shift (a : ℤ) (k m : ℕ) (hk : a.natAbs = k) (hk1 : 1 ≤ k) (hm : 0 < m) :
    (1 / ((k : ℝ) * m) : ℝ) • (Complex.exp ((((labelAzimuth m (a, 0) : ℝ) * (rotShift ((k : ℝ) * m) + 0) : ℝ) : ℂ) *
      Complex.I) * (((labelAzimuth m (a, 0) : ℝ) : ℂ) * Complex.I)) = 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hM : (k : ℝ) * m ≠ 0 := by positivity
  rcases Int.natAbs_eq a with h | h <;> rw [hk] at h <;> subst h
  · have e : ((labelAzimuth m ((k : ℤ), 0) : ℤ) : ℝ) * (rotShift ((k : ℝ) * m) + 0) = -(Real.pi / 2) := by
      simp only [labelAzimuth, rotShift]
      push_cast
      field_simp
      ring
    rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp only [labelAzimuth]
    rw [Complex.real_smul]
    have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
    have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
    push_cast
    field_simp
    linear_combination -Complex.I_mul_I
  · have e : ((labelAzimuth m (-(k : ℤ), 0) : ℤ) : ℝ) * (rotShift ((k : ℝ) * m) + 0) = Real.pi / 2 := by
      simp only [labelAzimuth, rotShift]
      push_cast
      field_simp
      ring
    rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp only [labelAzimuth]
    rw [Complex.real_smul]
    have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
    have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
    push_cast
    field_simp
    linear_combination -Complex.I_mul_I

theorem phaseSum_deriv_zero {P : ShapeParams} {D : TimeFieldData} {k : ℕ} (hk : ∀ κ ∈ D.keys, κ.label.1.natAbs = k)
    (hk1 : 1 ≤ k) (hm : 0 < P.azimuthOrder) (σ : ℝ) (y : Space) :
    (1 / ((k : ℝ) * P.azimuthOrder)) • realPartVec (∑ κ ∈ D.keys,
        (Complex.exp ((((labelAzimuth P.azimuthOrder κ.label : ℝ) * (rotShift ((k : ℝ) * P.azimuthOrder) + 0) : ℝ) : ℂ) *
          Complex.I) * (((labelAzimuth P.azimuthOrder κ.label : ℝ) : ℂ) * Complex.I)) • keyVector P κ (D.amp κ) σ y) =
      shapeInfoField P D σ y := by
  rw [← map_smul, Finset.smul_sum, shapeInfoField, complexField]
  congr 1
  refine Finset.sum_congr rfl fun κ hκ => ?_
  rw [← smul_assoc]
  have h := phase_at_shift κ.label.1 k P.azimuthOrder (hk κ hκ) hk1 hm
  have e : labelAzimuth P.azimuthOrder κ.label = labelAzimuth P.azimuthOrder (κ.label.1, 0) := rfl
  rw [e, h, one_smul]

theorem axisPot_dirDeriv {P : ShapeParams} {D : TimeFieldData} (hD : IsTimeFieldData D) {k : ℕ}
    (hk : ∀ κ ∈ D.keys, κ.label.1.natAbs = k) (hk1 : 1 ≤ k) (hm : 0 < P.azimuthOrder) (σ : ℝ) (y : Space)
    (hG : DifferentiableAt ℝ (axisPot ((k : ℝ) * P.azimuthOrder) (shapeInfoField P D) σ) y) :
    fderiv ℝ (axisPot ((k : ℝ) * P.azimuthOrder) (shapeInfoField P D) σ) y (turnVec y) =
      shapeInfoField P D σ y + turnVec (axisPot ((k : ℝ) * P.azimuthOrder) (shapeInfoField P D) σ y) := by
  set M : ℝ := (k : ℝ) * P.azimuthOrder with hMdef
  have h1 : HasDerivAt (fun u => axialRot u y) (turnVec y) 0 := by
    have := hasDerivAt_rot (hasDerivAt_const (0 : ℝ) y)
    simpa [axialRot_zero, turnVec] using this
  have h2 : HasDerivAt (fun u => axisPot M (shapeInfoField P D) σ (axialRot u y))
      (fderiv ℝ (axisPot M (shapeInfoField P D) σ) y (turnVec y)) 0 :=
    hG.hasFDerivAt.comp_hasDerivAt_of_eq 0 h1 (axialRot_zero y).symm
  have h3 := hasDerivAt_rot (hasDerivAt_phaseSum P D M σ y 0)
  have hfun : (fun u => axisPot M (shapeInfoField P D) σ (axialRot u y)) =
      fun u => axialRot u (phaseSum P D M σ y u) := funext fun u => axisPot_rot hD M σ u y
  rw [hfun] at h2
  rw [h2.unique h3, axialRot_zero, axialRot_zero, ← axisPot_eq hD, phaseSum_deriv_zero hk hk1 hm]

theorem div_smul_realPart_sum (s : Finset FieldKey) (c : FieldKey → ℂ) (f : FieldKey → Space → Fin 3 → ℂ) (a : ℝ)
    (y : Space) (hf : ∀ κ ∈ s, DifferentiableAt ℝ (f κ) y) (h0 : ∀ κ ∈ s, complexDivergence (f κ) y = 0) :
    divergenceAt (fun y' => a • realPartVec (∑ κ ∈ s, c κ • f κ y')) y = 0 := by
  have hd : HasFDerivAt (fun y' => a • realPartVec (∑ κ ∈ s, c κ • f κ y'))
      (a • realPartVec.comp (∑ κ ∈ s, c κ • fderiv ℝ (f κ) y)) y := by
    have hs := HasFDerivAt.fun_sum (u := s) (fun κ hκ => ((hf κ hκ).hasFDerivAt.const_smul (c κ)))
    exact (realPartVec.hasFDerivAt.comp y hs).const_smul a
  simp only [divergenceAt, hd.fderiv]
  have e : ∀ i : Fin 3, ((a • realPartVec.comp (∑ κ ∈ s, c κ • fderiv ℝ (f κ) y)) (unitVector i)) i =
      a * (∑ κ ∈ s, c κ * fderiv ℝ (f κ) y (unitVector i) i).re := by
    intro i
    simp [realPartVec]
  simp only [e, ← Finset.mul_sum, ← Complex.re_sum]
  rw [Finset.sum_comm]
  have h1 : ∑ κ ∈ s, ∑ i : Fin 3, c κ * fderiv ℝ (f κ) y (unitVector i) i = 0 := by
    refine Finset.sum_eq_zero fun κ hκ => ?_
    rw [← Finset.mul_sum]
    have := h0 κ hκ
    simp only [complexDivergence] at this
    rw [this, mul_zero]
  rw [h1]
  simp

theorem axisPot_div {P : ShapeParams} {D : TimeFieldData} (hD : IsTimeFieldData D) (hP : IsShapeParams P)
    (M σ : ℝ) (y : Space) : divergenceAt (axisPot M (shapeInfoField P D) σ) y = 0 := by
  have hfun : axisPot M (shapeInfoField P D) σ = fun y' => phaseSum P D M σ y' 0 :=
    funext fun y' => axisPot_eq hD M σ y'
  rw [hfun]
  refine div_smul_realPart_sum D.keys _ (fun κ => keyVector P κ (D.amp κ) σ) (1 / M) y (fun κ hκ => ?_)
    (fun κ hκ => shapeParts_closed.key_divergence P D κ σ y hP hD hκ)
  by_cases h1 : κ.label.1 = 0
  · exact ((shapeParts_closed.type_two_smooth P D κ σ hP hD hκ h1).smooth.differentiable (by norm_num)) y
  · exact ((shapeParts_closed.type_one_smooth P D κ σ hP hD hκ h1).smooth.differentiable (by norm_num)) y

def axisCross (g y : Space) : Space :=
  (-(g 2 * y 0)) • unitVector 0 + (-(g 2 * y 1)) • unitVector 1 + (g 0 * y 0 + g 1 * y 1) • unitVector 2

theorem axisCross_apply (g y : Space) :
    axisCross g y 0 = -(g 2 * y 0) ∧ axisCross g y 1 = -(g 2 * y 1) ∧ axisCross g y 2 = g 0 * y 0 + g 1 * y 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [axisCross, unit_apply]

theorem comp_le (g : Space) (i : Fin 3) : |g i| ≤ ‖g‖ := by
  have := PiLp.norm_apply_le g i
  simpa [Real.norm_eq_abs] using this

theorem axisCross_norm (g y : Space) : ‖axisCross g y‖ ≤ 4 * ‖g‖ * ‖y‖ := by
  have hu : ∀ i : Fin 3, ‖unitVector i‖ = 1 := fun i => by simp [unitVector]
  have a0 := comp_le g 0
  have a1 := comp_le g 1
  have a2 := comp_le g 2
  have b0 := comp_le y 0
  have b1 := comp_le y 1
  have hg := norm_nonneg g
  have hy := norm_nonneg y
  calc ‖axisCross g y‖ ≤ |g 2 * y 0| + |g 2 * y 1| + |g 0 * y 0 + g 1 * y 1| := by
        refine (norm_add₃_le).trans ?_
        simp only [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_neg]
        exact le_refl _
    _ ≤ ‖g‖ * ‖y‖ + ‖g‖ * ‖y‖ + (‖g‖ * ‖y‖ + ‖g‖ * ‖y‖) := by
        refine add_le_add (add_le_add ?_ ?_) ((abs_add_le _ _).trans (add_le_add ?_ ?_)) <;>
          rw [abs_mul] <;> exact mul_le_mul (by assumption) (by assumption) (abs_nonneg _) hg
    _ ≤ 4 * ‖g‖ * ‖y‖ := by nlinarith [mul_nonneg hg hy]

def axisCrossL : Space →L[ℝ] Space →L[ℝ] Space :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ axisCross
      (fun a b y => by apply space_ext <;> simp [axisCross_apply] <;> ring)
      (fun c a y => by apply space_ext <;> simp [axisCross_apply] <;> ring)
      (fun g a b => by apply space_ext <;> simp [axisCross_apply] <;> ring)
      (fun c g a => by apply space_ext <;> simp [axisCross_apply] <;> ring))
    4 (fun g y => axisCross_norm g y)

theorem axisCrossL_apply (g y : Space) : axisCrossL g y = axisCross g y := rfl

theorem axisCrossL_norm : ‖axisCrossL‖ ≤ 4 :=
  LinearMap.mkContinuous₂_norm_le _ (by norm_num) _

theorem curl_axisCross {G : Space → Space} {G' : Space →L[ℝ] Space} {y F : Space} (hG : HasFDerivAt G G' y)
    (hdir : G' (turnVec y) = F + turnVec (G y)) (hdiv : ∑ i : Fin 3, G' (unitVector i) i = 0) :
    AdjointDefect.curlAt (fun v => axisCross (G v) v) y = F := by
  have hA : HasFDerivAt (fun v => axisCrossL (G v) v)
      (axisCrossL.precompR Space (G y) (ContinuousLinearMap.id ℝ Space) + axisCrossL.precompL Space G' y) y :=
    axisCrossL.hasFDerivAt_of_bilinear hG (hasFDerivAt_id y)
  have hfun : (fun v => axisCross (G v) v) = fun v => axisCrossL (G v) v := rfl
  rw [hfun, AdjointDefect.curlAt, hA.fderiv]
  have hT : turnVec y = (-(y 1)) • unitVector 0 + (y 0) • unitVector 1 := rfl
  rw [hT, map_add, map_smul, map_smul] at hdir
  have d0 := congrArg (fun w : Space => w 0) hdir
  have d1 := congrArg (fun w : Space => w 1) hdir
  have d2 := congrArg (fun w : Space => w 2) hdir
  simp only [Fin.sum_univ_three] at hdiv
  simp [turnVec, unit_apply] at d0 d1 d2
  apply space_ext
  · simp [axisCrossL_apply, axisCross_apply, unit_apply]
    linear_combination d0 + y 1 * hdiv
  · simp [axisCrossL_apply, axisCross_apply, unit_apply]
    linear_combination d1 - y 0 * hdiv
  · simp [axisCrossL_apply, axisCross_apply, unit_apply]
    linear_combination d2

structure PotentialPack (F A : ℝ → Space → Space) (C : ℝ) : Prop where
  smooth : ContDiff ℝ 1 (fun z : ℝ × Space => A z.1 z.2)
  periodic : IsTimePeriodic A
  curl : ∀ σ y, AdjointDefect.curlAt (A σ) y = F σ y
  bound : ∀ σ y, ‖A σ y‖ ≤ C / (1 + ‖y‖) ^ 2 ∧ ‖deriv (fun s => A s y) σ‖ ≤ C / (1 + ‖y‖) ^ 2 ∧
    ‖fderiv ℝ (A σ) y‖ ≤ C / (1 + ‖y‖) ^ 3

theorem slice_smooth {A : ℝ → Space → Space} (h : ContDiff ℝ 1 (fun z : ℝ × Space => A z.1 z.2)) (σ : ℝ) :
    ContDiff ℝ 1 (A σ) :=
  h.comp (contDiff_const.prodMk contDiff_id)

theorem time_smooth {A : ℝ → Space → Space} (h : ContDiff ℝ 1 (fun z : ℝ × Space => A z.1 z.2)) (y : Space) :
    ContDiff ℝ 1 (fun s => A s y) :=
  h.comp (contDiff_id.prodMk contDiff_const)

theorem pack_sum {ι : Type*} (s : Finset ι) (F A : ι → ℝ → Space → Space) (C : ι → ℝ)
    (h : ∀ i ∈ s, PotentialPack (F i) (A i) (C i)) :
    PotentialPack (fun σ y => ∑ i ∈ s, F i σ y) (fun σ y => ∑ i ∈ s, A i σ y) (∑ i ∈ s, C i) := by
  refine ⟨ContDiff.sum fun i hi => (h i hi).smooth, fun σ y => ?_, fun σ y => ?_, fun σ y => ?_⟩
  · exact Finset.sum_congr rfl fun i hi => (h i hi).periodic σ y
  · have hd : ∀ i ∈ s, DifferentiableAt ℝ (A i σ) y := fun i hi =>
      (slice_smooth (h i hi).smooth σ).differentiable (by norm_num) y
    rw [AdjointDefect.curlAt, fderiv_fun_sum hd]
    rw [← Finset.sum_congr rfl fun i hi => (h i hi).curl σ y]
    simp only [AdjointDefect.curlAt, FunLike.coe_sum, Finset.sum_apply, WithLp.ofLp_sum,
      Finset.sum_add_distrib, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul]
  · have hd : ∀ i ∈ s, DifferentiableAt ℝ (A i σ) y := fun i hi =>
      (slice_smooth (h i hi).smooth σ).differentiable (by norm_num) y
    have ht : ∀ i ∈ s, DifferentiableAt ℝ (fun s' => A i s' y) σ := fun i hi =>
      (time_smooth (h i hi).smooth y).differentiable (by norm_num) σ
    refine ⟨?_, ?_, ?_⟩
    · refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_div]
      exact Finset.sum_le_sum fun i hi => ((h i hi).bound σ y).1
    · rw [deriv_fun_sum ht]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_div]
      exact Finset.sum_le_sum fun i hi => ((h i hi).bound σ y).2.1
    · rw [fderiv_fun_sum hd]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_div]
      exact Finset.sum_le_sum fun i hi => ((h i hi).bound σ y).2.2

theorem mul_norm_div_le (K r : ℝ) (n : ℕ) (hK : 0 ≤ K) (hr : 0 ≤ r) :
    K / (1 + r) ^ (n + 1) * r ≤ K / (1 + r) ^ n := by
  have h1 : 0 < 1 + r := by linarith
  rw [pow_succ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : K * r * (1 + r) ^ n ≤ K * ((1 + r) ^ n * (1 + r)) := by
    rw [mul_comm ((1 + r) ^ n) (1 + r), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hK) (by positivity)
  linarith

theorem div_pow_mono (K r : ℝ) (n : ℕ) (hK : 0 ≤ K) (hr : 0 ≤ r) :
    K / (1 + r) ^ (n + 1) ≤ K / (1 + r) ^ n := by
  have h1 : 1 ≤ 1 + r := by linarith
  exact div_le_div_of_nonneg_left hK (by positivity) (pow_le_pow_right₀ h1 (by omega))

theorem pack_of_cross {F G : ℝ → Space → Space} {K : ℝ} (hK : 0 ≤ K)
    (hG : ContDiff ℝ 1 (fun z : ℝ × Space => G z.1 z.2)) (hper : IsTimePeriodic G)
    (hb : ∀ σ y, ‖G σ y‖ ≤ K / (1 + ‖y‖) ^ 3 ∧ ‖deriv (fun s => G s y) σ‖ ≤ K / (1 + ‖y‖) ^ 3 ∧
      ‖fderiv ℝ (G σ) y‖ ≤ K / (1 + ‖y‖) ^ 4)
    (hcurl : ∀ σ y, AdjointDefect.curlAt (fun v => axisCross (G σ v) v) y = F σ y) :
    PotentialPack F (fun σ y => axisCross (G σ y) y) (8 * K) := by
  have hK8 : K ≤ 8 * K := by linarith
  refine ⟨?_, fun σ y => ?_, hcurl, fun σ y => ?_⟩
  · exact axisCrossL.isBoundedBilinearMap.contDiff.comp (hG.prodMk contDiff_snd)
  · simp only [hper σ y]
  obtain ⟨b1, b2, b3⟩ := hb σ y
  have hr := norm_nonneg y
  have hGd : HasFDerivAt (G σ) (fderiv ℝ (G σ) y) y :=
    ((slice_smooth hG σ).differentiable (by norm_num) y).hasFDerivAt
  have hGt : HasDerivAt (fun s => G s y) (deriv (fun s => G s y) σ) σ :=
    ((time_smooth hG y).differentiable (by norm_num) σ).hasDerivAt
  refine ⟨?_, ?_, ?_⟩
  · calc ‖axisCross (G σ y) y‖ ≤ 4 * ‖G σ y‖ * ‖y‖ := axisCross_norm _ _
      _ ≤ 4 * (K / (1 + ‖y‖) ^ 3) * ‖y‖ := by gcongr
      _ = 4 * (K / (1 + ‖y‖) ^ (2 + 1) * ‖y‖) := by ring
      _ ≤ 4 * (K / (1 + ‖y‖) ^ 2) := by gcongr; exact mul_norm_div_le K _ 2 hK hr
      _ ≤ 8 * K / (1 + ‖y‖) ^ 2 := by
        rw [mul_div_assoc]
        gcongr
        norm_num
  · have hd : HasDerivAt (fun s => axisCross (G s y) y) (axisCross (deriv (fun s => G s y) σ) y) σ :=
      (axisCrossL.flip y).hasFDerivAt.comp_hasDerivAt σ hGt
    rw [hd.deriv]
    calc ‖axisCross (deriv (fun s => G s y) σ) y‖ ≤ 4 * ‖deriv (fun s => G s y) σ‖ * ‖y‖ := axisCross_norm _ _
      _ ≤ 4 * (K / (1 + ‖y‖) ^ 3) * ‖y‖ := by gcongr
      _ = 4 * (K / (1 + ‖y‖) ^ (2 + 1) * ‖y‖) := by ring
      _ ≤ 4 * (K / (1 + ‖y‖) ^ 2) := by gcongr; exact mul_norm_div_le K _ 2 hK hr
      _ ≤ 8 * K / (1 + ‖y‖) ^ 2 := by
        rw [mul_div_assoc]
        gcongr
        norm_num
  · have hA : HasFDerivAt (fun v => axisCrossL (G σ v) v)
        (axisCrossL.precompR Space (G σ y) (ContinuousLinearMap.id ℝ Space) +
          axisCrossL.precompL Space (fderiv ℝ (G σ) y) y) y :=
      axisCrossL.hasFDerivAt_of_bilinear hGd (hasFDerivAt_id y)
    have hfun : (fun v => axisCross (G σ v) v) = fun v => axisCrossL (G σ v) v := rfl
    show ‖fderiv ℝ (fun v => axisCross (G σ v) v) y‖ ≤ _
    rw [hfun, hA.fderiv]
    have hpos : 0 ≤ 8 * K / (1 + ‖y‖) ^ 3 := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hpos fun v => ?_
    have hv : (axisCrossL.precompR Space (G σ y) (ContinuousLinearMap.id ℝ Space) +
        axisCrossL.precompL Space (fderiv ℝ (G σ) y) y) v =
        axisCross (G σ y) v + axisCross (fderiv ℝ (G σ) y v) y := rfl
    rw [hv]
    have e1 := axisCross_norm (G σ y) v
    have e2 := axisCross_norm (fderiv ℝ (G σ) y v) y
    have e3 := ContinuousLinearMap.le_opNorm (fderiv ℝ (G σ) y) v
    have hv := norm_nonneg v
    have f1 : ‖fderiv ℝ (G σ) y‖ * ‖y‖ ≤ K / (1 + ‖y‖) ^ 3 := by
      calc ‖fderiv ℝ (G σ) y‖ * ‖y‖ ≤ K / (1 + ‖y‖) ^ (3 + 1) * ‖y‖ := by gcongr
        _ ≤ K / (1 + ‖y‖) ^ 3 := mul_norm_div_le K _ 3 hK hr
    calc ‖axisCross (G σ y) v + axisCross (fderiv ℝ (G σ) y v) y‖
        ≤ 4 * ‖G σ y‖ * ‖v‖ + 4 * (‖fderiv ℝ (G σ) y‖ * ‖v‖) * ‖y‖ := by
          refine (norm_add_le _ _).trans (add_le_add e1 (e2.trans ?_))
          gcongr
      _ = 4 * (‖G σ y‖ + ‖fderiv ℝ (G σ) y‖ * ‖y‖) * ‖v‖ := by ring
      _ ≤ 4 * (K / (1 + ‖y‖) ^ 3 + K / (1 + ‖y‖) ^ 3) * ‖v‖ := by gcongr
      _ = 8 * K / (1 + ‖y‖) ^ 3 * ‖v‖ := by ring

theorem typeOne_pack (hdec : FieldDecayOrderHolds) {P : ShapeParams} {D : TimeFieldData} (hP : IsShapeParams P)
    (hD : IsTimeFieldData D) {k : ℕ} (hk : ∀ κ ∈ D.keys, κ.label.1.natAbs = k) (hk1 : 1 ≤ k)
    (hi : ∀ κ ∈ D.keys, 3 ≤ (D.amp κ).highOrder) :
    ∃ C, PotentialPack (shapeInfoField P D)
      (fun σ y => axisCross (axisPot ((k : ℝ) * P.azimuthOrder) (shapeInfoField P D) σ y) y) C := by
  have hm := hP.azimuthOrder_pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hm0 : (0 : ℝ) < P.azimuthOrder := by exact_mod_cast hm
  obtain ⟨hF, hFper, -, -⟩ := shapeParts_closed.field_smooth P D hP hD
  obtain ⟨C, hC⟩ := hdec P D 3 hP hD hi
  have hC0 : 0 ≤ C := by
    have h := (hC 0 0).1
    simp only [norm_zero, add_zero, one_pow, div_one] at h
    exact (norm_nonneg _).trans h
  set M : ℝ := (k : ℝ) * P.azimuthOrder with hMdef
  have hM : 0 < M := mul_pos hk0 hm0
  set s : ℝ := rotShift M with hsdef
  have hG : ContDiff ℝ 1 (fun z : ℝ × Space => axisPot M (shapeInfoField P D) z.1 z.2) := by
    have hin : ContDiff ℝ 1 (fun z : ℝ × Space => (z.1, rotL s z.2)) :=
      contDiff_fst.prodMk ((rotL s).contDiff.comp contDiff_snd)
    exact ((rotL (-s)).contDiff.comp (hF.comp hin)).const_smul (1 / M)
  have hper : IsTimePeriodic (axisPot M (shapeInfoField P D)) := fun σ y => by
    simp only [axisPot, hFper σ _]
  refine ⟨8 * (C / M), pack_of_cross (by positivity) hG hper (fun σ y => ?_) (fun σ y => ?_)⟩
  · obtain ⟨c1, c2, c3, -⟩ := hC σ (axialRot s y)
    rw [axialRot_norm] at c1 c2 c3
    have hFd : HasFDerivAt (shapeInfoField P D σ) (fderiv ℝ (shapeInfoField P D σ) (rotL s y)) (rotL s y) :=
      ((slice_smooth hF σ).differentiable (by norm_num) _).hasFDerivAt
    have hGd : HasFDerivAt (axisPot M (shapeInfoField P D) σ)
        ((1 / M) • ((rotL (-s)).comp ((fderiv ℝ (shapeInfoField P D σ) (rotL s y)).comp (rotL s)))) y :=
      ((rotL (-s)).hasFDerivAt.comp y (hFd.comp y (rotL s).hasFDerivAt)).const_smul (1 / M)
    have hFt : HasDerivAt (fun s' => shapeInfoField P D s' (rotL s y))
        (deriv (fun s' => shapeInfoField P D s' (rotL s y)) σ) σ :=
      ((time_smooth hF _).differentiable (by norm_num) σ).hasDerivAt
    have hGt : HasDerivAt (fun s' => axisPot M (shapeInfoField P D) s' y)
        ((1 / M) • rotL (-s) (deriv (fun s' => shapeInfoField P D s' (rotL s y)) σ)) σ :=
      ((rotL (-s)).hasFDerivAt.comp_hasDerivAt σ hFt).const_smul (1 / M)
    have hinv : 0 < 1 / M := by positivity
    refine ⟨?_, ?_, ?_⟩
    · calc ‖axisPot M (shapeInfoField P D) σ y‖ = 1 / M * ‖shapeInfoField P D σ (axialRot s y)‖ := by
            rw [axisPot, norm_smul, axialRot_norm, Real.norm_of_nonneg hinv.le]
        _ ≤ 1 / M * (C / (1 + ‖y‖) ^ 3) := by gcongr
        _ = C / M / (1 + ‖y‖) ^ 3 := by ring
    · rw [hGt.deriv, norm_smul, rotL_apply, axialRot_norm, Real.norm_of_nonneg hinv.le]
      calc 1 / M * ‖deriv (fun s' => shapeInfoField P D s' (rotL s y)) σ‖ ≤ 1 / M * (C / (1 + ‖y‖) ^ 3) := by
            gcongr
            exact c2
        _ = C / M / (1 + ‖y‖) ^ 3 := by ring
    · rw [hGd.fderiv, norm_smul, Real.norm_of_nonneg hinv.le]
      have e1 := ContinuousLinearMap.opNorm_comp_le (rotL (-s))
        ((fderiv ℝ (shapeInfoField P D σ) (rotL s y)).comp (rotL s))
      have e2 := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ (shapeInfoField P D σ) (rotL s y)) (rotL s)
      have r1 := rotL_norm_le (-s)
      have r2 := rotL_norm_le s
      have hn := norm_nonneg (fderiv ℝ (shapeInfoField P D σ) (rotL s y))
      have hn2 := norm_nonneg ((fderiv ℝ (shapeInfoField P D σ) (rotL s y)).comp (rotL s))
      have : ‖(rotL (-s)).comp ((fderiv ℝ (shapeInfoField P D σ) (rotL s y)).comp (rotL s))‖ ≤
          ‖fderiv ℝ (shapeInfoField P D σ) (rotL s y)‖ := by
        calc _ ≤ ‖rotL (-s)‖ * ‖(fderiv ℝ (shapeInfoField P D σ) (rotL s y)).comp (rotL s)‖ := e1
          _ ≤ 1 * (‖fderiv ℝ (shapeInfoField P D σ) (rotL s y)‖ * 1) := by
              gcongr
              exact e2.trans (by gcongr)
          _ = _ := by ring
      calc 1 / M * ‖(rotL (-s)).comp ((fderiv ℝ (shapeInfoField P D σ) (rotL s y)).comp (rotL s))‖
          ≤ 1 / M * (C / (1 + ‖y‖) ^ 4) := by
            gcongr
            exact this.trans c3
        _ = C / M / (1 + ‖y‖) ^ 4 := by ring
  · have hGd : DifferentiableAt ℝ (axisPot M (shapeInfoField P D) σ) y :=
      (slice_smooth hG σ).differentiable (by norm_num) y
    refine curl_axisCross hGd.hasFDerivAt (axisPot_dirDeriv hD hk hk1 hm σ y hGd) ?_
    have := axisPot_div hD hP M σ y
    simpa [divergenceAt] using this

end FieldPot

end Internal

end Instantiation

end CellReduction

end Breakdown
