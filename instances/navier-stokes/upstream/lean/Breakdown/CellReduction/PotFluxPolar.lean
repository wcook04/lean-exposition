import Breakdown.CellReduction.PotentialShape
import Breakdown.CellReduction.PotFluxSpherical
import Breakdown.CertCell.ShapeSphericalDivFrame
import Breakdown.CertCell.ShapeSplineSmooth
import Breakdown.CertCell.ShapeSplineSlope
import Breakdown.CertCell.ShapeJetJoin
import Breakdown.FracCell.GivenToolkit
import Breakdown.FracCell.GivenAuxDualParts
import Breakdown.FracCell.GivenAuxDualPartsRestOpen

open scoped ContDiff
open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.PotentialShape

open CertCell CertCell.GivenShape
open CellCert.GivenFields (heightRatio polarVecQ)

namespace Internal.PolarFlux

open CertCell.GivenShape.SphericalDivInternal (polarField polarField_apply polarField_diff div_polarField)

def sphereTangent (r ϑ a : ℝ) : Space :=
  (r * Real.cos ϑ * Real.cos a) • unitVector 0 + (r * Real.cos ϑ * Real.sin a) • unitVector 1 +
    (-(r * Real.sin ϑ)) • unitVector 2

def polarDiv (f : Space → ℂ) (y : Space) : ℂ :=
  fderiv ℝ f y (polarField y) + ((2 * y 2 / ‖y‖ ^ 2 : ℝ) : ℂ) * f y

theorem sphericalPoint_eq (r ϑ a : ℝ) : sphericalPoint r ϑ a =
    (r * Real.sin ϑ * Real.cos a) • unitVector 0 + (r * Real.sin ϑ * Real.sin a) • unitVector 1 +
      (r * Real.cos ϑ) • unitVector 2 := by
  ext i
  fin_cases i <;> simp [sphericalPoint, CellCert.Spectral.cylPoint, unitVector]

theorem sphericalPoint_apply (r ϑ a : ℝ) : sphericalPoint r ϑ a 0 = r * Real.sin ϑ * Real.cos a ∧
    sphericalPoint r ϑ a 1 = r * Real.sin ϑ * Real.sin a ∧ sphericalPoint r ϑ a 2 = r * Real.cos ϑ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [sphericalPoint, CellCert.Spectral.cylPoint]

theorem norm_sphericalPoint {r : ℝ} (hr : 0 ≤ r) (ϑ a : ℝ) : ‖sphericalPoint r ϑ a‖ = r := by
  obtain ⟨h0, h1, h2⟩ := sphericalPoint_apply r ϑ a
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs, h0, h1, h2]
  have e : (r * Real.sin ϑ * Real.cos a) ^ 2 + (r * Real.sin ϑ * Real.sin a) ^ 2 + (r * Real.cos ϑ) ^ 2 = r ^ 2 := by
    linear_combination (r ^ 2 * Real.sin ϑ ^ 2) * Real.cos_sq_add_sin_sq a + r ^ 2 * Real.sin_sq_add_cos_sq ϑ
  rw [e, Real.sqrt_sq hr]

theorem hasDerivAt_sphericalPoint (r ϑ a : ℝ) :
    HasDerivAt (fun s => sphericalPoint r s a) (sphereTangent r ϑ a) ϑ := by
  have e : (fun s => sphericalPoint r s a) = fun s => (r * Real.sin s * Real.cos a) • unitVector 0 +
      (r * Real.sin s * Real.sin a) • unitVector 1 + (r * Real.cos s) • unitVector 2 :=
    funext fun s => sphericalPoint_eq r s a
  rw [e]
  have h0 := (((Real.hasDerivAt_sin ϑ).const_mul r).mul_const (Real.cos a)).smul_const (unitVector 0 : Space)
  have h1 := (((Real.hasDerivAt_sin ϑ).const_mul r).mul_const (Real.sin a)).smul_const (unitVector 1 : Space)
  have h2 := ((Real.hasDerivAt_cos ϑ).const_mul r).smul_const (unitVector 2 : Space)
  refine ((h0.add h1).add h2).congr_deriv ?_
  simp only [sphereTangent]
  rw [show r * -Real.sin ϑ = -(r * Real.sin ϑ) by ring]

theorem continuous_sphericalPoint (r a : ℝ) : Continuous fun s => sphericalPoint r s a :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_sphericalPoint r s a).continuousAt

theorem polarField_sphericalPoint {r : ℝ} (hr : 0 < r) (ϑ a : ℝ) :
    r • polarField (sphericalPoint r ϑ a) = Real.sin ϑ • sphereTangent r ϑ a := by
  have hn := norm_sphericalPoint hr.le ϑ a
  obtain ⟨h0, h1, h2⟩ := sphericalPoint_apply r ϑ a
  have hr0 : r ≠ 0 := hr.ne'
  ext i
  fin_cases i
  · simp [polarField, sphereTangent, unitVector, hn, h0, h2]
    field_simp
  · simp [polarField, sphereTangent, unitVector, hn, h1, h2]
    field_simp
  · simp [polarField, sphereTangent, unitVector, hn, h2]
    field_simp
    linear_combination Real.sin_sq_add_cos_sq ϑ

theorem clm_apply_coords (L : Space →L[ℝ] ℝ) (w : Space) : L w = ∑ i : Fin 3, L (unitVector i) * w i := by
  have e : w = ∑ i : Fin 3, w i • unitVector i := by
    ext j
    fin_cases j <;> simp [unitVector, Fin.sum_univ_three]
  conv_lhs => rw [e]
  simp [map_sum, mul_comm]

theorem grad_pairing (φ : Space → ℝ) (f : Space → ℂ) (y : Space) :
    ∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) * (f y * (polarVecQ y i : ℂ)) =
      f y * (fderiv ℝ φ y (polarField y) : ℂ) := by
  rw [clm_apply_coords (fderiv ℝ φ y) (polarField y)]
  simp only [polarField_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem fderiv_polarField_sph {r : ℝ} (hr : 0 < r) (ϑ a : ℝ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : Space →L[ℝ] E) :
    L (polarField (sphericalPoint r ϑ a)) = (r⁻¹ * Real.sin ϑ) • L (sphereTangent r ϑ a) := by
  have h := congrArg L (polarField_sphericalPoint hr ϑ a)
  rw [map_smul, map_smul] at h
  rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem slice_identity {f : Space → ℂ} {φ : Space → ℝ} (hφ : Differentiable ℝ φ) {r a : ℝ} (hr : 0 < r)
    {S : Set ℝ} (hS : S.Countable)
    (hg : ContinuousOn (fun ϑ => (Real.sin ϑ ^ 2) • f (sphericalPoint r ϑ a)) (Icc 0 Real.pi))
    (hd : ∀ ϑ ∈ Ioo 0 Real.pi \ S, DifferentiableAt ℝ f (sphericalPoint r ϑ a))
    (h1 : IntervalIntegrable (fun ϑ => (r ^ 2 * Real.sin ϑ) •
      ((φ (sphericalPoint r ϑ a) : ℂ) * polarDiv f (sphericalPoint r ϑ a))) volume 0 Real.pi)
    (h2 : IntervalIntegrable (fun ϑ => (r ^ 2 * Real.sin ϑ) • ∑ i : Fin 3,
      (fderiv ℝ φ (sphericalPoint r ϑ a) (unitVector i) : ℂ) *
        (f (sphericalPoint r ϑ a) * (polarVecQ (sphericalPoint r ϑ a) i : ℂ))) volume 0 Real.pi) :
    ∫ ϑ in (0 : ℝ)..Real.pi, (r ^ 2 * Real.sin ϑ) •
      ((φ (sphericalPoint r ϑ a) : ℂ) * polarDiv f (sphericalPoint r ϑ a)) =
    -∫ ϑ in (0 : ℝ)..Real.pi, (r ^ 2 * Real.sin ϑ) • ∑ i : Fin 3,
      (fderiv ℝ φ (sphericalPoint r ϑ a) (unitVector i) : ℂ) *
        (f (sphericalPoint r ϑ a) * (polarVecQ (sphericalPoint r ϑ a) i : ℂ)) := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  set u : ℝ → ℂ := fun ϑ => (φ (sphericalPoint r ϑ a) : ℂ) with hu_def
  set u' : ℝ → ℂ := fun ϑ => (fderiv ℝ φ (sphericalPoint r ϑ a) (sphereTangent r ϑ a) : ℂ) with hu'_def
  set g : ℝ → ℂ := fun ϑ => (Real.sin ϑ ^ 2) • f (sphericalPoint r ϑ a) with hg_def
  set g' : ℝ → ℂ := fun ϑ => (Real.sin ϑ ^ 2) • fderiv ℝ f (sphericalPoint r ϑ a) (sphereTangent r ϑ a) +
    (2 * Real.sin ϑ * Real.cos ϑ) • f (sphericalPoint r ϑ a) with hg'_def
  have hu : ∀ ϑ, HasDerivAt u (u' ϑ) ϑ := fun ϑ =>
    ((hφ _).hasFDerivAt.comp_hasDerivAt ϑ (hasDerivAt_sphericalPoint r ϑ a)).ofReal_comp
  have hgd : ∀ ϑ ∈ Ioo 0 Real.pi \ S, HasDerivAt g (g' ϑ) ϑ := by
    intro ϑ hϑ
    have hs : HasDerivAt (fun s => Real.sin s ^ 2) (2 * Real.sin ϑ * Real.cos ϑ) ϑ := by
      refine ((Real.hasDerivAt_sin ϑ).pow 2).congr_deriv ?_
      push_cast
      ring
    exact hs.smul ((hd ϑ hϑ).hasFDerivAt.comp_hasDerivAt ϑ (hasDerivAt_sphericalPoint r ϑ a))
  have hA : ∀ ϑ, (r ^ 2 * Real.sin ϑ) • ((φ (sphericalPoint r ϑ a) : ℂ) * polarDiv f (sphericalPoint r ϑ a)) =
      (r : ℂ) * (u ϑ * g' ϑ) := by
    intro ϑ
    simp only [polarDiv, hu_def, hg'_def]
    rw [fderiv_polarField_sph hr, norm_sphericalPoint hr.le, (sphericalPoint_apply r ϑ a).2.2]
    simp only [Complex.real_smul]
    push_cast
    field_simp
  have hB : ∀ ϑ, (r ^ 2 * Real.sin ϑ) • ∑ i : Fin 3, (fderiv ℝ φ (sphericalPoint r ϑ a) (unitVector i) : ℂ) *
      (f (sphericalPoint r ϑ a) * (polarVecQ (sphericalPoint r ϑ a) i : ℂ)) = (r : ℂ) * (u' ϑ * g ϑ) := by
    intro ϑ
    rw [grad_pairing, fderiv_polarField_sph hr]
    simp only [hu'_def, hg_def, Complex.real_smul, smul_eq_mul]
    push_cast
    field_simp
  have hi1 : IntervalIntegrable (fun ϑ => u ϑ * g' ϑ) volume 0 Real.pi := by
    have e : (fun ϑ => u ϑ * g' ϑ) = fun ϑ => ((r⁻¹ : ℝ) : ℂ) * ((r ^ 2 * Real.sin ϑ) •
        ((φ (sphericalPoint r ϑ a) : ℂ) * polarDiv f (sphericalPoint r ϑ a))) := by
      funext ϑ
      rw [hA ϑ]
      push_cast
      field_simp
    rw [e]
    exact h1.const_mul _
  have hi2 : IntervalIntegrable (fun ϑ => u' ϑ * g ϑ) volume 0 Real.pi := by
    have e : (fun ϑ => u' ϑ * g ϑ) = fun ϑ => ((r⁻¹ : ℝ) : ℂ) * ((r ^ 2 * Real.sin ϑ) • ∑ i : Fin 3,
        (fderiv ℝ φ (sphericalPoint r ϑ a) (unitVector i) : ℂ) *
          (f (sphericalPoint r ϑ a) * (polarVecQ (sphericalPoint r ϑ a) i : ℂ))) := by
      funext ϑ
      rw [hB ϑ]
      push_cast
      field_simp
    rw [e]
    exact h2.const_mul _
  have hcu : Continuous u :=
    Complex.continuous_ofReal.comp (hφ.continuous.comp (continuous_sphericalPoint r a))
  have hF := integral_eq_of_hasDerivAt_off_countable_of_le (fun ϑ => u ϑ * g ϑ)
    (fun ϑ => u' ϑ * g ϑ + u ϑ * g' ϑ) Real.pi_pos.le hS (hcu.continuousOn.mul hg)
    (fun ϑ hϑ => (hu ϑ).mul (hgd ϑ hϑ)) (hi2.add hi1)
  have hend : u Real.pi * g Real.pi - u 0 * g 0 = 0 := by
    simp [hg_def]
  rw [hend, intervalIntegral.integral_add hi2 hi1] at hF
  have hkey : ∫ ϑ in (0 : ℝ)..Real.pi, u ϑ * g' ϑ = -∫ ϑ in (0 : ℝ)..Real.pi, u' ϑ * g ϑ := by
    linear_combination hF
  rw [intervalIntegral.integral_congr (fun ϑ _ => hA ϑ), intervalIntegral.integral_congr (fun ϑ _ => hB ϑ),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hkey]
  ring

theorem weak_identity {f : Space → ℂ}
    (hV : ∀ i : Fin 3, LocallyIntegrable (fun y => f y * (polarVecQ y i : ℂ)))
    (hD : LocallyIntegrable (polarDiv f))
    (hslice : ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi)),
      ContinuousOn (fun ϑ => (Real.sin ϑ ^ 2) • f (sphericalPoint q.1 ϑ q.2)) (Icc 0 Real.pi) ∧
        ∃ S : Set ℝ, S.Countable ∧ ∀ ϑ ∈ Ioo 0 Real.pi \ S, DifferentiableAt ℝ f (sphericalPoint q.1 ϑ q.2))
    {φ : Space → ℝ} (hφ : IsTestFunction φ) :
    ∫ y, (φ y : ℂ) * polarDiv f y =
      -∫ y, ∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) * (f y * (polarVecQ y i : ℂ)) := by
  have hφd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hφc : Continuous (fun y => (φ y : ℂ)) := Complex.continuous_ofReal.comp hφ.1.continuous
  have hφs : HasCompactSupport (fun y => (φ y : ℂ)) := hφ.2.comp_left Complex.ofReal_zero
  have hI1 : Integrable (fun y => (φ y : ℂ) * polarDiv f y) := by
    simpa [smul_eq_mul] using hD.integrable_smul_left_of_hasCompactSupport hφc hφs
  have hI2 : Integrable (fun y => ∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) * (f y * (polarVecQ y i : ℂ))) := by
    refine integrable_finsetSum _ fun i _ => ?_
    have hc : Continuous (fun y => (fderiv ℝ φ y (unitVector i) : ℂ)) :=
      Complex.continuous_ofReal.comp ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hs : HasCompactSupport (fun y => (fderiv ℝ φ y (unitVector i) : ℂ)) :=
      (hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector i)).comp_left Complex.ofReal_zero
    simpa [smul_eq_mul] using (hV i).integrable_smul_left_of_hasCompactSupport hc hs
  rw [integral_eq_spherical_polar_interval _ hI1, integral_eq_spherical_polar_interval _ hI2, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hslice, spherical_polar_slice_intervalIntegrable _ hI1,
    spherical_polar_slice_intervalIntegrable _ hI2, ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)]
    with q hq h1 h2 hmem
  obtain ⟨hc, S, hS, hd⟩ := hq
  exact slice_identity hφd hmem.1 hS hc hd h1 h2

open CertCell.GivenShape.Internal (pieceEval pieceEval_bounded polyEval_hasDerivAt_second toSpline_piece
  atSecond_sum atSecond_term dofPoly_jets_agree)
open CertCell.GivenShape.Internal.JoinedSpline (glue_continuous inner_facts join_x evP evP_continuous)

theorem jet_atSecond_join {H : JetSpline} (hx : IsJetAxis H.xAxis (-1) 1) (i k : ℕ)
    (hk : k + 1 < CellCert.GivenFields.cellCount H.xAxis.breaks) :
    CellCert.GivenFields.atSecond ((H.xAxis.breaks.getD (k + 1) 0 : ℝ) : ℂ) (H.toSpline.piece i k) =
      CellCert.GivenFields.atSecond ((H.xAxis.breaks.getD (k + 1) 0 : ℝ) : ℂ) (H.toSpline.piece i (k + 1)) := by
  rw [toSpline_piece, toSpline_piece, atSecond_sum, atSecond_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [atSecond_sum, atSecond_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [atSecond_term, atSecond_term]
  have h := dofPoly_jets_agree (fun n p o _ _ hab ho => iterate_derivative_nodalLeft_eval_left n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalLeft_eval_right n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalRight_eval_right n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalRight_eval_left n p o hab ho)
    (fun n s o a b ho => iterate_derivative_bubblePoly_eval_left n s o a b ho)
    (fun n s o a b ho => iterate_derivative_bubblePoly_eval_right n s o a b ho)
    H.xAxis hx.sorted (k + 1) (by omega) hk 0 hx.depth_pos e
  simp only [Function.iterate_zero, id_eq, Nat.add_sub_cancel] at h
  rw [h]

theorem evalHalf_continuous_height {H : JetSpline} (hx : IsJetAxis H.xAxis (-1) 1) (t : ℝ) :
    Continuous (fun x => H.toSpline.evalHalf t x) := by
  obtain ⟨hs, hc, hg⟩ := inner_facts H.xAxis.breaks (by norm_num : (-1 : ℝ) < 1) hx.sorted hx.first hx.last
  have h := glue_continuous Prod.snd continuous_snd _ hs
    (fun j q => evP (H.toSpline.piece (CellCert.GivenFields.cellIndex H.tAxis.breaks t) j) (t, q.2))
    (fun j => (evP_continuous _).comp (continuous_const.prodMk continuous_snd))
    (fun k hk p hp => by
      show evP _ (t, p.2) = evP _ (t, p.2)
      rw [hp, hg k hk]
      exact join_x (jet_atSecond_join hx _ k (by omega)) t)
  have h2 := h.comp (continuous_const.prodMk continuous_id : Continuous fun x : ℝ => ((0 : ℝ), x))
  refine h2.congr fun x => ?_
  simp only [Function.comp_apply]
  rfl

theorem evalHalf_hasDerivAt_height (H : JetSpline) (t x : ℝ) (hx : x ∉ H.xAxis.breaks) :
    HasDerivAt (fun s => H.toSpline.evalHalf t s)
      (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1
        (H.toSpline.piece (CellCert.GivenFields.cellIndex H.tAxis.breaks t)
          (CellCert.GivenFields.cellIndex H.xAxis.breaks x)))) x := by
  refine (polyEval_hasDerivAt_second _ t x).congr_of_eventuallyEq ?_
  filter_upwards [FracInternal.cellIndex_eventually H.xAxis.breaks x hx] with s hs
  show MvPolynomial.eval _ (H.toSpline.piece _ (CellCert.GivenFields.cellIndex H.xAxis.breaks s)) = _
  rw [hs]
  rfl

theorem evalHalf_bound (H : JetSpline) : ∃ M, 0 ≤ M ∧ ∀ t x : ℝ, |t| ≤ 1 → |x| ≤ 1 →
    ‖H.toSpline.evalHalf t x‖ ≤ M :=
  pieceEval_bounded H.tAxis.breaks H.xAxis.breaks H.toSpline.piece 1

theorem evalHalf_height_bound (H : JetSpline) : ∃ M, 0 ≤ M ∧ ∀ t x : ℝ, |t| ≤ 1 → |x| ≤ 1 →
    ‖MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1
      (H.toSpline.piece (CellCert.GivenFields.cellIndex H.tAxis.breaks t)
        (CellCert.GivenFields.cellIndex H.xAxis.breaks x)))‖ ≤ M :=
  pieceEval_bounded H.tAxis.breaks H.xAxis.breaks (fun i j => MvPolynomial.pderiv 1 (H.toSpline.piece i j)) 1

def axisProfile (k : ℕ) (ws : Bool) (x : ℝ) : ℝ :=
  (1 - x ^ 2) ^ (k + 1) * (if ws then Real.sqrt (1 - x ^ 2) else 1)

theorem axisProfile_continuous (k : ℕ) (ws : Bool) : Continuous (axisProfile k ws) := by
  unfold axisProfile
  cases ws <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop

theorem axisProfile_abs_le (k : ℕ) (ws : Bool) {x : ℝ} (hx : |x| ≤ 1) : |axisProfile k ws x| ≤ 1 := by
  have hu0 : 0 ≤ 1 - x ^ 2 := by nlinarith [abs_le.1 hx, sq_abs x, abs_nonneg x]
  have hu1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hp0 : 0 ≤ (1 - x ^ 2) ^ (k + 1) := pow_nonneg hu0 _
  have hp1 : (1 - x ^ 2) ^ (k + 1) ≤ 1 := pow_le_one₀ hu0 hu1
  unfold axisProfile
  cases ws
  · simp only [Bool.false_eq_true, if_false, mul_one]
    rw [abs_of_nonneg hp0]
    exact hp1
  · simp only [if_true]
    rw [abs_of_nonneg (mul_nonneg hp0 (Real.sqrt_nonneg _))]
    exact mul_le_one₀ hp1 (Real.sqrt_nonneg _) (Real.sqrt_le_one.2 hu1)

theorem axisProfile_sine_eq (k : ℕ) (x : ℝ) : axisProfile k true x = Real.sqrt (1 - x ^ 2) ^ (2 * k + 3) := by
  unfold axisProfile
  simp only [if_true]
  rcases le_or_gt 0 (1 - x ^ 2) with h | h
  · have hv : 1 - x ^ 2 = Real.sqrt (1 - x ^ 2) ^ 2 := (Real.sq_sqrt h).symm
    set v := Real.sqrt (1 - x ^ 2)
    rw [hv]
    ring
  · rw [Real.sqrt_eq_zero'.2 h.le]
    simp

theorem axisProfile_deriv (k : ℕ) (ws : Bool) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∃ d : ℝ, HasDerivAt (axisProfile k ws) d x ∧ |d| ≤ 2 * k + 3 := by
  have hu0 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hu1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hxa : |x| ≤ 1 := abs_le.2 ⟨hx.1.le, hx.2.le⟩
  have hu : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * x)) x := by
    refine ((hasDerivAt_pow 2 x).const_sub 1).congr_deriv ?_
    push_cast
    ring
  cases ws
  · have e : axisProfile k false = fun x : ℝ => (1 - x ^ 2) ^ (k + 1) := by
      funext y
      simp [axisProfile]
    rw [e]
    refine ⟨_, hu.pow (k + 1), ?_⟩
    have hp : (1 - x ^ 2) ^ k ≤ 1 := pow_le_one₀ hu0.le hu1
    have hp0 : 0 ≤ (1 - x ^ 2) ^ k := pow_nonneg hu0.le _
    rw [Nat.add_sub_cancel, abs_mul, abs_mul, abs_neg, abs_mul, abs_of_nonneg hp0]
    push_cast
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ k + 1), abs_two]
    have hb : ((k : ℝ) + 1) * (1 - x ^ 2) ^ k * (2 * |x|) ≤ ((k : ℝ) + 1) * 1 * (2 * 1) := by
      gcongr
    linarith
  · have e : axisProfile k true = fun x : ℝ => Real.sqrt (1 - x ^ 2) ^ (2 * k + 3) :=
      funext (axisProfile_sine_eq k)
    rw [e]
    have hs := (hu.sqrt hu0.ne').pow (2 * k + 3)
    refine ⟨_, hs, ?_⟩
    set v := Real.sqrt (1 - x ^ 2) with hv
    have hv0 : 0 < v := Real.sqrt_pos.2 hu0
    have hv1 : v ≤ 1 := Real.sqrt_le_one.2 hu1
    have e2 : ((2 * k + 3 : ℕ) : ℝ) * v ^ (2 * k + 3 - 1) * (-(2 * x) / (2 * v)) =
        -((2 * k + 3) * x * v ^ (2 * k + 1)) := by
      rw [show 2 * k + 3 - 1 = (2 * k + 1) + 1 by omega, pow_succ]
      field_simp
      push_cast
      ring
    rw [e2, abs_neg, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hv0.le _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * k + 3)]
    have hw : v ^ (2 * k + 1) ≤ 1 := pow_le_one₀ hv0.le hv1
    have hw0 : 0 ≤ v ^ (2 * k + 1) := pow_nonneg hv0.le _
    have hb : (2 * (k : ℝ) + 3) * |x| * v ^ (2 * k + 1) ≤ (2 * (k : ℝ) + 3) * 1 * 1 := by
      gcongr
    linarith

theorem heightRatio_sph {r : ℝ} (hr : 0 < r) (s a : ℝ) : heightRatio (sphericalPoint r s a) = Real.cos s := by
  rw [show heightRatio (sphericalPoint r s a) = sphericalPoint r s a 2 / ‖sphericalPoint r s a‖ from rfl,
    norm_sphericalPoint hr.le, (sphericalPoint_apply r s a).2.2]
  field_simp

theorem chartCoord_sph (P : ShapeParams) {r : ℝ} (hr : 0 < r) (s a : ℝ) :
    chartCoord P (sphericalPoint r s a) = r / (r + P.chartLength) := by
  rw [chartCoord, norm_sphericalPoint hr.le]

theorem pointAngle_sph {r s : ℝ} (hr : 0 < r) (hs : s ∈ Ioo 0 Real.pi) (a : ℝ) :
    pointAngle (sphericalPoint r s a) = pointAngle (sphericalPoint r (Real.pi / 2) a) := by
  have key : ∀ s', 0 < Real.sin s' → pointAngle (sphericalPoint r s' a) =
      Complex.arg ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I) := by
    intro s' hs'
    obtain ⟨h0, h1, -⟩ := sphericalPoint_apply r s' a
    rw [pointAngle, h0, h1]
    rw [show ((r * Real.sin s' * Real.cos a : ℝ) : ℂ) + ((r * Real.sin s' * Real.sin a : ℝ) : ℂ) * Complex.I =
      ((r * Real.sin s' : ℝ) : ℂ) * ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.arg_real_mul _ (mul_pos hr hs')
  rw [key s (Real.sin_pos_of_pos_of_lt_pi hs.1 hs.2), key _ (by rw [Real.sin_pi_div_two]; norm_num)]

def sliceFactor (P : ShapeParams) (κ : FieldKey) (M : ℤ) (σ r a : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
    (M : ℝ) * pointAngle (sphericalPoint r (Real.pi / 2) a) +
      (κ.phaseIndex : ℝ) * P.radialPhase (r ^ 2) : ℝ) : ℂ) * Complex.I)

def sliceProfile (P : ShapeParams) (S : PotScalar) (ws : Bool) (r x : ℝ) : ℂ :=
  CellCert.GivenFields.weightPoly S.lowOrder S.highOrder (r / (r + P.chartLength)) *
    ((axisProfile S.axisPower ws x : ℝ) : ℂ) * S.amp.toSpline.evalHalf (r / (r + P.chartLength)) x

theorem slice_eq (P : ShapeParams) (κ : FieldKey) (M : ℤ) (ws : Bool) (S : PotScalar) (σ : ℝ) {r : ℝ}
    (hr : 0 < r) (a : ℝ) {s : ℝ} (hs : s ∈ Icc 0 Real.pi) :
    (Real.sin s ^ 2) • scalarValue P κ M ws S σ (sphericalPoint r s a) =
      sliceFactor P κ M σ r a * sliceProfile P S ws r (Real.cos s) := by
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst h0
    simp [sliceProfile, axisProfile]
  rcases eq_or_lt_of_le hs.2 with hπ | hπ
  · subst hπ
    simp [sliceProfile, axisProfile]
  have hmem : s ∈ Ioo 0 Real.pi := ⟨h0, hπ⟩
  have hsin : Real.sin s ^ 2 = 1 - Real.cos s ^ 2 := Real.sin_sq s
  cases ws <;>
  · simp only [scalarValue, sliceFactor, sliceProfile, axisProfile, polarSine, heightRatio_sph hr,
      chartCoord_sph P hr, pointAngle_sph hr hmem, norm_sphericalPoint hr.le, hsin, Complex.real_smul,
      Bool.false_eq_true, if_false, if_true]
    push_cast
    ring

theorem heightRatio_abs_le (y : Space) : |heightRatio y| ≤ 1 := by
  rw [show heightRatio y = y 2 / ‖y‖ from rfl]
  rcases eq_or_ne y 0 with h | h
  · subst h
    simp
  · rw [abs_div, abs_of_pos (norm_pos_iff.2 h), div_le_one (norm_pos_iff.2 h)]
    have := PiLp.norm_apply_le y 2
    rwa [Real.norm_eq_abs] at this

theorem norm_sq_coords (y : Space) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

theorem sph_repr {y : Space} (hy : y ≠ 0) :
    sphericalPoint ‖y‖ (Real.arccos (heightRatio y)) (pointAngle y) = y := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hh := abs_le.1 (heightRatio_abs_le y)
  have hsq := norm_sq_coords y
  have hρ : ‖y‖ * Real.sqrt (1 - heightRatio y ^ 2) = ‖((y 0 : ℂ) + (y 1 : ℂ) * Complex.I)‖ := by
    rw [Complex.norm_add_mul_I, ← Real.sqrt_sq hn.le, ← Real.sqrt_mul (sq_nonneg _)]
    congr 1
    rw [show heightRatio y = y 2 / ‖y‖ from rfl, div_pow]
    field_simp
    linarith
  have hy_eq : y = (y 0) • unitVector 0 + (y 1) • unitVector 1 + (y 2) • unitVector 2 := by
    ext i
    fin_cases i <;> simp [unitVector]
  rw [sphericalPoint_eq]
  conv_rhs => rw [hy_eq]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;> congr 1
  · rw [Real.sin_arccos, hρ, pointAngle, Complex.norm_mul_cos_arg]
    simp
  · rw [Real.sin_arccos, hρ, pointAngle, Complex.norm_mul_sin_arg]
    simp
  · rw [Real.cos_arccos hh.1 hh.2, show heightRatio y = y 2 / ‖y‖ from rfl]
    field_simp

open CertCell.GivenShape.SphericalDivInternal (pointAngle_hasFDerivAt radialPhase_hasFDerivAt
  chartCoord_hasFDerivAt heightRatio_hasFDerivAt)
open CertCell.GivenShape.Internal.JoinedSpline (evP_hasFDerivAt)

theorem scalarValue_differentiableAt (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (M : ℤ)
    (ws : Bool) (S : PotScalar) (σ : ℝ) {y : Space} (hy0 : y ≠ 0) (hy1 : 0 < y 0 ∨ y 1 ≠ 0)
    (hh : |heightRatio y| < 1) (ht : chartCoord P y ∉ S.amp.tAxis.breaks)
    (hx : heightRatio y ∉ S.amp.xAxis.breaks) :
    DifferentiableAt ℝ (scalarValue P κ M ws S σ) y := by
  obtain ⟨La, ha, -⟩ := pointAngle_hasFDerivAt hy1
  obtain ⟨Lr, hr, -⟩ := radialPhase_hasFDerivAt hP.phase y
  obtain ⟨Lc, hc, -⟩ := chartCoord_hasFDerivAt P hP.chartLength_pos hy0
  obtain ⟨Lh, hhd, -⟩ := heightRatio_hasFDerivAt hy0
  have hθ : DifferentiableAt ℝ (fun z : Space => 2 * Real.pi * (labelTime κ.label : ℝ) * σ +
      (M : ℝ) * pointAngle z + (κ.phaseIndex : ℝ) * P.radialPhase (‖z‖ ^ 2)) y :=
    ((differentiableAt_const _).add (ha.differentiableAt.const_mul _)).add (hr.differentiableAt.const_mul _)
  have hE : DifferentiableAt ℝ (fun z : Space => Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
      (M : ℝ) * pointAngle z + (κ.phaseIndex : ℝ) * P.radialPhase (‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I)) y :=
    ((Complex.ofRealCLM.differentiableAt.comp y hθ).mul_const Complex.I).cexp
  have hW : DifferentiableAt ℝ
      (fun z : Space => CellCert.GivenFields.weightPoly S.lowOrder S.highOrder (chartCoord P z)) y := by
    have : DifferentiableAt ℝ
        (fun z : Space => chartCoord P z ^ S.lowOrder * (1 - chartCoord P z) ^ S.highOrder) y :=
      (hc.differentiableAt.pow _).mul (((differentiableAt_const _).sub hc.differentiableAt).pow _)
    exact Complex.ofRealCLM.differentiableAt.comp y this
  have hQ : DifferentiableAt ℝ (fun z : Space => (((1 - heightRatio z ^ 2) ^ S.axisPower *
      (if ws then polarSine z else 1) : ℝ) : ℂ)) y := by
    have hu : DifferentiableAt ℝ (fun z : Space => 1 - heightRatio z ^ 2) y :=
      (differentiableAt_const _).sub (hhd.differentiableAt.pow 2)
    have hpos : 1 - heightRatio y ^ 2 ≠ 0 := by
      have := abs_lt.1 hh
      nlinarith
    refine Complex.ofRealCLM.differentiableAt.comp y ((hu.pow _).mul ?_)
    cases ws
    · simp only [Bool.false_eq_true, if_false]
      exact differentiableAt_const _
    · simp only [if_true]
      exact hu.sqrt hpos
  have hH : DifferentiableAt ℝ
      (fun z : Space => S.amp.toSpline.evalHalf (chartCoord P z) (heightRatio z)) y := by
    set Q := S.amp.toSpline.piece (CellCert.GivenFields.cellIndex S.amp.tAxis.breaks (chartCoord P y))
      (CellCert.GivenFields.cellIndex S.amp.xAxis.breaks (heightRatio y))
    have hd := ((evP_hasFDerivAt Q (chartCoord P y, heightRatio y)).comp y (hc.prodMk hhd)).differentiableAt
    refine hd.congr_of_eventuallyEq ?_
    have h1 := hc.continuousAt.tendsto.eventually (FracInternal.cellIndex_eventually _ _ ht)
    have h2 := hhd.continuousAt.tendsto.eventually (FracInternal.cellIndex_eventually _ _ hx)
    filter_upwards [h1, h2] with z hz1 hz2
    show MvPolynomial.eval _ (S.amp.toSpline.piece
      (CellCert.GivenFields.cellIndex S.amp.tAxis.breaks (chartCoord P z))
      (CellCert.GivenFields.cellIndex S.amp.xAxis.breaks (heightRatio z))) = _
    rw [hz1, hz2]
    rfl
  exact ((hE.mul hW).mul hQ).mul hH

theorem coord_measurable (i : Fin 3) : Measurable fun z : Space => z i :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.measurable

theorem scalarValue_measurable (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (M : ℤ)
    (ws : Bool) (S : PotScalar) (σ : ℝ) : Measurable (scalarValue P κ M ws S σ) := by
  have hpa0 : Measurable fun z : Space => ((z 0 : ℝ) : ℂ) + ((z 1 : ℝ) : ℂ) * Complex.I :=
    (Complex.measurable_ofReal.comp (coord_measurable 0)).add
      ((Complex.measurable_ofReal.comp (coord_measurable 1)).mul_const _)
  have hpa : Measurable pointAngle := by
    have e : pointAngle = fun z : Space => Complex.arg (((z 0 : ℝ) : ℂ) + ((z 1 : ℝ) : ℂ) * Complex.I) := by
      funext z
      rfl
    rw [e]
    exact Complex.measurable_arg.comp hpa0
  have hrp : Measurable fun z : Space => P.radialPhase (‖z‖ ^ 2) := by
    obtain ⟨δ, hδ, hcd⟩ := hP.phase.smooth
    have hcn : Continuous fun z : Space => ‖z‖ ^ 2 := by fun_prop
    refine (hcd.continuousOn.comp_continuous hcn fun z => ?_).measurable
    show -δ < ‖z‖ ^ 2
    nlinarith [sq_nonneg ‖z‖]
  have hch : Measurable (chartCoord P) := measurable_norm.div (measurable_norm.add_const _)
  have hht : Measurable heightRatio := (coord_measurable 2).div measurable_norm
  have hE : Measurable fun z : Space => Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
      (M : ℝ) * pointAngle z + (κ.phaseIndex : ℝ) * P.radialPhase (‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      ((measurable_const.add (hpa.const_mul _)).add (hrp.const_mul _))).mul_const _)
  have hW : Measurable fun z : Space =>
      CellCert.GivenFields.weightPoly S.lowOrder S.highOrder (chartCoord P z) :=
    Complex.measurable_ofReal.comp ((hch.pow_const _).mul ((measurable_const.sub hch).pow_const _))
  have hs : Measurable fun z : Space => (if ws then polarSine z else 1) := by
    cases ws
    · exact measurable_const
    · exact (measurable_const.sub (hht.pow_const 2)).sqrt
  have hQ : Measurable fun z : Space => (((1 - heightRatio z ^ 2) ^ S.axisPower *
      (if ws then polarSine z else 1) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (((measurable_const.sub (hht.pow_const 2)).pow_const _).mul hs)
  have hH : Measurable fun z : Space => S.amp.toSpline.evalHalf (chartCoord P z) (heightRatio z) := by
    have h := (CellCert.GivenFields.DualPartsInternal.evalHalf_measurable S.amp.toSpline).comp
      (hch.prodMk hht)
    exact h
  have e : scalarValue P κ M ws S σ = fun z => Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
      (M : ℝ) * pointAngle z + (κ.phaseIndex : ℝ) * P.radialPhase (‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
      CellCert.GivenFields.weightPoly S.lowOrder S.highOrder (chartCoord P z) *
      (((1 - heightRatio z ^ 2) ^ S.axisPower * (if ws then polarSine z else 1) : ℝ) : ℂ) *
      S.amp.toSpline.evalHalf (chartCoord P z) (heightRatio z) := by
    funext z
    rfl
  rw [e]
  exact ((hE.mul hW).mul hQ).mul hH

theorem weightPoly_norm_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (a b : ℕ) :
    ‖CellCert.GivenFields.weightPoly a b t‖ ≤ 1 := by
  have h1' : 0 ≤ 1 - t := by linarith
  simp only [CellCert.GivenFields.weightPoly, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg h0 _) (pow_nonneg h1' _))]
  exact mul_le_one₀ (pow_le_one₀ h0 h1) (pow_nonneg h1' _) (pow_le_one₀ h1' (by linarith))

theorem chartCoord_mem (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) :
    0 ≤ chartCoord P y ∧ chartCoord P y ≤ 1 :=
  ⟨div_nonneg (norm_nonneg _) (by positivity), div_le_one_of_le₀ (by linarith) (by positivity)⟩

theorem profile_abs_le (k : ℕ) (ws : Bool) {x : ℝ} (hx : |x| ≤ 1) :
    |(1 - x ^ 2) ^ k * (if ws then Real.sqrt (1 - x ^ 2) else 1)| ≤ 1 := by
  have hu0 : 0 ≤ 1 - x ^ 2 := by nlinarith [abs_le.1 hx, sq_abs x, abs_nonneg x]
  have hu1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hp0 : 0 ≤ (1 - x ^ 2) ^ k := pow_nonneg hu0 _
  have hp1 : (1 - x ^ 2) ^ k ≤ 1 := pow_le_one₀ hu0 hu1
  cases ws
  · simp only [Bool.false_eq_true, if_false, mul_one]
    rw [abs_of_nonneg hp0]
    exact hp1
  · simp only [if_true]
    rw [abs_of_nonneg (mul_nonneg hp0 (Real.sqrt_nonneg _))]
    exact mul_le_one₀ hp1 (Real.sqrt_nonneg _) (Real.sqrt_le_one.2 hu1)

theorem scalarValue_bound (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (M : ℤ)
    (ws : Bool) (S : PotScalar) (σ : ℝ) : ∃ B, 0 ≤ B ∧ ∀ y, ‖scalarValue P κ M ws S σ y‖ ≤ B := by
  obtain ⟨Bh, hBh0, hBh⟩ := evalHalf_bound S.amp
  refine ⟨Bh, hBh0, fun y => ?_⟩
  obtain ⟨hc0, hc1⟩ := chartCoord_mem P hP.chartLength_pos y
  have hh := heightRatio_abs_le y
  have h1 := weightPoly_norm_le hc0 hc1 S.lowOrder S.highOrder
  have h2 : ‖((((1 - heightRatio y ^ 2) ^ S.axisPower * (if ws then polarSine y else 1)) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact profile_abs_le S.axisPower ws hh
  have h3 := hBh (chartCoord P y) (heightRatio y) (by rw [abs_of_nonneg hc0]; exact hc1) hh
  have hE : ‖Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ + (M : ℝ) * pointAngle y +
      (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  show ‖Complex.exp _ * CellCert.GivenFields.weightPoly _ _ _ * _ * _‖ ≤ Bh
  rw [norm_mul, norm_mul, norm_mul, hE, one_mul]
  calc _ ≤ 1 * 1 * Bh := by gcongr
    _ = Bh := by ring

theorem polarField_measurable : Measurable polarField :=
  (((coord_measurable 2).mul ((measurable_norm.pow_const 2).inv)).smul measurable_id).add_const _

theorem polarVecQ_measurable (i : Fin 3) : Measurable fun y => polarVecQ y i := by
  have e : (fun y => polarVecQ y i) = fun y => (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (polarField y) :=
    funext fun y => by simp [polarField_apply]
  rw [e]
  exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.measurable.comp polarField_measurable

theorem locInt_of_bounded {g : Space → ℂ} (hm : AEStronglyMeasurable g volume) (B : ℝ)
    (hb : ∀ y, ‖g y‖ ≤ B) : LocallyIntegrable g volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne hm (ae_of_all _ hb)

theorem polarDiv_of_slice {f : Space → ℂ} {r ϑ a : ℝ} (hr : 0 < r) (hϑ : Real.sin ϑ ≠ 0)
    (hf : DifferentiableAt ℝ f (sphericalPoint r ϑ a)) {G : ℂ}
    (hG : HasDerivAt (fun s => (Real.sin s ^ 2) • f (sphericalPoint r s a)) G ϑ) :
    polarDiv f (sphericalPoint r ϑ a) = ((r * Real.sin ϑ)⁻¹ : ℝ) • G := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hs : HasDerivAt (fun s => Real.sin s ^ 2) (2 * Real.sin ϑ * Real.cos ϑ) ϑ := by
    refine ((Real.hasDerivAt_sin ϑ).pow 2).congr_deriv ?_
    push_cast
    ring
  have h2 := hs.smul (hf.hasFDerivAt.comp_hasDerivAt ϑ (hasDerivAt_sphericalPoint r ϑ a))
  rw [hG.unique h2]
  simp only [polarDiv]
  rw [fderiv_polarField_sph hr, norm_sphericalPoint hr.le, (sphericalPoint_apply r ϑ a).2.2]
  simp only [Complex.real_smul, Function.comp_apply]
  generalize Real.sin ϑ = s at hϑ ⊢
  generalize Real.cos ϑ = c
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hϑ
  push_cast
  field_simp

theorem sliceProfile_continuous (P : ShapeParams) (S : PotScalar) (ws : Bool)
    (hxA : IsJetAxis S.amp.xAxis (-1) 1) (r : ℝ) : Continuous (sliceProfile P S ws r) :=
  (continuous_const.mul (Complex.continuous_ofReal.comp (axisProfile_continuous _ _))).mul
    (evalHalf_continuous_height hxA _)

theorem sliceProfile_hasDerivAt (P : ShapeParams) (hP : IsShapeParams P) (S : PotScalar) (ws : Bool)
    {Bh Bhx : ℝ}
    (hBh : ∀ t x : ℝ, |t| ≤ 1 → |x| ≤ 1 → ‖S.amp.toSpline.evalHalf t x‖ ≤ Bh)
    (hBhx : ∀ t x : ℝ, |t| ≤ 1 → |x| ≤ 1 → ‖MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1
      (S.amp.toSpline.piece (CellCert.GivenFields.cellIndex S.amp.tAxis.breaks t)
        (CellCert.GivenFields.cellIndex S.amp.xAxis.breaks x)))‖ ≤ Bhx)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo (-1 : ℝ) 1) (hxb : x ∉ S.amp.xAxis.breaks) :
    ∃ L', HasDerivAt (sliceProfile P S ws r) L' x ∧ ‖L'‖ ≤ (2 * S.axisPower + 3) * Bh + Bhx := by
  have hL := hP.chartLength_pos
  have ht0 : 0 ≤ r / (r + P.chartLength) := div_nonneg hr.le (by linarith)
  have ht1 : r / (r + P.chartLength) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
  have hta : |r / (r + P.chartLength)| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have hxa : |x| ≤ 1 := abs_le.2 ⟨hx.1.le, hx.2.le⟩
  obtain ⟨d, hd, hdb⟩ := axisProfile_deriv S.axisPower ws hx
  have hh := evalHalf_hasDerivAt_height S.amp (r / (r + P.chartLength)) x hxb
  have hprod := ((hd.ofReal_comp).const_mul
    (CellCert.GivenFields.weightPoly S.lowOrder S.highOrder (r / (r + P.chartLength)))).mul hh
  refine ⟨_, hprod, ?_⟩
  have hW := weightPoly_norm_le ht0 ht1 S.lowOrder S.highOrder
  have hψ := axisProfile_abs_le S.axisPower ws hxa
  have h1 := hBh _ x hta hxa
  have h2 := hBhx _ x hta hxa
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have hd0 : 0 ≤ |d| := abs_nonneg d
  have e1 : ‖CellCert.GivenFields.weightPoly S.lowOrder S.highOrder (r / (r + P.chartLength))‖ * |d| *
      ‖S.amp.toSpline.evalHalf (r / (r + P.chartLength)) x‖ ≤ 1 * (2 * S.axisPower + 3) * Bh := by
    gcongr
  have e2 : ‖CellCert.GivenFields.weightPoly S.lowOrder S.highOrder (r / (r + P.chartLength))‖ *
      |axisProfile S.axisPower ws x| * ‖MvPolynomial.eval ![((r / (r + P.chartLength) : ℝ) : ℂ), (x : ℂ)]
        (MvPolynomial.pderiv 1 (S.amp.toSpline.piece
          (CellCert.GivenFields.cellIndex S.amp.tAxis.breaks (r / (r + P.chartLength)))
          (CellCert.GivenFields.cellIndex S.amp.xAxis.breaks x)))‖ ≤ 1 * 1 * Bhx := by
    gcongr
  linarith

theorem height_abs_lt {y : Space} (hy0 : y 0 ≠ 0) : |heightRatio y| < 1 := by
  have hyne : y ≠ 0 := by
    intro h
    apply hy0
    rw [h]
    simp
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hyne
  have hsq := norm_sq_coords y
  have h0 : 0 < y 0 ^ 2 := by positivity
  have hlt : |y 2| < ‖y‖ := abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (y 1)]) hn.le
  rw [show heightRatio y = y 2 / ‖y‖ from rfl, abs_div, abs_of_pos hn, div_lt_one hn]
  exact hlt

theorem polarDiv_bound (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (M : ℤ) (ws : Bool)
    (S : PotScalar) (σ : ℝ) {Bh Bhx : ℝ}
    (hBh : ∀ t x : ℝ, |t| ≤ 1 → |x| ≤ 1 → ‖S.amp.toSpline.evalHalf t x‖ ≤ Bh)
    (hBhx : ∀ t x : ℝ, |t| ≤ 1 → |x| ≤ 1 → ‖MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1
      (S.amp.toSpline.piece (CellCert.GivenFields.cellIndex S.amp.tAxis.breaks t)
        (CellCert.GivenFields.cellIndex S.amp.xAxis.breaks x)))‖ ≤ Bhx)
    {y : Space} (hy0 : y 0 ≠ 0) (hy1 : y 1 ≠ 0) (ht : chartCoord P y ∉ S.amp.tAxis.breaks)
    (hx : heightRatio y ∉ S.amp.xAxis.breaks) :
    ‖polarDiv (scalarValue P κ M ws S σ) y‖ ≤ ((2 * S.axisPower + 3) * Bh + Bhx) * ‖y‖⁻¹ := by
  have hyne : y ≠ 0 := by
    intro h
    apply hy0
    rw [h]
    simp
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hyne
  have hh : |heightRatio y| < 1 := height_abs_lt hy0
  obtain ⟨hh1, hh2⟩ := abs_lt.1 hh
  have hϑ0 : 0 < Real.arccos (heightRatio y) := Real.arccos_pos.2 hh2
  have hϑπ : Real.arccos (heightRatio y) < Real.pi := Real.arccos_lt_pi.2 hh1
  have hsin : 0 < Real.sin (Real.arccos (heightRatio y)) := Real.sin_pos_of_pos_of_lt_pi hϑ0 hϑπ
  have hcos : Real.cos (Real.arccos (heightRatio y)) = heightRatio y := Real.cos_arccos hh1.le hh2.le
  have hrep := sph_repr hyne
  obtain ⟨L', hL', hL'b⟩ := sliceProfile_hasDerivAt P hP S ws hBh hBhx hr
    (x := Real.cos (Real.arccos (heightRatio y))) (by rw [hcos]; exact ⟨hh1, hh2⟩) (by rw [hcos]; exact hx)
  have hf : DifferentiableAt ℝ (scalarValue P κ M ws S σ)
      (sphericalPoint ‖y‖ (Real.arccos (heightRatio y)) (pointAngle y)) := by
    rw [hrep]
    exact scalarValue_differentiableAt P hP κ M ws S σ hyne (Or.inr hy1) hh ht hx
  have hG : HasDerivAt (fun s => (Real.sin s ^ 2) •
      scalarValue P κ M ws S σ (sphericalPoint ‖y‖ s (pointAngle y)))
      (sliceFactor P κ M σ ‖y‖ (pointAngle y) * ((-Real.sin (Real.arccos (heightRatio y))) • L'))
      (Real.arccos (heightRatio y)) := by
    have h1 := (hL'.scomp (Real.arccos (heightRatio y)) (Real.hasDerivAt_cos _)).const_mul
      (sliceFactor P κ M σ ‖y‖ (pointAngle y))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds hϑ0 hϑπ] with s hs
    exact slice_eq P κ M ws S σ hr (pointAngle y) hs
  have hD := polarDiv_of_slice hr hsin.ne' hf hG
  rw [hrep] at hD
  rw [hD]
  have hE : ‖sliceFactor P κ M σ ‖y‖ (pointAngle y)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  rw [norm_smul, norm_mul, norm_smul, hE, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_pos hsin,
    abs_of_pos (inv_pos.2 (mul_pos hr hsin))]
  have e : (‖y‖ * Real.sin (Real.arccos (heightRatio y)))⁻¹ *
      (1 * (Real.sin (Real.arccos (heightRatio y)) * ‖L'‖)) = ‖L'‖ * ‖y‖⁻¹ := by
    field_simp
  rw [e]
  gcongr

theorem ae_chartCoord_ne (P : ShapeParams) (hL : 0 < P.chartLength) (b : ℝ) :
    ∀ᵐ y : Space, chartCoord P y ≠ b := by
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_)
    (Measure.addHaar_sphere volume (0 : Space) (b * P.chartLength / (1 - b)))
  simp only [ne_eq, Decidable.not_not, Set.mem_ofPred_eq, chartCoord] at hy
  have hpos : 0 < ‖y‖ + P.chartLength := by positivity
  rw [div_eq_iff hpos.ne'] at hy
  have hb : b ≠ 1 := by
    intro e
    rw [e] at hy
    linarith
  have hne : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
  rw [mem_sphere_zero_iff_norm, eq_div_iff hne]
  linarith

theorem ae_generic_point (P : ShapeParams) (hP : IsShapeParams P) (S : PotScalar) :
    ∀ᵐ y : Space, y 0 ≠ 0 ∧ y 1 ≠ 0 ∧ chartCoord P y ∉ S.amp.tAxis.breaks ∧
      heightRatio y ∉ S.amp.xAxis.breaks := by
  have ht : ∀ᵐ y : Space, ∀ b ∈ {a | a ∈ S.amp.tAxis.breaks}, chartCoord P y ≠ b :=
    (Filter.eventually_all_finite (List.finite_toSet _)).2 fun b _ => ae_chartCoord_ne P hP.chartLength_pos b
  have hx : ∀ᵐ y : Space, ∀ b ∈ {a | a ∈ S.amp.xAxis.breaks}, |heightRatio y| ≠ |b| :=
    (Filter.eventually_all_finite (List.finite_toSet _)).2 fun b _ => FracInternal.ae_heightRatio_abs_ne |b|
  filter_upwards [FracInternal.ae_coord_ne_zero 0, FracInternal.ae_coord_ne_zero 1, ht, hx]
    with y h0 h1 h2 h3
  exact ⟨h0, h1, fun h => h2 _ h rfl, fun h => h3 _ h rfl⟩

theorem polarVecQ_hasFDerivAt {y : Space} (hy : y ≠ 0) (i : Fin 3) :
    HasFDerivAt (fun z => ((polarVecQ z i : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ polarField y))) y := by
  have e : (fun z => ((polarVecQ z i : ℝ) : ℂ)) =
      fun z => Complex.ofRealCLM ((EuclideanSpace.proj i : Space →L[ℝ] ℝ) (polarField z)) :=
    funext fun z => by simp [polarField_apply]
  rw [e]
  exact Complex.ofRealCLM.hasFDerivAt.comp y
    ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y (polarField_diff hy).hasFDerivAt)

theorem clm_apply_coords_complex (L : Space →L[ℝ] ℂ) (w : Space) :
    L w = ∑ i : Fin 3, (w i : ℂ) * L (unitVector i) := by
  have e : w = ∑ i : Fin 3, w i • unitVector i := by
    ext j
    fin_cases j <;> simp [unitVector, Fin.sum_univ_three]
  conv_lhs => rw [e]
  simp [map_sum, Complex.real_smul]

theorem div_eq_polarDiv {f : Space → ℂ} {y : Space} (hy : y ≠ 0) (hf : DifferentiableAt ℝ f y) :
    ∑ i : Fin 3, fderiv ℝ (fun x => f x * (polarVecQ x i : ℂ)) y (unitVector i) = polarDiv f y := by
  have hterm : ∀ i : Fin 3, fderiv ℝ (fun x => f x * (polarVecQ x i : ℂ)) y (unitVector i) =
      f y * ((fderiv ℝ polarField y (unitVector i) i : ℝ) : ℂ) +
        (polarVecQ y i : ℂ) * fderiv ℝ f y (unitVector i) := by
    intro i
    have hm : HasFDerivAt (fun x => f x * ((polarVecQ x i : ℝ) : ℂ)) _ y :=
      hf.hasFDerivAt.mul (polarVecQ_hasFDerivAt hy i)
    rw [hm.fderiv]
    simp
  have hdiv : ∑ i : Fin 3, (fderiv ℝ polarField y (unitVector i)) i = 2 * y 2 / ‖y‖ ^ 2 := div_polarField hy
  simp only [hterm, Finset.sum_add_distrib]
  rw [polarDiv, clm_apply_coords_complex (fderiv ℝ f y) (polarField y), ← Finset.mul_sum,
    ← Complex.ofReal_sum, hdiv]
  simp only [polarField_apply]
  ring

theorem polar_weak_of {f : Space → ℂ}
    (hV : ∀ i : Fin 3, LocallyIntegrable (fun y => f y * (polarVecQ y i : ℂ)))
    (hdiff : ∀ᵐ y, DifferentiableAt ℝ f y) (hD : LocallyIntegrable (polarDiv f))
    (hslice : ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi)),
      ContinuousOn (fun ϑ => (Real.sin ϑ ^ 2) • f (sphericalPoint q.1 ϑ q.2)) (Icc 0 Real.pi) ∧
        ∃ S : Set ℝ, S.Countable ∧ ∀ ϑ ∈ Ioo 0 Real.pi \ S, DifferentiableAt ℝ f (sphericalPoint q.1 ϑ q.2)) :
    (∀ i : Fin 3, LocallyIntegrable (fun y => f y * (polarVecQ y i : ℂ))) ∧
    (∀ᵐ y, ∀ i : Fin 3, DifferentiableAt ℝ (fun x => f x * (polarVecQ x i : ℂ)) y) ∧
    LocallyIntegrable (fun y => ∑ i : Fin 3, fderiv ℝ (fun x => f x * (polarVecQ x i : ℂ)) y (unitVector i)) ∧
    ∀ φ, IsTestFunction φ →
      ∫ y, (φ y : ℂ) * (∑ i : Fin 3, fderiv ℝ (fun x => f x * (polarVecQ x i : ℂ)) y (unitVector i)) =
      -∫ y, ∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) * (f y * (polarVecQ y i : ℂ)) := by
  have hne : ∀ᵐ y : Space, y ≠ 0 := by
    rw [ae_iff]
    simp
  have heq : (fun y => ∑ i : Fin 3, fderiv ℝ (fun x => f x * (polarVecQ x i : ℂ)) y (unitVector i))
      =ᵐ[volume] polarDiv f := by
    filter_upwards [hne, hdiff] with y hy hfy
    exact div_eq_polarDiv hy hfy
  refine ⟨hV, ?_, hD.congr heq.symm, fun φ hφ => ?_⟩
  · filter_upwards [hne, hdiff] with y hy hfy i
    exact hfy.mul (polarVecQ_hasFDerivAt hy i).differentiableAt
  · rw [← weak_identity hV hD hslice hφ]
    refine integral_congr_ae ?_
    filter_upwards [heq] with y hy
    rw [hy]

theorem ae_radius_generic (P : ShapeParams) (hP : IsShapeParams P) (l : List ℝ) :
    ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi)),
      q.1 / (q.1 + P.chartLength) ∉ l := by
  have hL := hP.chartLength_pos
  set T : Set ℝ := {r | 0 < r ∧ r / (r + P.chartLength) ∈ l} with hT
  have hTc : T.Countable := by
    have hsub : T ⊆ ⋃ b ∈ {a | a ∈ l}, {r : ℝ | 0 < r ∧ r / (r + P.chartLength) = b} :=
      fun r hr => mem_biUnion hr.2 ⟨hr.1, rfl⟩
    refine Countable.mono hsub ((List.finite_toSet l).countable.biUnion fun b _ => ?_)
    refine Subsingleton.countable fun r1 h1 r2 h2 => ?_
    have e := h1.2.trans h2.2.symm
    rw [div_eq_div_iff (by linarith [h1.1]) (by linarith [h2.1])] at e
    have : P.chartLength * (r1 - r2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hprod : (volume : Measure (ℝ × ℝ)) (T ×ˢ univ) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, hTc.measure_zero, zero_mul]
  have hae : ∀ᵐ q : ℝ × ℝ ∂volume, q ∉ T ×ˢ univ := by
    rw [ae_iff]
    exact measure_mono_null (fun q hq => not_not.1 hq) hprod
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)]
    with q h1 h2 hmem
  exact h1 ⟨⟨h2.1, hmem⟩, mem_univ _⟩

theorem angles_countable (l : List ℝ) : {s | s ∈ Icc 0 Real.pi ∧ Real.cos s ∈ l}.Countable := by
  have hsub : {s | s ∈ Icc 0 Real.pi ∧ Real.cos s ∈ l} ⊆
      ⋃ b ∈ {a | a ∈ l}, {s | s ∈ Icc 0 Real.pi ∧ Real.cos s = b} :=
    fun s hs => mem_biUnion hs.2 ⟨hs.1, rfl⟩
  refine Countable.mono hsub ((List.finite_toSet l).countable.biUnion fun b _ => ?_)
  exact Subsingleton.countable fun s1 h1 s2 h2 => Real.injOn_cos h1.1 h2.1 (h1.2.trans h2.2.symm)

theorem polarScalar_weak (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (M : ℤ) (ws : Bool)
    (S : PotScalar) (hxA : IsJetAxis S.amp.xAxis (-1) 1) (σ : ℝ) :
    (∀ i : Fin 3, LocallyIntegrable (fun y => scalarValue P κ M ws S σ y * (polarVecQ y i : ℂ))) ∧
    (∀ᵐ y, ∀ i : Fin 3, DifferentiableAt ℝ (fun x => scalarValue P κ M ws S σ x * (polarVecQ x i : ℂ)) y) ∧
    LocallyIntegrable (fun y => ∑ i : Fin 3,
      fderiv ℝ (fun x => scalarValue P κ M ws S σ x * (polarVecQ x i : ℂ)) y (unitVector i)) ∧
    ∀ φ, IsTestFunction φ →
      ∫ y, (φ y : ℂ) * (∑ i : Fin 3,
        fderiv ℝ (fun x => scalarValue P κ M ws S σ x * (polarVecQ x i : ℂ)) y (unitVector i)) =
      -∫ y, ∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) *
        (scalarValue P κ M ws S σ y * (polarVecQ y i : ℂ)) := by
  obtain ⟨B, hB0, hB⟩ := scalarValue_bound P hP κ M ws S σ
  have hfm := scalarValue_measurable P hP κ M ws S σ
  have hV : ∀ i : Fin 3, LocallyIntegrable (fun y => scalarValue P κ M ws S σ y * (polarVecQ y i : ℂ)) := by
    intro i
    refine locInt_of_bounded (hfm.mul (Complex.measurable_ofReal.comp (polarVecQ_measurable i))).aestronglyMeasurable
      B fun y => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖scalarValue P κ M ws S σ y‖ * |polarVecQ y i| ≤ B * 1 := by
          gcongr
          · exact hB y
          · exact CellCert.GivenFields.DualRestOpenInternal.polar_le y i
      _ = B := mul_one B
  have hgen := ae_generic_point P hP S
  have hne0 : ∀ y : Space, y 0 ≠ 0 → y ≠ 0 := by
    intro y h0 h
    apply h0
    rw [h]
    simp
  have hdiff : ∀ᵐ y, DifferentiableAt ℝ (scalarValue P κ M ws S σ) y := by
    filter_upwards [hgen] with y hy
    exact scalarValue_differentiableAt P hP κ M ws S σ (hne0 y hy.1) (Or.inr hy.2.1) (height_abs_lt hy.1)
      hy.2.2.1 hy.2.2.2
  obtain ⟨Bh, hBh0, hBh⟩ := evalHalf_bound S.amp
  obtain ⟨Bhx, -, hBhx⟩ := evalHalf_height_bound S.amp
  have hDm : AEStronglyMeasurable (polarDiv (scalarValue P κ M ws S σ)) volume := by
    have h1 : AEStronglyMeasurable (fun y => fderiv ℝ (scalarValue P κ M ws S σ) y (polarField y)) volume :=
      (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Space) (F := ℂ)).continuous.comp_aestronglyMeasurable
        ((measurable_fderiv ℝ (scalarValue P κ M ws S σ)).aestronglyMeasurable.prodMk
          polarField_measurable.aestronglyMeasurable)
    have h2 : Measurable (fun y : Space => ((2 * y 2 / ‖y‖ ^ 2 : ℝ) : ℂ) * scalarValue P κ M ws S σ y) :=
      (Complex.measurable_ofReal.comp ((measurable_const.mul (coord_measurable 2)).div
        (measurable_norm.pow_const 2))).mul hfm
    exact h1.add h2.aestronglyMeasurable
  have hD : LocallyIntegrable (polarDiv (scalarValue P κ M ws S σ)) := by
    refine CellCert.GivenFields.DualRestOpenInternal.locInt_of_inv hDm ((2 * S.axisPower + 3) * Bh + Bhx) ?_
    filter_upwards [hgen] with y hy
    exact polarDiv_bound P hP κ M ws S σ hBh hBhx hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
  refine polar_weak_of hV hdiff hD ?_
  filter_upwards [ae_radius_generic P hP S.amp.tAxis.breaks,
    ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with q hq hmem
  obtain ⟨hr, ha⟩ := hmem
  have hr' : 0 < q.1 := hr
  refine ⟨?_, {s | s ∈ Icc 0 Real.pi ∧ Real.cos s ∈ S.amp.xAxis.breaks}, angles_countable _,
    fun ϑ hϑ => ?_⟩
  · have hc : Continuous fun s => sliceFactor P κ M σ q.1 q.2 * sliceProfile P S ws q.1 (Real.cos s) :=
      continuous_const.mul ((sliceProfile_continuous P S ws hxA q.1).comp Real.continuous_cos)
    exact hc.continuousOn.congr fun s hs => slice_eq P κ M ws S σ hr' q.2 hs
  · obtain ⟨⟨h0, hπ⟩, hnot⟩ := hϑ
    have hsin : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
    obtain ⟨c0, c1, -⟩ := sphericalPoint_apply q.1 ϑ q.2
    have hyne : sphericalPoint q.1 ϑ q.2 ≠ 0 := by
      intro h
      have := norm_sphericalPoint hr'.le ϑ q.2
      rw [h, norm_zero] at this
      linarith
    have hy1 : 0 < sphericalPoint q.1 ϑ q.2 0 ∨ sphericalPoint q.1 ϑ q.2 1 ≠ 0 := by
      by_cases hsa : Real.sin q.2 = 0
      · left
        have ha0 : q.2 = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt ha.1 ha.2).1 hsa
        rw [c0, ha0, Real.cos_zero, mul_one]
        exact mul_pos hr' hsin
      · right
        rw [c1]
        exact mul_ne_zero (mul_ne_zero hr'.ne' hsin.ne') hsa
    have hh : |heightRatio (sphericalPoint q.1 ϑ q.2)| < 1 := by
      rw [heightRatio_sph hr']
      refine abs_lt_of_sq_lt_sq ?_ zero_le_one
      nlinarith [Real.sin_sq_add_cos_sq ϑ]
    refine scalarValue_differentiableAt P hP κ M ws S σ hyne hy1 hh ?_ ?_
    · rw [chartCoord_sph P hr']
      exact hq
    · rw [heightRatio_sph hr']
      exact fun hc => hnot ⟨⟨h0.le, hπ.le⟩, hc⟩

end Internal.PolarFlux

theorem polarFluxPart_weakDivergence (P : ShapeParams) (F : PotentialSeries) (hP : IsShapeParams P)
    (hF : IsPotentialSeries F) (κ : FieldKey) (hκ : κ ∈ F.keys) (c : PotComponent) (σ : ℝ) :
    (∀ i : Fin 3, LocallyIntegrable
      (fun y => componentValue P κ (F.data κ).polarFlux c σ y * (polarVecQ y i : ℂ))) ∧
    (∀ᵐ y, ∀ i : Fin 3, DifferentiableAt ℝ
      (fun x => componentValue P κ (F.data κ).polarFlux c σ x * (polarVecQ x i : ℂ)) y) ∧
    LocallyIntegrable (fun y => ∑ i : Fin 3, fderiv ℝ
      (fun x => componentValue P κ (F.data κ).polarFlux c σ x * (polarVecQ x i : ℂ)) y (unitVector i)) ∧
    ∀ φ, IsTestFunction φ →
      ∫ y, (φ y : ℂ) * (∑ i : Fin 3, fderiv ℝ
        (fun x => componentValue P κ (F.data κ).polarFlux c σ x * (polarVecQ x i : ℂ)) y (unitVector i)) =
      -∫ y, ∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) *
        (componentValue P κ (F.data κ).polarFlux c σ y * (polarVecQ y i : ℂ)) :=
  Internal.PolarFlux.polarScalar_weak P hP κ (labelAzimuth P.azimuthOrder κ.label + c.shift) c.carriesSine
    ((F.data κ).polarFlux c) (hF.polarFlux_mesh κ hκ c).2 σ

end Breakdown.PotentialShape
