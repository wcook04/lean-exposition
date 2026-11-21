import Breakdown.Cert.CoerciveSmoothEpsSetting
import Breakdown.Cert.CoerciveSmoothPieceEpsRestDefs
import Breakdown.Cert.CoerciveSmoothMuWave
import Breakdown.Cert.CoerciveSmoothEpsPointwiseSecondDeriv

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothEpsPointwise

open Internal.SmoothPieceEpsCore Internal.MuSmooth Internal.PieceAbsorb

theorem rot_frame (φ a : ℝ) (y : Space) :
    axialRot (-φ) ((1 / 2 : ℝ) • axialRot φ y - a • axialPerp (axialRot φ y)) = (1 / 2 : ℝ) • y - a • axialPerp y := by
  have h := Real.sin_sq_add_cos_sq φ
  ext i
  fin_cases i
  · simp [axialRot, axialPerp, unitVector, Real.cos_neg, Real.sin_neg]
    linear_combination ((1 / 2) * y 0 + a * y 1) * h
  · simp [axialRot, axialPerp, unitVector, Real.cos_neg, Real.sin_neg]
    linear_combination ((1 / 2) * y 1 - a * y 0) * h
  · simp [axialRot, axialPerp, unitVector]

section Bounds

variable {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
  {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}

theorem transport_le (hS : SmoothEpsInternal.EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) (c : C)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    cnorm3 (modeVel ι (transportRest (m.rate c y) W v) σ y)
      ≤ ‖relativeVelocity W (m.rate c) y‖ * vortGradAmp (secondDerivField v) ι σ y
        + ∑ α ∈ m.waves, velAmp W α σ y * vortGradAmp (secondDerivField v) (ι - α) σ y := by
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hS.smooth.smooth 2
  set a := m.rate c y with ha
  set u : ℝ → Space → Space := fun s x => W s x + (1 / 2 : ℝ) • x - a • axialPerp x with hu
  set d := relativeVelocity W (m.rate c) y with hd
  have hU : ∀ τ φ : ℝ, ∀ j : Fin 3, ((axialRot (-φ) (u (σ + τ) (axialRot φ y)) j : ℝ) : ℂ)
      = ((fun j => d j) j : ℂ) + ∑ α ∈ m.waves,
        Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I) * modeVel α W σ y j := by
    intro τ φ j
    have e1 : axialRot (-φ) (u (σ + τ) (axialRot φ y))
        = axialRot (-φ) (W (σ + τ) (axialRot φ y)) + ((1 / 2 : ℝ) • y - a • axialPerp y) := by
      simp only [hu]
      rw [add_sub_assoc, Internal.Field.axialRot_add, rot_frame]
    have e2 : d = meanField W y + ((1 / 2 : ℝ) • y - a • axialPerp y) := by
      simp only [hd, relativeVelocity, axialPerp, ha]
      rw [add_sub_assoc]
    simp only
    rw [e1, e2, PiLp.add_apply, PiLp.add_apply, Complex.ofReal_add, Complex.ofReal_add,
      velW_expansion hS.flow_smooth hS.flow_periodic m.waves hS.admissible.waves_neg hS.valid.harmonics σ τ φ y j]
    ring
  have hK : Continuous (fun z : ℝ × Space => fderiv ℝ (vortField v z.1) z.2) := vortGrad_continuous hv2
  have hT : modeVel ι (transportRest a W v) σ y = fun i => ∑ j : Fin 3,
      (modeGrad ι (fun s x => fderiv ℝ (vortField v s) x) σ y (i, j) * ((d j : ℝ) : ℂ)
        + ∑ α ∈ m.waves, modeGrad (ι - α) (fun s x => fderiv ℝ (vortField v s) x) σ y (i, j) * modeVel α W σ y j) :=
    funext fun i => mode_product_vec m.waves (fun s x => fderiv ℝ (vortField v s) x) hK u σ y (fun j => d j)
      (fun α j => modeVel α W σ y j) hU ι i
  rw [hT]
  refine (cnorm3_product_le m.waves (fun κ => modeGrad κ (fun s x => fderiv ℝ (vortField v s) x) σ y) d
    (fun α j => modeVel α W σ y j) ι).trans (le_of_eq ?_)
  simp only [modeGrad_vort_eq hv2]
  rw [mul_comm]
  rfl

theorem stretch_split (hS : SmoothEpsInternal.EpsSetting m P b w W w₀ epsSup epsGradSup ratio v)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    ∃ R : Fin 3 → ℂ, modeVel ι (stretchRest W v) σ y
        = (fun i => ∑ j : Fin 3, ((fderiv ℝ (meanField W) y (unitVector j) i : ℝ) : ℂ) * vortMode v ι σ y j) + R
      ∧ cnorm3 R ≤ ∑ α ∈ m.waves, gradAmp (gradField W) α σ y * vortAmp (gradField v) (ι - α) σ y := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hS.smooth.smooth 1
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hS.smooth.smooth 2
  obtain ⟨B, hB⟩ := grad_bound_of_decay hS.flow_decay
  have hvc : Continuous (fun z : ℝ × Space => vortField v z.1 z.2) := vortField_continuous hv2
  have hE := fun τ φ i j => gradW_expansion hS.flow_smooth hB hS.flow_periodic m.waves hS.admissible.waves_neg
    hS.valid.harmonics σ τ φ y i j
  have hmp := fun i => mode_product m.waves W (vortField v) hvc σ y
    (fun i j => fderiv ℝ (meanField W) y (unitVector j) i) (fun α ij => modeGrad α (gradField W) σ y ij) hE ι i
  have hω : ∀ κ, modeVel κ (vortField v) σ y = vortMode v κ σ y := fun κ => (vortMode_eq_modeVel hv1 κ σ y).symm
  refine ⟨fun i => ∑ j : Fin 3, ∑ α ∈ m.waves, modeGrad α (gradField W) σ y (i, j) * vortMode v (ι - α) σ y j,
    ?_, ?_⟩
  · funext i
    rw [Pi.add_apply]
    have h := hmp i
    simp only [hω] at h
    refine h.trans ?_
    rw [Finset.sum_add_distrib]
  · have hsplit : (fun i => ∑ j : Fin 3, ∑ α ∈ m.waves, modeGrad α (gradField W) σ y (i, j) * vortMode v (ι - α) σ y j)
        = ∑ α ∈ m.waves, (fun i => ∑ j : Fin 3, modeGrad α (gradField W) σ y (i, j) * vortMode v (ι - α) σ y j) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_comm]
    rw [hsplit]
    refine (cnorm3_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    exact cnorm3_mat_le (modeGrad α (gradField W) σ y) _

theorem vortTransport_le (hS : SmoothEpsInternal.EpsSetting m P b w W w₀ epsSup epsGradSup ratio v)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    cnorm3 (modeVel ι (vortTransportRest W v) σ y)
      ≤ ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * velAmp v ι σ y
        + ∑ α ∈ m.waves, vortGradAmp (secondDerivField W) α σ y * velAmp v (ι - α) σ y := by
  obtain ⟨B, hB⟩ := grad_bound_of_decay hS.flow_decay
  obtain ⟨B₂, hB₂⟩ := secondDeriv_bound_of_decay hS.flow_decay
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hS.smooth.smooth.continuous
  set A := fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y
  set g : ℤ × ℤ → Fin 3 × Fin 3 → ℂ := fun α ij => curlGradOfSecondDeriv (modeSecondDeriv α (secondDerivField W) σ y) ij
  have hE : ∀ τ φ : ℝ, ∀ i j : Fin 3,
      ((axialRot (-φ) (fderiv ℝ (vortField W (σ + τ)) (axialRot φ y) (axialRot φ (unitVector j))) i : ℝ) : ℂ)
        = ((fun i j => A (unitVector j) i) i j : ℂ) + ∑ α ∈ m.waves,
          Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I) * g α (i, j) :=
    fun τ φ i j => vortGradW_expansion hS.flow_smooth hB hB₂ hS.flow_periodic m.waves hS.admissible.waves_neg
      hS.valid.harmonics σ τ φ y i j
  have hmp : ∀ i, modeVel ι (vortTransportRest W v) σ y i
      = ∑ j : Fin 3, ((((fun i j => A (unitVector j) i) i j : ℝ) : ℂ) * modeVel ι v σ y j
        + ∑ α ∈ m.waves, g α (i, j) * modeVel (ι - α) v σ y j) :=
    fun i => mode_product m.waves (vortField W) v hvc σ y (fun i j => A (unitVector j) i) g hE ι i
  have hsplit : modeVel ι (vortTransportRest W v) σ y
      = (fun i => ∑ j : Fin 3, ((A (unitVector j) i : ℝ) : ℂ) * modeVel ι v σ y j)
        + ∑ α ∈ m.waves, (fun i => ∑ j : Fin 3, g α (i, j) * modeVel (ι - α) v σ y j) := by
    funext i
    rw [hmp i, Pi.add_apply, Finset.sum_apply, Finset.sum_add_distrib, Finset.sum_comm (s := m.waves)]
  rw [hsplit]
  refine (cnorm3_add_le _ _).trans (add_le_add (cnorm3_clm_le A _) ?_)
  refine (cnorm3_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
  exact cnorm3_mat_le (g α) _

theorem vortStretch_le (hS : SmoothEpsInternal.EpsSetting m P b w W w₀ epsSup epsGradSup ratio v)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    cnorm3 (modeVel ι (vortStretchRest W v) σ y)
      ≤ ‖curlVec (fderiv ℝ (meanField W) y)‖ * gradAmp (gradField v) ι σ y
        + ∑ α ∈ m.waves, vortAmp (gradField W) α σ y * gradAmp (gradField v) (ι - α) σ y := by
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hS.smooth.smooth 2
  obtain ⟨B, hB⟩ := grad_bound_of_decay hS.flow_decay
  have hK : Continuous (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) := continuous_fderiv_slice hv2
  have hU := fun τ φ j => vortW_expansion hS.flow_smooth hB hS.flow_periodic m.waves hS.admissible.waves_neg
    hS.valid.harmonics σ τ φ y j
  have hT : modeVel ι (vortStretchRest W v) σ y = fun i => ∑ j : Fin 3,
      (modeGrad ι (fun s x => fderiv ℝ (v s) x) σ y (i, j) * ((curlVec (fderiv ℝ (meanField W) y) j : ℝ) : ℂ)
        + ∑ α ∈ m.waves, modeGrad (ι - α) (fun s x => fderiv ℝ (v s) x) σ y (i, j)
          * curlOfGrad (modeGrad α (gradField W) σ y) j) :=
    funext fun i => mode_product_vec m.waves (fun s x => fderiv ℝ (v s) x) hK (vortField W) σ y
      (fun j => curlVec (fderiv ℝ (meanField W) y) j) (fun α j => curlOfGrad (modeGrad α (gradField W) σ y) j) hU ι i
  rw [hT]
  refine (cnorm3_product_le m.waves (fun κ => modeGrad κ (fun s x => fderiv ℝ (v s) x) σ y)
    (curlVec (fderiv ℝ (meanField W) y)) (fun α j => curlOfGrad (modeGrad α (gradField W) σ y) j) ι).trans
    (le_of_eq ?_)
  rw [mul_comm]
  rfl

theorem frame_split (hS : SmoothEpsInternal.EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) (a : ℝ)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeVel ι (frameRest a W v) σ y
      = modeVel ι (transportRest a W v) σ y - modeVel ι (stretchRest W v) σ y
        + modeVel ι (vortTransportRest W v) σ y - modeVel ι (vortStretchRest W v) σ y
        + modeVel ι (rotationRest a v) σ y := by
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hS.smooth.smooth 2
  have hW := hS.flow_smooth
  have cv : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv2.continuous
  have cW : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  have c1 : Continuous (fun z : ℝ × Space => transportRest a W v z.1 z.2) := by
    unfold transportRest
    have hx : Continuous (fun z : ℝ × Space => (1 / 2 : ℝ) • z.2) := by fun_prop
    have hp : Continuous (fun z : ℝ × Space => a • axialPerp z.2) :=
      (axialPerp_continuous.comp continuous_snd).const_smul a
    exact (vortGrad_continuous hv2).clm_apply ((cW.add hx).sub hp)
  have c2 : Continuous (fun z : ℝ × Space => stretchRest W v z.1 z.2) := by
    unfold stretchRest
    exact (continuous_fderiv_slice hW).clm_apply (vortField_continuous hv2)
  have c3 : Continuous (fun z : ℝ × Space => vortTransportRest W v z.1 z.2) := by
    unfold vortTransportRest
    exact (vortGrad_continuous hW).clm_apply cv
  have c4 : Continuous (fun z : ℝ × Space => vortStretchRest W v z.1 z.2) := by
    unfold vortStretchRest
    exact (continuous_fderiv_slice hv2).clm_apply (vortField_continuous hW)
  have c5 : Continuous (fun z : ℝ × Space => rotationRest a v z.1 z.2) := by
    unfold rotationRest
    exact (axialPerp_continuous.comp (vortField_continuous hv2)).const_smul a
  have c12 : Continuous (fun z : ℝ × Space => (transportRest a W v - stretchRest W v) z.1 z.2) := c1.sub c2
  have c123 : Continuous (fun z : ℝ × Space =>
      (transportRest a W v - stretchRest W v + vortTransportRest W v) z.1 z.2) := c12.add c3
  have c1234 : Continuous (fun z : ℝ × Space =>
      (transportRest a W v - stretchRest W v + vortTransportRest W v - vortStretchRest W v) z.1 z.2) := c123.sub c4
  have e : frameRest a W v = transportRest a W v - stretchRest W v + vortTransportRest W v
      - vortStretchRest W v + rotationRest a v := rfl
  rw [e, Internal.Field.modeVel_add c1234 c5, modeVel_sub' c123 c4, Internal.Field.modeVel_add c12 c3,
    modeVel_sub' c1 c2]

end Bounds

private theorem cross_bound (e c0 c1 c2 p0 p1 p2 q0 q1 q2 K : ℝ) (hK : K ^ 2 = c0 ^ 2 + c1 ^ 2 + c2 ^ 2)
    (hK0 : 0 ≤ K) :
    -e * (c0 * (p1 * q2 - p2 * q1) + c1 * (p2 * q0 - p0 * q2) + c2 * (p0 * q1 - p1 * q0))
      ≤ |e| * ((1 / 2) * K) * ((p0 ^ 2 + q0 ^ 2) + (p1 ^ 2 + q1 ^ 2) + (p2 ^ 2 + q2 ^ 2)) := by
  have hu : (p1 * q2 - p2 * q1) ^ 2 + (p2 * q0 - p0 * q2) ^ 2 + (p0 * q1 - p1 * q0) ^ 2
      ≤ (p0 ^ 2 + p1 ^ 2 + p2 ^ 2) * (q0 ^ 2 + q1 ^ 2 + q2 ^ 2) := by
    nlinarith [sq_nonneg (p0 * q0 + p1 * q1 + p2 * q2)]
  have hs : (c0 * (p1 * q2 - p2 * q1) + c1 * (p2 * q0 - p0 * q2) + c2 * (p0 * q1 - p1 * q0)) ^ 2
      ≤ K ^ 2 * ((p1 * q2 - p2 * q1) ^ 2 + (p2 * q0 - p0 * q2) ^ 2 + (p0 * q1 - p1 * q0) ^ 2) := by
    rw [hK]
    nlinarith [sq_nonneg (c0 * (p2 * q0 - p0 * q2) - c1 * (p1 * q2 - p2 * q1)),
      sq_nonneg (c0 * (p0 * q1 - p1 * q0) - c2 * (p1 * q2 - p2 * q1)),
      sq_nonneg (c1 * (p0 * q1 - p1 * q0) - c2 * (p2 * q0 - p0 * q2))]
  have hPQ : (p0 ^ 2 + p1 ^ 2 + p2 ^ 2) * (q0 ^ 2 + q1 ^ 2 + q2 ^ 2)
      ≤ (((p0 ^ 2 + q0 ^ 2) + (p1 ^ 2 + q1 ^ 2) + (p2 ^ 2 + q2 ^ 2)) / 2) ^ 2 := by
    nlinarith [sq_nonneg ((p0 ^ 2 + p1 ^ 2 + p2 ^ 2) - (q0 ^ 2 + q1 ^ 2 + q2 ^ 2))]
  generalize (c0 * (p1 * q2 - p2 * q1) + c1 * (p2 * q0 - p0 * q2) + c2 * (p0 * q1 - p1 * q0)) = s at hs ⊢
  generalize (p1 * q2 - p2 * q1) ^ 2 + (p2 * q0 - p0 * q2) ^ 2 + (p0 * q1 - p1 * q0) ^ 2 = U at hu hs
  generalize (p0 ^ 2 + p1 ^ 2 + p2 ^ 2) * (q0 ^ 2 + q1 ^ 2 + q2 ^ 2) = PQ at hu hPQ
  have hN : 0 ≤ (p0 ^ 2 + q0 ^ 2) + (p1 ^ 2 + q1 ^ 2) + (p2 ^ 2 + q2 ^ 2) := by positivity
  generalize (p0 ^ 2 + q0 ^ 2) + (p1 ^ 2 + q1 ^ 2) + (p2 ^ 2 + q2 ^ 2) = N at hPQ hN ⊢
  have hsq : (-e * s) ^ 2 ≤ (|e| * ((1 / 2) * K) * N) ^ 2 := by
    have h1 : (-e * s) ^ 2 = e ^ 2 * s ^ 2 := by ring
    have h2 : (|e| * ((1 / 2) * K) * N) ^ 2 = e ^ 2 * (K ^ 2 * (N / 2) ^ 2) := by
      rw [mul_pow, mul_pow, mul_pow, sq_abs]
      ring
    rw [h1, h2]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg e)
    calc s ^ 2 ≤ K ^ 2 * U := hs
      _ ≤ K ^ 2 * PQ := mul_le_mul_of_nonneg_left hu (sq_nonneg _)
      _ ≤ K ^ 2 * (N / 2) ^ 2 := mul_le_mul_of_nonneg_left hPQ (sq_nonneg _)
  exact StretchInternal.le_of_sq_le_sq_of_nonneg hsq (by positivity)

theorem mean_stretch_re_le (e : ℝ) (A : Space →L[ℝ] Space) (x : Fin 3 → ℂ) :
    (Complex.I * (e : ℂ) * cdot x (fun i => ∑ j : Fin 3, ((A (unitVector j) i : ℝ) : ℂ) * x j)).re
      ≤ |e| * ((1 / 2) * ‖curlVec A‖) * cnormSq x := by
  have hc0 : curlVec A 0 = A (unitVector 1) 2 - A (unitVector 2) 1 := by
    simp [curlVec, Fin.sum_univ_three, alternatingSymbol, unitVector]
    ring
  have hc1 : curlVec A 1 = A (unitVector 2) 0 - A (unitVector 0) 2 := by
    simp [curlVec, Fin.sum_univ_three, alternatingSymbol, unitVector]
    ring
  have hc2 : curlVec A 2 = A (unitVector 0) 1 - A (unitVector 1) 0 := by
    simp [curlVec, Fin.sum_univ_three, alternatingSymbol, unitVector]
    ring
  have hre : (Complex.I * (e : ℂ) * cdot x (fun i => ∑ j : Fin 3, ((A (unitVector j) i : ℝ) : ℂ) * x j)).re
      = -e * (curlVec A 0 * ((x 1).re * (x 2).im - (x 2).re * (x 1).im)
        + curlVec A 1 * ((x 2).re * (x 0).im - (x 0).re * (x 2).im)
        + curlVec A 2 * ((x 0).re * (x 1).im - (x 1).re * (x 0).im)) := by
    rw [hc0, hc1, hc2]
    simp only [cdot, Fin.sum_univ_three, map_add, map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have hK : ‖curlVec A‖ ^ 2 = curlVec A 0 ^ 2 + curlVec A 1 ^ 2 + curlVec A 2 ^ 2 := by
    rw [space_norm_sq, Fin.sum_univ_three]
  have hX : cnormSq x = ((x 0).re ^ 2 + (x 0).im ^ 2) + ((x 1).re ^ 2 + (x 1).im ^ 2)
      + ((x 2).re ^ 2 + (x 2).im ^ 2) := by
    simp only [cnormSq, Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hre, hX]
  exact cross_bound e _ _ _ _ _ _ _ _ _ _ hK (norm_nonneg _)

theorem re_cdot_abs_le (e : ℝ) (x z : Fin 3 → ℂ) :
    |(Complex.I * (e : ℂ) * cdot x z).re| ≤ |e| * cnorm3 x * cnorm3 z := by
  refine (Internal.FieldModes.abs_re_I_mul_le e _).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (Internal.Field.norm_cdot_le_sqrt x z) (abs_nonneg e)

end Internal.SmoothEpsPointwise

end Coercive

end Breakdown
