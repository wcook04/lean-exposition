import Breakdown.FracCell.GivenProfileDefs
import Breakdown.FracCell.GivenToolkit
import Breakdown.FracCell.FieldJointSmooth

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace FieldDriftInternal

def planeTurn (θ : ℝ) (y : Space) : Space :=
  EuclideanSpace.single 0 (Real.cos θ * y 0 - Real.sin θ * y 1) +
    EuclideanSpace.single 1 (Real.sin θ * y 0 + Real.cos θ * y 1) + EuclideanSpace.single 2 (y 2)

theorem planeTurn_coords (θ : ℝ) (y : Space) :
    planeTurn θ y 0 = Real.cos θ * y 0 - Real.sin θ * y 1 ∧
      planeTurn θ y 1 = Real.sin θ * y 0 + Real.cos θ * y 1 ∧ planeTurn θ y 2 = y 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [planeTurn]

theorem norm_planeTurn (θ : ℝ) (y : Space) : ‖planeTurn θ y‖ = ‖y‖ := by
  obtain ⟨h0, h1, h2⟩ := planeTurn_coords θ y
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, h0, h1, h2]
  have := Real.sin_sq_add_cos_sq θ
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * this

theorem norm_scale (τ : ℝ) (y : Space) : ‖Real.exp τ • y‖ = Real.exp τ * ‖y‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos τ)]

theorem flowPoint_norm (τ θ : ℝ) (y : Space) :
    ‖Real.exp τ • planeTurn θ y‖ = ‖Real.exp τ • y‖ := by
  rw [norm_scale, norm_scale, norm_planeTurn]

theorem flowPoint_height (τ θ : ℝ) (y : Space) :
    heightRatio (Real.exp τ • planeTurn θ y) = heightRatio y := by
  unfold heightRatio
  rw [flowPoint_norm, norm_scale]
  simp only [PiLp.smul_apply, smul_eq_mul, (planeTurn_coords θ y).2.2]
  rcases eq_or_ne ‖y‖ 0 with h | h
  · simp [h]
  · field_simp

theorem flowPoint_modePhase (P : ChartParams) (n : ℤ) (β τ θ : ℝ) (y : Space) (hy : y 0 ≠ 0) :
    modePhase P n β (Real.exp τ • planeTurn θ y) =
      Complex.exp (Complex.I * (((n : ℝ) * (P.m : ℝ) * θ : ℝ) : ℂ)) * modePhase P n β (Real.exp τ • y) := by
  obtain ⟨h0, h1, _⟩ := planeTurn_coords θ y
  set c : ℝ := Real.exp τ with hc
  have hcpos : 0 < c := Real.exp_pos τ
  have hw : (⟨(c • planeTurn θ y) 0, (c • planeTurn θ y) 1⟩ : ℂ) =
      ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) * ⟨(c • y) 0, (c • y) 1⟩ := by
    apply Complex.ext <;> simp [h0, h1, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_im] <;> ring
  have hw0 : (⟨(c • y) 0, (c • y) 1⟩ : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    rcases this with h' | h'
    · exact hcpos.ne' h'
    · exact hy h'
  have hu0 : ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im] at hr hi
    have := Real.sin_sq_add_cos_sq θ
    rw [hr, hi] at this
    norm_num at this
  have hang : (Complex.arg (((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) * ⟨(c • y) 0, (c • y) 1⟩) :
      Real.Angle) = ((θ + Complex.arg ⟨(c • y) 0, (c • y) 1⟩ : ℝ) : Real.Angle) := by
    rw [Complex.arg_mul_coe_angle hu0 hw0, Real.Angle.coe_add]
    congr 1
    have := Complex.arg_cos_add_sin_mul_I_coe_angle (θ : Real.Angle)
    rwa [Real.Angle.cos_coe, Real.Angle.sin_coe] at this
  obtain ⟨j, hj⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hang
  unfold modePhase angleOf logPhase
  rw [hw, flowPoint_norm]
  have harg : Complex.arg (((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) * ⟨(c • y) 0, (c • y) 1⟩) =
      Complex.arg ⟨(c • y) 0, (c • y) 1⟩ + θ + 2 * Real.pi * j := by linarith
  rw [harg, ← Complex.exp_add]
  have e1 : Complex.exp (Complex.I * (((n * P.m : ℤ) : ℝ) * (2 * Real.pi * j) : ℝ)) = 1 := by
    rw [← Complex.exp_int_mul_two_pi_mul_I (n * P.m * j)]
    congr 1
    push_cast
    ring
  rw [← mul_one (Complex.exp (Complex.I * _ + _)), ← e1, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem flowPoint_frames (τ θ : ℝ) (y : Space) (hy : y ≠ 0) :
    let p := Real.exp τ • planeTurn θ y
    (radialVec p 0 = Real.cos θ * radialVec y 0 - Real.sin θ * radialVec y 1 ∧
      radialVec p 1 = Real.sin θ * radialVec y 0 + Real.cos θ * radialVec y 1 ∧ radialVec p 2 = radialVec y 2) ∧
    (polarVecQ p 0 = Real.cos θ * polarVecQ y 0 - Real.sin θ * polarVecQ y 1 ∧
      polarVecQ p 1 = Real.sin θ * polarVecQ y 0 + Real.cos θ * polarVecQ y 1 ∧ polarVecQ p 2 = polarVecQ y 2) ∧
    (azimVecQ p 0 = Real.cos θ * azimVecQ y 0 - Real.sin θ * azimVecQ y 1 ∧
      azimVecQ p 1 = Real.sin θ * azimVecQ y 0 + Real.cos θ * azimVecQ y 1 ∧ azimVecQ p 2 = azimVecQ y 2) := by
  intro p
  obtain ⟨h0, h1, h2⟩ := planeTurn_coords θ y
  have hn : ‖p‖ = Real.exp τ * ‖y‖ := by rw [flowPoint_norm, norm_scale]
  have hh : heightRatio p = heightRatio y := flowPoint_height τ θ y
  have hne : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have he : Real.exp τ ≠ 0 := (Real.exp_pos τ).ne'
  have hp0 : p 0 = Real.exp τ * (Real.cos θ * y 0 - Real.sin θ * y 1) := by
    simp only [p, PiLp.smul_apply, smul_eq_mul, h0]
  have hp1 : p 1 = Real.exp τ * (Real.sin θ * y 0 + Real.cos θ * y 1) := by
    simp only [p, PiLp.smul_apply, smul_eq_mul, h1]
  have hp2 : p 2 = Real.exp τ * y 2 := by
    simp only [p, PiLp.smul_apply, smul_eq_mul, h2]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · simp only [radialVec, hn, hp0]; field_simp
  · simp only [radialVec, hn, hp1]; field_simp
  · simp only [radialVec, hn, hp2]; field_simp
  · show heightRatio p * p 0 / ‖p‖ = Real.cos θ * (heightRatio y * y 0 / ‖y‖) - Real.sin θ * (heightRatio y * y 1 / ‖y‖)
    rw [hh, hn, hp0]; field_simp
  · show heightRatio p * p 1 / ‖p‖ = Real.sin θ * (heightRatio y * y 0 / ‖y‖) + Real.cos θ * (heightRatio y * y 1 / ‖y‖)
    rw [hh, hn, hp1]; field_simp
  · show -(qOf p) = -(qOf y)
    unfold qOf
    rw [hh]
  · show -(p 1) / ‖p‖ = Real.cos θ * (-(y 1) / ‖y‖) - Real.sin θ * (y 0 / ‖y‖)
    rw [hn, hp1]; field_simp; ring
  · show p 0 / ‖p‖ = Real.sin θ * (-(y 1) / ‖y‖) + Real.cos θ * (y 0 / ‖y‖)
    rw [hn, hp0]; field_simp; ring
  · show (0 : ℝ) = 0
    rfl

theorem re_turn_combo (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (D : ℂ) (S : Finset ℤ) (ph R0 R1 R2 : ℤ → ℂ)
    (a0 a1 b0 b1 d0 d1 : ℝ) :
    c * (D * ∑ n ∈ S, ph n * (R0 n * ((c * a0 - s * a1 : ℝ) : ℂ) + R1 n * ((c * b0 - s * b1 : ℝ) : ℂ) +
        R2 n * ((c * d0 - s * d1 : ℝ) : ℂ))).re +
      s * (D * ∑ n ∈ S, ph n * (R0 n * ((s * a0 + c * a1 : ℝ) : ℂ) + R1 n * ((s * b0 + c * b1 : ℝ) : ℂ) +
        R2 n * ((s * d0 + c * d1 : ℝ) : ℂ))).re =
      (D * ∑ n ∈ S, ph n * (R0 n * (a0 : ℂ) + R1 n * (b0 : ℂ) + R2 n * (d0 : ℂ))).re := by
  have hcs' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  rw [← Complex.re_ofReal_mul, ← Complex.re_ofReal_mul, ← Complex.add_re]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  linear_combination (D * ph n * (R0 n * a0 + R1 n * b0 + R2 n * d0)) * hcs'

theorem re_turn_combo' (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (D : ℂ) (S : Finset ℤ) (ph R0 R1 R2 : ℤ → ℂ)
    (a0 a1 b0 b1 d0 d1 : ℝ) :
    -s * (D * ∑ n ∈ S, ph n * (R0 n * ((c * a0 - s * a1 : ℝ) : ℂ) + R1 n * ((c * b0 - s * b1 : ℝ) : ℂ) +
        R2 n * ((c * d0 - s * d1 : ℝ) : ℂ))).re +
      c * (D * ∑ n ∈ S, ph n * (R0 n * ((s * a0 + c * a1 : ℝ) : ℂ) + R1 n * ((s * b0 + c * b1 : ℝ) : ℂ) +
        R2 n * ((s * d0 + c * d1 : ℝ) : ℂ))).re =
      (D * ∑ n ∈ S, ph n * (R0 n * (a1 : ℂ) + R1 n * (b1 : ℂ) + R2 n * (d1 : ℂ))).re := by
  have hcs' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  rw [← Complex.re_ofReal_mul, ← Complex.re_ofReal_mul, ← Complex.add_re]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  linear_combination (D * ph n * (R0 n * a1 + R1 n * b1 + R2 n * d1)) * hcs'

theorem flow_identity (P : ChartParams) (F : FieldData) (β τ θ : ℝ) (y : Space) (hy : y 0 ≠ 0) :
    planeTurn (-θ) (fieldOf P F β (Real.exp τ • planeTurn θ y)) =
      ofComponents (fun i => ((decayFactor P (Real.exp τ • y) : ℂ) * ∑ n ∈ F.modes,
        (Complex.exp (Complex.I * (((n : ℝ) * (P.m : ℝ) * θ : ℝ) : ℂ)) * modePhase P n β (Real.exp τ • y)) *
          (reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 0 * radialVec y i +
            reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 1 * polarVecQ y i +
              reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 2 * azimVecQ y i)).re) := by
  have hy' : y ≠ 0 := fun h => hy (by simp [h])
  set p := Real.exp τ • planeTurn θ y with hp
  have hdec : decayFactor P p = decayFactor P (Real.exp τ • y) := by
    unfold decayFactor chartS chartT
    rw [hp, flowPoint_norm]
  have hT : chartT P p = chartT P (Real.exp τ • y) := by
    unfold chartT
    rw [hp, flowPoint_norm]
  have hH : heightRatio p = heightRatio y := flowPoint_height τ θ y
  have hph : ∀ n, modePhase P n β p = Complex.exp (Complex.I * (((n : ℝ) * (P.m : ℝ) * θ : ℝ) : ℂ)) *
      modePhase P n β (Real.exp τ • y) := fun n => flowPoint_modePhase P n β τ θ y hy
  obtain ⟨⟨r0, r1, r2⟩, ⟨q0, q1, q2⟩, ⟨z0, z1, z2⟩⟩ := flowPoint_frames τ θ y hy'
  have hv : ∀ j, fieldOf P F β p j = ((decayFactor P (Real.exp τ • y) : ℂ) * ∑ n ∈ F.modes,
      (Complex.exp (Complex.I * (((n : ℝ) * (P.m : ℝ) * θ : ℝ) : ℂ)) * modePhase P n β (Real.exp τ • y)) *
        (reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 0 * radialVec p j +
          reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 1 * polarVecQ p j +
            reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 2 * azimVecQ p j)).re := by
    intro j
    simp only [fieldOf, FracInternal.ofComponents_apply, hdec, hT, hH, hph]
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by rw [add_comm]; exact Real.sin_sq_add_cos_sq θ
  have c0 := re_turn_combo (Real.cos θ) (Real.sin θ) hcs (decayFactor P (Real.exp τ • y) : ℂ) F.modes
    (fun n => Complex.exp (Complex.I * (((n : ℝ) * (P.m : ℝ) * θ : ℝ) : ℂ)) * modePhase P n β (Real.exp τ • y))
    (fun n => reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 0)
    (fun n => reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 1)
    (fun n => reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 2)
    (radialVec y 0) (radialVec y 1) (polarVecQ y 0) (polarVecQ y 1) (azimVecQ y 0) (azimVecQ y 1)
  have c1 := re_turn_combo' (Real.cos θ) (Real.sin θ) hcs (decayFactor P (Real.exp τ • y) : ℂ) F.modes
    (fun n => Complex.exp (Complex.I * (((n : ℝ) * (P.m : ℝ) * θ : ℝ) : ℂ)) * modePhase P n β (Real.exp τ • y))
    (fun n => reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 0)
    (fun n => reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 1)
    (fun n => reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 2)
    (radialVec y 0) (radialVec y 1) (polarVecQ y 0) (polarVecQ y 1) (azimVecQ y 0) (azimVecQ y 1)
  beta_reduce at c0 c1
  set W : Fin 3 → ℝ := fun i => ((decayFactor P (Real.exp τ • y) : ℂ) * ∑ n ∈ F.modes,
        (Complex.exp (Complex.I * (((n : ℝ) * (P.m : ℝ) * θ : ℝ) : ℂ)) * modePhase P n β (Real.exp τ • y)) *
          (reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 0 * radialVec y i +
            reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 1 * polarVecQ y i +
              reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 2 * azimVecQ y i)).re with hW
  have e0 : (planeTurn (-θ) (fieldOf P F β p)) 0 = ofComponents W 0 := by
    rw [(planeTurn_coords _ _).1, Real.cos_neg, Real.sin_neg, FracInternal.ofComponents_apply, hv 0, hv 1,
      r0, r1, q0, q1, z0, z1, hW]
    linarith
  have e1 : (planeTurn (-θ) (fieldOf P F β p)) 1 = ofComponents W 1 := by
    rw [(planeTurn_coords _ _).2.1, Real.cos_neg, Real.sin_neg, FracInternal.ofComponents_apply, hv 0, hv 1,
      r0, r1, q0, q1, z0, z1, hW]
    linarith
  have e2 : (planeTurn (-θ) (fieldOf P F β p)) 2 = ofComponents W 2 := by
    rw [(planeTurn_coords _ _).2.2, FracInternal.ofComponents_apply, hv 2, r2, q2, z2, hW]
  ext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2


def flowTerm (P : ChartParams) (D : FieldData) (n : ℤ) (β om t x : ℝ) (k : Fin 3) : ℂ :=
  ((1 + 2 * P.eps * (1 - t) : ℝ) : ℂ) * reducedField P D n β t x k +
    ((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' => reducedField P D n β t' x k) t +
      Complex.I * (((n : ℝ) * (P.m : ℝ) * om * (1 - coreRatioT P t) : ℝ) : ℂ) * reducedField P D n β t x k

open FracInternal.FieldJoint

theorem planeTurn_split (θ : ℝ) (y : Space) :
    planeTurn θ y = Real.cos θ • (EuclideanSpace.single 0 (y 0) + EuclideanSpace.single 1 (y 1) : Space) +
      Real.sin θ • axialTurn y + EuclideanSpace.single 2 (y 2) := by
  ext i
  fin_cases i <;> simp [planeTurn, axialTurn] <;> ring

theorem split_base (y : Space) :
    (EuclideanSpace.single 0 (y 0) + EuclideanSpace.single 1 (y 1) : Space) + EuclideanSpace.single 2 (y 2) = y := by
  ext i
  fin_cases i <;> simp

theorem curve_hasDerivAt (om : ℝ) (y : Space) :
    HasDerivAt (fun τ : ℝ => Real.exp τ • planeTurn (om * τ) y) (y + om • axialTurn y) 0 := by
  have hc : HasDerivAt (fun τ : ℝ => Real.cos (om * τ)) 0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul om).cos
  have hs : HasDerivAt (fun τ : ℝ => Real.sin (om * τ)) om 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul om).sin
  have hinner : HasDerivAt (fun τ : ℝ => Real.cos (om * τ) • (EuclideanSpace.single 0 (y 0) + EuclideanSpace.single 1 (y 1) : Space) +
      Real.sin (om * τ) • axialTurn y + (EuclideanSpace.single 2 (y 2) : Space))
      ((0 : ℝ) • (EuclideanSpace.single 0 (y 0) + EuclideanSpace.single 1 (y 1) : Space) + om • axialTurn y) 0 :=
    ((hc.smul_const _).add (hs.smul_const _)).add_const _
  have hex : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
  have h := hex.smul hinner
  have e : (fun τ : ℝ => Real.exp τ • planeTurn (om * τ) y) = fun τ : ℝ => Real.exp τ •
      (Real.cos (om * τ) • (EuclideanSpace.single 0 (y 0) + EuclideanSpace.single 1 (y 1) : Space) +
        Real.sin (om * τ) • axialTurn y + (EuclideanSpace.single 2 (y 2) : Space)) :=
    funext fun τ => by rw [planeTurn_split]
  rw [e]
  refine h.congr_deriv ?_
  simp only [Real.exp_zero, one_smul, zero_smul, zero_add, mul_zero, Real.cos_zero, Real.sin_zero]
  rw [add_zero, split_base, add_comm]

theorem planeTurn_zero (z : Space) : planeTurn 0 z = z := by
  rw [planeTurn_split]
  simp only [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]
  exact split_base z

theorem curve_zero (om : ℝ) (y : Space) : Real.exp 0 • planeTurn (om * 0) y = y := by
  rw [planeTurn_split]
  simp only [Real.exp_zero, one_smul, mul_zero, Real.cos_zero, Real.sin_zero, zero_smul, add_zero]
  exact split_base y

theorem scaled_chartT (P : ChartParams) (y : Space) (τ : ℝ) :
    chartT P (Real.exp τ • y) = Real.exp τ * ‖y‖ / (Real.exp τ * ‖y‖ + P.L0) := by
  unfold chartT
  rw [norm_scale]

theorem chartT_hasDerivAt (P : ChartParams) (hP : IsChartParams P) (y : Space) :
    HasDerivAt (fun τ : ℝ => chartT P (Real.exp τ • y)) (chartT P y * (1 - chartT P y)) 0 := by
  have hL := hP.L0_pos
  have hn := norm_nonneg y
  have e : (fun τ : ℝ => chartT P (Real.exp τ • y)) = fun τ => Real.exp τ * ‖y‖ / (Real.exp τ * ‖y‖ + P.L0) :=
    funext fun τ => scaled_chartT P y τ
  rw [e]
  have h1 : HasDerivAt (fun τ : ℝ => Real.exp τ * ‖y‖) (Real.exp 0 * ‖y‖) 0 := (Real.hasDerivAt_exp 0).mul_const _
  have hden : Real.exp 0 * ‖y‖ + P.L0 ≠ 0 := by rw [Real.exp_zero]; linarith
  refine (h1.div (h1.add_const P.L0) hden).congr_deriv ?_
  unfold chartT
  rw [Real.exp_zero]
  have : ‖y‖ + P.L0 ≠ 0 := by linarith
  field_simp

theorem decay_hasDerivAt (P : ChartParams) (hP : IsChartParams P) (y : Space) :
    HasDerivAt (fun τ : ℝ => decayFactor P (Real.exp τ • y))
      (-(2 * P.eps * chartT P y * decayFactor P y)) 0 := by
  have hL := hP.L0_pos
  have hs : 1 - chartT P y ≠ 0 := by
    unfold chartT
    have hn := norm_nonneg y
    have : ‖y‖ / (‖y‖ + P.L0) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have h := ((chartT_hasDerivAt P hP y).const_sub 1).rpow_const (p := 2 * P.eps)
    (Or.inl (by simpa [Real.exp_zero] using hs))
  unfold decayFactor chartS
  refine h.congr_deriv ?_
  simp only [Real.exp_zero, one_smul]
  rw [Real.rpow_sub_one hs]
  field_simp

theorem angleOf_scale (y : Space) (τ : ℝ) : angleOf (Real.exp τ • y) = angleOf y := by
  unfold angleOf
  have e : (⟨(Real.exp τ • y) 0, (Real.exp τ • y) 1⟩ : ℂ) = ((Real.exp τ : ℝ) : ℂ) * ⟨y 0, y 1⟩ := by
    apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      PiLp.smul_apply, smul_eq_mul] <;> ring
  rw [e, Complex.arg_real_mul _ (Real.exp_pos τ)]

theorem logPhase_hasDerivAt (P : ChartParams) (hP : IsChartParams P) (y : Space) :
    HasDerivAt (fun τ : ℝ => logPhase P (Real.exp τ • y)) (coreRatioT P (chartT P y)) 0 := by
  have hL := hP.L0_pos
  have hr := hP.rc_pos
  have hn := norm_nonneg y
  have e : (fun τ : ℝ => logPhase P (Real.exp τ • y)) =
      fun τ => (1 / 2) * Real.log (1 + (Real.exp τ * ‖y‖) ^ 2 / P.rc ^ 2) := by
    funext τ
    unfold logPhase
    rw [norm_scale]
  rw [e]
  have h1 : HasDerivAt (fun τ : ℝ => 1 + (Real.exp τ * ‖y‖) ^ 2 / P.rc ^ 2)
      (2 * (Real.exp 0 * ‖y‖) ^ (2 - 1) * (Real.exp 0 * ‖y‖) / P.rc ^ 2) 0 := by
    have := (((Real.hasDerivAt_exp 0).mul_const ‖y‖).pow 2).div_const (P.rc ^ 2)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this.const_add 1
  have hpos : 1 + (Real.exp 0 * ‖y‖) ^ 2 / P.rc ^ 2 ≠ 0 := by positivity
  refine ((h1.log hpos).const_mul (1 / 2)).congr_deriv ?_
  have hq : ‖y‖ + P.L0 ≠ 0 := by linarith
  have hrr : ‖y‖ ^ 2 + P.rc ^ 2 ≠ 0 := by positivity
  have hA : 1 / 2 * (2 * (Real.exp 0 * ‖y‖) ^ (2 - 1) * (Real.exp 0 * ‖y‖) / P.rc ^ 2 /
      (1 + (Real.exp 0 * ‖y‖) ^ 2 / P.rc ^ 2)) = ‖y‖ ^ 2 / (‖y‖ ^ 2 + P.rc ^ 2) := by
    rw [Real.exp_zero]
    field_simp
    ring
  have hB : coreRatioT P (chartT P y) = ‖y‖ ^ 2 / (‖y‖ ^ 2 + P.rc ^ 2) := by
    unfold coreRatioT chartT
    have e1 : 1 - ‖y‖ / (‖y‖ + P.L0) = P.L0 / (‖y‖ + P.L0) := by field_simp; ring
    rw [e1, div_pow, div_pow]
    have : (‖y‖ ^ 2 + P.rc ^ 2) * P.L0 ^ 2 ≠ 0 := by positivity
    field_simp
  rw [hA, hB]

theorem phase_hasDerivAt (P : ChartParams) (hP : IsChartParams P) (n : ℤ) (β om : ℝ) (y : Space) :
    HasDerivAt (fun τ : ℝ => Complex.exp (Complex.I * (((n : ℝ) * (P.m : ℝ) * (om * τ) : ℝ) : ℂ)) *
        modePhase P n β (Real.exp τ • y))
      (Complex.I * (((n : ℝ) * (P.m : ℝ) * om + n * β * coreRatioT P (chartT P y) : ℝ) : ℂ) *
        modePhase P n β y) 0 := by
  have e : (fun τ : ℝ => Complex.exp (Complex.I * (((n : ℝ) * (P.m : ℝ) * (om * τ) : ℝ) : ℂ)) *
        modePhase P n β (Real.exp τ • y)) = fun τ : ℝ => Complex.exp (Complex.I *
          ((((n : ℝ) * (P.m : ℝ) * (om * τ)) + (((n * P.m : ℤ) : ℝ) * angleOf y +
            n * β * logPhase P (Real.exp τ • y)) : ℝ) : ℂ)) := by
    funext τ
    unfold modePhase
    rw [angleOf_scale, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  have hin : HasDerivAt (fun τ : ℝ => (((n : ℝ) * (P.m : ℝ) * (om * τ)) + (((n * P.m : ℤ) : ℝ) * angleOf y +
      n * β * logPhase P (Real.exp τ • y)) : ℝ))
      ((n : ℝ) * (P.m : ℝ) * (om * 1) + (n * β * coreRatioT P (chartT P y))) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_mul om |>.const_mul _).add
      (((logPhase_hasDerivAt P hP y).const_mul (n * β)).const_add _)
  have h := ((hin.ofReal_comp).const_mul Complex.I).cexp
  refine h.congr_deriv ?_
  have e0 : Complex.exp (Complex.I * ((((n : ℝ) * (P.m : ℝ) * (om * 0)) + (((n * P.m : ℤ) : ℝ) * angleOf y +
      n * β * logPhase P (Real.exp 0 • y)) : ℝ) : ℂ)) = modePhase P n β y := by
    unfold modePhase
    rw [Real.exp_zero, one_smul]
    congr 2
    push_cast
    ring
  rw [e0]
  push_cast
  ring

theorem reduced_hasDerivAt (P : ChartParams) (hP : IsChartParams P) (F : FieldData) (n : ℤ) (β : ℝ)
    {y : Space} (hx0 : heightRatio y ≠ 0)
    (hgen : ∀ S ∈ [(F.amp n).radialAmp, (F.amp n).polarAmp, (F.amp n).streamAmp, (F.amp n).swirlAmp],
      chartT P y ∉ S.mesh.tBreaks ∧ |heightRatio y| ∉ S.mesh.xBreaks) (k : Fin 3) :
    HasDerivAt (fun τ : ℝ => reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) k)
      ((chartT P y * (1 - chartT P y)) •
        deriv (fun t' => reducedField P F n β t' (heightRatio y) k) (chartT P y)) 0 := by
  have hd : DifferentiableAt ℝ (fun t' => reducedField P F n β t' (heightRatio y) k) (chartT P y) := by
    have hc := ContDiffAt.comp (f := fun t' : ℝ => (β, t', heightRatio y)) (chartT P y)
      (reduced_contDiffAt P hP F n hx0 hgen β k) (contDiffAt_const.prodMk (contDiffAt_id.prodMk contDiffAt_const))
    exact hc.differentiableAt (by simp)
  have h0 : chartT P (Real.exp 0 • y) = chartT P y := by rw [Real.exp_zero, one_smul]
  have hg : HasDerivAt (fun t' => reducedField P F n β t' (heightRatio y) k)
      (deriv (fun t' => reducedField P F n β t' (heightRatio y) k) (chartT P y)) (chartT P (Real.exp 0 • y)) := by
    rw [h0]
    exact hd.hasDerivAt
  exact hg.scomp 0 (chartT_hasDerivAt P hP y)

theorem rhs_hasDerivAt (P : ChartParams) (hP : IsChartParams P) (F : FieldData) (β om : ℝ) {y : Space}
    (hx0 : heightRatio y ≠ 0)
    (hgen : ∀ n ∈ F.modes, ∀ S ∈ [(F.amp n).radialAmp, (F.amp n).polarAmp, (F.amp n).streamAmp,
      (F.amp n).swirlAmp], chartT P y ∉ S.mesh.tBreaks ∧ |heightRatio y| ∉ S.mesh.xBreaks) (a0 b0 c0 : ℝ) :
    HasDerivAt (fun τ : ℝ => ((decayFactor P (Real.exp τ • y) : ℂ) * ∑ n ∈ F.modes,
        (Complex.exp (Complex.I * (((n : ℝ) * (P.m : ℝ) * (om * τ) : ℝ) : ℂ)) * modePhase P n β (Real.exp τ • y)) *
          (reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 0 * a0 +
            reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 1 * b0 +
              reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 2 * c0)).re)
      (((((-(2 * P.eps * chartT P y * decayFactor P y)) : ℝ) : ℂ) * ∑ n ∈ F.modes, modePhase P n β y *
          (reducedField P F n β (chartT P y) (heightRatio y) 0 * a0 +
            reducedField P F n β (chartT P y) (heightRatio y) 1 * b0 +
              reducedField P F n β (chartT P y) (heightRatio y) 2 * c0) +
        (decayFactor P y : ℂ) * ∑ n ∈ F.modes,
          (Complex.I * (((n : ℝ) * (P.m : ℝ) * om + n * β * coreRatioT P (chartT P y) : ℝ) : ℂ) *
              modePhase P n β y *
            (reducedField P F n β (chartT P y) (heightRatio y) 0 * a0 +
              reducedField P F n β (chartT P y) (heightRatio y) 1 * b0 +
                reducedField P F n β (chartT P y) (heightRatio y) 2 * c0) +
          modePhase P n β y *
            ((chartT P y * (1 - chartT P y)) • deriv (fun t' => reducedField P F n β t' (heightRatio y) 0)
                (chartT P y) * a0 +
              (chartT P y * (1 - chartT P y)) • deriv (fun t' => reducedField P F n β t' (heightRatio y) 1)
                (chartT P y) * b0 +
              (chartT P y * (1 - chartT P y)) • deriv (fun t' => reducedField P F n β t' (heightRatio y) 2)
                (chartT P y) * c0)))).re 0 := by
  have hD := (decay_hasDerivAt P hP y).ofReal_comp
  have hS : ∀ n ∈ F.modes, HasDerivAt (fun τ : ℝ =>
      (Complex.exp (Complex.I * (((n : ℝ) * (P.m : ℝ) * (om * τ) : ℝ) : ℂ)) * modePhase P n β (Real.exp τ • y)) *
          (reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 0 * a0 +
            reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 1 * b0 +
              reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 2 * c0))
      (Complex.I * (((n : ℝ) * (P.m : ℝ) * om + n * β * coreRatioT P (chartT P y) : ℝ) : ℂ) *
              modePhase P n β y *
            (reducedField P F n β (chartT P (Real.exp 0 • y)) (heightRatio y) 0 * a0 +
              reducedField P F n β (chartT P (Real.exp 0 • y)) (heightRatio y) 1 * b0 +
                reducedField P F n β (chartT P (Real.exp 0 • y)) (heightRatio y) 2 * c0) +
          (Complex.exp (Complex.I * (((n : ℝ) * (P.m : ℝ) * (om * 0) : ℝ) : ℂ)) * modePhase P n β (Real.exp 0 • y)) *
            ((chartT P y * (1 - chartT P y)) • deriv (fun t' => reducedField P F n β t' (heightRatio y) 0)
                (chartT P y) * a0 +
              (chartT P y * (1 - chartT P y)) • deriv (fun t' => reducedField P F n β t' (heightRatio y) 1)
                (chartT P y) * b0 +
              (chartT P y * (1 - chartT P y)) • deriv (fun t' => reducedField P F n β t' (heightRatio y) 2)
                (chartT P y) * c0)) 0 := fun n hn =>
    (phase_hasDerivAt P hP n β om y).mul
      ((((reduced_hasDerivAt P hP F n β hx0 (hgen n hn) 0).mul_const (a0 : ℂ)).add
        ((reduced_hasDerivAt P hP F n β hx0 (hgen n hn) 1).mul_const (b0 : ℂ))).add
          ((reduced_hasDerivAt P hP F n β hx0 (hgen n hn) 2).mul_const (c0 : ℂ)))
  have hZ := hD.fun_mul (HasDerivAt.fun_sum hS)
  have hre := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hZ
  refine hre.congr_deriv ?_
  simp only [Real.exp_zero, one_smul, mul_zero, Complex.ofReal_zero, Complex.exp_zero, one_mul,
    Complex.reCLM_apply]

theorem flow_combo (P : ChartParams) (F : FieldData) (α a β om : ℝ) (hα : α = 1 + P.eps)
    (hβ : β = -(2 * α * (P.m : ℝ) * a)) (hom : om = 2 * α * a) (y : Space) (a0 b0 c0 : ℝ) :
    (2 * α - 1) * ((decayFactor P y : ℂ) * ∑ n ∈ F.modes, modePhase P n β y *
          (reducedField P F n β (chartT P y) (heightRatio y) 0 * a0 +
            reducedField P F n β (chartT P y) (heightRatio y) 1 * b0 +
              reducedField P F n β (chartT P y) (heightRatio y) 2 * c0)).re +
      (((((-(2 * P.eps * chartT P y * decayFactor P y)) : ℝ) : ℂ) * ∑ n ∈ F.modes, modePhase P n β y *
          (reducedField P F n β (chartT P y) (heightRatio y) 0 * a0 +
            reducedField P F n β (chartT P y) (heightRatio y) 1 * b0 +
              reducedField P F n β (chartT P y) (heightRatio y) 2 * c0) +
        (decayFactor P y : ℂ) * ∑ n ∈ F.modes,
          (Complex.I * (((n : ℝ) * (P.m : ℝ) * om + n * β * coreRatioT P (chartT P y) : ℝ) : ℂ) *
              modePhase P n β y *
            (reducedField P F n β (chartT P y) (heightRatio y) 0 * a0 +
              reducedField P F n β (chartT P y) (heightRatio y) 1 * b0 +
                reducedField P F n β (chartT P y) (heightRatio y) 2 * c0) +
          modePhase P n β y *
            ((chartT P y * (1 - chartT P y)) • deriv (fun t' => reducedField P F n β t' (heightRatio y) 0)
                (chartT P y) * a0 +
              (chartT P y * (1 - chartT P y)) • deriv (fun t' => reducedField P F n β t' (heightRatio y) 1)
                (chartT P y) * b0 +
              (chartT P y * (1 - chartT P y)) • deriv (fun t' => reducedField P F n β t' (heightRatio y) 2)
                (chartT P y) * c0)))).re =
      ((decayFactor P y : ℂ) * ∑ n ∈ F.modes, modePhase P n β y *
        (flowTerm P F n β om (chartT P y) (heightRatio y) 0 * a0 +
          flowTerm P F n β om (chartT P y) (heightRatio y) 1 * b0 +
            flowTerm P F n β om (chartT P y) (heightRatio y) 2 * c0)).re := by
  rw [← Complex.re_ofReal_mul, ← Complex.add_re]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [flowTerm, Complex.real_smul]
  subst hβ hom
  subst hα
  push_cast
  ring

theorem drift_flow_formula_of (P : ChartParams) (hP : IsChartParams P) (F : FieldData) (α a : ℝ)
    (hα : α = 1 + P.eps) (y : Space) (h0 : y 0 ≠ 0) (h1 : y 1 ≠ 0) (h2 : y 2 ≠ 0)
    (hgen : ∀ n ∈ F.modes, ∀ S ∈ [(F.amp n).radialAmp, (F.amp n).polarAmp, (F.amp n).streamAmp,
      (F.amp n).swirlAmp], chartT P y ∉ S.mesh.tBreaks ∧ |heightRatio y| ∉ S.mesh.xBreaks) :
    (2 * α) • driftField α a (fieldOf P F (-(2 * α * (P.m : ℝ) * a)))
        (fun z => fderiv ℝ (fieldOf P F (-(2 * α * (P.m : ℝ) * a))) z) y =
      ofComponents (fun i => ((decayFactor P y : ℂ) * ∑ n ∈ F.modes,
        modePhase P n (-(2 * α * (P.m : ℝ) * a)) y *
          (flowTerm P F n (-(2 * α * (P.m : ℝ) * a)) (2 * α * a) (chartT P y) (heightRatio y) 0 * radialVec y i +
            flowTerm P F n (-(2 * α * (P.m : ℝ) * a)) (2 * α * a) (chartT P y) (heightRatio y) 1 * polarVecQ y i +
              flowTerm P F n (-(2 * α * (P.m : ℝ) * a)) (2 * α * a) (chartT P y) (heightRatio y) 2 *
                azimVecQ y i)).re) := by
  set β : ℝ := -(2 * α * (P.m : ℝ) * a) with hβ
  set om : ℝ := 2 * α * a with hom
  have hy0 : y ≠ 0 := fun h => h0 (by simp [h])
  have hx0 : heightRatio y ≠ 0 := div_ne_zero h2 (norm_ne_zero_iff.2 hy0)
  have hvd : HasFDerivAt (fieldOf P F β) (fderiv ℝ (fieldOf P F β) y) y := by
    have hc := ContDiffAt.comp (f := fun z : Space => (β, z)) y (joint_fieldOf P hP F hy0 h1 hx0 hgen β)
      (contDiffAt_const.prodMk contDiffAt_id)
    exact (hc.differentiableAt (by simp)).hasFDerivAt
  set G := fderiv ℝ (fieldOf P F β) y with hG
  set vfix := fieldOf P F β y with hv0
  have hV : HasDerivAt (fun τ : ℝ => fieldOf P F β (Real.exp τ • planeTurn (om * τ) y))
      (G (y + om • axialTurn y)) 0 :=
    hvd.comp_hasDerivAt_of_eq 0 (curve_hasDerivAt om y) (curve_zero om y).symm
  have hVj : ∀ j : Fin 3, HasDerivAt (fun τ : ℝ => fieldOf P F β (Real.exp τ • planeTurn (om * τ) y) j)
      ((G (y + om • axialTurn y)) j) 0 := fun j =>
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hV
  have hVpos : fieldOf P F β (Real.exp 0 • planeTurn (om * 0) y) = vfix := by rw [curve_zero]
  have hfi : ∀ i : Fin 3, (fun τ : ℝ => (planeTurn (-(om * τ)) (fieldOf P F β (Real.exp τ • planeTurn (om * τ) y))) i) =
      fun τ : ℝ => ((decayFactor P (Real.exp τ • y) : ℂ) * ∑ n ∈ F.modes,
        (Complex.exp (Complex.I * (((n : ℝ) * (P.m : ℝ) * (om * τ) : ℝ) : ℂ)) * modePhase P n β (Real.exp τ • y)) *
          (reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 0 * radialVec y i +
            reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 1 * polarVecQ y i +
              reducedField P F n β (chartT P (Real.exp τ • y)) (heightRatio y) 2 * azimVecQ y i)).re := by
    intro i
    funext τ
    rw [flow_identity P F β τ (om * τ) y h0, FracInternal.ofComponents_apply]
  have hfi0 : ∀ i : Fin 3, vfix i = ((decayFactor P y : ℂ) * ∑ n ∈ F.modes, modePhase P n β y *
          (reducedField P F n β (chartT P y) (heightRatio y) 0 * radialVec y i +
            reducedField P F n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
              reducedField P F n β (chartT P y) (heightRatio y) 2 * azimVecQ y i)).re := by
    intro i
    have := congrFun (hfi i) 0
    simp only [mul_zero, neg_zero, Real.exp_zero, one_smul, Complex.ofReal_zero, Complex.exp_zero,
      one_mul] at this
    rw [← this, planeTurn_zero, planeTurn_zero]
  have hc : HasDerivAt (fun τ : ℝ => Real.cos (-(om * τ))) 0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul om).neg.cos
  have hs : HasDerivAt (fun τ : ℝ => Real.sin (-(om * τ))) (-om) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul om).neg.sin
  have hL0 : HasDerivAt (fun τ : ℝ => (planeTurn (-(om * τ)) (fieldOf P F β (Real.exp τ • planeTurn (om * τ) y))) 0)
      ((G (y + om • axialTurn y)) 0 + om * vfix 1) 0 := by
    have e : (fun τ : ℝ => (planeTurn (-(om * τ)) (fieldOf P F β (Real.exp τ • planeTurn (om * τ) y))) 0) =
        fun τ : ℝ => Real.cos (-(om * τ)) * (fieldOf P F β (Real.exp τ • planeTurn (om * τ) y)) 0 -
          Real.sin (-(om * τ)) * (fieldOf P F β (Real.exp τ • planeTurn (om * τ) y)) 1 :=
      funext fun τ => (planeTurn_coords _ _).1
    rw [e]
    refine ((hc.fun_mul (hVj 0)).fun_sub (hs.fun_mul (hVj 1))).congr_deriv ?_
    simp only [mul_zero, neg_zero, Real.cos_zero, Real.sin_zero, Real.exp_zero, one_smul, planeTurn_zero, ← hv0,
      zero_mul, one_mul, zero_add]
    ring
  have hL1 : HasDerivAt (fun τ : ℝ => (planeTurn (-(om * τ)) (fieldOf P F β (Real.exp τ • planeTurn (om * τ) y))) 1)
      ((G (y + om • axialTurn y)) 1 - om * vfix 0) 0 := by
    have e : (fun τ : ℝ => (planeTurn (-(om * τ)) (fieldOf P F β (Real.exp τ • planeTurn (om * τ) y))) 1) =
        fun τ : ℝ => Real.sin (-(om * τ)) * (fieldOf P F β (Real.exp τ • planeTurn (om * τ) y)) 0 +
          Real.cos (-(om * τ)) * (fieldOf P F β (Real.exp τ • planeTurn (om * τ) y)) 1 :=
      funext fun τ => (planeTurn_coords _ _).2.1
    rw [e]
    refine ((hs.fun_mul (hVj 0)).fun_add (hc.fun_mul (hVj 1))).congr_deriv ?_
    simp only [mul_zero, neg_zero, Real.cos_zero, Real.sin_zero, Real.exp_zero, one_smul, planeTurn_zero, ← hv0,
      zero_mul, one_mul, zero_add]
    ring
  have hL2 : HasDerivAt (fun τ : ℝ => (planeTurn (-(om * τ)) (fieldOf P F β (Real.exp τ • planeTurn (om * τ) y))) 2)
      ((G (y + om • axialTurn y)) 2) 0 := by
    have e : (fun τ : ℝ => (planeTurn (-(om * τ)) (fieldOf P F β (Real.exp τ • planeTurn (om * τ) y))) 2) =
        fun τ : ℝ => (fieldOf P F β (Real.exp τ • planeTurn (om * τ) y)) 2 :=
      funext fun τ => (planeTurn_coords _ _).2.2
    rw [e]
    exact hVj 2
  have hR : ∀ i : Fin 3, _ := fun i => rhs_hasDerivAt P hP F β om hx0 hgen (radialVec y i) (polarVecQ y i) (azimVecQ y i)
  have u0 := hL0.unique (by rw [hfi 0]; exact hR 0)
  have u1 := hL1.unique (by rw [hfi 1]; exact hR 1)
  have u2 := hL2.unique (by rw [hfi 2]; exact hR 2)
  have hαne : α ≠ 0 := by rw [hα]; linarith [hP.eps_pos]
  have hdr : (2 * α) • driftField α a (fieldOf P F β) (fun z => fderiv ℝ (fieldOf P F β) z) y =
      (2 * α - 1) • vfix + G (y + om • axialTurn y) - om • axialTurn vfix := by
    unfold driftField
    rw [map_add, map_smul]
    match_scalars <;> field_simp <;> ring
  have c0 := flow_combo P F α a β om hα hβ hom y (radialVec y 0) (polarVecQ y 0) (azimVecQ y 0)
  have c1 := flow_combo P F α a β om hα hβ hom y (radialVec y 1) (polarVecQ y 1) (azimVecQ y 1)
  have c2 := flow_combo P F α a β om hα hβ hom y (radialVec y 2) (polarVecQ y 2) (azimVecQ y 2)
  have hJ0 : (axialTurn vfix) 0 = -(vfix 1) := by simp [axialTurn]
  have hJ1 : (axialTurn vfix) 1 = vfix 0 := by simp [axialTurn]
  have hJ2 : (axialTurn vfix) 2 = 0 := by simp [axialTurn]
  rw [hdr]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      FracInternal.ofComponents_apply]
    rw [← c0, ← u0, ← hfi0 0, hJ0]
    ring
  · simp only [Fin.mk_one, Fin.isValue, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      FracInternal.ofComponents_apply]
    rw [← c1, ← u1, ← hfi0 1, hJ1]
    ring
  · simp only [Fin.reduceFinMk, Fin.isValue, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      FracInternal.ofComponents_apply]
    rw [← c2, ← u2, ← hfi0 2, hJ2]
    ring


theorem drift_flow_formula (P : ChartParams) (hP : IsChartParams P) (F : FieldData) (α a : ℝ)
    (hα : α = 1 + P.eps) (y : Space) (h0 : y 0 ≠ 0) (h1 : y 1 ≠ 0) (h2 : y 2 ≠ 0)
    (hgen : ∀ n ∈ F.modes, ∀ S ∈ [(F.amp n).radialAmp, (F.amp n).polarAmp, (F.amp n).streamAmp,
      (F.amp n).swirlAmp], chartT P y ∉ S.mesh.tBreaks ∧ |heightRatio y| ∉ S.mesh.xBreaks) :
    (2 * α) • driftField α a (fieldOf P F (-(2 * α * (P.m : ℝ) * a)))
        (fun z => fderiv ℝ (fieldOf P F (-(2 * α * (P.m : ℝ) * a))) z) y =
      ofComponents (fun i => ((decayFactor P y : ℂ) * ∑ n ∈ F.modes,
        modePhase P n (-(2 * α * (P.m : ℝ) * a)) y *
          (flowTerm P F n (-(2 * α * (P.m : ℝ) * a)) (2 * α * a) (chartT P y) (heightRatio y) 0 * radialVec y i +
            flowTerm P F n (-(2 * α * (P.m : ℝ) * a)) (2 * α * a) (chartT P y) (heightRatio y) 1 * polarVecQ y i +
              flowTerm P F n (-(2 * α * (P.m : ℝ) * a)) (2 * α * a) (chartT P y) (heightRatio y) 2 *
                azimVecQ y i)).re) := by
  exact drift_flow_formula_of P hP F α a hα y h0 h1 h2 hgen

private theorem partial_t {G : ℝ → ℝ → ℝ → ℂ} (hG : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => G q.1 q.2.1 q.2.2)) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => deriv (fun t' => G q.1 t' q.2.2) q.2.1) ∧
      ∀ β t x, HasDerivAt (fun t' => G β t' x) (deriv (fun t' => G β t' x) t) t := by
  set g := fun q : ℝ × ℝ × ℝ => G q.1 q.2.1 q.2.2 with hg
  have hc : ∀ β t x : ℝ, HasDerivAt (fun t' : ℝ => ((β, t', x) : ℝ × ℝ × ℝ)) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) t :=
    fun β t x => (hasDerivAt_const t β).prodMk ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hd : ∀ q, HasFDerivAt g (fderiv ℝ g q) q := fun q =>
    ((hG.differentiable (by simp)) q).hasFDerivAt
  have key : ∀ β t x, HasDerivAt (fun t' => G β t' x) (fderiv ℝ g (β, t, x) ((0 : ℝ), (1 : ℝ), (0 : ℝ))) t :=
    fun β t x => by
      have h := (hd (β, t, x)).comp_hasDerivAt t (hc β t x)
      exact h
  refine ⟨?_, fun β t x => (key β t x).differentiableAt.hasDerivAt⟩
  have h1 : ContDiff ℝ ∞ (fun q => fderiv ℝ g q ((0 : ℝ), (1 : ℝ), (0 : ℝ))) :=
    (hG.fderiv_right le_rfl).clm_apply contDiff_const
  convert h1 using 1
  funext q
  exact (key q.1 q.2.1 q.2.2).deriv

private theorem weight_of_vanish {G : ℝ → ℝ → ℝ → ℂ}
    (hG : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => G q.1 q.2.1 q.2.2)) (h1 : ∀ β x, G β 1 x = 0) (B : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ β : ℝ, |β| ≤ B → ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 →
      ‖G β t x‖ ≤ K * (1 - t) ∧
        ‖G β t x + ((1 - t : ℝ) : ℂ) * deriv (fun t' => G β t' x) t‖ ≤ K * (1 - t) ^ 2 := by
  obtain ⟨hD1, hd1⟩ := partial_t hG
  set G1 : ℝ → ℝ → ℝ → ℂ := fun β t x => deriv (fun t' => G β t' x) t with hG1
  obtain ⟨hD2, hd2⟩ := partial_t (G := G1) hD1
  set S : Set (ℝ × ℝ × ℝ) := Set.Icc (-B) B ×ˢ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 with hS
  have hSc : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C1, hC1⟩ := hSc.exists_bound_of_continuousOn hD1.continuous.continuousOn
  obtain ⟨C2, hC2⟩ := hSc.exists_bound_of_continuousOn hD2.continuous.continuousOn
  refine ⟨|C1| + |C2|, by positivity, fun β hβ t x ht0 ht1 hx => ?_⟩
  have hmem : ∀ s ∈ Set.Icc t 1, ((β, s, x) : ℝ × ℝ × ℝ) ∈ S := fun s hs =>
    ⟨abs_le.1 hβ, ⟨ht0.trans hs.1, hs.2⟩, abs_le.1 hx⟩
  have hone : (1 : ℝ) ∈ Set.Icc t 1 := ⟨ht1, le_rfl⟩
  have hst : 0 ≤ 1 - t := by linarith
  constructor
  · have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => G β s x) (f' := fun s => G1 β s x)
      (C := C1) (fun s _ => (hd1 β s x).hasDerivWithinAt)
      (fun s hs => hC1 _ (hmem s (Set.Ico_subset_Icc_self hs))) 1 hone
    simp only [h1, zero_sub, norm_neg] at this
    calc ‖G β t x‖ ≤ C1 * (1 - t) := this
      _ ≤ (|C1| + |C2|) * (1 - t) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C1, abs_nonneg C2]) hst
  · set φ : ℝ → ℂ := fun s => G β s x + ((1 - s : ℝ) : ℂ) * G1 β s x with hφdef
    have hφ : ∀ s, HasDerivAt φ (((1 - s : ℝ) : ℂ) * deriv (fun t' => G1 β t' x) s) s := by
      intro s
      have ha : HasDerivAt (fun s : ℝ => ((1 - s : ℝ) : ℂ)) (((-1 : ℝ)) : ℂ) s := by
        simpa using ((hasDerivAt_id s).const_sub 1).ofReal_comp
      refine ((hd1 β s x).add (ha.mul (hd2 β s x))).congr_deriv ?_
      push_cast
      ring
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ)
      (f' := fun s => ((1 - s : ℝ) : ℂ) * deriv (fun t' => G1 β t' x) s)
      (C := |C2| * (1 - t)) (fun s _ => (hφ s).hasDerivWithinAt) (fun s hs => ?_) 1 hone
    · have hφ1 : φ 1 = 0 := by simp [φ, h1]
      rw [hφ1, zero_sub, norm_neg] at this
      calc _ = ‖φ t‖ := rfl
        _ ≤ |C2| * (1 - t) * (1 - t) := this
        _ ≤ (|C1| + |C2|) * (1 - t) ^ 2 := by
          have : |C2| ≤ |C1| + |C2| := by linarith [abs_nonneg C1]
          nlinarith [mul_nonneg hst hst]
    · have hb := hC2 _ (hmem s (Set.Ico_subset_Icc_self hs))
      simp only at hb
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
      calc (1 - s) * ‖deriv (fun t' => G1 β t' x) s‖ ≤ (1 - t) * |C2| :=
            mul_le_mul (by linarith [hs.1]) (hb.trans (le_abs_self _)) (norm_nonneg _) hst
        _ = |C2| * (1 - t) := by ring


private def genField (P : ChartParams) (D : FieldData) (n : ℤ) (β : ℝ) (fr fp fs fw : ℝ → ℝ → ℂ) (t x : ℝ) :
    Fin 3 → ℂ :=
  if n = 0 then
    let p := fun t' : ℝ => weightPoly 1 D.highOrder t'
    ![-(p t * heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * fs t' x') t x),
      -(twistedScale P 0 β (fun t' x' => p t' * fs t' x') t x + 2 * (p t * fs t x)),
      p t * fw t x]
  else
    let p := fun t' : ℝ => weightPoly (D.lowOrder n) D.highOrder t'
    let ur := fun t' x' => p t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * fr t' x'
    let uθ := fun t' x' => p t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * fp t' x'
    ![ur t x, uθ t x,
      (Complex.I / ((n * P.m : ℤ) : ℂ)) *
        (twistedScale P n β ur t x + 2 * ur t x - heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * uθ t' x') t x)]

private theorem reduced_eq_gen (P : ChartParams) (D : FieldData) (n : ℤ) (β t x : ℝ) :
    reducedField P D n β t x = genField P D n β ((D.amp n).radialAmp.eval false) ((D.amp n).polarAmp.eval true)
      ((D.amp n).streamAmp.eval true) ((D.amp n).swirlAmp.eval false) t x := by
  unfold reducedField genField
  split_ifs with h
  · subst h
    rfl
  · rfl

private theorem gen_vanish (P : ChartParams) (D : FieldData) (hD : D.highOrder = 1) (n : ℤ) (β : ℝ)
    (fr fp fs fw : ℝ → ℝ → ℂ) (x : ℝ) (k : Fin 3) : genField P D n β fr fp fs fw 1 x k = 0 := by
  unfold genField
  split_ifs with h
  · fin_cases k <;> simp [heightDeriv, twistedScale, radialScale, weightPoly, hD]
  · fin_cases k <;> simp [heightDeriv, twistedScale, radialScale, weightPoly, hD]

private theorem slice_t {f g : ℝ → ℝ → ℂ} {z : ℝ × ℝ}
    (h : (fun q : ℝ × ℝ => f q.1 q.2) =ᶠ[nhds z] (fun q => g q.1 q.2)) :
    (fun t' => f t' z.2) =ᶠ[nhds z.1] (fun t' => g t' z.2) := by
  have hc : Filter.Tendsto (fun t' : ℝ => ((t', z.2) : ℝ × ℝ)) (nhds z.1) (nhds z) := by
    have := ((continuous_id.prodMk continuous_const : Continuous fun t' : ℝ => ((t', z.2) : ℝ × ℝ))).tendsto z.1
    simpa using this
  exact hc.eventually h

private theorem slice_x {f g : ℝ → ℝ → ℂ} {z : ℝ × ℝ}
    (h : (fun q : ℝ × ℝ => f q.1 q.2) =ᶠ[nhds z] (fun q => g q.1 q.2)) :
    (fun x' => f z.1 x') =ᶠ[nhds z.2] (fun x' => g z.1 x') := by
  have hc : Filter.Tendsto (fun x' : ℝ => ((z.1, x') : ℝ × ℝ)) (nhds z.2) (nhds z) := by
    have := ((continuous_const.prodMk continuous_id : Continuous fun x' : ℝ => ((z.1, x') : ℝ × ℝ))).tendsto z.2
    simpa using this
  exact hc.eventually h

private theorem germ_mul {f g : ℝ → ℝ → ℂ} (a : ℝ → ℝ → ℂ) {z : ℝ × ℝ}
    (h : (fun q : ℝ × ℝ => f q.1 q.2) =ᶠ[nhds z] (fun q => g q.1 q.2)) :
    (fun q : ℝ × ℝ => a q.1 q.2 * f q.1 q.2) =ᶠ[nhds z] (fun q => a q.1 q.2 * g q.1 q.2) := by
  filter_upwards [h] with q hq
  rw [hq]

private theorem slice_x_mul {f g : ℝ → ℝ → ℂ} (a : ℝ → ℝ → ℂ) {z : ℝ × ℝ}
    (h : (fun q : ℝ × ℝ => f q.1 q.2) =ᶠ[nhds z] (fun q => g q.1 q.2)) :
    (fun x' => a z.1 x' * f z.1 x') =ᶠ[nhds z.2] (fun x' => a z.1 x' * g z.1 x') :=
  slice_x (f := fun t x => a t x * f t x) (g := fun t x => a t x * g t x) (germ_mul a h)

private theorem slice_t_mul {f g : ℝ → ℝ → ℂ} (a : ℝ → ℝ → ℂ) {z : ℝ × ℝ}
    (h : (fun q : ℝ × ℝ => f q.1 q.2) =ᶠ[nhds z] (fun q => g q.1 q.2)) :
    (fun t' => a t' z.2 * f t' z.2) =ᶠ[nhds z.1] (fun t' => a t' z.2 * g t' z.2) :=
  slice_t (f := fun t x => a t x * f t x) (g := fun t x => a t x * g t x) (germ_mul a h)

private theorem gen_eq_of_germ (P : ChartParams) (D : FieldData) (n : ℤ) (β : ℝ)
    {fr fp fs fw gr gp gs gw : ℝ → ℝ → ℂ} {z : ℝ × ℝ}
    (hr : (fun q : ℝ × ℝ => fr q.1 q.2) =ᶠ[nhds z] (fun q => gr q.1 q.2))
    (hp : (fun q : ℝ × ℝ => fp q.1 q.2) =ᶠ[nhds z] (fun q => gp q.1 q.2))
    (hs : (fun q : ℝ × ℝ => fs q.1 q.2) =ᶠ[nhds z] (fun q => gs q.1 q.2))
    (hw : (fun q : ℝ × ℝ => fw q.1 q.2) =ᶠ[nhds z] (fun q => gw q.1 q.2)) (k : Fin 3) :
    genField P D n β fr fp fs fw z.1 z.2 k = genField P D n β gr gp gs gw z.1 z.2 k := by
  have er : fr z.1 z.2 = gr z.1 z.2 := hr.eq_of_nhds
  have ep : fp z.1 z.2 = gp z.1 z.2 := hp.eq_of_nhds
  have es : fs z.1 z.2 = gs z.1 z.2 := hs.eq_of_nhds
  have ew : fw z.1 z.2 = gw z.1 z.2 := hw.eq_of_nhds
  unfold genField
  split_ifs with h
  · have d1 := (slice_x_mul (fun _ x' => ((1 - x' ^ 2 : ℝ) : ℂ)) hs).deriv_eq
    have d2 := (slice_t_mul (fun t' _ => weightPoly 1 D.highOrder t') hs).deriv_eq
    fin_cases k <;> simp only [heightDeriv, twistedScale, radialScale, es, ew, d1, d2, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
  · have d1 := (slice_x_mul (f := fun t x => weightPoly (D.lowOrder n) D.highOrder t * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * fp t x)
      (g := fun t x => weightPoly (D.lowOrder n) D.highOrder t * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * gp t x)
      (fun _ x' => ((1 - x' ^ 2 : ℝ) : ℂ))
      (germ_mul (fun t' x' => weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n)
        hp)).deriv_eq
    have d2 := (slice_t_mul
      (fun t' x' => weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n) hr).deriv_eq
    fin_cases k <;> simp only [heightDeriv, twistedScale, radialScale, er, ep, d1, d2, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]

private theorem gen_germ (P : ChartParams) (D : FieldData) (n : ℤ) (β : ℝ)
    {fr fp fs fw gr gp gs gw : ℝ → ℝ → ℂ} {z : ℝ × ℝ}
    (hr : (fun q : ℝ × ℝ => fr q.1 q.2) =ᶠ[nhds z] (fun q => gr q.1 q.2))
    (hp : (fun q : ℝ × ℝ => fp q.1 q.2) =ᶠ[nhds z] (fun q => gp q.1 q.2))
    (hs : (fun q : ℝ × ℝ => fs q.1 q.2) =ᶠ[nhds z] (fun q => gs q.1 q.2))
    (hw : (fun q : ℝ × ℝ => fw q.1 q.2) =ᶠ[nhds z] (fun q => gw q.1 q.2)) (k : Fin 3) :
    (fun q : ℝ × ℝ => genField P D n β fr fp fs fw q.1 q.2 k) =ᶠ[nhds z]
      (fun q => genField P D n β gr gp gs gw q.1 q.2 k) := by
  filter_upwards [hr.eventuallyEq_nhds, hp.eventuallyEq_nhds, hs.eventuallyEq_nhds, hw.eventuallyEq_nhds]
    with q h1 h2 h3 h4
  exact gen_eq_of_germ P D n β h1 h2 h3 h4 k

private theorem gen_contDiffAt (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (n : ℤ) {t x : ℝ}
    {fr fp fs fw : ℝ → ℝ → ℂ} (hr : SmoothNear fr (t, x)) (hpo : SmoothNear fp (t, x))
    (hs : SmoothNear fs (t, x)) (hw : SmoothNear fw (t, x)) (β0 : ℝ) (k : Fin 3) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => genField P D n q.1 fr fp fs fw q.2.1 q.2.2 k) (β0, t, x) := by
  have hq : SmoothNear (fun _ x' => ((1 - x' ^ 2 : ℝ) : ℂ)) (t, x) :=
    smoothNear_real (g := fun _ x' => 1 - x' ^ 2) (by fun_prop)
  by_cases hn : n = 0
  · let p : ℝ → ℂ := fun t' => weightPoly 1 D.highOrder t'
    have hp : SmoothNear (fun t' _ => p t') (t, x) := by
      unfold p weightPoly
      exact smoothNear_real (g := fun t' _ => t' ^ 1 * (1 - t') ^ D.highOrder) (by fun_prop)
    have hpΨ : SmoothNear (fun t' x' => p t' * fs t' x') (t, x) := smoothNear_mul hp hs
    have hqΨ : SmoothNear (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * fs t' x') (t, x) := smoothNear_mul hq hs
    fin_cases k
    · have key : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => -(p q.2.1 * heightDeriv
          (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * fs t' x') q.2.1 q.2.2)) (β0, t, x) :=
        ((smoothNear_contDiffAt hp β0).mul (smoothNear_contDiffAt (smoothNear_derivX hqΨ) β0)).neg
      exact key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by simp only [genField, if_pos hn]; rfl)
    · have key : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => -(twistedScale P 0 q.1
          (fun t' x' => p t' * fs t' x') q.2.1 q.2.2 + 2 * (p q.2.1 * fs q.2.1 q.2.2))) (β0, t, x) :=
        ((twisted_contDiffAt P hP 0 hpΨ β0).add (contDiffAt_const.mul (smoothNear_contDiffAt hpΨ β0))).neg
      exact key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by simp only [genField, if_pos hn]; rfl)
    · have key : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => p q.2.1 * fw q.2.1 q.2.2) (β0, t, x) :=
        smoothNear_contDiffAt (smoothNear_mul hp hw) β0
      exact key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by simp only [genField, if_pos hn]; rfl)
  · let p : ℝ → ℂ := fun t' => weightPoly (D.lowOrder n) D.highOrder t'
    have hp : SmoothNear (fun t' _ => p t') (t, x) := by
      unfold p weightPoly
      exact smoothNear_real (g := fun t' _ => t' ^ D.lowOrder n * (1 - t') ^ D.highOrder) (by fun_prop)
    let ur : ℝ → ℝ → ℂ := fun t' x' => p t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * fr t' x'
    let uθ : ℝ → ℝ → ℂ := fun t' x' => p t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * fp t' x'
    have hur : SmoothNear ur (t, x) := smoothNear_mul (smoothNear_mul hp (smoothNear_pow hq _)) hr
    have huθ : SmoothNear uθ (t, x) := smoothNear_mul (smoothNear_mul hp (smoothNear_pow hq _)) hpo
    fin_cases k
    · exact (smoothNear_contDiffAt hur β0).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun q => by simp only [genField, if_neg hn]; rfl)
    · exact (smoothNear_contDiffAt huθ β0).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun q => by simp only [genField, if_neg hn]; rfl)
    · have key : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => (Complex.I / ((n * P.m : ℤ) : ℂ)) *
          (twistedScale P n q.1 ur q.2.1 q.2.2 + 2 * ur q.2.1 q.2.2 -
            heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * uθ t' x') q.2.1 q.2.2)) (β0, t, x) :=
        contDiffAt_const.mul (((twisted_contDiffAt P hP n hur β0).add
          (contDiffAt_const.mul (smoothNear_contDiffAt hur β0))).sub
            (smoothNear_contDiffAt (smoothNear_derivX (smoothNear_mul hq huθ)) β0))
      exact key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by simp only [genField, if_neg hn]; rfl)

private def polyAmp (odd c : Bool) (Q : MvPolynomial (Fin 2) ℂ) (t x : ℝ) : ℂ :=
  (if odd && c then -1 else 1) * MvPolynomial.eval ![(t : ℂ), (((if c then -1 else 1) * x : ℝ) : ℂ)] Q

private theorem polyAmp_contDiff (odd c : Bool) (Q : MvPolynomial (Fin 2) ℂ) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => polyAmp odd c Q q.1 q.2) :=
  contDiff_const.mul (FracInternal.mvPoly_eval_contDiff Q contDiff_fst (contDiff_const.mul contDiff_snd))

private theorem gen_poly_contDiff (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (n : ℤ) (c : Bool)
    (Qr Qp Qs Qw : MvPolynomial (Fin 2) ℂ) (k : Fin 3) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => genField P D n q.1 (polyAmp false c Qr) (polyAmp true c Qp)
      (polyAmp true c Qs) (polyAmp false c Qw) q.2.1 q.2.2 k) :=
  contDiff_iff_contDiffAt.2 fun q => gen_contDiffAt P hP D n (t := q.2.1) (x := q.2.2)
    (smoothNear_smooth (polyAmp_contDiff _ _ _)) (smoothNear_smooth (polyAmp_contDiff _ _ _))
    (smoothNear_smooth (polyAmp_contDiff _ _ _)) (smoothNear_smooth (polyAmp_contDiff _ _ _)) q.1 k

private theorem spline_germ (S : Spline) (odd : Bool) {t x : ℝ} (ht : t ∉ S.mesh.tBreaks)
    (hx : |x| ∉ S.mesh.xBreaks) (hx0 : x ≠ 0) :
    (fun z : ℝ × ℝ => S.eval odd z.1 z.2) =ᶠ[nhds (t, x)] (fun z => polyAmp odd (decide (x < 0))
      (S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks |x|)) z.1 z.2) := by
  have h1 : ∀ᶠ z in nhds (t, x), cellIndex S.mesh.tBreaks z.1 = cellIndex S.mesh.tBreaks t :=
    (continuous_fst.tendsto (t, x)).eventually (FracInternal.cellIndex_eventually _ _ ht)
  have h2 : ∀ᶠ z in nhds (t, x), cellIndex S.mesh.xBreaks |z.2| = cellIndex S.mesh.xBreaks |x| :=
    ((continuous_abs.comp continuous_snd).tendsto (t, x)).eventually (FracInternal.cellIndex_eventually _ _ hx)
  have h3 : ∀ᶠ z in nhds (t, x), (z.2 < 0 ↔ x < 0) ∧ |z.2| = (if x < 0 then -1 else 1) * z.2 := by
    rcases lt_or_gt_of_ne hx0 with h | h
    · filter_upwards [(continuous_snd.tendsto (t, x)).eventually (eventually_lt_nhds h)] with z hz
      refine ⟨⟨fun _ => h, fun _ => hz⟩, ?_⟩
      rw [if_pos h, abs_of_neg hz]
      ring
    · filter_upwards [(continuous_snd.tendsto (t, x)).eventually (eventually_gt_nhds h)] with z hz
      refine ⟨⟨fun h' => absurd h' (not_lt.2 hz.le), fun h' => absurd h' (not_lt.2 h.le)⟩, ?_⟩
      rw [if_neg (not_lt.2 h.le), abs_of_pos hz]
      ring
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  unfold Spline.eval Spline.evalHalf polyAmp
  rw [hz1, hz2, hz3.2]
  simp only [hz3.1, decide_eq_true_eq]

private theorem cellIndex_le (l : List ℝ) (u : ℝ) : cellIndex l u ≤ l.length := by
  unfold cellIndex
  calc _ ≤ ((l.drop 1).dropLast).length := List.length_filter_le _ _
    _ ≤ l.length := by simp only [List.length_dropLast, List.length_drop]; omega


theorem reduced_weight_bounds (P : ChartParams) (hP : IsChartParams P) (F : FieldData) (hF : IsFieldData P 1 F)
    (B : ℝ) :
    ∃ K : ℝ, ∀ β : ℝ, |β| ≤ B → ∀ n ∈ F.modes, ∀ k : Fin 3, ∀ t x : ℝ, 0 ≤ t → t < 1 →
      |x| ≤ 1 → x ≠ 0 →
      (∀ S ∈ [(F.amp n).radialAmp, (F.amp n).polarAmp, (F.amp n).streamAmp, (F.amp n).swirlAmp],
        t ∉ S.mesh.tBreaks ∧ |x| ∉ S.mesh.xBreaks) →
      ‖reducedField P F n β t x k‖ ≤ K * (1 - t) ∧
        ‖reducedField P F n β t x k + ((1 - t : ℝ) : ℂ) * deriv (fun t' => reducedField P F n β t' x k) t‖ ≤
          K * (1 - t) ^ 2 := by
  classical
  have hpiece : ∀ (n : ℤ) (Qr Qp Qs Qw : MvPolynomial (Fin 2) ℂ) (c : Bool) (k : Fin 3), ∃ K : ℝ, 0 ≤ K ∧
      ∀ β : ℝ, |β| ≤ B → ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 →
        ‖genField P F n β (polyAmp false c Qr) (polyAmp true c Qp) (polyAmp true c Qs) (polyAmp false c Qw) t x k‖
          ≤ K * (1 - t) ∧
        ‖genField P F n β (polyAmp false c Qr) (polyAmp true c Qp) (polyAmp true c Qs) (polyAmp false c Qw) t x k +
          ((1 - t : ℝ) : ℂ) * deriv (fun t' => genField P F n β (polyAmp false c Qr) (polyAmp true c Qp)
            (polyAmp true c Qs) (polyAmp false c Qw) t' x k) t‖ ≤ K * (1 - t) ^ 2 :=
    fun n Qr Qp Qs Qw c k => weight_of_vanish (G := fun β t x => genField P F n β (polyAmp false c Qr)
      (polyAmp true c Qp) (polyAmp true c Qs) (polyAmp false c Qw) t x k)
      (gen_poly_contDiff P hP F n c Qr Qp Qs Qw k) (fun β x => gen_vanish P F hF.highOrder_eq n β _ _ _ _ x k) B
  choose Kf hKf0 hKf using hpiece
  let pieces : Spline → Finset (MvPolynomial (Fin 2) ℂ) := fun S =>
    ((Finset.range (S.mesh.tBreaks.length + 1)) ×ˢ (Finset.range (S.mesh.xBreaks.length + 1))).image
      (fun ij => S.piece ij.1 ij.2)
  have hmemP : ∀ S : Spline, ∀ t x : ℝ,
      S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks x) ∈ pieces S := fun S t x =>
    Finset.mem_image.2 ⟨(cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks x), Finset.mem_product.2
      ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (cellIndex_le _ _)),
        Finset.mem_range.2 (Nat.lt_succ_of_le (cellIndex_le _ _))⟩, rfl⟩
  let T : Finset (ℤ × MvPolynomial (Fin 2) ℂ × MvPolynomial (Fin 2) ℂ × MvPolynomial (Fin 2) ℂ ×
      MvPolynomial (Fin 2) ℂ × Bool × Fin 3) :=
    F.modes.biUnion fun n => (pieces (F.amp n).radialAmp ×ˢ pieces (F.amp n).polarAmp ×ˢ
      pieces (F.amp n).streamAmp ×ˢ pieces (F.amp n).swirlAmp ×ˢ (Finset.univ : Finset (Bool × Fin 3))).image
        fun q => (n, q)
  let Kt : (ℤ × MvPolynomial (Fin 2) ℂ × MvPolynomial (Fin 2) ℂ × MvPolynomial (Fin 2) ℂ ×
      MvPolynomial (Fin 2) ℂ × Bool × Fin 3) → ℝ :=
    fun τ => Kf τ.1 τ.2.1 τ.2.2.1 τ.2.2.2.1 τ.2.2.2.2.1 τ.2.2.2.2.2.1 τ.2.2.2.2.2.2
  refine ⟨∑ τ ∈ T, Kt τ, fun β hβ n hn k t x ht0 ht1 hx1 hx0 hgen => ?_⟩
  have hr := hgen (F.amp n).radialAmp (by simp)
  have hpo := hgen (F.amp n).polarAmp (by simp)
  have hs := hgen (F.amp n).streamAmp (by simp)
  have hw := hgen (F.amp n).swirlAmp (by simp)
  have hloc : (fun q : ℝ × ℝ => reducedField P F n β q.1 q.2 k) =ᶠ[nhds (t, x)]
      (fun q => genField P F n β (polyAmp false (decide (x < 0)) ((F.amp n).radialAmp.piece
          (cellIndex (F.amp n).radialAmp.mesh.tBreaks t) (cellIndex (F.amp n).radialAmp.mesh.xBreaks |x|)))
        (polyAmp true (decide (x < 0)) ((F.amp n).polarAmp.piece
          (cellIndex (F.amp n).polarAmp.mesh.tBreaks t) (cellIndex (F.amp n).polarAmp.mesh.xBreaks |x|)))
        (polyAmp true (decide (x < 0)) ((F.amp n).streamAmp.piece
          (cellIndex (F.amp n).streamAmp.mesh.tBreaks t) (cellIndex (F.amp n).streamAmp.mesh.xBreaks |x|)))
        (polyAmp false (decide (x < 0)) ((F.amp n).swirlAmp.piece
          (cellIndex (F.amp n).swirlAmp.mesh.tBreaks t) (cellIndex (F.amp n).swirlAmp.mesh.xBreaks |x|)))
        q.1 q.2 k) := by
    have e : (fun q : ℝ × ℝ => reducedField P F n β q.1 q.2 k) = fun q => genField P F n β
        ((F.amp n).radialAmp.eval false) ((F.amp n).polarAmp.eval true) ((F.amp n).streamAmp.eval true)
        ((F.amp n).swirlAmp.eval false) q.1 q.2 k := funext fun q => by rw [reduced_eq_gen]
    rw [e]
    exact gen_germ P F n β (spline_germ _ false hr.1 hr.2 hx0) (spline_germ _ true hpo.1 hpo.2 hx0)
      (spline_germ _ true hs.1 hs.2 hx0) (spline_germ _ false hw.1 hw.2 hx0) k
  have hsl := slice_t (f := fun t' x' => reducedField P F n β t' x' k)
    (g := fun t' x' => genField P F n β (polyAmp false (decide (x < 0)) ((F.amp n).radialAmp.piece
          (cellIndex (F.amp n).radialAmp.mesh.tBreaks t) (cellIndex (F.amp n).radialAmp.mesh.xBreaks |x|)))
        (polyAmp true (decide (x < 0)) ((F.amp n).polarAmp.piece
          (cellIndex (F.amp n).polarAmp.mesh.tBreaks t) (cellIndex (F.amp n).polarAmp.mesh.xBreaks |x|)))
        (polyAmp true (decide (x < 0)) ((F.amp n).streamAmp.piece
          (cellIndex (F.amp n).streamAmp.mesh.tBreaks t) (cellIndex (F.amp n).streamAmp.mesh.xBreaks |x|)))
        (polyAmp false (decide (x < 0)) ((F.amp n).swirlAmp.piece
          (cellIndex (F.amp n).swirlAmp.mesh.tBreaks t) (cellIndex (F.amp n).swirlAmp.mesh.xBreaks |x|)))
        t' x' k) (z := (t, x)) hloc
  dsimp only at hsl
  rw [hsl.eq_of_nhds, hsl.deriv_eq]
  obtain ⟨b1, b2⟩ := hKf n _ _ _ _ (decide (x < 0)) k β hβ t x ht0 ht1.le hx1
  have hmem : (n, (F.amp n).radialAmp.piece
          (cellIndex (F.amp n).radialAmp.mesh.tBreaks t) (cellIndex (F.amp n).radialAmp.mesh.xBreaks |x|),
        (F.amp n).polarAmp.piece
          (cellIndex (F.amp n).polarAmp.mesh.tBreaks t) (cellIndex (F.amp n).polarAmp.mesh.xBreaks |x|),
        (F.amp n).streamAmp.piece
          (cellIndex (F.amp n).streamAmp.mesh.tBreaks t) (cellIndex (F.amp n).streamAmp.mesh.xBreaks |x|),
        (F.amp n).swirlAmp.piece
          (cellIndex (F.amp n).swirlAmp.mesh.tBreaks t) (cellIndex (F.amp n).swirlAmp.mesh.xBreaks |x|),
        decide (x < 0), k) ∈ T :=
    Finset.mem_biUnion.2 ⟨n, hn, Finset.mem_image.2 ⟨_, Finset.mem_product.2 ⟨hmemP _ _ _,
      Finset.mem_product.2 ⟨hmemP _ _ _, Finset.mem_product.2 ⟨hmemP _ _ _,
        Finset.mem_product.2 ⟨hmemP _ _ _, Finset.mem_univ _⟩⟩⟩⟩, rfl⟩⟩
  have hle := Finset.single_le_sum (f := Kt) (fun τ _ => hKf0 _ _ _ _ _ _ _) hmem
  have hst : 0 ≤ 1 - t := by linarith
  exact ⟨b1.trans (mul_le_mul_of_nonneg_right hle hst), b2.trans (mul_le_mul_of_nonneg_right hle (by positivity))⟩

theorem core_gap_le (P : ChartParams) (hP : IsChartParams P) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ 1 - coreRatioT P t ∧ 1 - coreRatioT P t ≤ max 2 (4 * P.rc ^ 2 / P.L0 ^ 2) * (1 - t) := by
  have hL := hP.L0_pos
  have hr := hP.rc_pos
  have hs : 0 < 1 - t := by linarith
  have hden : 0 < P.L0 ^ 2 * t ^ 2 + P.rc ^ 2 * (1 - t) ^ 2 := by positivity
  have e : 1 - coreRatioT P t = P.rc ^ 2 * (1 - t) ^ 2 / (P.L0 ^ 2 * t ^ 2 + P.rc ^ 2 * (1 - t) ^ 2) := by
    unfold coreRatioT
    field_simp
    ring
  rw [e]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hden]
  by_cases h : t < 1 / 2
  · have h2 : 2 * (1 - t) ≤ max 2 (4 * P.rc ^ 2 / P.L0 ^ 2) * (1 - t) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hs.le
    have h3 : P.rc ^ 2 * (1 - t) ^ 2 ≤ 2 * (1 - t) * (P.L0 ^ 2 * t ^ 2 + P.rc ^ 2 * (1 - t) ^ 2) := by
      have : 0 ≤ P.L0 ^ 2 * t ^ 2 := by positivity
      nlinarith [sq_nonneg (1 - t), mul_pos hr hr]
    calc _ ≤ 2 * (1 - t) * (P.L0 ^ 2 * t ^ 2 + P.rc ^ 2 * (1 - t) ^ 2) := h3
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hden.le
  · replace h := not_lt.1 h
    have hq : 0 < 4 * P.rc ^ 2 / P.L0 ^ 2 := by positivity
    have h2 : 4 * P.rc ^ 2 / P.L0 ^ 2 * (1 - t) ≤ max 2 (4 * P.rc ^ 2 / P.L0 ^ 2) * (1 - t) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hs.le
    have h3 : P.rc ^ 2 * (1 - t) ^ 2 ≤ 4 * P.rc ^ 2 / P.L0 ^ 2 * (1 - t) *
        (P.L0 ^ 2 * t ^ 2 + P.rc ^ 2 * (1 - t) ^ 2) := by
      have ht2 : 1 / 4 ≤ t ^ 2 := by nlinarith
      have e2 : 4 * P.rc ^ 2 / P.L0 ^ 2 * (1 - t) * (P.L0 ^ 2 * t ^ 2 + P.rc ^ 2 * (1 - t) ^ 2) =
          4 * P.rc ^ 2 * (1 - t) * t ^ 2 + 4 * P.rc ^ 2 / P.L0 ^ 2 * (1 - t) * (P.rc ^ 2 * (1 - t) ^ 2) := by
        field_simp
      rw [e2]
      have : 0 ≤ 4 * P.rc ^ 2 / P.L0 ^ 2 * (1 - t) * (P.rc ^ 2 * (1 - t) ^ 2) := by positivity
      have h1t : (1 - t) ^ 2 ≤ (1 - t) := by nlinarith
      have k1 : P.rc ^ 2 * (1 - t) ^ 2 ≤ P.rc ^ 2 * (1 - t) := mul_le_mul_of_nonneg_left h1t (by positivity)
      have k2 : P.rc ^ 2 * (1 - t) * 1 ≤ P.rc ^ 2 * (1 - t) * (4 * t ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have k3 : P.rc ^ 2 * (1 - t) * (4 * t ^ 2) = 4 * P.rc ^ 2 * (1 - t) * t ^ 2 := by ring
      linarith
    calc _ ≤ _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hden.le

theorem flowTerm_bound (P : ChartParams) (hP : IsChartParams P) (F : FieldData) (hF : IsFieldData P 1 F)
    (B : ℝ) :
    ∃ C : ℝ, ∀ β om : ℝ, |β| ≤ B → |om| ≤ B → ∀ n ∈ F.modes, ∀ k : Fin 3, ∀ t x : ℝ, 0 ≤ t → t < 1 →
      |x| ≤ 1 → x ≠ 0 →
      (∀ S ∈ [(F.amp n).radialAmp, (F.amp n).polarAmp, (F.amp n).streamAmp, (F.amp n).swirlAmp],
        t ∉ S.mesh.tBreaks ∧ |x| ∉ S.mesh.xBreaks) →
      ‖flowTerm P F n β om t x k‖ ≤ C * (1 - t) ^ 2 := by
  obtain ⟨K, hK⟩ := reduced_weight_bounds P hP F hF B
  set N : ℝ := ∑ n ∈ F.modes, |(n : ℝ)| with hN
  set M : ℝ := max 2 (4 * P.rc ^ 2 / P.L0 ^ 2) with hM
  have heps := hP.eps_pos
  refine ⟨|K| + (1 + 2 * P.eps) * |K| + N * (P.m : ℝ) * |B| * M * |K|,
    fun β om hβ hom n hn k t x ht0 ht1 hx1 hx0 hgen => ?_⟩
  obtain ⟨hR1, hR2⟩ := hK β hβ n hn k t x ht0 ht1 hx1 hx0 hgen
  obtain ⟨hg0, hg1⟩ := core_gap_le P hP ht0 ht1
  set R := reducedField P F n β t x k with hR
  set R' := deriv (fun t' => reducedField P F n β t' x k) t with hR'
  have hs : 0 < 1 - t := by linarith
  have hnN : |(n : ℝ)| ≤ N := Finset.single_le_sum (f := fun n : ℤ => |(n : ℝ)|) (fun _ _ => abs_nonneg _) hn
  have e : flowTerm P F n β om t x k = (t : ℂ) * (R + ((1 - t : ℝ) : ℂ) * R') +
      (((1 + 2 * P.eps) * (1 - t) : ℝ) : ℂ) * R +
        Complex.I * (((n : ℝ) * (P.m : ℝ) * om * (1 - coreRatioT P t) : ℝ) : ℂ) * R := by
    simp only [flowTerm, hR, hR']
    push_cast
    ring
  rw [e]
  have hK0 : 0 ≤ K := by
    have := (norm_nonneg R).trans hR1
    nlinarith
  have b1 : ‖(t : ℂ) * (R + ((1 - t : ℝ) : ℂ) * R')‖ ≤ |K| * (1 - t) ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_nonneg hK0]
    calc t * ‖R + ((1 - t : ℝ) : ℂ) * R'‖ ≤ 1 * (K * (1 - t) ^ 2) :=
          mul_le_mul ht1.le hR2 (norm_nonneg _) zero_le_one
      _ = K * (1 - t) ^ 2 := one_mul _
  have b2 : ‖(((1 + 2 * P.eps) * (1 - t) : ℝ) : ℂ) * R‖ ≤ (1 + 2 * P.eps) * |K| * (1 - t) ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg hK0]
    calc (1 + 2 * P.eps) * (1 - t) * ‖R‖ ≤ (1 + 2 * P.eps) * (1 - t) * (K * (1 - t)) :=
          mul_le_mul_of_nonneg_left hR1 (by positivity)
      _ = (1 + 2 * P.eps) * K * (1 - t) ^ 2 := by ring
  have b3 : ‖Complex.I * (((n : ℝ) * (P.m : ℝ) * om * (1 - coreRatioT P t) : ℝ) : ℂ) * R‖ ≤
      N * (P.m : ℝ) * |B| * M * |K| * (1 - t) ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hg0, Nat.abs_cast, abs_of_nonneg hK0]
    have hB : |om| ≤ |B| := hom.trans (le_abs_self B)
    have hm0 : (0 : ℝ) ≤ P.m := Nat.cast_nonneg _
    calc |(n : ℝ)| * (P.m : ℝ) * |om| * (1 - coreRatioT P t) * ‖R‖ ≤
        N * (P.m : ℝ) * |B| * (M * (1 - t)) * (K * (1 - t)) := by
          gcongr
      _ = N * (P.m : ℝ) * |B| * M * K * (1 - t) ^ 2 := by ring
  calc _ ≤ ‖(t : ℂ) * (R + ((1 - t : ℝ) : ℂ) * R')‖ + ‖(((1 + 2 * P.eps) * (1 - t) : ℝ) : ℂ) * R‖ +
        ‖Complex.I * (((n : ℝ) * (P.m : ℝ) * om * (1 - coreRatioT P t) : ℝ) : ℂ) * R‖ := norm_add₃_le
    _ ≤ |K| * (1 - t) ^ 2 + (1 + 2 * P.eps) * |K| * (1 - t) ^ 2 + N * (P.m : ℝ) * |B| * M * |K| * (1 - t) ^ 2 :=
        add_le_add (add_le_add b1 b2) b3
    _ = _ := by ring

end FieldDriftInternal

end GivenFields

end CellCert

end Breakdown
