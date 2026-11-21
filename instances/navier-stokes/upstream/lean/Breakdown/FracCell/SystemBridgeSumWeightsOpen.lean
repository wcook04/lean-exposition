import Breakdown.FracCell.CellSystemDefs
import Breakdown.FracCell.GivenDataDefs
import Breakdown.FracCell.GivenProfileBoundsFieldParts

open scoped ContDiff ENNReal
open MeasureTheory Matrix Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula
open _root_.Breakdown.CellCert.Finite

namespace SumWeightsOpen

private def quadTrig (q0 q1 q2 r0 r1 r2 κ u : ℝ) : ℝ :=
  (q0 + q1 * u + q2 * u ^ 2) * Real.cos (κ * u) + (r0 + r1 * u + r2 * u ^ 2) * Real.sin (κ * u)

private theorem quadTrig_hasDerivAt (q0 q1 q2 r0 r1 r2 κ u : ℝ) :
    HasDerivAt (quadTrig q0 q1 q2 r0 r1 r2 κ)
      (quadTrig (q1 + κ * r0) (2 * q2 + κ * r1) (κ * r2) (r1 - κ * q0) (2 * r2 - κ * q1) (-(κ * q2)) κ u) u := by
  have hk : HasDerivAt (fun x : ℝ => κ * x) κ u := by simpa using (hasDerivAt_id u).const_mul κ
  have hq : HasDerivAt (fun x : ℝ => q0 + q1 * x + q2 * x ^ 2) (q1 + 2 * q2 * u) u := by
    have h := (((hasDerivAt_id u).const_mul q1).const_add q0).add ((hasDerivAt_pow 2 u).const_mul q2)
    refine h.congr_deriv ?_
    simp
    ring
  have hr : HasDerivAt (fun x : ℝ => r0 + r1 * x + r2 * x ^ 2) (r1 + 2 * r2 * u) u := by
    have h := (((hasDerivAt_id u).const_mul r1).const_add r0).add ((hasDerivAt_pow 2 u).const_mul r2)
    refine h.congr_deriv ?_
    simp
    ring
  have h := (hq.mul hk.cos).add (hr.mul hk.sin)
  show HasDerivAt (fun x => (q0 + q1 * x + q2 * x ^ 2) * Real.cos (κ * x) +
    (r0 + r1 * x + r2 * x ^ 2) * Real.sin (κ * x)) _ u
  refine h.congr_deriv ?_
  simp only [quadTrig]
  ring

private theorem quadTrig_bound (q0 q1 q2 r0 r1 r2 κ u : ℝ) :
    |quadTrig q0 q1 q2 r0 r1 r2 κ u| ≤ (|q0| + |q1| + |q2| + |r0| + |r1| + |r2|) * (1 + |u|) ^ 2 := by
  unfold quadTrig
  have c1 := Real.abs_cos_le_one (κ * u)
  have s1 := Real.abs_sin_le_one (κ * u)
  have hu := abs_nonneg u
  have poly : ∀ p0 p1 p2 : ℝ, |p0 + p1 * u + p2 * u ^ 2| ≤ (|p0| + |p1| + |p2|) * (1 + |u|) ^ 2 := by
    intro p0 p1 p2
    have e0 : (1 : ℝ) ≤ (1 + |u|) ^ 2 := by nlinarith
    have e1 : |u| ≤ (1 + |u|) ^ 2 := by nlinarith
    have e2 : |u| ^ 2 ≤ (1 + |u|) ^ 2 := by nlinarith
    have t1 : |p0 + p1 * u + p2 * u ^ 2| ≤ |p0| + |p1| * |u| + |p2| * |u| ^ 2 := by
      calc |p0 + p1 * u + p2 * u ^ 2| ≤ |p0 + p1 * u| + |p2 * u ^ 2| := abs_add_le _ _
        _ ≤ |p0| + |p1 * u| + |p2 * u ^ 2| := by gcongr; exact abs_add_le _ _
        _ = |p0| + |p1| * |u| + |p2| * |u| ^ 2 := by rw [abs_mul, abs_mul, abs_pow]
    have m1 := mul_le_mul_of_nonneg_left e1 (abs_nonneg p1)
    have m2 := mul_le_mul_of_nonneg_left e2 (abs_nonneg p2)
    have m0 := mul_le_mul_of_nonneg_left e0 (abs_nonneg p0)
    generalize (1 + |u|) ^ 2 = X at *
    nlinarith
  have a1 := poly q0 q1 q2
  have a2 := poly r0 r1 r2
  have hX : 0 ≤ (1 + |u|) ^ 2 := by positivity
  calc |(q0 + q1 * u + q2 * u ^ 2) * Real.cos (κ * u) + (r0 + r1 * u + r2 * u ^ 2) * Real.sin (κ * u)|
      ≤ |q0 + q1 * u + q2 * u ^ 2| * |Real.cos (κ * u)| + |r0 + r1 * u + r2 * u ^ 2| * |Real.sin (κ * u)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
    _ ≤ (|q0| + |q1| + |q2|) * (1 + |u|) ^ 2 * 1 + (|r0| + |r1| + |r2|) * (1 + |u|) ^ 2 * 1 := by
        gcongr
    _ = _ := by ring

private theorem quadTrig_contDiff (q0 q1 q2 r0 r1 r2 κ : ℝ) : ContDiff ℝ 1 (quadTrig q0 q1 q2 r0 r1 r2 κ) := by
  show ContDiff ℝ 1 (fun x => (q0 + q1 * x + q2 * x ^ 2) * Real.cos (κ * x) +
    (r0 + r1 * x + r2 * x ^ 2) * Real.sin (κ * x))
  fun_prop

private def cosPart (a b c k β : ℝ) : ℝ := (a + b * β) * Real.cos (k * (β - c))

private def sinPart (a b c k β : ℝ) : ℝ := (a + b * β) * Real.sin (k * (β - c))

private def cosSlope (a b c k β : ℝ) : ℝ :=
  b * Real.cos (k * (β - c)) - (a + b * β) * k * Real.sin (k * (β - c))

private def sinSlope (a b c k β : ℝ) : ℝ :=
  b * Real.sin (k * (β - c)) + (a + b * β) * k * Real.cos (k * (β - c))

private def cosCurv (a b c k β : ℝ) : ℝ :=
  -(2 * b * k * Real.sin (k * (β - c))) - (a + b * β) * k ^ 2 * Real.cos (k * (β - c))

private def sinCurv (a b c k β : ℝ) : ℝ :=
  2 * b * k * Real.cos (k * (β - c)) - (a + b * β) * k ^ 2 * Real.sin (k * (β - c))

private theorem angle_hasDerivAt (k c β : ℝ) : HasDerivAt (fun x : ℝ => k * (x - c)) k β := by
  simpa using ((hasDerivAt_id β).sub_const c).const_mul k

private theorem lin_hasDerivAt (a b β : ℝ) : HasDerivAt (fun x : ℝ => a + b * x) b β := by
  simpa using ((hasDerivAt_id β).const_mul b).const_add a

private theorem cosPart_hasDerivAt (a b c k β : ℝ) : HasDerivAt (cosPart a b c k) (cosSlope a b c k β) β := by
  have h := (lin_hasDerivAt a b β).mul (angle_hasDerivAt k c β).cos
  show HasDerivAt (fun x => (a + b * x) * Real.cos (k * (x - c))) _ β
  refine h.congr_deriv ?_
  simp only [cosSlope]
  ring

private theorem sinPart_hasDerivAt (a b c k β : ℝ) : HasDerivAt (sinPart a b c k) (sinSlope a b c k β) β := by
  have h := (lin_hasDerivAt a b β).mul (angle_hasDerivAt k c β).sin
  show HasDerivAt (fun x => (a + b * x) * Real.sin (k * (x - c))) _ β
  refine h.congr_deriv ?_
  simp only [sinSlope]
  ring

private theorem cosSlope_hasDerivAt (a b c k β : ℝ) : HasDerivAt (cosSlope a b c k) (cosCurv a b c k β) β := by
  have h := ((angle_hasDerivAt k c β).cos.const_mul b).sub
    (((lin_hasDerivAt a b β).mul_const k).mul (angle_hasDerivAt k c β).sin)
  show HasDerivAt (fun x => b * Real.cos (k * (x - c)) - (a + b * x) * k * Real.sin (k * (x - c))) _ β
  refine h.congr_deriv ?_
  simp only [cosCurv]
  ring

private theorem sinSlope_hasDerivAt (a b c k β : ℝ) : HasDerivAt (sinSlope a b c k) (sinCurv a b c k β) β := by
  have h := ((angle_hasDerivAt k c β).sin.const_mul b).add
    (((lin_hasDerivAt a b β).mul_const k).mul (angle_hasDerivAt k c β).cos)
  show HasDerivAt (fun x => b * Real.sin (k * (x - c)) + (a + b * x) * k * Real.cos (k * (x - c))) _ β
  refine h.congr_deriv ?_
  simp only [sinCurv]
  ring

private theorem cosCurv_eq (a b c n β u : ℝ) :
    cosCurv a b c (n * u) β = quadTrig 0 0 (-((a + b * β) * n ^ 2)) 0 (-(2 * b * n)) 0 (n * (β - c)) u := by
  simp only [cosCurv, quadTrig]
  rw [show n * u * (β - c) = n * (β - c) * u by ring]
  ring

private theorem sinCurv_eq (a b c n β u : ℝ) :
    sinCurv a b c (n * u) β = -quadTrig 0 (-(2 * b * n)) 0 0 0 ((a + b * β) * n ^ 2) (n * (β - c)) u := by
  simp only [sinCurv, quadTrig]
  rw [show n * u * (β - c) = n * (β - c) * u by ring]
  ring

private theorem ofComponents_sum (s : Finset ℤ) (w : ℤ → Fin 3 → ℝ) :
    ofComponents (fun i => ∑ n ∈ s, w n i) = ∑ n ∈ s, ofComponents (w n) := by
  ext j
  fin_cases j <;> simp [ofComponents]

private theorem fieldOf_modeSum (P : ChartParams) (D : FieldData) (β : ℝ) (y : Space) :
    fieldOf P D β y = ∑ n ∈ D.modes, modeFieldOf P D β n y := by
  unfold fieldOf modeFieldOf
  rw [← ofComponents_sum]
  congr 1
  funext i
  rw [Finset.mul_sum, Complex.re_sum]

private theorem mode_zero_const (P : ChartParams) (D : FieldData) (β : ℝ) :
    modeFieldOf P D β 0 = modeFieldOf P D 0 0 := by
  funext y
  simp [modeFieldOf, modePhase, reducedField, twistedScale]

private theorem mode_rot (P : ChartParams) (F : FieldData) (n : ℤ) (hn : n ≠ 0) (β : ℝ) (y : Space) :
    modeFieldOf P F β n y =
      cosPart 1 (-1) 0 (n * logPhase P y) β • modeFieldOf P F 0 n y -
        sinPart 1 (-1) 0 (n * logPhase P y) β • modeFieldOf P (FracCellInternal.quarterTurnData F n) 0 n y +
      (cosPart 0 1 1 (n * logPhase P y) β • modeFieldOf P F 1 n y -
        sinPart 0 1 1 (n * logPhase P y) β • modeFieldOf P (FracCellInternal.quarterTurnData F n) 1 n y) := by
  rw [FracCellInternal.mode_phase_identity P F n hn β y]
  simp only [cosPart, sinPart]
  rw [show (1 : ℝ) + -1 * β = 1 - β by ring, show (0 : ℝ) + 1 * β = β by ring,
    show (n : ℝ) * logPhase P y * (β - 0) = n * β * logPhase P y by ring,
    show (n : ℝ) * logPhase P y * (β - 1) = n * (β - 1) * logPhase P y by ring]
  module

private def slopeVec (P : ChartParams) (F : FieldData) (β : ℝ) (n : ℤ) (y : Space) : Space :=
  if n = 0 then 0 else
    cosSlope 1 (-1) 0 (n * logPhase P y) β • modeFieldOf P F 0 n y -
        sinSlope 1 (-1) 0 (n * logPhase P y) β • modeFieldOf P (FracCellInternal.quarterTurnData F n) 0 n y +
      (cosSlope 0 1 1 (n * logPhase P y) β • modeFieldOf P F 1 n y -
        sinSlope 0 1 1 (n * logPhase P y) β • modeFieldOf P (FracCellInternal.quarterTurnData F n) 1 n y)

private def curvVec (P : ChartParams) (F : FieldData) (β : ℝ) (n : ℤ) (y : Space) : Space :=
  if n = 0 then 0 else
    cosCurv 1 (-1) 0 (n * logPhase P y) β • modeFieldOf P F 0 n y -
        sinCurv 1 (-1) 0 (n * logPhase P y) β • modeFieldOf P (FracCellInternal.quarterTurnData F n) 0 n y +
      (cosCurv 0 1 1 (n * logPhase P y) β • modeFieldOf P F 1 n y -
        sinCurv 0 1 1 (n * logPhase P y) β • modeFieldOf P (FracCellInternal.quarterTurnData F n) 1 n y)

private theorem mode_hasDerivAt (P : ChartParams) (F : FieldData) (n : ℤ) (y : Space) (b : ℝ) :
    HasDerivAt (fun x => modeFieldOf P F x n y) (slopeVec P F b n y) b := by
  by_cases h0 : n = 0
  · subst h0
    simp only [slopeVec, if_true]
    have : (fun x => modeFieldOf P F x 0 y) = fun _ => modeFieldOf P F 0 0 y := by
      funext x
      rw [mode_zero_const P F x]
    rw [this]
    exact hasDerivAt_const _ _
  · simp only [slopeVec, h0, if_false]
    have : (fun x => modeFieldOf P F x n y) = fun x =>
        cosPart 1 (-1) 0 (n * logPhase P y) x • modeFieldOf P F 0 n y -
          sinPart 1 (-1) 0 (n * logPhase P y) x • modeFieldOf P (FracCellInternal.quarterTurnData F n) 0 n y +
        (cosPart 0 1 1 (n * logPhase P y) x • modeFieldOf P F 1 n y -
          sinPart 0 1 1 (n * logPhase P y) x • modeFieldOf P (FracCellInternal.quarterTurnData F n) 1 n y) := by
      funext x
      exact mode_rot P F n h0 x y
    rw [this]
    exact (((cosPart_hasDerivAt _ _ _ _ b).smul_const _).sub ((sinPart_hasDerivAt _ _ _ _ b).smul_const _)).add
      (((cosPart_hasDerivAt _ _ _ _ b).smul_const _).sub ((sinPart_hasDerivAt _ _ _ _ b).smul_const _))

private theorem slope_hasDerivAt (P : ChartParams) (F : FieldData) (n : ℤ) (y : Space) (β : ℝ) :
    HasDerivAt (fun x => slopeVec P F x n y) (curvVec P F β n y) β := by
  by_cases h0 : n = 0
  · simp only [slopeVec, curvVec, h0, if_true]
    exact hasDerivAt_const _ _
  · simp only [slopeVec, curvVec, h0, if_false]
    exact (((cosSlope_hasDerivAt _ _ _ _ β).smul_const _).sub ((sinSlope_hasDerivAt _ _ _ _ β).smul_const _)).add
      (((cosSlope_hasDerivAt _ _ _ _ β).smul_const _).sub ((sinSlope_hasDerivAt _ _ _ _ β).smul_const _))

private theorem phaseCurv_eq (P : ChartParams) (F : FieldData) (β : ℝ) :
    phaseCurvField P F β = fun y => ∑ n ∈ F.modes, curvVec P F β n y := by
  funext y
  unfold phaseCurvField
  have h1 : (fun b => deriv (fun b' => fieldOf P F b' y) b) = fun b => ∑ n ∈ F.modes, slopeVec P F b n y := by
    funext b
    have he : (fun b' => fieldOf P F b' y) = fun b' => ∑ n ∈ F.modes, modeFieldOf P F b' n y := by
      funext b'
      exact fieldOf_modeSum P F b' y
    rw [he]
    exact (HasDerivAt.fun_sum fun n _ => mode_hasDerivAt P F n y b).deriv
  rw [h1]
  exact (HasDerivAt.fun_sum fun n _ => slope_hasDerivAt P F n y β).deriv

private def Good (f : Space → Space) : Prop :=
  ContDiff ℝ 1 f ∧ ∃ R C : ℝ, ∀ y : Space, R ≤ ‖y‖ → ‖fderiv ℝ f y‖ ≤ C * ‖y‖ ^ (-(2 : ℝ))

private theorem good_add {f g : Space → Space} (hf : Good f) (hg : Good g) : Good (fun y => f y + g y) := by
  obtain ⟨hf1, R1, C1, hf2⟩ := hf
  obtain ⟨hg1, R2, C2, hg2⟩ := hg
  refine ⟨hf1.add hg1, max R1 R2, C1 + C2, fun y hy => ?_⟩
  rw [fderiv_fun_add (hf1.differentiable (by norm_num) y) (hg1.differentiable (by norm_num) y)]
  have a1 := hf2 y (le_of_max_le_left hy)
  have a2 := hg2 y (le_of_max_le_right hy)
  calc ‖fderiv ℝ f y + fderiv ℝ g y‖ ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ g y‖ := norm_add_le _ _
    _ ≤ (C1 + C2) * ‖y‖ ^ (-(2 : ℝ)) := by rw [add_mul]; linarith

private theorem good_zero : Good (fun _ : Space => (0 : Space)) := by
  refine ⟨contDiff_const, 0, 0, fun y _ => ?_⟩
  simp

private theorem good_sum (s : Finset ℤ) (f : ℤ → Space → Space) (h : ∀ n ∈ s, Good (f n)) :
    Good (fun y => ∑ n ∈ s, f n y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero
  | insert i s hi ih =>
    have e : (fun y => ∑ n ∈ insert i s, f n y) = fun y => f i y + ∑ n ∈ s, f n y := by
      funext y
      rw [Finset.sum_insert hi]
    rw [e]
    exact good_add (h i (Finset.mem_insert_self i s)) (ih fun n hn => h n (Finset.mem_insert_of_mem hn))

private theorem logPhase_contDiff (P : ChartParams) : ContDiff ℝ 1 (logPhase P) := by
  show ContDiff ℝ 1 (fun y : Space => (1 / 2) * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2))
  refine contDiff_const.mul ((contDiff_const.add ((contDiff_norm_sq ℝ).div_const _)).log fun y => ?_)
  positivity

private theorem logPhase_hasFDerivAt (P : ChartParams) (hP : IsChartParams P) (y : Space) :
    HasFDerivAt (logPhase P) ((P.rc ^ 2 + ‖y‖ ^ 2)⁻¹ • innerSL ℝ y) y := by
  have hrc : 0 < P.rc := hP.rc_pos
  have h1 : HasFDerivAt (fun x : Space => ‖x‖ ^ 2) (2 • innerSL ℝ y) y := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hpos' : 1 + (P.rc ^ 2)⁻¹ * ‖y‖ ^ 2 ≠ 0 := by positivity
  have h3 := (((h1.const_mul (P.rc ^ 2)⁻¹).const_add 1).log hpos').const_mul (1 / 2 : ℝ)
  have hfun : logPhase P = fun y : Space => (1 / 2) * Real.log (1 + (P.rc ^ 2)⁻¹ * ‖y‖ ^ 2) := by
    funext z
    simp only [logPhase, div_eq_inv_mul]
  rw [hfun]
  refine h3.congr_fderiv ?_
  ext v
  simp
  field_simp

private theorem logPhase_fderiv_le (P : ChartParams) (hP : IsChartParams P) (y : Space) (hy : 0 < ‖y‖) :
    ‖fderiv ℝ (logPhase P) y‖ ≤ ‖y‖ ^ (-(1 : ℝ)) := by
  have hrc := hP.rc_pos
  rw [(logPhase_hasFDerivAt P hP y).fderiv, norm_smul, innerSL_apply_norm, Real.norm_eq_abs,
    abs_of_pos (by positivity), Real.rpow_neg_one, ← div_eq_inv_mul, div_le_iff₀ (by positivity),
    inv_mul_eq_div, le_div_iff₀ hy]
  nlinarith [sq_nonneg P.rc]

private theorem logPhase_nonneg (P : ChartParams) (y : Space) : 0 ≤ logPhase P y := by
  unfold logPhase
  have : 1 ≤ 1 + ‖y‖ ^ 2 / P.rc ^ 2 := by
    have : 0 ≤ ‖y‖ ^ 2 / P.rc ^ 2 := by positivity
    linarith
  have := Real.log_nonneg this
  positivity

private theorem logPhase_growth (P : ChartParams) (hP : IsChartParams P) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y : Space, 1 ≤ ‖y‖ → (1 + logPhase P y) ^ 2 ≤ A * ‖y‖ ^ P.eps := by
  have hrc := hP.rc_pos
  have he := hP.eps_pos
  have hK0p : 0 < 1 + 1 / P.rc ^ 2 := by positivity
  have hεp : 0 < P.eps / 4 := by positivity
  refine ⟨(1 + (1 + 1 / P.rc ^ 2) ^ (P.eps / 4) / (2 * (P.eps / 4))) ^ 2, by positivity, fun y hy => ?_⟩
  have hρ : 0 < ‖y‖ := by linarith
  have hX1 : 1 ≤ 1 + ‖y‖ ^ 2 / P.rc ^ 2 := by
    have : 0 ≤ ‖y‖ ^ 2 / P.rc ^ 2 := by positivity
    linarith
  have hXle : 1 + ‖y‖ ^ 2 / P.rc ^ 2 ≤ (1 + 1 / P.rc ^ 2) * ‖y‖ ^ 2 := by
    have h1 : (1 : ℝ) ≤ ‖y‖ ^ 2 := by nlinarith
    have : (1 + 1 / P.rc ^ 2) * ‖y‖ ^ 2 = ‖y‖ ^ 2 + ‖y‖ ^ 2 / P.rc ^ 2 := by ring
    linarith
  have hpow : (1 + ‖y‖ ^ 2 / P.rc ^ 2) ^ (P.eps / 4) ≤ (1 + 1 / P.rc ^ 2) ^ (P.eps / 4) * ‖y‖ ^ (P.eps / 2) := by
    calc (1 + ‖y‖ ^ 2 / P.rc ^ 2) ^ (P.eps / 4) ≤ ((1 + 1 / P.rc ^ 2) * ‖y‖ ^ 2) ^ (P.eps / 4) :=
          Real.rpow_le_rpow (by linarith) hXle hεp.le
      _ = (1 + 1 / P.rc ^ 2) ^ (P.eps / 4) * ‖y‖ ^ (P.eps / 2) := by
        rw [Real.mul_rpow hK0p.le (by positivity), show ‖y‖ ^ 2 = ‖y‖ ^ (2 : ℝ) by rw [Real.rpow_two],
          ← Real.rpow_mul hρ.le]
        congr 2
        ring
  have hlog := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ 1 + ‖y‖ ^ 2 / P.rc ^ 2) hεp
  have hL0 := logPhase_nonneg P y
  have h1e : 1 ≤ ‖y‖ ^ (P.eps / 2) := Real.one_le_rpow hy (by positivity)
  have hL : logPhase P y ≤ (1 + 1 / P.rc ^ 2) ^ (P.eps / 4) / (2 * (P.eps / 4)) * ‖y‖ ^ (P.eps / 2) := by
    unfold logPhase
    calc (1 / 2) * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2)
        ≤ (1 / 2) * ((1 + ‖y‖ ^ 2 / P.rc ^ 2) ^ (P.eps / 4) / (P.eps / 4)) := by gcongr
      _ ≤ (1 / 2) * ((1 + 1 / P.rc ^ 2) ^ (P.eps / 4) * ‖y‖ ^ (P.eps / 2) / (P.eps / 4)) := by gcongr
      _ = _ := by field_simp
  have hB : 1 + logPhase P y ≤ (1 + (1 + 1 / P.rc ^ 2) ^ (P.eps / 4) / (2 * (P.eps / 4))) * ‖y‖ ^ (P.eps / 2) := by
    have : (1 + (1 + 1 / P.rc ^ 2) ^ (P.eps / 4) / (2 * (P.eps / 4))) * ‖y‖ ^ (P.eps / 2) =
        ‖y‖ ^ (P.eps / 2) + (1 + 1 / P.rc ^ 2) ^ (P.eps / 4) / (2 * (P.eps / 4)) * ‖y‖ ^ (P.eps / 2) := by ring
    linarith
  have hsq : (‖y‖ ^ (P.eps / 2)) ^ 2 = ‖y‖ ^ P.eps := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    congr 1
    push_cast
    ring
  calc (1 + logPhase P y) ^ 2
      ≤ ((1 + (1 + 1 / P.rc ^ 2) ^ (P.eps / 4) / (2 * (P.eps / 4))) * ‖y‖ ^ (P.eps / 2)) ^ 2 := by
        gcongr
    _ = _ := by rw [mul_pow, hsq]

private theorem good_piece (P : ChartParams) (hP : IsChartParams P) (q0 q1 q2 r0 r1 r2 κ : ℝ)
    {V : Space → Space} (hV : ContDiff ℝ 1 V) (R0 C0 : ℝ)
    (hfar : ∀ y : Space, R0 ≤ ‖y‖ →
      ‖V y‖ ≤ C0 * ‖y‖ ^ (-(1 + P.eps)) ∧ ‖fderiv ℝ V y‖ ≤ C0 * ‖y‖ ^ (-(2 + P.eps))) :
    Good (fun y => quadTrig q0 q1 q2 r0 r1 r2 κ (logPhase P y) • V y) := by
  have hL := logPhase_contDiff P
  have hp := quadTrig_contDiff q0 q1 q2 r0 r1 r2 κ
  refine ⟨(hp.comp hL).smul hV, ?_⟩
  obtain ⟨A, hA, hgr⟩ := logPhase_growth P hP
  set K : ℝ := (|q0| + |q1| + |q2| + |r0| + |r1| + |r2|) +
    (|q1 + κ * r0| + |2 * q2 + κ * r1| + |κ * r2| + |r1 - κ * q0| + |2 * r2 - κ * q1| + |-(κ * q2)|) with hK
  have hK0 : 0 ≤ K := by positivity
  have hb0 : ∀ u, |quadTrig q0 q1 q2 r0 r1 r2 κ u| ≤ K * (1 + |u|) ^ 2 := by
    intro u
    refine (quadTrig_bound _ _ _ _ _ _ κ u).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [hK]
    have : 0 ≤ |q1 + κ * r0| + |2 * q2 + κ * r1| + |κ * r2| + |r1 - κ * q0| + |2 * r2 - κ * q1| + |-(κ * q2)| := by
      positivity
    linarith
  have hb1 : ∀ u, |quadTrig (q1 + κ * r0) (2 * q2 + κ * r1) (κ * r2) (r1 - κ * q0) (2 * r2 - κ * q1) (-(κ * q2)) κ u|
      ≤ K * (1 + |u|) ^ 2 := by
    intro u
    refine (quadTrig_bound _ _ _ _ _ _ κ u).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [hK]
    have : 0 ≤ |q0| + |q1| + |q2| + |r0| + |r1| + |r2| := by positivity
    linarith
  refine ⟨max R0 1, 2 * K * |C0| * A, fun y hy => ?_⟩
  have hy1 : 1 ≤ ‖y‖ := le_of_max_le_right hy
  have hρ : 0 < ‖y‖ := by linarith
  obtain ⟨v1, v2⟩ := hfar y (le_of_max_le_left hy)
  have hd : HasFDerivAt (fun z => quadTrig q0 q1 q2 r0 r1 r2 κ (logPhase P z) • V z)
      (quadTrig q0 q1 q2 r0 r1 r2 κ (logPhase P y) • fderiv ℝ V y +
        (quadTrig (q1 + κ * r0) (2 * q2 + κ * r1) (κ * r2) (r1 - κ * q0) (2 * r2 - κ * q1) (-(κ * q2)) κ
          (logPhase P y) • fderiv ℝ (logPhase P) y).smulRight (V y)) y := by
    have h1 := (quadTrig_hasDerivAt q0 q1 q2 r0 r1 r2 κ (logPhase P y)).comp_hasFDerivAt y
      ((hL.differentiable (by norm_num)) y).hasFDerivAt
    exact h1.smul ((hV.differentiable (by norm_num)) y).hasFDerivAt
  rw [hd.fderiv]
  have hL0 := logPhase_nonneg P y
  have hDL := logPhase_fderiv_le P hP y hρ
  have hg := hgr y hy1
  set ρ := ‖y‖ with hρd
  set W : ℝ := (1 + logPhase P y) ^ 2 with hW
  have hW0 : 0 ≤ W := by positivity
  have p0 : |quadTrig q0 q1 q2 r0 r1 r2 κ (logPhase P y)| ≤ K * W := by
    have := hb0 (logPhase P y)
    rwa [abs_of_nonneg hL0] at this
  have p1 : |quadTrig (q1 + κ * r0) (2 * q2 + κ * r1) (κ * r2) (r1 - κ * q0) (2 * r2 - κ * q1) (-(κ * q2)) κ
      (logPhase P y)| ≤ K * W := by
    have := hb1 (logPhase P y)
    rwa [abs_of_nonneg hL0] at this
  have w1 : ‖V y‖ ≤ |C0| * ρ ^ (-(1 + P.eps)) :=
    v1.trans (mul_le_mul_of_nonneg_right (le_abs_self C0) (by positivity))
  have w2 : ‖fderiv ℝ V y‖ ≤ |C0| * ρ ^ (-(2 + P.eps)) :=
    v2.trans (mul_le_mul_of_nonneg_right (le_abs_self C0) (by positivity))
  have e1 : ρ ^ (-(1 : ℝ)) * ρ ^ (-(1 + P.eps)) = ρ ^ (-(2 + P.eps)) := by
    rw [← Real.rpow_add hρ]
    congr 1
    ring
  have e2 : ρ ^ P.eps * ρ ^ (-(2 + P.eps)) = ρ ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hρ]
    congr 1
    ring
  have q1n : 0 ≤ ρ ^ (-(2 + P.eps)) := by positivity
  calc ‖quadTrig q0 q1 q2 r0 r1 r2 κ (logPhase P y) • fderiv ℝ V y +
        (quadTrig (q1 + κ * r0) (2 * q2 + κ * r1) (κ * r2) (r1 - κ * q0) (2 * r2 - κ * q1) (-(κ * q2)) κ
          (logPhase P y) • fderiv ℝ (logPhase P) y).smulRight (V y)‖
      ≤ |quadTrig q0 q1 q2 r0 r1 r2 κ (logPhase P y)| * ‖fderiv ℝ V y‖ +
        |quadTrig (q1 + κ * r0) (2 * q2 + κ * r1) (κ * r2) (r1 - κ * q0) (2 * r2 - κ * q1) (-(κ * q2)) κ
          (logPhase P y)| * ‖fderiv ℝ (logPhase P) y‖ * ‖V y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (K * W) * (|C0| * ρ ^ (-(2 + P.eps))) + (K * W) * ρ ^ (-(1 : ℝ)) * (|C0| * ρ ^ (-(1 + P.eps))) := by
        gcongr
    _ = 2 * K * |C0| * W * ρ ^ (-(2 + P.eps)) := by
        rw [show (K * W) * ρ ^ (-(1 : ℝ)) * (|C0| * ρ ^ (-(1 + P.eps))) =
          (K * W) * |C0| * (ρ ^ (-(1 : ℝ)) * ρ ^ (-(1 + P.eps))) by ring, e1]
        ring
    _ ≤ 2 * K * |C0| * (A * ρ ^ P.eps) * ρ ^ (-(2 + P.eps)) := by gcongr
    _ = 2 * K * |C0| * A * ρ ^ (-(2 : ℝ)) := by
        rw [show 2 * K * |C0| * (A * ρ ^ P.eps) * ρ ^ (-(2 + P.eps)) =
          2 * K * |C0| * A * (ρ ^ P.eps * ρ ^ (-(2 + P.eps))) by ring, e2]

private theorem mode_contDiff_wave (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 1 D)
    (c : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) : ContDiff ℝ 1 (modeFieldOf P D c n) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases hy : y = 0
  · subst hy
    exact modeFieldOf_contDiffAt_origin_wave P hP hD c n hn h0
  · exact modeFieldOf_contDiffAt_axis_of P hP hD c n hn h0 y hy

private theorem good_mode (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 1 D)
    (c : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) (q0 q1 q2 r0 r1 r2 κ : ℝ) :
    Good (fun y => quadTrig q0 q1 q2 r0 r1 r2 κ (logPhase P y) • modeFieldOf P D c n y) := by
  obtain ⟨R, C, h⟩ := FracCellInternal.modeFieldOf_far_bounds P hP D hD c n hn
  exact good_piece P hP q0 q1 q2 r0 r1 r2 κ (mode_contDiff_wave P hP D hD c n hn h0) R C
    fun y hy => ⟨(h y hy).1, (h y hy).2.1⟩

private theorem good_curvVec (P : ChartParams) (hP : IsChartParams P) (F : FieldData) (hF : IsFieldData P 1 F)
    (β : ℝ) (n : ℤ) (hn : n ∈ F.modes) : Good (fun y => curvVec P F β n y) := by
  by_cases h0 : n = 0
  · have e : (fun y => curvVec P F β n y) = fun _ => (0 : Space) := by
      funext y
      simp [curvVec, h0]
    rw [e]
    exact good_zero
  · have hQ := FracCellInternal.quarterTurnData_isFieldData P F hF n h0
    have hnQ : n ∈ (FracCellInternal.quarterTurnData F n).modes := hn
    have e : (fun y => curvVec P F β n y) = fun y =>
        (quadTrig 0 0 (-((1 + -1 * β) * (n : ℝ) ^ 2)) 0 (-(2 * -1 * (n : ℝ))) 0 (n * (β - 0)) (logPhase P y) •
            modeFieldOf P F 0 n y +
          quadTrig 0 (-(2 * -1 * (n : ℝ))) 0 0 0 ((1 + -1 * β) * (n : ℝ) ^ 2) (n * (β - 0)) (logPhase P y) •
            modeFieldOf P (FracCellInternal.quarterTurnData F n) 0 n y) +
        (quadTrig 0 0 (-((0 + 1 * β) * (n : ℝ) ^ 2)) 0 (-(2 * 1 * (n : ℝ))) 0 (n * (β - 1)) (logPhase P y) •
            modeFieldOf P F 1 n y +
          quadTrig 0 (-(2 * 1 * (n : ℝ))) 0 0 0 ((0 + 1 * β) * (n : ℝ) ^ 2) (n * (β - 1)) (logPhase P y) •
            modeFieldOf P (FracCellInternal.quarterTurnData F n) 1 n y) := by
      funext y
      simp only [curvVec, h0, if_false]
      rw [cosCurv_eq, sinCurv_eq, cosCurv_eq, sinCurv_eq, neg_smul, neg_smul, sub_neg_eq_add, sub_neg_eq_add]
    rw [e]
    exact good_add (good_add (good_mode P hP F hF 0 n hn h0 _ _ _ _ _ _ _) (good_mode P hP _ hQ 0 n hnQ h0 _ _ _ _ _ _ _))
      (good_add (good_mode P hP F hF 1 n hn h0 _ _ _ _ _ _ _) (good_mode P hP _ hQ 1 n hnQ h0 _ _ _ _ _ _ _))

private theorem weighted_of_good {f : Space → Space} (h : Good f) :
    ∃ C : ℝ, ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  obtain ⟨hc, R, C, hb⟩ := h
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Space) (max R 1)).exists_bound_of_continuousOn
    (hc.continuous_fderiv (by norm_num)).continuousOn
  refine ⟨|M| * (1 + max R 1) ^ 2 + 4 * |C|, fun y => ?_⟩
  have hp : 0 < 1 + ‖y‖ := by positivity
  have hw : (1 + ‖y‖) ^ (-(2 : ℝ)) = ((1 + ‖y‖) ^ 2)⁻¹ := by rw [Real.rpow_neg hp.le, Real.rpow_two]
  rw [hw, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hM0 : 0 ≤ |M| * (1 + max R 1) ^ 2 := by positivity
  have hC0 : 0 ≤ 4 * |C| := by positivity
  rcases le_total ‖y‖ (max R 1) with h | h
  · have hy : y ∈ Metric.closedBall (0 : Space) (max R 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact h
    have h1 : ‖fderiv ℝ f y‖ ≤ |M| := (hM y hy).trans (le_abs_self M)
    have hq : (1 + ‖y‖) ^ 2 ≤ (1 + max R 1) ^ 2 := by gcongr
    have := mul_le_mul h1 hq (by positivity) (abs_nonneg M)
    linarith
  · have hy1 : 1 ≤ ‖y‖ := (le_max_right R 1).trans h
    have hρ : 0 < ‖y‖ := by linarith
    have h2 := hb y ((le_max_left R 1).trans h)
    rw [Real.rpow_neg hρ.le, Real.rpow_two] at h2
    have hD2 : ‖fderiv ℝ f y‖ * ‖y‖ ^ 2 ≤ |C| := by
      have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ ‖y‖ ^ 2)
      rw [mul_assoc, inv_mul_cancel₀ (by positivity), mul_one] at this
      exact this.trans (le_abs_self C)
    have e1 : (1 + ‖y‖) ^ 2 ≤ 4 * ‖y‖ ^ 2 := by nlinarith
    have e2 := mul_le_mul_of_nonneg_left e1 (norm_nonneg (fderiv ℝ f y))
    linarith

theorem phaseCurv_regular (P : ChartParams) (hP : IsChartParams P) (F : FieldData) (hF : IsFieldData P 1 F)
    (β : ℝ) : ContDiff ℝ 1 (phaseCurvField P F β) ∧
      ∃ C : ℝ, ∀ y, ‖fderiv ℝ (phaseCurvField P F β) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  have hg : Good (phaseCurvField P F β) := by
    rw [phaseCurv_eq P F β]
    exact good_sum F.modes (fun n y => curvVec P F β n y) fun n hn => good_curvVec P hP F hF β n hn
  exact ⟨hg.1, weighted_of_good hg⟩

end SumWeightsOpen

end CellSystem

end CellCert

end Breakdown
