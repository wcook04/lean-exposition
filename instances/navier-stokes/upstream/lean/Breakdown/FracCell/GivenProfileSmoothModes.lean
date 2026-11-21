import Breakdown.FracCell.GivenAuxActuatorOpen
import Breakdown.FracCell.GivenToolkit
import Breakdown.FracCell.FieldJointSmooth
import Breakdown.FracCell.GivenAuxPinSmoothLocal

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

open CellCert.GivenFields SteadyCert

def reducedDivergence (P : ChartParams) (D : FieldData) (n : ℤ) (β t x : ℝ) : ℂ :=
  twistedScale P n β (fun t' x' => reducedField P D n β t' x' 0) t x + 2 * reducedField P D n β t x 0 -
    heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * reducedField P D n β t' x' 1) t x +
      Complex.I * ((n * P.m : ℤ) : ℂ) * reducedField P D n β t x 2

theorem modeFieldOf_fderiv_locallySlope_wave {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) :
    LocallyLipschitz (fderiv ℝ (modeFieldOf P D β n)) :=
  modeFieldOf_fderiv_localSlope_wave P hP hD β n hn h0

theorem modeFieldOf_fderiv_locallySlope_mean {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) (hn : (0 : ℤ) ∈ D.modes) :
    LocallyLipschitz (fderiv ℝ (modeFieldOf P D β 0)) :=
  modeFieldOf_fderiv_localSlope_mean P hP hD β hn

private theorem g_div_smul {c : Space → ℝ} {W : Space → Space} {y : Space} (hc : DifferentiableAt ℝ c y)
    (hW : DifferentiableAt ℝ W y) :
    divergenceAt (fun z => c z • W z) y = fderiv ℝ c y (W y) + c y * divergenceAt W y := by
  unfold divergenceAt
  rw [fderiv_fun_smul hc hW]
  have hW' : W y = ∑ i : Fin 3, (W y i) • unitVector i := by
    ext j
    fin_cases j <;> simp [unitVector, Fin.sum_univ_three]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  rw [add_comm]
  congr 1
  conv_rhs => rw [hW', map_sum]
  simp [mul_comm]

private theorem g_div_add {F G : Space → Space} {y : Space} (hF : DifferentiableAt ℝ F y)
    (hG : DifferentiableAt ℝ G y) :
    divergenceAt (fun z => F z + G z) y = divergenceAt F y + divergenceAt G y := by
  unfold divergenceAt
  rw [fderiv_fun_add hF hG]
  simp [Finset.sum_add_distrib]

private theorem g_div_add_const {F : Space → Space} {y : Space} (v : Space) :
    divergenceAt (fun z => F z + v) y = divergenceAt F y := by
  unfold divergenceAt
  rw [fderiv_add_const]

private theorem g_div_id (y : Space) : divergenceAt (fun z : Space => z) y = 3 := by
  unfold divergenceAt
  rw [fderiv_fun_id]
  simp [unitVector]

private theorem g_norm_hasFDerivAt {y : Space} (hy : y ≠ 0) :
    HasFDerivAt (fun z : Space => ‖z‖) ((1 / (2 * ‖y‖)) • (2 • innerSL ℝ y)) y := by
  have h := ((hasStrictFDerivAt_norm_sq y).hasFDerivAt).sqrt (by positivity)
  have e : (fun z : Space => Real.sqrt (‖z‖ ^ 2)) = fun z => ‖z‖ := funext fun z => Real.sqrt_sq (norm_nonneg z)
  rw [e, Real.sqrt_sq (norm_nonneg y)] at h
  exact h

private theorem g_norm_fderiv {y : Space} (hy : y ≠ 0) (w : Space) :
    fderiv ℝ (fun z : Space => ‖z‖) y w = (y 0 * w 0 + y 1 * w 1 + y 2 * w 2) / ‖y‖ := by
  rw [(g_norm_hasFDerivAt hy).fderiv]
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  simp [Fin.sum_univ_three, PiLp.inner_apply]
  field_simp


private theorem g_radial_fderiv {h : ℝ → ℝ} {y : Space} (hy : y ≠ 0) (hh : DifferentiableAt ℝ h ‖y‖) (w : Space) :
    fderiv ℝ (fun z : Space => h ‖z‖) y w = deriv h ‖y‖ * ((y 0 * w 0 + y 1 * w 1 + y 2 * w 2) / ‖y‖) := by
  have hc := hh.hasDerivAt.comp_hasFDerivAt y (g_norm_hasFDerivAt hy)
  rw [show (fun z : Space => h ‖z‖) = h ∘ fun z => ‖z‖ from rfl, hc.fderiv, ← g_norm_fderiv hy w,
    (g_norm_hasFDerivAt hy).fderiv]
  simp

private theorem g_radial_diff {h : ℝ → ℝ} {y : Space} (hy : y ≠ 0) (hh : DifferentiableAt ℝ h ‖y‖) :
    DifferentiableAt ℝ (fun z : Space => h ‖z‖) y :=
  (hh.hasDerivAt.comp_hasFDerivAt y (g_norm_hasFDerivAt hy)).differentiableAt

private theorem g_coord_fderiv (j : Fin 3) (y w : Space) : fderiv ℝ (fun z : Space => z j) y w = w j := by
  have h : HasFDerivAt (fun z : Space => z j) (EuclideanSpace.proj j : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt
  rw [h.fderiv]
  simp

private theorem g_rvec_eq (z : Space) : ofComponents (radialVec z) = ‖z‖⁻¹ • z := by
  ext i
  fin_cases i <;> simp [ofComponents, radialVec, div_eq_inv_mul]

private theorem g_pvec_eq (z : Space) : ofComponents (polarVecQ z) = (z 2 * (‖z‖ ^ 2)⁻¹) • z + (-unitVector 2) := by
  ext i
  fin_cases i <;> simp [ofComponents, polarVecQ, qOf, heightRatio, unitVector, div_pow] <;> ring

private theorem g_avec_eq (z : Space) : ofComponents (azimVecQ z) =
    ‖z‖⁻¹ • (z 0 • unitVector 1 + (-z 1) • unitVector 0) := by
  ext i
  fin_cases i <;> simp [ofComponents, azimVecQ, unitVector, div_eq_inv_mul]


private theorem g_inner_self (y : Space) : y 0 * y 0 + y 1 * y 1 + y 2 * y 2 = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_three, sq]

private theorem g_inv_diff {y : Space} (hy : y ≠ 0) : DifferentiableAt ℝ (fun z : Space => ‖z‖⁻¹) y :=
  g_radial_diff (h := fun u => u⁻¹) hy (differentiableAt_inv (norm_ne_zero_iff.2 hy))

private theorem g_inv_fderiv {y : Space} (hy : y ≠ 0) (w : Space) :
    fderiv ℝ (fun z : Space => ‖z‖⁻¹) y w = -((y 0 * w 0 + y 1 * w 1 + y 2 * w 2) / ‖y‖ ^ 3) := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  rw [g_radial_fderiv (h := fun u => u⁻¹) hy (differentiableAt_inv hn) w, deriv_inv]
  field_simp

private theorem g_div_const (v : Space) (y : Space) : divergenceAt (fun _ : Space => v) y = 0 := by
  unfold divergenceAt
  simp

private theorem g_div_rvec {y : Space} (hy : y ≠ 0) : divergenceAt (fun z : Space => ‖z‖⁻¹ • z) y = 2 / ‖y‖ := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  rw [g_div_smul (c := fun z : Space => ‖z‖⁻¹) (W := fun z => z) (g_inv_diff hy) differentiableAt_id, g_div_id,
    g_inv_fderiv hy, g_inner_self]
  field_simp
  ring

private theorem g_div_pvec {y : Space} (hy : y ≠ 0) :
    divergenceAt (fun z : Space => (z 2 * (‖z‖ ^ 2)⁻¹) • z + (-unitVector 2)) y = 2 * y 2 / ‖y‖ ^ 2 := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hc2 : DifferentiableAt ℝ (fun z : Space => z 2) y :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt
  have hsq : DifferentiableAt ℝ (fun z : Space => (‖z‖ ^ 2)⁻¹) y :=
    g_radial_diff (h := fun u => (u ^ 2)⁻¹) hy ((differentiableAt_pow 2).inv (pow_ne_zero 2 hn))
  rw [g_div_add_const, g_div_smul (c := fun z : Space => z 2 * (‖z‖ ^ 2)⁻¹) (W := fun z => z) (hc2.mul hsq)
    differentiableAt_id, g_div_id, fderiv_fun_mul hc2 hsq]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [g_coord_fderiv, g_radial_fderiv (h := fun u => (u ^ 2)⁻¹) hy ((differentiableAt_pow 2).inv (pow_ne_zero 2 hn)),
    g_inner_self]
  rw [show deriv (fun u : ℝ => (u ^ 2)⁻¹) ‖y‖ = _ from ((hasDerivAt_pow 2 ‖y‖).inv (pow_ne_zero 2 hn)).deriv]
  simp only [Nat.cast_ofNat]
  field_simp
  ring

private theorem g_div_avec {y : Space} (hy : y ≠ 0) :
    divergenceAt (fun z : Space => ‖z‖⁻¹ • (z 0 • unitVector 1 + (-z 1) • unitVector 0)) y = 0 := by
  have hc : ∀ j : Fin 3, DifferentiableAt ℝ (fun z : Space => z j) y := fun j =>
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).differentiableAt
  have hJ : DifferentiableAt ℝ (fun z : Space => z 0 • unitVector 1 + (-z 1) • unitVector 0) y :=
    ((hc 0).smul_const _).add ((hc 1).neg.smul_const _)
  rw [g_div_smul (g_inv_diff hy) hJ, g_inv_fderiv hy,
    g_div_add (F := fun z : Space => z 0 • unitVector 1) (G := fun z : Space => (-z 1) • unitVector 0)
      ((hc 0).smul_const _) ((hc 1).neg.smul_const _),
    g_div_smul (c := fun z : Space => z 0) (W := fun _ => unitVector 1) (hc 0) (differentiableAt_const _),
    g_div_smul (c := fun z : Space => -z 1) (W := fun _ => unitVector 0) (hc 1).neg (differentiableAt_const _),
    g_div_const, g_div_const]
  simp [unitVector, g_coord_fderiv]
  left
  ring


private theorem g_T_deriv (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ∃ L : Space →L[ℝ] ℝ, HasFDerivAt (chartT P) L y ∧
      ∀ w, L w = P.L0 / (‖y‖ + P.L0) ^ 2 * ((y 0 * w 0 + y 1 * w 1 + y 2 * w 2) / ‖y‖) := by
  have hL := hP.L0_pos
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hne : ‖y‖ + P.L0 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun u : ℝ => u / (u + P.L0)) (P.L0 / (‖y‖ + P.L0) ^ 2) ‖y‖ := by
    have := (hasDerivAt_id ‖y‖).div ((hasDerivAt_id ‖y‖).add_const P.L0) hne
    rw [show P.L0 / (‖y‖ + P.L0) ^ 2 = (1 * (id ‖y‖ + P.L0) - id ‖y‖ * 1) / (id ‖y‖ + P.L0) ^ 2 by
      simp only [id]; ring]
    exact this
  refine ⟨_, h1.comp_hasFDerivAt y (g_norm_hasFDerivAt hy), fun w => ?_⟩
  have hi : (innerSL ℝ y) w = y 0 * w 0 + y 1 * w 1 + y 2 * w 2 := by
    simp [Fin.sum_univ_three, PiLp.inner_apply, mul_comm]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, hi]
  field_simp
  ring

private theorem g_X_deriv {y : Space} (hy : y ≠ 0) :
    ∃ L : Space →L[ℝ] ℝ, HasFDerivAt heightRatio L y ∧
      ∀ w, L w = w 2 / ‖y‖ - y 2 * (y 0 * w 0 + y 1 * w 1 + y 2 * w 2) / ‖y‖ ^ 3 := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have h2 : HasFDerivAt (fun z : Space => z 2) (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have hi := (hasDerivAt_inv hn).comp_hasFDerivAt y (g_norm_hasFDerivAt hy)
  have e : heightRatio = fun z : Space => z 2 * ‖z‖⁻¹ := funext fun z => by simp [heightRatio, div_eq_mul_inv]
  rw [e]
  refine ⟨_, h2.mul hi, fun w => ?_⟩
  simp [Fin.sum_univ_three, PiLp.inner_apply]
  field_simp
  ring


private theorem g_ell_deriv (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ∃ L : Space →L[ℝ] ℝ, HasFDerivAt (logPhase P) L y ∧
      ∀ w, L w = (y 0 * w 0 + y 1 * w 1 + y 2 * w 2) / (P.rc ^ 2 + ‖y‖ ^ 2) := by
  have hrc := hP.rc_pos
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hpos : (1 : ℝ) + ‖y‖ ^ 2 / P.rc ^ 2 ≠ 0 := by positivity
  have h1 := ((((hasDerivAt_pow 2 ‖y‖).div_const (P.rc ^ 2)).const_add 1).log hpos).const_mul (1 / 2 : ℝ)
  refine ⟨_, h1.comp_hasFDerivAt y (g_norm_hasFDerivAt hy), fun w => ?_⟩
  have hi : (innerSL ℝ y) w = y 0 * w 0 + y 1 * w 1 + y 2 * w 2 := by
    simp [Fin.sum_univ_three, PiLp.inner_apply, mul_comm]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, hi]
  field_simp
  ring

private theorem g_angle_deriv {y : Space} (hy : y 1 ≠ 0) :
    ∃ L : Space →L[ℝ] ℝ, HasFDerivAt angleOf L y ∧
      ∀ w, L w = (y 0 * w 1 - y 1 * w 0) / (y 0 ^ 2 + y 1 ^ 2) := by
  set c : ℂ := ⟨y 0, y 1⟩ with hc
  have hslit : c ∈ Complex.slitPlane := Or.inr hy
  have hc0 : c ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hpl : HasFDerivAt (fun z : Space => (⟨z 0, z 1⟩ : ℂ))
      ((Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ)) +
        (Complex.I • (Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ)))) y := by
    have e : (fun z : Space => (⟨z 0, z 1⟩ : ℂ)) = fun z => ((Complex.ofRealCLM.comp
        (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ)) + (Complex.I • (Complex.ofRealCLM.comp
        (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ)))) z := by
      funext z
      apply Complex.ext <;> simp
    rw [e]
    exact ContinuousLinearMap.hasFDerivAt _
  have hlog := ((Complex.hasStrictDerivAt_log hslit).hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp y hpl
  have him := Complex.imCLM.hasFDerivAt.comp y hlog
  have e2 : angleOf = fun z : Space => Complex.imCLM (Complex.log (⟨z 0, z 1⟩ : ℂ)) := by
    funext z
    simp [angleOf, Complex.log_im]
  rw [e2]
  refine ⟨_, him, fun w => ?_⟩
  have hn : y 0 ^ 2 + y 1 ^ 2 ≠ 0 := by positivity
  simp [Complex.inv_re, Complex.inv_im, Complex.normSq_apply, hc]
  field_simp
  ring


private theorem g_decay_deriv (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ∃ L : Space →L[ℝ] ℝ, HasFDerivAt (decayFactor P) L y ∧
      ∀ w, L w = -(2 * P.eps * decayFactor P y * (y 0 * w 0 + y 1 * w 1 + y 2 * w 2) /
        ((‖y‖ + P.L0) * ‖y‖)) := by
  have hL := hP.L0_pos
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hne : ‖y‖ + P.L0 ≠ 0 := by positivity
  obtain ⟨LT, hT, hTv⟩ := g_T_deriv P hP hy
  have hs : chartS P y = P.L0 / (‖y‖ + P.L0) := by
    unfold chartS chartT
    field_simp
    ring
  have hs0 : chartS P y ≠ 0 := by rw [hs]; positivity
  have h1 : HasFDerivAt (chartS P) (-LT) y := by
    have := hT.const_sub 1
    exact this
  have h2 := h1.rpow_const (p := 2 * P.eps) (Or.inl hs0)
  refine ⟨_, h2, fun w => ?_⟩
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.neg_apply, hTv]
  rw [Real.rpow_sub_one hs0]
  unfold decayFactor
  rw [hs]
  field_simp

private theorem g_phase_deriv (P : ChartParams) (hP : IsChartParams P) (n : ℤ) (β : ℝ) {y : Space} (hy : y 1 ≠ 0) :
    ∃ L : Space →L[ℝ] ℂ, HasFDerivAt (fun z => (decayFactor P z : ℂ) * modePhase P n β z) L y ∧
      ∀ w, L w = (decayFactor P y : ℂ) * modePhase P n β y *
        (((-(2 * P.eps * (y 0 * w 0 + y 1 * w 1 + y 2 * w 2) / ((‖y‖ + P.L0) * ‖y‖))) : ℝ) +
          Complex.I * ((((n * P.m : ℤ) : ℝ) * ((y 0 * w 1 - y 1 * w 0) / (y 0 ^ 2 + y 1 ^ 2)) +
            n * β * ((y 0 * w 0 + y 1 * w 1 + y 2 * w 2) / (P.rc ^ 2 + ‖y‖ ^ 2)) : ℝ) : ℂ)) := by
  have hy0 : y ≠ 0 := fun h => hy (by simp [h])
  obtain ⟨Ld, hd, hdv⟩ := g_decay_deriv P hP hy0
  obtain ⟨La, ha, hav⟩ := g_angle_deriv hy
  obtain ⟨Le, he, hev⟩ := g_ell_deriv P hP hy0
  have hθ := (ha.const_mul (((n * P.m : ℤ) : ℝ))).add (he.const_mul ((n : ℝ) * β))
  have hθc := (Complex.ofRealCLM.hasFDerivAt.comp y hθ).const_mul Complex.I
  have hΦ := hθc.cexp
  have hdc := Complex.ofRealCLM.hasFDerivAt.comp y hd
  have hg := hdc.mul hΦ
  have eΦ : Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * angleOf y + n * β * logPhase P y : ℝ) : ℂ)) =
      modePhase P n β y := rfl
  refine ⟨_, hg, fun w => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, hdv, hav, hev, Function.comp_apply,
    Pi.add_apply, eΦ]
  push_cast
  ring


private theorem g_re_combo (a b c0 c1 c2 : ℂ) (u v w : ℝ) :
    (a * (b * (c0 * u + c1 * v + c2 * w))).re = (a * b * c0).re * u + (a * b * c1).re * v + (a * b * c2).re * w := by
  have e : a * (b * (c0 * u + c1 * v + c2 * w)) = a * b * c0 * u + a * b * c1 * v + a * b * c2 * w := by ring
  rw [e]
  simp only [Complex.add_re, Complex.re_mul_ofReal]

private theorem g_decomp (P : ChartParams) (D : FieldData) (β : ℝ) (n : ℤ) :
    modeFieldOf P D β n = fun z =>
      ((decayFactor P z : ℂ) * modePhase P n β z * reducedField P D n β (chartT P z) (heightRatio z) 0).re •
          (‖z‖⁻¹ • z) +
        ((decayFactor P z : ℂ) * modePhase P n β z * reducedField P D n β (chartT P z) (heightRatio z) 1).re •
          ((z 2 * (‖z‖ ^ 2)⁻¹) • z + (-unitVector 2)) +
        ((decayFactor P z : ℂ) * modePhase P n β z * reducedField P D n β (chartT P z) (heightRatio z) 2).re •
          (‖z‖⁻¹ • (z 0 • unitVector 1 + (-z 1) • unitVector 0)) := by
  funext z
  rw [← g_rvec_eq, ← g_pvec_eq, ← g_avec_eq]
  ext i
  simp only [modeFieldOf, ofComponents_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, g_re_combo]

private theorem g_part_deriv {G : Space → ℂ} {LG : Space →L[ℝ] ℂ} {T X : Space → ℝ} {LT LX : Space →L[ℝ] ℝ}
    {R : ℝ × ℝ → ℂ} {y : Space} (hG : HasFDerivAt G LG y) (hT : HasFDerivAt T LT y) (hX : HasFDerivAt X LX y)
    (hR : DifferentiableAt ℝ R (T y, X y)) :
    DifferentiableAt ℝ (fun z => (G z * R (T z, X z)).re) y ∧ ∀ w,
      fderiv ℝ (fun z => (G z * R (T z, X z)).re) y w =
        (LG w * R (T y, X y) + G y * (LT w * deriv (fun t' => R (t', X y)) (T y) +
          LX w * deriv (fun x' => R (T y, x')) (X y))).re := by
  have hTX : HasFDerivAt (fun z => (T z, X z)) (LT.prod LX) y := hT.prodMk hX
  have hRc := hR.hasFDerivAt.comp y hTX
  have hm := hG.mul hRc
  have hre : HasFDerivAt (fun z => (G z * R (T z, X z)).re) _ y := Complex.reCLM.hasFDerivAt.comp y hm
  refine ⟨hre.differentiableAt, fun w => ?_⟩
  rw [hre.fderiv]
  have ht : HasDerivAt (fun t' : ℝ => ((t', X y) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) (T y) :=
    (hasDerivAt_id (T y)).prodMk (hasDerivAt_const (T y) (X y))
  have hx : HasDerivAt (fun x' : ℝ => ((T y, x') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) (X y) :=
    (hasDerivAt_const (X y) (T y)).prodMk (hasDerivAt_id (X y))
  have d1 := (hR.hasFDerivAt.comp_hasDerivAt (T y) ht).deriv
  have d2 := (hR.hasFDerivAt.comp_hasDerivAt (X y) hx).deriv
  have hsplit : fderiv ℝ R (T y, X y) (LT w, LX w) =
      LT w * fderiv ℝ R (T y, X y) ((1 : ℝ), (0 : ℝ)) + LX w * fderiv ℝ R (T y, X y) ((0 : ℝ), (1 : ℝ)) := by
    have e : ((LT w, LX w) : ℝ × ℝ) = LT w • ((1 : ℝ), (0 : ℝ)) + LX w • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [e, map_add, map_smul, map_smul]
    simp [Complex.real_smul]
  simp only [Function.comp_def] at d1 d2
  rw [d1, d2]
  simp [hsplit]
  ring


private theorem g_main {P : ChartParams} (hP : IsChartParams P) (D : FieldData) (β : ℝ) (n : ℤ)
    {y : Space} (hy : y 1 ≠ 0)
    (hR : ∀ k : Fin 3, DifferentiableAt ℝ (fun q : ℝ × ℝ => reducedField P D n β q.1 q.2 k)
      ((chartT P y, heightRatio y) : ℝ × ℝ)) :
    divergenceAt (modeFieldOf P D β n) y =
      ((decayFactor P y : ℂ) * modePhase P n β y *
        reducedDivergence P D n β (chartT P y) (heightRatio y)).re / ‖y‖ := by
  have hy0 : y ≠ 0 := fun h => hy (by simp [h])
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy0
  have hL := hP.L0_pos
  have hrc := hP.rc_pos
  have hne : ‖y‖ + P.L0 ≠ 0 := by positivity
  have hρ : y 0 ^ 2 + y 1 ^ 2 ≠ 0 := by positivity
  have hr2 : y 0 * y 0 + y 1 * y 1 + y 2 * y 2 = ‖y‖ ^ 2 := g_inner_self y
  obtain ⟨LG, hG, hGv⟩ := g_phase_deriv P hP n β hy
  obtain ⟨LT, hT, hTv⟩ := g_T_deriv P hP hy0
  obtain ⟨LX, hX, hXv⟩ := g_X_deriv hy0
  have hp : ∀ k : Fin 3, DifferentiableAt ℝ (fun z => ((decayFactor P z : ℂ) * modePhase P n β z *
      reducedField P D n β (chartT P z) (heightRatio z) k).re) y ∧ ∀ w,
      fderiv ℝ (fun z => ((decayFactor P z : ℂ) * modePhase P n β z *
        reducedField P D n β (chartT P z) (heightRatio z) k).re) y w =
        (LG w * reducedField P D n β (chartT P y) (heightRatio y) k +
          (decayFactor P y : ℂ) * modePhase P n β y *
            (LT w * deriv (fun t' => reducedField P D n β t' (heightRatio y) k) (chartT P y) +
              LX w * deriv (fun x' => reducedField P D n β (chartT P y) x' k) (heightRatio y))).re :=
    fun k => g_part_deriv (R := fun q : ℝ × ℝ => reducedField P D n β q.1 q.2 k) hG hT hX (hR k)
  have hc : ∀ j : Fin 3, DifferentiableAt ℝ (fun z : Space => z j) y := fun j =>
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).differentiableAt
  have hsq : DifferentiableAt ℝ (fun z : Space => (‖z‖ ^ 2)⁻¹) y :=
    g_radial_diff (h := fun u => (u ^ 2)⁻¹) hy0 ((differentiableAt_pow 2).inv (pow_ne_zero 2 hn))
  have hW0 : DifferentiableAt ℝ (fun z : Space => ‖z‖⁻¹ • z) y := (g_inv_diff hy0).smul differentiableAt_id
  have hW1 : DifferentiableAt ℝ (fun z : Space => (z 2 * (‖z‖ ^ 2)⁻¹) • z + (-unitVector 2)) y :=
    (((hc 2).mul hsq).smul differentiableAt_id).add_const _
  have hW2 : DifferentiableAt ℝ (fun z : Space => ‖z‖⁻¹ • (z 0 • unitVector 1 + (-z 1) • unitVector 0)) y :=
    (g_inv_diff hy0).smul (((hc 0).smul_const _).add ((hc 1).neg.smul_const _))
  obtain ⟨a, ha⟩ : ∃ a : Fin 3 → Space → ℝ, a = fun k z => ((decayFactor P z : ℂ) * modePhase P n β z *
      reducedField P D n β (chartT P z) (heightRatio z) k).re := ⟨_, rfl⟩
  have hdec : modeFieldOf P D β n = fun z => a 0 z • (‖z‖⁻¹ • z) +
      a 1 z • ((z 2 * (‖z‖ ^ 2)⁻¹) • z + (-unitVector 2)) +
      a 2 z • (‖z‖⁻¹ • (z 0 • unitVector 1 + (-z 1) • unitVector 0)) := by
    rw [ha]
    exact g_decomp P D β n
  have hp' : ∀ k : Fin 3, DifferentiableAt ℝ (a k) y ∧ ∀ w, fderiv ℝ (a k) y w =
        (LG w * reducedField P D n β (chartT P y) (heightRatio y) k +
          (decayFactor P y : ℂ) * modePhase P n β y *
            (LT w * deriv (fun t' => reducedField P D n β t' (heightRatio y) k) (chartT P y) +
              LX w * deriv (fun x' => reducedField P D n β (chartT P y) x' k) (heightRatio y))).re := by
    rw [ha]
    exact hp
  have hay : ∀ k, a k y = ((decayFactor P y : ℂ) * modePhase P n β y *
      reducedField P D n β (chartT P y) (heightRatio y) k).re := fun k => by rw [ha]
  have d0 : DifferentiableAt ℝ (fun z => a 0 z • (‖z‖⁻¹ • z)) y := (hp' 0).1.smul hW0
  have d1 : DifferentiableAt ℝ (fun z => a 1 z • ((z 2 * (‖z‖ ^ 2)⁻¹) • z + (-unitVector 2))) y :=
    (hp' 1).1.smul hW1
  have d2 : DifferentiableAt ℝ (fun z => a 2 z • (‖z‖⁻¹ • (z 0 • unitVector 1 + (-z 1) • unitVector 0))) y :=
    (hp' 2).1.smul hW2
  have d01 : DifferentiableAt ℝ (fun z => a 0 z • (‖z‖⁻¹ • z) +
      a 1 z • ((z 2 * (‖z‖ ^ 2)⁻¹) • z + (-unitVector 2))) y := d0.add d1
  rw [hdec, g_div_add d01 d2, g_div_add d0 d1, g_div_smul (hp' 0).1 hW0, g_div_smul (hp' 1).1 hW1,
    g_div_smul (hp' 2).1 hW2, g_div_rvec hy0, g_div_pvec hy0, g_div_avec hy0, (hp' 0).2, (hp' 1).2, (hp' 2).2,
    hay, hay, hay]
  have i0 : y 0 * (‖y‖⁻¹ • y) 0 + y 1 * (‖y‖⁻¹ • y) 1 + y 2 * (‖y‖⁻¹ • y) 2 = ‖y‖ := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    field_simp
    linear_combination hr2
  have i1 : y 0 * ((y 2 * (‖y‖ ^ 2)⁻¹) • y + (-unitVector 2)) 0 + y 1 * ((y 2 * (‖y‖ ^ 2)⁻¹) • y + (-unitVector 2)) 1 +
      y 2 * ((y 2 * (‖y‖ ^ 2)⁻¹) • y + (-unitVector 2)) 2 = 0 := by
    simp [unitVector]
    field_simp
    linear_combination y 2 * hr2
  have i2 : y 0 * (‖y‖⁻¹ • (y 0 • unitVector 1 + (-y 1) • unitVector 0)) 0 +
      y 1 * (‖y‖⁻¹ • (y 0 • unitVector 1 + (-y 1) • unitVector 0)) 1 +
      y 2 * (‖y‖⁻¹ • (y 0 • unitVector 1 + (-y 1) • unitVector 0)) 2 = 0 := by
    simp [unitVector]
    ring
  have a0 : (y 0 * (‖y‖⁻¹ • y) 1 - y 1 * (‖y‖⁻¹ • y) 0) = 0 := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have a1 : (y 0 * ((y 2 * (‖y‖ ^ 2)⁻¹) • y + (-unitVector 2)) 1 -
      y 1 * ((y 2 * (‖y‖ ^ 2)⁻¹) • y + (-unitVector 2)) 0) = 0 := by
    simp [unitVector]
    ring
  have a2 : (y 0 * (‖y‖⁻¹ • (y 0 • unitVector 1 + (-y 1) • unitVector 0)) 1 -
      y 1 * (‖y‖⁻¹ • (y 0 • unitVector 1 + (-y 1) • unitVector 0)) 0) = (y 0 ^ 2 + y 1 ^ 2) / ‖y‖ := by
    simp [unitVector]
    field_simp
  have c0 : (‖y‖⁻¹ • y) 2 = y 2 / ‖y‖ := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have c1 : ((y 2 * (‖y‖ ^ 2)⁻¹) • y + (-unitVector 2)) 2 = y 2 ^ 2 / ‖y‖ ^ 2 - 1 := by
    simp [unitVector]
    ring
  have c2 : (‖y‖⁻¹ • (y 0 • unitVector 1 + (-y 1) • unitVector 0)) 2 = 0 := by
    simp [unitVector]
  rw [hGv, hGv, hGv, hTv, hTv, hTv, hXv, hXv, hXv, i0, i1, i2, a0, a1, a2, c0, c1, c2]
  have hR1x : DifferentiableAt ℝ (fun x' => reducedField P D n β (chartT P y) x' 1) (heightRatio y) :=
    (hR 1).comp (heightRatio y) ((hasDerivAt_const (heightRatio y) (chartT P y)).prodMk
      (hasDerivAt_id (heightRatio y))).differentiableAt
  have hq : HasDerivAt (fun x' : ℝ => ((1 - x' ^ 2 : ℝ) : ℂ)) ((-(2 * heightRatio y) : ℝ) : ℂ) (heightRatio y) := by
    have := ((hasDerivAt_pow 2 (heightRatio y)).const_sub 1).ofReal_comp
    convert this using 2
    push_cast
    ring
  have hhd : heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * reducedField P D n β t' x' 1) (chartT P y)
      (heightRatio y) = ((-(2 * heightRatio y) : ℝ) : ℂ) * reducedField P D n β (chartT P y) (heightRatio y) 1 +
        ((1 - heightRatio y ^ 2 : ℝ) : ℂ) * deriv (fun x' => reducedField P D n β (chartT P y) x' 1) (heightRatio y) := by
    unfold heightDeriv
    rw [deriv_fun_mul hq.differentiableAt hR1x, hq.deriv]
  have ht : chartT P y = ‖y‖ / (‖y‖ + P.L0) := rfl
  have hx : heightRatio y = y 2 / ‖y‖ := rfl
  have hcr : coreRatioT P (‖y‖ / (‖y‖ + P.L0)) = ‖y‖ ^ 2 / (P.rc ^ 2 + ‖y‖ ^ 2) := by
    unfold coreRatioT
    field_simp
    ring
  unfold reducedDivergence
  rw [hhd]
  unfold twistedScale radialScale
  rw [ht, hx, hcr]
  simp only [← Complex.re_mul_ofReal, ← Complex.add_re]
  rw [← Complex.div_ofReal_re]
  congr 1
  have hnC : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hneC : (‖y‖ : ℂ) + P.L0 ≠ 0 := by exact_mod_cast hne
  have hrcC : (P.rc : ℂ) ^ 2 + (‖y‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (by positivity : P.rc ^ 2 + ‖y‖ ^ 2 ≠ 0)
  have hρC : (y 0 : ℂ) ^ 2 + (y 1 : ℂ) ^ 2 ≠ 0 := by
    have h := Complex.ofReal_ne_zero.2 hρ
    push_cast at h
    exact h
  push_cast
  field_simp
  ring

theorem modeFieldOf_divergence_eq {P : ChartParams} (hP : IsChartParams P) (D : FieldData) (β : ℝ) (n : ℤ)
    {y : Space} (hy : y 1 ≠ 0)
    (hR : ∀ k : Fin 3, DifferentiableAt ℝ (fun q : ℝ × ℝ => reducedField P D n β q.1 q.2 k)
      ((chartT P y, heightRatio y) : ℝ × ℝ)) :
    divergenceAt (modeFieldOf P D β n) y =
      ((decayFactor P y : ℂ) * modePhase P n β y *
        reducedDivergence P D n β (chartT P y) (heightRatio y)).re / ‖y‖ :=
  g_main hP D β n hy hR

private theorem partials_eventually {G : ℝ × ℝ → ℂ} {z : ℝ × ℝ} (hG : ContDiffAt ℝ 2 G z) :
    ∀ᶠ w in nhds z, deriv (fun x' => G (w.1, x')) w.2 = fderiv ℝ G w ((0 : ℝ), (1 : ℝ)) ∧
      deriv (fun t' => G (t', w.2)) w.1 = fderiv ℝ G w ((1 : ℝ), (0 : ℝ)) := by
  filter_upwards [hG.eventually (by simp)] with w hw
  have hd : DifferentiableAt ℝ G w := hw.differentiableAt (by norm_num)
  have hx : HasDerivAt (fun x' : ℝ => ((w.1, x') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) w.2 :=
    (hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id w.2)
  have ht : HasDerivAt (fun t' : ℝ => ((t', w.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) w.1 :=
    (hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2)
  exact ⟨(hd.hasFDerivAt.comp_hasDerivAt w.2 hx).deriv, (hd.hasFDerivAt.comp_hasDerivAt w.1 ht).deriv⟩

private theorem mixed_partials {G : ℝ × ℝ → ℂ} {t x : ℝ} (hG : ContDiffAt ℝ 2 G (t, x)) :
    deriv (fun t' => deriv (fun x' => G (t', x')) x) t = deriv (fun x' => deriv (fun t' => G (t', x')) t) x ∧
      DifferentiableAt ℝ (fun x' => deriv (fun t' => G (t', x')) t) x ∧
      DifferentiableAt ℝ (fun t' => deriv (fun x' => G (t', x')) x) t := by
  have hD2 : DifferentiableAt ℝ (fderiv ℝ G) (t, x) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym := hG.isSymmSndFDerivAt (by simp)
  have hev := partials_eventually hG
  have hx : HasDerivAt (fun x' : ℝ => ((t, x') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) x :=
    (hasDerivAt_const x t).prodMk (hasDerivAt_id x)
  have ht : HasDerivAt (fun t' : ℝ => ((t', x) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have e1 : (fun t' => deriv (fun x' => G (t', x')) x) =ᶠ[nhds t]
      fun t' => fderiv ℝ G (t', x) ((0 : ℝ), (1 : ℝ)) :=
    (ht.continuousAt.tendsto.eventually hev).mono fun t' h => h.1
  have e2 : (fun x' => deriv (fun t' => G (t', x')) t) =ᶠ[nhds x]
      fun x' => fderiv ℝ G (t, x') ((1 : ℝ), (0 : ℝ)) :=
    (hx.continuousAt.tendsto.eventually hev).mono fun x' h => h.2
  have d1 : HasDerivAt (fun t' => fderiv ℝ G (t', x) ((0 : ℝ), (1 : ℝ)))
      (fderiv ℝ (fderiv ℝ G) (t, x) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))) t := by
    have := (hD2.hasFDerivAt.comp_hasDerivAt t ht)
    exact this.clm_apply (hasDerivAt_const t ((0 : ℝ), (1 : ℝ)))  |>.congr_deriv (by simp)
  have d2 : HasDerivAt (fun x' => fderiv ℝ G (t, x') ((1 : ℝ), (0 : ℝ)))
      (fderiv ℝ (fderiv ℝ G) (t, x) ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))) x := by
    have := (hD2.hasFDerivAt.comp_hasDerivAt x hx)
    exact this.clm_apply (hasDerivAt_const x ((1 : ℝ), (0 : ℝ)))  |>.congr_deriv (by simp)
  refine ⟨?_, (d2.congr_of_eventuallyEq e2).differentiableAt, (d1.congr_of_eventuallyEq e1).differentiableAt⟩
  rw [(d1.congr_of_eventuallyEq e1).deriv, (d2.congr_of_eventuallyEq e2).deriv]
  exact hsym _ _


theorem modeFieldOf_differentiableAt_of {P : ChartParams} (hP : IsChartParams P) (D : FieldData) (β : ℝ)
    (n : ℤ) {y : Space} (hy : y 1 ≠ 0)
    (hR : ∀ k : Fin 3, DifferentiableAt ℝ (fun q : ℝ × ℝ => reducedField P D n β q.1 q.2 k)
      ((chartT P y, heightRatio y) : ℝ × ℝ)) :
    DifferentiableAt ℝ (modeFieldOf P D β n) y := by
  have hy0 : y ≠ 0 := fun h => hy (by simp [h])
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy0
  obtain ⟨LG, hG, -⟩ := g_phase_deriv P hP n β hy
  obtain ⟨LT, hT, -⟩ := g_T_deriv P hP hy0
  obtain ⟨LX, hX, -⟩ := g_X_deriv hy0
  have hp : ∀ k : Fin 3, DifferentiableAt ℝ (fun z => ((decayFactor P z : ℂ) * modePhase P n β z *
      reducedField P D n β (chartT P z) (heightRatio z) k).re) y :=
    fun k => (g_part_deriv (R := fun q : ℝ × ℝ => reducedField P D n β q.1 q.2 k) hG hT hX (hR k)).1
  have hc : ∀ j : Fin 3, DifferentiableAt ℝ (fun z : Space => z j) y := fun j =>
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).differentiableAt
  have hsq : DifferentiableAt ℝ (fun z : Space => (‖z‖ ^ 2)⁻¹) y :=
    g_radial_diff (h := fun u => (u ^ 2)⁻¹) hy0 ((differentiableAt_pow 2).inv (pow_ne_zero 2 hn))
  rw [g_decomp]
  exact (((hp 0).smul ((g_inv_diff hy0).smul differentiableAt_id)).add
    ((hp 1).smul ((((hc 2).mul hsq).smul differentiableAt_id).add_const _))).add
    ((hp 2).smul ((g_inv_diff hy0).smul (((hc 0).smul_const _).add ((hc 1).neg.smul_const _))))

theorem reducedField_differentiableAt_generic (P : ChartParams) (hP : IsChartParams P) (D : FieldData)
    (n : ℤ) (β : ℝ) {t x : ℝ} (hx0 : x ≠ 0)
    (hgen : ∀ S ∈ [(D.amp n).radialAmp, (D.amp n).polarAmp, (D.amp n).streamAmp, (D.amp n).swirlAmp],
      t ∉ S.mesh.tBreaks ∧ |x| ∉ S.mesh.xBreaks) (k : Fin 3) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => reducedField P D n β q.1 q.2 k) ((t, x) : ℝ × ℝ) := by
  have h := FieldJoint.reduced_contDiffAt P hP D n hx0 hgen β k
  have hl : DifferentiableAt ℝ (fun q : ℝ × ℝ => ((β, q.1, q.2) : ℝ × ℝ × ℝ)) ((t, x) : ℝ × ℝ) := by
    fun_prop
  exact (h.differentiableAt (by simp)).comp ((t, x) : ℝ × ℝ) hl

theorem reducedDivergence_mean_eq_zero (P : ChartParams) (D : FieldData) (β : ℝ) {t x : ℝ} (hx : x ≠ 0)
    (ht : t ∉ (D.amp 0).streamAmp.mesh.tBreaks) (hxb : |x| ∉ (D.amp 0).streamAmp.mesh.xBreaks) :
    reducedDivergence P D 0 β t x = 0 := by
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ × ℝ → ℂ, H = fun z => ((1 - z.2 ^ 2 : ℝ) : ℂ) *
      (weightPoly 1 D.highOrder z.1 * (D.amp 0).streamAmp.eval true z.1 z.2) := ⟨_, rfl⟩
  have hΨ : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => (D.amp 0).streamAmp.eval true z.1 z.2) (t, x) := by
    obtain ⟨Q, hQ, hev⟩ := spline_eventually_poly (D.amp 0).streamAmp true t x ht hxb hx
    exact (hQ.contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)).congr_of_eventuallyEq hev
  have hpc : ContDiff ℝ 2 (fun t' : ℝ => weightPoly 1 D.highOrder t') := by
    have h1 : ContDiff ℝ 2 (fun t' : ℝ => t' ^ 1 * (1 - t') ^ D.highOrder) := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp h1
  have hqc : ContDiff ℝ 2 (fun x' : ℝ => ((1 - x' ^ 2 : ℝ) : ℂ)) := by
    have h1 : ContDiff ℝ 2 (fun x' : ℝ => 1 - x' ^ 2) := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp h1
  have hH : ContDiffAt ℝ 2 H (t, x) := by
    rw [hHdef]
    exact (hqc.contDiffAt.comp (t, x) contDiffAt_snd).mul ((hpc.contDiffAt.comp (t, x) contDiffAt_fst).mul hΨ)
  obtain ⟨hmix, hdx, -⟩ := mixed_partials hH
  have hneg : ∀ (g : ℝ → ℂ) (s : ℝ), deriv (fun y => -g y) s = -deriv g s := fun g s => deriv.neg
  have hR0 : (fun t' x' => reducedField P D 0 β t' x' 0) = fun t' x' => -(deriv (fun x'' => H (t', x'')) x') := by
    funext t' x'
    rw [hHdef]
    simp only [reducedField, if_pos rfl, Matrix.cons_val_zero, heightDeriv]
    rw [show (fun x'' : ℝ => ((1 - x'' ^ 2 : ℝ) : ℂ) * (weightPoly 1 D.highOrder t' *
        (D.amp 0).streamAmp.eval true t' x'')) = fun x'' => weightPoly 1 D.highOrder t' *
        (((1 - x'' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t' x'') from
      funext fun x'' => by ring, deriv_const_mul_field]
  have hR1 : (fun x' => ((1 - x' ^ 2 : ℝ) : ℂ) * reducedField P D 0 β t x' 1) = fun x' =>
      -(((t * (1 - t) : ℝ) : ℂ) * deriv (fun s => H (s, x')) t + (2 - ((2 * P.eps * t : ℝ) : ℂ)) * H (t, x')) := by
    funext x'
    rw [hHdef]
    simp only [reducedField, if_pos rfl, Matrix.cons_val_one, Matrix.cons_val_zero, twistedScale, radialScale]
    rw [deriv_const_mul_field]
    simp only [Int.cast_zero, zero_mul, Complex.ofReal_zero, mul_zero, zero_sub]
    ring
  have hHx : DifferentiableAt ℝ (fun x' => H (t, x')) x :=
    (hH.differentiableAt (by norm_num)).comp x
      ((hasDerivAt_const x t).prodMk (hasDerivAt_id x)).differentiableAt
  have hR0' : reducedField P D 0 β t x 0 = -(deriv (fun x'' => H (t, x'')) x) := congrFun (congrFun hR0 t) x
  unfold reducedDivergence heightDeriv
  rw [hR0, hR1, hR0']
  simp only [twistedScale, radialScale, Int.cast_zero, zero_mul, Complex.ofReal_zero, mul_zero, zero_sub]
  rw [hneg, hneg, deriv_fun_add (hdx.const_mul _) (hHx.const_mul _), deriv_const_mul _ hdx,
    deriv_const_mul _ hHx, hmix]
  ring

end FracInternal

end Breakdown
