import Breakdown.CertCell.ShapeStatements

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (radialVec polarVecQ azimVecQ heightRatio qOf radialScale heightDeriv)

namespace SphericalDivInternal

theorem inner_coords (y w : Space) : (innerSL ℝ y) w = y 0 * w 0 + y 1 * w 1 + y 2 * w 2 := by
  simp [Fin.sum_univ_three, PiLp.inner_apply, mul_comm]

theorem coords_sq (y : Space) : y 0 * y 0 + y 1 * y 1 + y 2 * y 2 = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_three, sq]

theorem norm_hasFDerivAt {y : Space} (hy : y ≠ 0) :
    HasFDerivAt (fun z : Space => ‖z‖) ((1 / (2 * ‖y‖)) • (2 • innerSL ℝ y)) y := by
  have h := ((hasStrictFDerivAt_norm_sq y).hasFDerivAt).sqrt (by positivity)
  have e : (fun z : Space => Real.sqrt (‖z‖ ^ 2)) = fun z => ‖z‖ := funext fun z => Real.sqrt_sq (norm_nonneg z)
  rw [e, Real.sqrt_sq (norm_nonneg y)] at h
  exact h

theorem norm_fderiv {y : Space} (hy : y ≠ 0) (w : Space) :
    fderiv ℝ (fun z : Space => ‖z‖) y w = (y 0 * w 0 + y 1 * w 1 + y 2 * w 2) / ‖y‖ := by
  rw [(norm_hasFDerivAt hy).fderiv]
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, inner_coords]
  field_simp
  ring

theorem radial_fderiv {h : ℝ → ℝ} {y : Space} (hy : y ≠ 0) (hh : DifferentiableAt ℝ h ‖y‖) (w : Space) :
    fderiv ℝ (fun z : Space => h ‖z‖) y w = deriv h ‖y‖ * ((y 0 * w 0 + y 1 * w 1 + y 2 * w 2) / ‖y‖) := by
  have hc := hh.hasDerivAt.comp_hasFDerivAt y (norm_hasFDerivAt hy)
  rw [show (fun z : Space => h ‖z‖) = h ∘ fun z => ‖z‖ from rfl, hc.fderiv, ← norm_fderiv hy w,
    (norm_hasFDerivAt hy).fderiv]
  simp

theorem radial_diff {h : ℝ → ℝ} {y : Space} (hy : y ≠ 0) (hh : DifferentiableAt ℝ h ‖y‖) :
    DifferentiableAt ℝ (fun z : Space => h ‖z‖) y :=
  (hh.hasDerivAt.comp_hasFDerivAt y (norm_hasFDerivAt hy)).differentiableAt

theorem coord_fderiv (j : Fin 3) (y w : Space) : fderiv ℝ (fun z : Space => z j) y w = w j := by
  have h : HasFDerivAt (fun z : Space => z j) (EuclideanSpace.proj j : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt
  rw [h.fderiv]
  simp

theorem coord_diff (j : Fin 3) (y : Space) : DifferentiableAt ℝ (fun z : Space => z j) y :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).differentiableAt

theorem inv_diff {y : Space} (hy : y ≠ 0) : DifferentiableAt ℝ (fun z : Space => ‖z‖⁻¹) y :=
  radial_diff (h := fun u => u⁻¹) hy (differentiableAt_inv (norm_ne_zero_iff.2 hy))

theorem inv_fderiv {y : Space} (hy : y ≠ 0) (w : Space) :
    fderiv ℝ (fun z : Space => ‖z‖⁻¹) y w = -((y 0 * w 0 + y 1 * w 1 + y 2 * w 2) / ‖y‖ ^ 3) := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  rw [radial_fderiv (h := fun u => u⁻¹) hy (differentiableAt_inv hn) w, deriv_inv]
  field_simp

theorem inv_sq_diff {y : Space} (hy : y ≠ 0) : DifferentiableAt ℝ (fun z : Space => (‖z‖ ^ 2)⁻¹) y :=
  radial_diff (h := fun u => (u ^ 2)⁻¹) hy
    ((differentiableAt_pow 2).inv (pow_ne_zero 2 (norm_ne_zero_iff.2 hy)))

theorem div_smul {c : Space → ℝ} {W : Space → Space} {y : Space} (hc : DifferentiableAt ℝ c y)
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

theorem div_add {F G : Space → Space} {y : Space} (hF : DifferentiableAt ℝ F y)
    (hG : DifferentiableAt ℝ G y) :
    divergenceAt (fun z => F z + G z) y = divergenceAt F y + divergenceAt G y := by
  unfold divergenceAt
  rw [fderiv_fun_add hF hG]
  simp [Finset.sum_add_distrib]

theorem div_add_const {F : Space → Space} {y : Space} (v : Space) :
    divergenceAt (fun z => F z + v) y = divergenceAt F y := by
  unfold divergenceAt
  rw [fderiv_add_const]

theorem div_id (y : Space) : divergenceAt (fun z : Space => z) y = 3 := by
  unfold divergenceAt
  rw [fderiv_fun_id]
  simp [unitVector]

theorem div_const (v : Space) (y : Space) : divergenceAt (fun _ : Space => v) y = 0 := by
  unfold divergenceAt
  simp

def radialField (z : Space) : Space := ‖z‖⁻¹ • z

def polarField (z : Space) : Space := (z 2 * (‖z‖ ^ 2)⁻¹) • z + (-unitVector 2)

def azimField (z : Space) : Space := ‖z‖⁻¹ • (z 0 • unitVector 1 + (-z 1) • unitVector 0)

theorem radialField_apply (z : Space) (i : Fin 3) : radialField z i = radialVec z i := by
  simp [radialField, radialVec, div_eq_inv_mul]

theorem polarField_apply (z : Space) (i : Fin 3) : polarField z i = polarVecQ z i := by
  fin_cases i <;> simp [polarField, polarVecQ, qOf, heightRatio, unitVector, div_pow] <;> ring

theorem azimField_apply (z : Space) (i : Fin 3) : azimField z i = azimVecQ z i := by
  fin_cases i <;> simp [azimField, azimVecQ, unitVector, div_eq_inv_mul]

theorem radialField_diff {y : Space} (hy : y ≠ 0) : DifferentiableAt ℝ radialField y :=
  (inv_diff hy).smul differentiableAt_id

theorem polarField_diff {y : Space} (hy : y ≠ 0) : DifferentiableAt ℝ polarField y :=
  (((coord_diff 2 y).mul (inv_sq_diff hy)).smul differentiableAt_id).add_const _

theorem azimField_diff {y : Space} (hy : y ≠ 0) : DifferentiableAt ℝ azimField y :=
  (inv_diff hy).smul (((coord_diff 0 y).smul_const _).add ((coord_diff 1 y).neg.smul_const _))

theorem div_radialField {y : Space} (hy : y ≠ 0) : divergenceAt radialField y = 2 / ‖y‖ := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  unfold radialField
  rw [div_smul (c := fun z : Space => ‖z‖⁻¹) (W := fun z => z) (inv_diff hy) differentiableAt_id, div_id,
    inv_fderiv hy, coords_sq]
  field_simp
  ring

theorem div_polarField {y : Space} (hy : y ≠ 0) : divergenceAt polarField y = 2 * y 2 / ‖y‖ ^ 2 := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hc2 := coord_diff 2 y
  have hsq := inv_sq_diff hy
  unfold polarField
  rw [div_add_const, div_smul (c := fun z : Space => z 2 * (‖z‖ ^ 2)⁻¹) (W := fun z => z) (hc2.mul hsq)
    differentiableAt_id, div_id, fderiv_fun_mul hc2 hsq]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [coord_fderiv, radial_fderiv (h := fun u => (u ^ 2)⁻¹) hy ((differentiableAt_pow 2).inv (pow_ne_zero 2 hn)),
    coords_sq]
  rw [show deriv (fun u : ℝ => (u ^ 2)⁻¹) ‖y‖ = _ from ((hasDerivAt_pow 2 ‖y‖).inv (pow_ne_zero 2 hn)).deriv]
  simp only [Nat.cast_ofNat]
  field_simp
  ring

theorem div_azimField {y : Space} (hy : y ≠ 0) : divergenceAt azimField y = 0 := by
  have hc := fun j : Fin 3 => coord_diff j y
  have hJ : DifferentiableAt ℝ (fun z : Space => z 0 • unitVector 1 + (-z 1) • unitVector 0) y :=
    ((hc 0).smul_const _).add ((hc 1).neg.smul_const _)
  unfold azimField
  rw [div_smul (inv_diff hy) hJ, inv_fderiv hy,
    div_add (F := fun z : Space => z 0 • unitVector 1) (G := fun z : Space => (-z 1) • unitVector 0)
      ((hc 0).smul_const _) ((hc 1).neg.smul_const _),
    div_smul (c := fun z : Space => z 0) (W := fun _ => unitVector 1) (hc 0) (differentiableAt_const _),
    div_smul (c := fun z : Space => -z 1) (W := fun _ => unitVector 0) (hc 1).neg (differentiableAt_const _),
    div_const, div_const]
  simp [unitVector, coord_fderiv]
  left
  ring


theorem chartCoord_hasFDerivAt (P : ShapeParams) (hL : 0 < P.chartLength) {y : Space} (hy : y ≠ 0) :
    ∃ L : Space →L[ℝ] ℝ, HasFDerivAt (chartCoord P) L y ∧
      ∀ w, L w = P.chartLength / (‖y‖ + P.chartLength) ^ 2 * ((y 0 * w 0 + y 1 * w 1 + y 2 * w 2) / ‖y‖) := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hne : ‖y‖ + P.chartLength ≠ 0 := by positivity
  have h1 : HasDerivAt (fun u : ℝ => u / (u + P.chartLength)) (P.chartLength / (‖y‖ + P.chartLength) ^ 2) ‖y‖ := by
    have := (hasDerivAt_id ‖y‖).div ((hasDerivAt_id ‖y‖).add_const P.chartLength) hne
    rw [show P.chartLength / (‖y‖ + P.chartLength) ^ 2 =
      (1 * (id ‖y‖ + P.chartLength) - id ‖y‖ * 1) / (id ‖y‖ + P.chartLength) ^ 2 by simp only [id]; ring]
    exact this
  refine ⟨_, h1.comp_hasFDerivAt y (norm_hasFDerivAt hy), fun w => ?_⟩
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, inner_coords]
  field_simp
  ring

theorem heightRatio_hasFDerivAt {y : Space} (hy : y ≠ 0) :
    ∃ L : Space →L[ℝ] ℝ, HasFDerivAt heightRatio L y ∧
      ∀ w, L w = w 2 / ‖y‖ - y 2 * (y 0 * w 0 + y 1 * w 1 + y 2 * w 2) / ‖y‖ ^ 3 := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have h2 : HasFDerivAt (fun z : Space => z 2) (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have hi := (hasDerivAt_inv hn).comp_hasFDerivAt y (norm_hasFDerivAt hy)
  have e : heightRatio = fun z : Space => z 2 * ‖z‖⁻¹ := funext fun z => by simp [heightRatio, div_eq_mul_inv]
  rw [e]
  refine ⟨_, h2.mul hi, fun w => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul,
    inner_coords, Function.comp_apply]
  simp
  field_simp
  ring

theorem radialPhase_hasFDerivAt {f : ℝ → ℝ} (hf : IsRadialPhase f) (y : Space) :
    ∃ L : Space →L[ℝ] ℝ, HasFDerivAt (fun z : Space => f (‖z‖ ^ 2)) L y ∧
      ∀ w, L w = deriv f (‖y‖ ^ 2) * (2 * (y 0 * w 0 + y 1 * w 1 + y 2 * w 2)) := by
  obtain ⟨δ, hδ, hc⟩ := hf.smooth
  have hmem : ‖y‖ ^ 2 ∈ Set.Ioi (-δ) := by
    simp only [Set.mem_Ioi]
    nlinarith [sq_nonneg ‖y‖]
  have hd : DifferentiableAt ℝ f (‖y‖ ^ 2) :=
    (hc.contDiffAt (isOpen_Ioi.mem_nhds hmem)).differentiableAt (by norm_num)
  have h := hd.hasDerivAt.comp_hasFDerivAt y (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  refine ⟨_, h, fun w => ?_⟩
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, inner_coords]
  ring

theorem planeCoord_hasFDerivAt (y : Space) :
    HasFDerivAt (fun z : Space => (z 0 : ℂ) + (z 1 : ℂ) * Complex.I)
      ((Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ)) +
        (Complex.I • (Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ)))) y := by
  have e : (fun z : Space => (z 0 : ℂ) + (z 1 : ℂ) * Complex.I) = fun z => ((Complex.ofRealCLM.comp
      (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ)) + (Complex.I • (Complex.ofRealCLM.comp
      (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ)))) z := by
    funext z
    simp [mul_comm]
  rw [e]
  exact ContinuousLinearMap.hasFDerivAt _

theorem pointAngle_hasFDerivAt {y : Space} (hy : 0 < y 0 ∨ y 1 ≠ 0) :
    ∃ L : Space →L[ℝ] ℝ, HasFDerivAt pointAngle L y ∧
      ∀ w, L w = (y 0 * w 1 - y 1 * w 0) / (y 0 ^ 2 + y 1 ^ 2) := by
  have hslit : (y 0 : ℂ) + (y 1 : ℂ) * Complex.I ∈ Complex.slitPlane := by
    rcases hy with h | h
    · left
      simpa using h
    · right
      simpa using h
  have hlog := ((Complex.hasStrictDerivAt_log hslit).hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp y
    (planeCoord_hasFDerivAt y)
  have him := Complex.imCLM.hasFDerivAt.comp y hlog
  have e2 : pointAngle = fun z : Space => Complex.imCLM (Complex.log ((z 0 : ℂ) + (z 1 : ℂ) * Complex.I)) := by
    funext z
    simp [pointAngle, Complex.log_im]
  rw [e2]
  refine ⟨_, him, fun w => ?_⟩
  have hn : y 0 ^ 2 + y 1 ^ 2 ≠ 0 := by
    rcases hy with h | h
    · positivity
    · positivity
  simp [Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  field_simp
  ring

theorem angularExp_neg (k : ℤ) {z : Space} (hz : (z 0 : ℂ) + (z 1 : ℂ) * Complex.I ≠ 0) :
    Complex.exp (Complex.I * (((k : ℝ) * pointAngle z : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (((k : ℝ) * pointAngle (-z) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (((k : ℝ) * Real.pi : ℝ) : ℂ)) := by
  have hneg : (((-z) 0 : ℝ) : ℂ) + (((-z) 1 : ℝ) : ℂ) * Complex.I = -((z 0 : ℂ) + (z 1 : ℂ) * Complex.I) := by
    simp only [PiLp.neg_apply, Complex.ofReal_neg]
    ring
  have ha := Complex.arg_neg_coe_angle hz
  rw [← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at ha
  obtain ⟨m, hm⟩ := ha
  unfold pointAngle
  rw [hneg, ← Complex.exp_add]
  have h2 : Complex.arg (-((z 0 : ℂ) + (z 1 : ℂ) * Complex.I)) =
      Complex.arg ((z 0 : ℂ) + (z 1 : ℂ) * Complex.I) + Real.pi + 2 * Real.pi * m := by linarith
  have e : Complex.I * (((k : ℝ) * Complex.arg (-((z 0 : ℂ) + (z 1 : ℂ) * Complex.I)) : ℝ) : ℂ) +
      Complex.I * (((k : ℝ) * Real.pi : ℝ) : ℂ) =
      Complex.I * (((k : ℝ) * Complex.arg ((z 0 : ℂ) + (z 1 : ℂ) * Complex.I) : ℝ) : ℂ) +
        ((k + k * m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [h2]
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem angularExp_hasFDerivAt (k : ℤ) {y : Space} (hy : y 0 ≠ 0 ∨ y 1 ≠ 0) :
    ∃ L : Space →L[ℝ] ℂ, HasFDerivAt (fun z : Space => Complex.exp (Complex.I * (((k : ℝ) * pointAngle z : ℝ) : ℂ))) L y ∧
      ∀ w, L w = Complex.exp (Complex.I * (((k : ℝ) * pointAngle y : ℝ) : ℂ)) *
        (Complex.I * (((k : ℝ) * ((y 0 * w 1 - y 1 * w 0) / (y 0 ^ 2 + y 1 ^ 2)) : ℝ) : ℂ)) := by
  have slit : ∀ x : Space, (0 < x 0 ∨ x 1 ≠ 0) →
      ∃ L : Space →L[ℝ] ℂ, HasFDerivAt (fun z : Space => Complex.exp (Complex.I * (((k : ℝ) * pointAngle z : ℝ) : ℂ))) L x ∧
        ∀ w, L w = Complex.exp (Complex.I * (((k : ℝ) * pointAngle x : ℝ) : ℂ)) *
          (Complex.I * (((k : ℝ) * ((x 0 * w 1 - x 1 * w 0) / (x 0 ^ 2 + x 1 ^ 2)) : ℝ) : ℂ)) := by
    intro x hx
    obtain ⟨La, ha, hav⟩ := pointAngle_hasFDerivAt hx
    have hθ := ((Complex.ofRealCLM.hasFDerivAt.comp x (ha.const_mul (k : ℝ))).const_mul Complex.I).cexp
    refine ⟨_, hθ, fun w => ?_⟩
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply, Function.comp_apply, hav]
  by_cases hs : 0 < y 0 ∨ y 1 ≠ 0
  · exact slit y hs
  · have hy1 : y 1 = 0 := by
      by_contra h
      exact hs (Or.inr h)
    have hy0 : y 0 < 0 := by
      rcases hy with h | h
      · exact lt_of_le_of_ne (not_lt.1 fun h' => hs (Or.inl h')) h
      · exact absurd hy1 h
    obtain ⟨L, hL, hLv⟩ := slit (-y) (Or.inl (by simp; linarith))
    have hc := (hL.comp y ((hasFDerivAt_id y).neg)).mul_const (Complex.exp (Complex.I * (((k : ℝ) * Real.pi : ℝ) : ℂ)))
    have hne : ∀ᶠ z in nhds y, (z 0 : ℂ) + (z 1 : ℂ) * Complex.I ≠ 0 := by
      have hy' : (y 0 : ℂ) + (y 1 : ℂ) * Complex.I ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      exact (planeCoord_hasFDerivAt y).continuousAt.eventually_ne hy'
    have hev : (fun z : Space => Complex.exp (Complex.I * (((k : ℝ) * pointAngle z : ℝ) : ℂ))) =ᶠ[nhds y]
        fun z => Complex.exp (Complex.I * (((k : ℝ) * pointAngle (-z) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (((k : ℝ) * Real.pi : ℝ) : ℂ)) :=
      hne.mono fun z hz => angularExp_neg k hz
    refine ⟨_, hc.congr_of_eventuallyEq hev, fun w => ?_⟩
    have hyv : (y 0 : ℂ) + (y 1 : ℂ) * Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    rw [angularExp_neg k hyv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, hLv, Function.comp_apply]
    simp only [PiLp.neg_apply, neg_sq]
    ring_nf

theorem keyPhase_split (P : ShapeParams) (κ : FieldKey) (σ : ℝ) (z : Space) :
    keyPhase P κ σ z = Complex.exp (Complex.I * ((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
        (κ.phaseIndex : ℝ) * P.radialPhase (‖z‖ ^ 2) : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((((labelAzimuth P.azimuthOrder κ.label : ℤ) : ℝ) * pointAngle z : ℝ) : ℂ)) := by
  unfold keyPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem keyPhase_hasFDerivAt (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (σ : ℝ)
    {y : Space} (hy : y 0 ≠ 0 ∨ y 1 ≠ 0) :
    ∃ L : Space →L[ℝ] ℂ, HasFDerivAt (keyPhase P κ σ) L y ∧ ∀ w, L w = keyPhase P κ σ y *
      (Complex.I * ((((labelAzimuth P.azimuthOrder κ.label : ℤ) : ℝ) * ((y 0 * w 1 - y 1 * w 0) / (y 0 ^ 2 + y 1 ^ 2)) +
        (κ.phaseIndex : ℝ) * (deriv P.radialPhase (‖y‖ ^ 2) * (2 * (y 0 * w 0 + y 1 * w 1 + y 2 * w 2))) : ℝ) : ℂ)) := by
  obtain ⟨Lf, hf, hfv⟩ := radialPhase_hasFDerivAt hP.phase y
  obtain ⟨La, ha, hav⟩ := angularExp_hasFDerivAt (labelAzimuth P.azimuthOrder κ.label) hy
  have hθ := (hf.const_mul (κ.phaseIndex : ℝ)).const_add (2 * Real.pi * (labelTime κ.label : ℝ) * σ)
  have hB := ((Complex.ofRealCLM.hasFDerivAt.comp y hθ).const_mul Complex.I).cexp
  have hprod := hB.mul ha
  have e : keyPhase P κ σ = fun z => Complex.exp (Complex.I * ((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
        (κ.phaseIndex : ℝ) * P.radialPhase (‖z‖ ^ 2) : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((((labelAzimuth P.azimuthOrder κ.label : ℤ) : ℝ) * pointAngle z : ℝ) : ℂ)) :=
    funext (keyPhase_split P κ σ)
  rw [e]
  refine ⟨_, hprod, fun w => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Function.comp_apply, hav, hfv]
  push_cast
  ring

theorem comp_hasFDerivAt_chart (U : ℝ → ℝ → Fin 3 → ℂ) (c : Fin 3) {T X : Space → ℝ}
    {LT LX : Space →L[ℝ] ℝ} {y : Space} (hT : HasFDerivAt T LT y) (hX : HasFDerivAt X LX y)
    (hR : DifferentiableAt ℝ (fun q : ℝ × ℝ => U q.1 q.2 c) (T y, X y)) :
    ∃ L : Space →L[ℝ] ℂ, HasFDerivAt (fun z => U (T z) (X z) c) L y ∧ ∀ w,
      L w = (LT w : ℂ) * deriv (fun t' => U t' (X y) c) (T y) + (LX w : ℂ) * deriv (fun x' => U (T y) x' c) (X y) := by
  have hTX : HasFDerivAt (fun z => (T z, X z)) (LT.prod LX) y := hT.prodMk hX
  have hRc := hR.hasFDerivAt.comp y hTX
  refine ⟨_, hRc, fun w => ?_⟩
  have ht : HasDerivAt (fun t' : ℝ => ((t', X y) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) (T y) :=
    (hasDerivAt_id (T y)).prodMk (hasDerivAt_const (T y) (X y))
  have hx : HasDerivAt (fun x' : ℝ => ((T y, x') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) (X y) :=
    (hasDerivAt_const (X y) (T y)).prodMk (hasDerivAt_id (X y))
  have d1 : deriv (fun t' => U t' (X y) c) (T y) =
      fderiv ℝ (fun q : ℝ × ℝ => U q.1 q.2 c) (T y, X y) ((1 : ℝ), (0 : ℝ)) := by
    have h := (hR.hasFDerivAt.comp_hasDerivAt (T y) ht).deriv
    exact h
  have d2 : deriv (fun x' => U (T y) x' c) (X y) =
      fderiv ℝ (fun q : ℝ × ℝ => U q.1 q.2 c) (T y, X y) ((0 : ℝ), (1 : ℝ)) := by
    have h := (hR.hasFDerivAt.comp_hasDerivAt (X y) hx).deriv
    exact h
  have e : ((LT w, LX w) : ℝ × ℝ) = LT w • ((1 : ℝ), (0 : ℝ)) + LX w • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, e, map_add, map_smul, map_smul, d1, d2,
    Complex.real_smul, Complex.real_smul]

def liftVec : Space →L[ℝ] (Fin 3 → ℂ) :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ)

theorem liftVec_apply (v : Space) (i : Fin 3) : liftVec v i = (v i : ℂ) := by
  simp [liftVec]

theorem cdiv_term (c : ℂ) (Lc : Space →L[ℝ] ℂ) (LW : Space →L[ℝ] Space) (v : Space) :
    ∑ i : Fin 3, ((c • liftVec.comp LW + Lc.smulRight (liftVec v)) (unitVector i)) i =
      c * ((∑ i : Fin 3, LW (unitVector i) i : ℝ) : ℂ) + Lc v := by
  have hv : Lc v = ∑ i : Fin 3, (v i : ℂ) * Lc (unitVector i) := by
    have e : v = ∑ i : Fin 3, v i • unitVector i := by
      ext j
      fin_cases j <;> simp [unitVector, Fin.sum_univ_three]
    conv_lhs => rw [e]
    simp [map_sum, Complex.real_smul]
  rw [hv]
  simp [liftVec_apply, Fin.sum_univ_three]
  ring

theorem sum_three_apply (A B C : Space →L[ℝ] (Fin 3 → ℂ)) :
    ∑ i : Fin 3, ((A + B + C) (unitVector i)) i =
      ∑ i : Fin 3, (A (unitVector i)) i + ∑ i : Fin 3, (B (unitVector i)) i + ∑ i : Fin 3, (C (unitVector i)) i := by
  simp [Finset.sum_add_distrib]

end SphericalDivInternal

end GivenShape

end CertCell

end Breakdown
