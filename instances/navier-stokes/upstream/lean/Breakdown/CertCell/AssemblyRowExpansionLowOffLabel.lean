import Breakdown.CertCell.AssemblyRowExpansionLowOrbit
import Breakdown.CertCell.CellCalculusStatements
import Breakdown.CertCell.BridgeStatements
import Breakdown.Cert.ExtendedCoerciveStatement
import Breakdown.CertCell.ModeShiftRotate
import Breakdown.CertCell.ModeShiftRotateTensor
import Breakdown.CertCell.MeanStretchTorus
import Breakdown.Cert.CoerciveCurlEnergy
import Breakdown.Cert.CoerciveModeDerivative

open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.Assembly.Internal.RowIdentity

open Breakdown Breakdown.CertCell CellCalculus CellCert CellCert.CellAnalysis

namespace OffSupport

open _root_.Breakdown.Coercive.Internal.ModeRotation (expFactor boxMeasure iter_eq_prod continuous_expFactor
  continuous_axialRot axialRot_apply)
open _root_.Breakdown.CertCell.Bridge.Internal.MeanStretch (phase expFactor_mul_phase expFactor_mul_expFactor
  expFactor_eq)

theorem expFactor_split (η : ℤ × ℤ) (τ φ : ℝ) :
    expFactor η τ φ = Complex.exp (-(((2 * Real.pi * η.1 * τ : ℝ) : ℂ) * Complex.I)) *
      Complex.exp (-(((η.2 * φ : ℝ) : ℂ) * Complex.I)) := by
  unfold expFactor
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integral_exp_period_eq_zero {c : ℂ} (hc : c ≠ 0) {L : ℝ} (hL : Complex.exp (c * L) = 1) :
    ∫ x in (0 : ℝ)..L, Complex.exp (c * x) = 0 := by
  rw [integral_exp_mul_complex hc, hL]
  simp

theorem angle_integral_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(((k * φ : ℝ) : ℂ) * Complex.I)) = 0 := by
  have e : ∀ φ : ℝ, Complex.exp (-(((k * φ : ℝ) : ℂ) * Complex.I))
      = Complex.exp ((-(k : ℂ) * Complex.I) * (φ : ℂ)) := fun φ => by
    congr 1
    push_cast
    ring
  simp_rw [e]
  refine integral_exp_period_eq_zero (mul_ne_zero (neg_ne_zero.2 (Int.cast_ne_zero.2 hk)) Complex.I_ne_zero) ?_
  rw [show (-(k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ) = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast
    ring]
  exact Complex.exp_int_mul_two_pi_mul_I _

theorem time_integral_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ τ in (0 : ℝ)..1, Complex.exp (-(((2 * Real.pi * k * τ : ℝ) : ℂ) * Complex.I)) = 0 := by
  have e : ∀ τ : ℝ, Complex.exp (-(((2 * Real.pi * k * τ : ℝ) : ℂ) * Complex.I))
      = Complex.exp ((((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) * (τ : ℂ)) := fun τ => by
    congr 1
    push_cast
    ring
  simp_rw [e]
  refine integral_exp_period_eq_zero
    (mul_ne_zero (Int.cast_ne_zero.2 (neg_ne_zero.2 hk)) Complex.two_pi_I_ne_zero) ?_
  rw [Complex.ofReal_one, mul_one]
  exact Complex.exp_int_mul_two_pi_mul_I _

theorem iter_expFactor_eq_zero {η : ℤ × ℤ} (hη : η ≠ 0) :
    ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), expFactor η τ φ = 0 := by
  simp_rw [expFactor_split, intervalIntegral.integral_const_mul]
  by_cases h2 : η.2 = 0
  · have h1 : η.1 ≠ 0 := fun h1 => hη (Prod.ext h1 h2)
    have e : ∀ φ : ℝ, Complex.exp (-(((η.2 * φ : ℝ) : ℂ) * Complex.I)) = 1 := fun φ => by simp [h2]
    simp_rw [e, intervalIntegral.integral_mul_const, time_integral_eq_zero h1, zero_mul]
  · simp_rw [angle_integral_eq_zero h2, mul_zero, intervalIntegral.integral_zero]

theorem boxMeasure_eq_restrict :
    boxMeasure = (volume : Measure (ℝ × ℝ)).restrict (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]

theorem integrable_box_of_continuous {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E}
    (hf : Continuous f) : Integrable f boxMeasure := by
  rw [boxMeasure_eq_restrict]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem iter_sum_eq_zero {κ : Type*} (s : Finset κ) (a b : κ → ℂ) (η ζ : κ → ℤ × ℤ)
    (hη : ∀ k ∈ s, η k ≠ 0) (hζ : ∀ k ∈ s, ζ k ≠ 0) :
    ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      ∑ k ∈ s, (a k * expFactor (η k) τ φ + b k * expFactor (ζ k) τ φ) = 0 := by
  have hc : ∀ (c : ℂ) (θ : ℤ × ℤ), Integrable (fun p : ℝ × ℝ => c * expFactor θ p.1 p.2) boxMeasure :=
    fun c θ => integrable_box_of_continuous (continuous_const.mul (continuous_expFactor θ))
  have hz : ∀ (c : ℂ) (θ : ℤ × ℤ), θ ≠ 0 → ∫ p, c * expFactor θ p.1 p.2 ∂boxMeasure = 0 := by
    intro c θ hθ
    rw [integral_const_mul, ← iter_eq_prod (fun τ φ => expFactor θ τ φ)
      (integrable_box_of_continuous (continuous_expFactor θ)), iter_expFactor_eq_zero hθ, mul_zero]
  have hs : ∀ k ∈ s, Integrable (fun p : ℝ × ℝ => a k * expFactor (η k) p.1 p.2 + b k * expFactor (ζ k) p.1 p.2)
      boxMeasure := fun k _ => (hc (a k) (η k)).add (hc (b k) (ζ k))
  rw [iter_eq_prod (fun τ φ => ∑ k ∈ s, (a k * expFactor (η k) τ φ + b k * expFactor (ζ k) τ φ))
    (integrable_finsetSum s hs), integral_finsetSum s hs]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [integral_add (hc (a k) (η k)) (hc (b k) (ζ k)), hz _ _ (hη k hk), hz _ _ (hζ k hk), add_zero]

theorem conj_phase (β : ℤ × ℤ) (τ φ : ℝ) : conj (phase β τ φ) = expFactor β τ φ := by
  rw [expFactor_eq, phase, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem expFactor_mul_re_phase (ξ β : ℤ × ℤ) (c : ℂ) (τ φ : ℝ) :
    expFactor ξ τ φ * (((phase β τ φ * c).re : ℝ) : ℂ)
      = (1 / 2 * c) * expFactor (ξ - β) τ φ + (1 / 2 * conj c) * expFactor (ξ + β) τ φ := by
  rw [Complex.re_eq_add_conj, map_mul, conj_phase, ← expFactor_mul_phase, ← expFactor_mul_expFactor]
  ring

theorem continuous_orbit_of {E : Type*} [TopologicalSpace E] {X : ℝ → Space → E}
    (hX : Continuous (fun z : ℝ × Space => X z.1 z.2)) (σ : ℝ) (y : Space) :
    Continuous (fun q : ℝ × ℝ => X (σ + q.1) (axialRot q.2 y)) :=
  hX.comp ((continuous_const.add continuous_fst).prodMk
    (continuous_axialRot.comp (continuous_snd.prodMk continuous_const)))

theorem coord_of_sum (r : Fin 3 → ℝ) (k : Fin 3) : (∑ j : Fin 3, r j • unitVector j) k = r k := by
  fin_cases k <;> simp [unitVector, Fin.sum_univ_three]

theorem rotated_expansion {X : ℝ → Space → Space} (hXp : IsTimePeriodic X)
    (hXc : Continuous (fun z : ℝ × Space => X z.1 z.2)) {S : Finset (ℤ × ℤ)}
    (hspan : ∀ σ x i, X σ x i = ∑ β ∈ S, (modeVel β X σ x i).re) (y : Space) (τ φ : ℝ) (l : Fin 3) :
    axialRot (-φ) (X τ (axialRot φ y)) l = ∑ β ∈ S, (phase β τ φ * modeVel β X 0 y l).re := by
  have hint : IntegrableOn (fun q : ℝ × ℝ => X (0 + q.1) (axialRot q.2 y))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi)) :=
    (continuous_orbit_of hXc 0 y).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hmode : ∀ β : ℤ × ℤ, ∀ i, modeVel β X τ (axialRot φ y) i
      = phase β τ φ * ∑ j : Fin 3, ((axialRot φ (unitVector j) i : ℝ) : ℂ) * modeVel β X 0 y j := by
    intro β i
    have h := congrFun (Bridge.modeShiftRotate X hXp β 0 τ φ y hint) i
    rw [zero_add] at h
    exact h
  have hXu : X τ (axialRot φ y)
      = axialRot φ (∑ k : Fin 3, (∑ β ∈ S, (phase β τ φ * modeVel β X 0 y k).re) • unitVector k) := by
    ext i
    rw [hspan, axialRot_apply]
    simp_rw [hmode, coord_of_sum, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun β _ => ?_
    rw [mul_left_comm, Complex.re_ofReal_mul]
  rw [hXu, _root_.Breakdown.Coercive.ModeDerivative.Internal.axialRot_neg_apply
    _root_.Breakdown.Coercive.axialRotationHolds_proof, coord_of_sum]

theorem modeVel_eq_zero_off_support {X : ℝ → Space → Space} (hXp : IsTimePeriodic X)
    (hXc : Continuous (fun z : ℝ × Space => X z.1 z.2)) {S : Finset (ℤ × ℤ)} (hsym : ∀ β ∈ S, -β ∈ S)
    (hspan : ∀ σ x i, X σ x i = ∑ β ∈ S, (modeVel β X σ x i).re) {ξ : ℤ × ℤ} (hξ : ξ ∉ S) (y : Space) :
    modeVel ξ X 0 y = 0 := by
  funext l
  have h1 : ∀ β ∈ S, ξ - β ≠ 0 := fun β hβ h => hξ (sub_eq_zero.1 h ▸ hβ)
  have h2 : ∀ β ∈ S, ξ + β ≠ 0 := fun β hβ h => hξ (eq_neg_of_add_eq_zero_left h ▸ hsym β hβ)
  have e : modeVel ξ X 0 y l = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      expFactor ξ τ φ * ((axialRot (-φ) (X τ (axialRot φ y)) l : ℝ) : ℂ) := by
    simp only [modeVel, modeAverage, zero_add]
    rfl
  have hz := iter_sum_eq_zero S (fun β => 1 / 2 * modeVel β X 0 y l) (fun β => 1 / 2 * conj (modeVel β X 0 y l))
    (fun β => ξ - β) (fun β => ξ + β) h1 h2
  rw [e, Pi.zero_apply]
  simp_rw [rotated_expansion hXp hXc hspan y, Complex.ofReal_sum, Finset.mul_sum, expFactor_mul_re_phase]
  rw [hz, mul_zero]

theorem continuous_spaceDeriv {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) := by
  have e : (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2)
      = fun z => (fderiv ℝ (fun w : ℝ × Space => W w.1 w.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext z
    exact ((hW.differentiable (by norm_num) (z.1, z.2)).hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).fderiv
  rw [e]
  exact (hW.continuous_fderiv (by norm_num)).clm_comp continuous_const

theorem periodic_vorticityOf {W : ℝ → Space → Space} (hW : IsTimePeriodic W) :
    IsTimePeriodic (vorticityOf W) := by
  intro σ y
  simp only [vorticityOf]
  rw [show W (σ + 1) = W σ from funext (hW σ)]

theorem continuous_vorticityOf {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => vorticityOf W z.1 z.2) := by
  have hD := continuous_spaceDeriv hW
  simp only [vorticityOf, curlVec]
  fun_prop

theorem curlVec_coord (A : Space →L[ℝ] Space) (i : Fin 3) :
    curlVec A i = ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * A (unitVector j) l := by
  unfold curlVec
  exact coord_of_sum _ i

theorem vorticity_expansion {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) {S : Finset (ℤ × ℤ)} (hS : Bridge.IsHarmonicExpansion S W HW)
    (σ : ℝ) (x : Space) (i : Fin 3) :
    vorticityOf W σ x i = ∑ β ∈ S, (modeVel β (vorticityOf W) σ x i).re := by
  have hD := continuous_spaceDeriv hW.smooth
  have hc : ∀ β : ℤ × ℤ, modeVel β (vorticityOf W) σ x = curlOfGrad (modeGrad β (gradField W) σ x) := fun β =>
    (_root_.Breakdown.Coercive.Internal.CurlEnergy.curlOfGrad_modeGrad_eq β (z := (σ, x))
      (integrable_box_of_continuous (continuous_orbit_of hD σ x))).symm
  simp_rw [hc]
  show curlVec (fderiv ℝ (W σ) x) i = _
  simp_rw [curlVec_coord, hS.gradient_span, curlOfGrad, Complex.re_sum, Complex.re_ofReal_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

end OffSupport

theorem labelVel_given_off_label {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {B : ℝ} (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) {S : Finset (ℤ × ℤ)}
    (hS : Bridge.IsHarmonicExpansion S W HW) (m : ℕ) {α : ℤ × ℤ} (hα : labelHarmonic m α ∉ S) (p : ℝ × ℝ) :
    labelVel m α W p = 0 ∧ labelVel m α (vorticityOf W) p = 0 :=
  ⟨OffSupport.modeVel_eq_zero_off_support hW.periodic hW.smooth.continuous hS.symmetric hS.field_span hα
      (planePoint p),
    OffSupport.modeVel_eq_zero_off_support (OffSupport.periodic_vorticityOf hW.periodic)
      (OffSupport.continuous_vorticityOf hW.smooth) hS.symmetric (OffSupport.vorticity_expansion hW hS) hα
      (planePoint p)⟩

end Breakdown.CertCell.Assembly.Internal.RowIdentity
