import Breakdown.CertCell.AssemblyRowExpansionLowOrbit
import Breakdown.CertCell.CellCalculusStatements
import Breakdown.CertCell.BridgeStatements
import Breakdown.Cert.ExtendedCoerciveStatement
import Breakdown.CertCell.ClassSupportLinks
import Breakdown.CertCell.ModeOffLattice
import Breakdown.CertCell.LabelArithmetic
import Breakdown.CertCell.ModeShiftRotate
import Breakdown.CertCell.ModeShiftRotateTensor
import Breakdown.CertCell.ModeConjugate
import Breakdown.Cert.CoerciveCurlEnergy
import Breakdown.Cert.CoerciveModeDerivative

open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.Assembly.Internal.RowIdentity

open Breakdown Breakdown.CertCell CellCalculus CellCert CellCert.CellAnalysis
open _root_.Breakdown.Coercive.Internal.ModeRotation (expFactor boxMeasure iter_eq_prod norm_expFactor continuous_expFactor)
open _root_.Breakdown.Coercive (axialRotationHolds_proof)

private def phaseFactor (β : ℤ × ℤ) (τ φ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I)

private def modeMean (ξ : ℤ × ℤ) (a : ℝ → ℝ → ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), expFactor ξ τ φ * ((a τ φ : ℝ) : ℂ)

private theorem norm_phaseFactor (β : ℤ × ℤ) (τ φ : ℝ) : ‖phaseFactor β τ φ‖ = 1 := by
  unfold phaseFactor
  exact Complex.norm_exp_ofReal_mul_I _

private theorem continuous_phaseFactor (β : ℤ × ℤ) : Continuous (fun q : ℝ × ℝ => phaseFactor β q.1 q.2) := by
  unfold phaseFactor
  fun_prop

private theorem expFactor_mul_phaseFactor (ξ β : ℤ × ℤ) (τ φ : ℝ) :
    expFactor ξ τ φ * phaseFactor β τ φ = expFactor (ξ - β) τ φ := by
  unfold expFactor phaseFactor
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  push_cast
  ring

private theorem expFactor_mul_conj_phaseFactor (ξ β : ℤ × ℤ) (τ φ : ℝ) :
    expFactor ξ τ φ * conj (phaseFactor β τ φ) = expFactor (ξ + β) τ φ := by
  unfold expFactor phaseFactor
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Prod.fst_add, Prod.snd_add, Int.cast_add]
  push_cast
  ring

private theorem integrable_expFactor_mul {ξ : ℤ × ℤ} {a : ℝ → ℝ → ℝ}
    (ha : Integrable (fun q : ℝ × ℝ => a q.1 q.2) boxMeasure) :
    Integrable (fun q : ℝ × ℝ => expFactor ξ q.1 q.2 * ((a q.1 q.2 : ℝ) : ℂ)) boxMeasure := by
  refine ha.norm.mono' ((continuous_expFactor ξ).aestronglyMeasurable.mul
    (Complex.continuous_ofReal.comp_aestronglyMeasurable ha.1)) ?_
  refine Filter.Eventually.of_forall fun q => ?_
  simp only [norm_mul, norm_expFactor, one_mul, Complex.norm_real, le_refl]

private theorem modeMean_eq_integral {ξ : ℤ × ℤ} {a : ℝ → ℝ → ℝ}
    (ha : Integrable (fun q : ℝ × ℝ => a q.1 q.2) boxMeasure) :
    modeMean ξ a = (1 / (2 * Real.pi) : ℂ) * ∫ q, expFactor ξ q.1 q.2 * ((a q.1 q.2 : ℝ) : ℂ) ∂boxMeasure := by
  unfold modeMean
  rw [iter_eq_prod (fun τ φ => expFactor ξ τ φ * ((a τ φ : ℝ) : ℂ)) (integrable_expFactor_mul ha)]

private theorem modeMean_sum {κ : Type*} (s : Finset κ) (ξ : ℤ × ℤ) (g : κ → ℝ → ℝ → ℝ)
    (hg : ∀ k ∈ s, Integrable (fun q : ℝ × ℝ => g k q.1 q.2) boxMeasure) :
    modeMean ξ (fun τ φ => ∑ k ∈ s, g k τ φ) = ∑ k ∈ s, modeMean ξ (g k) := by
  have hs : Integrable (fun q : ℝ × ℝ => ∑ k ∈ s, g k q.1 q.2) boxMeasure := integrable_finsetSum _ hg
  rw [modeMean_eq_integral hs]
  rw [Finset.sum_congr rfl fun k hk => modeMean_eq_integral (ξ := ξ) (hg k hk), ← Finset.mul_sum,
    ← integral_finsetSum _ fun k hk => integrable_expFactor_mul (hg k hk)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [Complex.ofReal_sum, Finset.mul_sum]

private theorem modeMean_const_mul (ξ : ℤ × ℤ) (r : ℝ) (a : ℝ → ℝ → ℝ) :
    modeMean ξ (fun τ φ => r * a τ φ) = (r : ℂ) * modeMean ξ a := by
  unfold modeMean
  simp_rw [Complex.ofReal_mul, mul_left_comm (expFactor ξ _ _) (r : ℂ), intervalIntegral.integral_const_mul]
  ring

private theorem modeMean_add {ξ : ℤ × ℤ} {a b : ℝ → ℝ → ℝ}
    (ha : Integrable (fun q : ℝ × ℝ => a q.1 q.2) boxMeasure)
    (hb : Integrable (fun q : ℝ × ℝ => b q.1 q.2) boxMeasure) :
    modeMean ξ (fun τ φ => a τ φ + b τ φ) = modeMean ξ a + modeMean ξ b := by
  rw [modeMean_eq_integral (ha.add hb), modeMean_eq_integral ha, modeMean_eq_integral hb, ← mul_add,
    ← integral_add (integrable_expFactor_mul ha) (integrable_expFactor_mul hb)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [Complex.ofReal_add, mul_add]

private theorem integrable_mul_re_phase {a : ℝ → ℝ → ℝ} (ha : Integrable (fun q : ℝ × ℝ => a q.1 q.2) boxMeasure)
    (β : ℤ × ℤ) (c : ℂ) :
    Integrable (fun q : ℝ × ℝ => a q.1 q.2 * (phaseFactor β q.1 q.2 * c).re) boxMeasure := by
  refine ha.mul_bdd (c := ‖c‖) ?_ (Filter.Eventually.of_forall fun q => ?_)
  · exact (Complex.continuous_re.comp ((continuous_phaseFactor β).mul continuous_const)).aestronglyMeasurable
  · refine (Real.norm_eq_abs _).le.trans ((Complex.abs_re_le_norm _).trans ?_)
    rw [norm_mul, norm_phaseFactor, one_mul]

private theorem modeMean_mul_re_phase {a : ℝ → ℝ → ℝ} (ha : Integrable (fun q : ℝ × ℝ => a q.1 q.2) boxMeasure)
    (ξ β : ℤ × ℤ) (c : ℂ) :
    modeMean ξ (fun τ φ => a τ φ * (phaseFactor β τ φ * c).re)
      = (1 / 2 : ℂ) * (c * modeMean (ξ - β) a + conj c * modeMean (ξ + β) a) := by
  rw [modeMean_eq_integral (integrable_mul_re_phase ha β c), modeMean_eq_integral ha,
    modeMean_eq_integral ha]
  have h1 := integrable_expFactor_mul (ξ := ξ - β) ha
  have h2 := integrable_expFactor_mul (ξ := ξ + β) ha
  have e : (fun q : ℝ × ℝ => expFactor ξ q.1 q.2 * ((a q.1 q.2 * (phaseFactor β q.1 q.2 * c).re : ℝ) : ℂ))
      = fun q => (1 / 2 : ℂ) * (c * (expFactor (ξ - β) q.1 q.2 * ((a q.1 q.2 : ℝ) : ℂ))
          + conj c * (expFactor (ξ + β) q.1 q.2 * ((a q.1 q.2 : ℝ) : ℂ))) := by
    funext q
    rw [← expFactor_mul_phaseFactor, ← expFactor_mul_conj_phaseFactor, Complex.ofReal_mul,
      Complex.re_eq_add_conj, map_mul]
    ring
  rw [e, integral_const_mul, integral_add (h1.const_mul c) (h2.const_mul _), integral_const_mul,
    integral_const_mul]
  ring

private theorem sum_neg_of_symmetric {M : Type*} [AddCommMonoid M] {S : Finset (ℤ × ℤ)} (hS : ∀ β ∈ S, -β ∈ S)
    (f : ℤ × ℤ → M) : ∑ β ∈ S, f (-β) = ∑ β ∈ S, f β := by
  refine Finset.sum_nbij' (fun β => -β) (fun β => -β) (fun β hβ => hS β hβ) (fun β hβ => hS β hβ)
    (fun β _ => neg_neg β) (fun β _ => neg_neg β) (fun β _ => rfl)

private theorem rotC_eq_zero (φ : ℝ) {c : Fin 3 → ℂ}
    (h : ∀ i, ∑ j : Fin 3, ((axialRot φ (unitVector j) i : ℝ) : ℂ) * c j = 0) : c = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp [axialRot, unitVector, Fin.sum_univ_three] at h0 h1 h2
  have hs : Complex.cos (φ : ℂ) ^ 2 + Complex.sin (φ : ℂ) ^ 2 = 1 := Complex.cos_sq_add_sin_sq _
  funext k
  fin_cases k
  · change c 0 = 0
    linear_combination Complex.cos (φ : ℂ) * h0 + Complex.sin (φ : ℂ) * h1 - c 0 * hs
  · change c 1 = 0
    linear_combination -Complex.sin (φ : ℂ) * h0 + Complex.cos (φ : ℂ) * h1 - c 1 * hs
  · change c 2 = 0
    exact h2

private theorem crossVec_axialRot (φ : ℝ) (a b : Space) (i : Fin 3) :
    axialRot φ (CellCalculus.crossVec a b) i
      = ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * axialRot φ a j * axialRot φ b l := by
  have h := Real.sin_sq_add_cos_sq φ
  fin_cases i <;>
  simp [axialRot, CellCalculus.crossVec, unitVector, Fin.sum_univ_three, alternatingSymbol]
  · ring
  · ring
  · linear_combination (a 1 * b 0 - a 0 * b 1) * h

private theorem permSign_eq_alternatingSymbol (i j l : Fin 3) : CellCert.permSign i j l = alternatingSymbol i j l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [CellCert.permSign, alternatingSymbol]

private theorem labelHarmonic_sub (m : ℕ) (ι α : ℤ × ℤ) :
    labelHarmonic m ι - labelHarmonic m α = labelHarmonic m (ι - α) := by
  ext <;> simp [labelHarmonic, labelTime, labelAzimuth] <;> ring

private theorem boxMeasure_eq_Icc :
    (volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi)) = boxMeasure := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    ← Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1)),
    ← Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 2 * Real.pi))]

private theorem integrableOn_Icc_of_box {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E}
    (h : Integrable f boxMeasure) : IntegrableOn f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi)) := by
  rw [IntegrableOn, boxMeasure_eq_Icc]
  exact h

private theorem integrable_box_of_continuous {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E}
    (hf : Continuous f) : Integrable f boxMeasure := by
  rw [← boxMeasure_eq_Icc]
  exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

private theorem continuous_orbit {E : Type*} [TopologicalSpace E] {X : ℝ → Space → E}
    (hX : Continuous (fun z : ℝ × Space => X z.1 z.2)) (σ : ℝ) (y : Space) :
    Continuous (fun q : ℝ × ℝ => X (σ + q.1) (axialRot q.2 y)) := by
  have h : Continuous (fun q : ℝ × ℝ => ((σ + q.1, axialRot q.2 y) : ℝ × Space)) := by
    refine (continuous_const.add continuous_fst).prodMk ?_
    unfold axialRot
    fun_prop
  exact hX.comp h

private theorem continuous_partialDeriv {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) := by
  have e : (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) =
      fun z => (fderiv ℝ (fun w : ℝ × Space => W w.1 w.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext z
    have hd := ((hW.differentiable (by norm_num)) (z.1, z.2)).hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)
    exact hd.fderiv
  rw [e]
  exact (hW.continuous_fderiv (by norm_num)).clm_comp continuous_const

private theorem axialRot_add_vec (φ : ℝ) (a b : Space) : axialRot φ (a + b) = axialRot φ a + axialRot φ b := by
  ext i
  fin_cases i <;> simp [axialRot, unitVector] <;> ring

private theorem coord_sum_unitVector (c : Fin 3 → ℝ) (i : Fin 3) : (∑ k : Fin 3, c k • unitVector k) i = c i := by
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

private theorem curlVec_apply (A : Space →L[ℝ] Space) (i : Fin 3) :
    curlVec A i = ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * A (unitVector j) l := by
  unfold curlVec
  exact coord_sum_unitVector _ i

private theorem rot_expansion {X : ℝ → Space → Space} (hXp : IsTimePeriodic X)
    (hXc : Continuous (fun z : ℝ × Space => X z.1 z.2)) {S : Finset (ℤ × ℤ)}
    (hspan : ∀ σ x i, X σ x i = ∑ β ∈ S, (modeVel β X σ x i).re) (y : Space) (τ φ : ℝ) (l : Fin 3) :
    axialRot (-φ) (X τ (axialRot φ y)) l = ∑ β ∈ S, (phaseFactor β τ φ * modeVel β X 0 y l).re := by
  have hrot : ∀ β : ℤ × ℤ, modeVel β X τ (axialRot φ y) = fun i =>
      phaseFactor β τ φ * ∑ j : Fin 3, ((axialRot φ (unitVector j) i : ℝ) : ℂ) * modeVel β X 0 y j := by
    intro β
    have h := Bridge.modeShiftRotate X hXp β 0 τ φ y
      (integrableOn_Icc_of_box (integrable_box_of_continuous (continuous_orbit hXc 0 y)))
    rw [zero_add] at h
    exact h
  set u : Space := ∑ k : Fin 3, (∑ β ∈ S, (phaseFactor β τ φ * modeVel β X 0 y k).re) • unitVector k with hu
  have hXu : X τ (axialRot φ y) = axialRot φ u := by
    ext i
    rw [hspan, _root_.Breakdown.Coercive.Internal.ModeRotation.axialRot_apply φ u i]
    simp_rw [hrot, hu, coord_sum_unitVector, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun β _ => ?_
    rw [mul_left_comm, Complex.re_ofReal_mul]
  rw [hXu, _root_.Breakdown.Coercive.ModeDerivative.Internal.axialRot_neg_apply axialRotationHolds_proof, hu,
    coord_sum_unitVector]

private theorem periodic_vorticity {W : ℝ → Space → Space} (hW : IsTimePeriodic W) : IsTimePeriodic (vorticityOf W) := by
  intro σ y
  simp only [vorticityOf]
  rw [show W (σ + 1) = W σ from funext (hW σ)]

private theorem continuous_vorticity {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => vorticityOf W z.1 z.2) := by
  have hD := continuous_partialDeriv hW
  simp only [vorticityOf, curlVec]
  fun_prop

private theorem vorticity_span {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) {S : Finset (ℤ × ℤ)} (hS : Bridge.IsHarmonicExpansion S W HW)
    (σ : ℝ) (x : Space) (i : Fin 3) :
    vorticityOf W σ x i = ∑ β ∈ S, (modeVel β (vorticityOf W) σ x i).re := by
  have hD := continuous_partialDeriv hW.smooth
  have hc : ∀ β : ℤ × ℤ, curlOfGrad (modeGrad β (gradField W) σ x) = modeVel β (vorticityOf W) σ x := by
    intro β
    exact _root_.Breakdown.Coercive.Internal.CurlEnergy.curlOfGrad_modeGrad_eq β (z := (σ, x))
      (integrable_box_of_continuous (continuous_orbit (X := gradField W) hD σ x))
  simp_rw [← hc]
  simp only [vorticityOf, curlVec_apply, curlOfGrad, hS.gradient_span, Finset.mul_sum, Complex.re_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.re_ofReal_mul]

private theorem modeMean_pair {a b : ℝ → ℝ → ℝ} (ha : Integrable (fun q : ℝ × ℝ => a q.1 q.2) boxMeasure)
    (hb : Integrable (fun q : ℝ × ℝ => b q.1 q.2) boxMeasure) (r : ℝ) (ξ β : ℤ × ℤ) (c d : ℂ) :
    modeMean ξ (fun τ φ => r * (a τ φ * (phaseFactor β τ φ * c).re + b τ φ * (phaseFactor β τ φ * d).re))
      = (r : ℂ) * ((1 / 2 : ℂ) * (c * modeMean (ξ - β) a + conj c * modeMean (ξ + β) a)
        + (1 / 2 : ℂ) * (d * modeMean (ξ - β) b + conj d * modeMean (ξ + β) b)) := by
  rw [modeMean_const_mul, modeMean_add (integrable_mul_re_phase ha β c) (integrable_mul_re_phase hb β d),
    modeMean_mul_re_phase ha, modeMean_mul_re_phase hb]

private theorem conj_modeVel (β : ℤ × ℤ) (X : ℝ → Space → Space) (σ : ℝ) (x : Space) (k : Fin 3) :
    conj (modeVel β X σ x k) = modeVel (-β) X σ x k :=
  (Bridge.modeAverage_neg_eq_conj β _ k).symm

private theorem modeVel_zero_eq (X : ℝ → Space → Space) (η : ℤ × ℤ) (y : Space) (k : Fin 3) :
    modeVel η X 0 y k = modeMean η (fun τ φ => axialRot (-φ) (X τ (axialRot φ y)) k) := by
  unfold modeVel modeAverage modeMean
  simp only [zero_add]
  rfl

private theorem coupling_at_point {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) {S : Finset (ℤ × ℤ)} (hS : Bridge.IsHarmonicExpansion S W HW)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)} (y : Space)
    (hvy : Integrable (fun q : ℝ × ℝ => v q.1 (axialRot q.2 y)) boxMeasure)
    (hGy : Integrable (fun q : ℝ × ℝ => G q.1 (axialRot q.2 y)) boxMeasure) (ξ : ℤ × ℤ) (i : Fin 3) :
    modeVel ξ (couplingField W v G) 0 y i = ∑ β ∈ S, ∑ j : Fin 3, ∑ l : Fin 3, (alternatingSymbol i j l : ℂ) *
      (curlOfGrad (modeGrad (ξ - β) G 0 y) j * modeVel β W 0 y l
        + modeVel β (vorticityOf W) 0 y j * modeVel (ξ - β) v 0 y l) := by
  have hvy0 : Integrable (fun q : ℝ × ℝ => v (0 + q.1) (axialRot q.2 y)) boxMeasure := by
    simpa only [zero_add] using hvy
  have hGy0 : Integrable (fun q : ℝ × ℝ => G (0 + q.1) (axialRot q.2 y)) boxMeasure := by
    simpa only [zero_add] using hGy
  obtain ⟨A, hA⟩ : ∃ A : Fin 3 → ℝ → ℝ → ℝ,
      A = fun j τ φ => axialRot (-φ) (curlVec (G τ (axialRot φ y))) j := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Fin 3 → ℝ → ℝ → ℝ, V = fun l τ φ => axialRot (-φ) (v τ (axialRot φ y)) l := ⟨_, rfl⟩
  have hAi : ∀ j, Integrable (fun q : ℝ × ℝ => A j q.1 q.2) boxMeasure := by
    intro j
    have e : (fun q : ℝ × ℝ => A j q.1 q.2) = fun q => ∑ a : Fin 3, ∑ b : Fin 3, alternatingSymbol j a b *
        axialRot (-q.2) (G (0 + q.1) (axialRot q.2 y) (axialRot q.2 (unitVector a))) b := by
      funext q
      rw [hA, zero_add]
      beta_reduce
      rw [← _root_.Breakdown.Coercive.Internal.CurlEnergy.curlVec_axialRot]
    rw [e]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (_root_.Breakdown.Coercive.Internal.ModeRotation.integrable_gradComponent axialRotationHolds_proof
        (z := (0, y)) hGy0 (b, a)).const_mul _
  have hVi : ∀ l, Integrable (fun q : ℝ × ℝ => V l q.1 q.2) boxMeasure := by
    intro l
    have h := _root_.Breakdown.Coercive.Internal.ModeRotation.integrable_velComponent axialRotationHolds_proof
      (z := (0, y)) hvy0 l
    subst hV
    simpa only [zero_add] using h
  have hAm : ∀ η j, modeMean η (A j) = curlOfGrad (modeGrad η G 0 y) j := by
    intro η j
    have hc : curlOfGrad (modeGrad η G 0 y) = modeVel η (fun s x => curlVec (G s x)) 0 y :=
      _root_.Breakdown.Coercive.Internal.CurlEnergy.curlOfGrad_modeGrad_eq η (z := (0, y)) hGy0
    rw [hc, modeVel_zero_eq]
    subst hA
    rfl
  have hVm : ∀ η l, modeMean η (V l) = modeVel η v 0 y l := by
    intro η l
    rw [modeVel_zero_eq]
    subst hV
    rfl
  have hWexp := rot_expansion hW.periodic hW.smooth.continuous hS.field_span y
  have hωexp := rot_expansion (periodic_vorticity hW.periodic) (continuous_vorticity hW.smooth)
    (vorticity_span hW hS) y
  obtain ⟨g, hg⟩ : ∃ g : Fin 3 → Fin 3 → ℤ × ℤ → ℝ → ℝ → ℝ, g = fun j l β τ φ =>
      alternatingSymbol i j l * (A j τ φ * (phaseFactor β τ φ * modeVel β W 0 y l).re
        + V l τ φ * (phaseFactor β τ φ * modeVel β (vorticityOf W) 0 y j).re) := ⟨_, rfl⟩
  have hgi : ∀ j l β, Integrable (fun q : ℝ × ℝ => g j l β q.1 q.2) boxMeasure := by
    intro j l β
    subst hg
    exact ((integrable_mul_re_phase (hAi j) β _).add (integrable_mul_re_phase (hVi l) β _)).const_mul _
  have hpt : ∀ τ φ, axialRot (-φ) (couplingField W v G τ (axialRot φ y)) i
      = ∑ j : Fin 3, ∑ l : Fin 3, ∑ β ∈ S, g j l β τ φ := by
    intro τ φ
    unfold couplingField
    rw [axialRot_add_vec, PiLp.add_apply, crossVec_axialRot, crossVec_axialRot, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hWexp, hωexp, hg, hA, hV]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  obtain ⟨t, ht⟩ : ∃ t : Fin 3 → Fin 3 → ℤ × ℤ → ℂ, t = fun j l β => (alternatingSymbol i j l : ℂ) *
      (curlOfGrad (modeGrad (ξ - β) G 0 y) j * modeVel β W 0 y l
        + modeVel β (vorticityOf W) 0 y j * modeVel (ξ - β) v 0 y l) := ⟨_, rfl⟩
  have hterm : ∀ j l β, modeMean ξ (g j l β) = (1 / 2 : ℂ) * t j l β + (1 / 2 : ℂ) * t j l (-β) := by
    intro j l β
    have e := modeMean_pair (hAi j) (hVi l) (alternatingSymbol i j l) ξ β
      (modeVel β W 0 y l) (modeVel β (vorticityOf W) 0 y j)
    have eg : g j l β = fun τ φ => alternatingSymbol i j l * (A j τ φ * (phaseFactor β τ φ * modeVel β W 0 y l).re
        + V l τ φ * (phaseFactor β τ φ * modeVel β (vorticityOf W) 0 y j).re) := by
      rw [hg]
    rw [eg, e, hAm, hAm, hVm, hVm, conj_modeVel, conj_modeVel, ht]
    simp only [sub_neg_eq_add]
    ring
  have hsum : modeMean ξ (fun τ φ => ∑ j : Fin 3, ∑ l : Fin 3, ∑ β ∈ S, g j l β τ φ)
      = ∑ j : Fin 3, ∑ l : Fin 3, ∑ β ∈ S, modeMean ξ (g j l β) := by
    refine (modeMean_sum Finset.univ ξ (fun j τ φ => ∑ l : Fin 3, ∑ β ∈ S, g j l β τ φ)
      fun j _ => integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun β _ => hgi j l β).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (modeMean_sum Finset.univ ξ (fun l τ φ => ∑ β ∈ S, g j l β τ φ)
      fun l _ => integrable_finsetSum _ fun β _ => hgi j l β).trans ?_
    exact Finset.sum_congr rfl fun l _ => modeMean_sum S ξ (fun β τ φ => g j l β τ φ) fun β _ => hgi j l β
  rw [modeVel_zero_eq, show (fun τ φ => axialRot (-φ) (couplingField W v G τ (axialRot φ y)) i)
    = fun τ φ => ∑ j : Fin 3, ∑ l : Fin 3, ∑ β ∈ S, g j l β τ φ from funext fun τ => funext fun φ => hpt τ φ,
    hsum]
  simp_rw [hterm]
  have hhalf : ∀ j l, ∑ β ∈ S, ((1 / 2 : ℂ) * t j l β + (1 / 2 : ℂ) * t j l (-β)) = ∑ β ∈ S, t j l β := by
    intro j l
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_neg_of_symmetric hS.symmetric (fun β => t j l β)]
    ring
  simp_rw [hhalf]
  rw [ht]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

private theorem integrable_apply_rot {M : ℝ × ℝ → (Space →L[ℝ] Space)} (hM : Integrable M boxMeasure) (j : Fin 3) :
    Integrable (fun q : ℝ × ℝ => M q (axialRot q.2 (unitVector j))) boxMeasure := by
  refine hM.norm.mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
  · have hc : Continuous (fun r : (ℝ × ℝ) × (Space →L[ℝ] Space) => r.2 (axialRot r.1.2 (unitVector j))) := by
      unfold axialRot
      fun_prop
    exact hc.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hM.1)
  · refine ((M q).le_opNorm _).trans ?_
    rw [_root_.Breakdown.Coercive.Internal.ModeRotation.norm_axialRot axialRotationHolds_proof, unitVector,
      PiLp.norm_single, norm_one, mul_one]

private theorem modeVel_zero_of_shift {v : ℝ → Space → Space} (hv : IsTimePeriodic v) {y : Space}
    (hvy : Integrable (fun q : ℝ × ℝ => v q.1 (axialRot q.2 y)) boxMeasure) (η : ℤ × ℤ) (s : ℝ × ℝ)
    (hs : modeVel η v s.1 (axialRot s.2 y) = 0) : modeVel η v 0 y = 0 := by
  have h := Bridge.modeShiftRotate v hv η 0 s.1 s.2 y
    (integrableOn_Icc_of_box (by simpa only [zero_add] using hvy))
  rw [zero_add, hs] at h
  refine rotC_eq_zero s.2 fun k => ?_
  have hk := congrFun h k
  rw [Pi.zero_apply] at hk
  exact (mul_eq_zero.1 hk.symm).resolve_left (Complex.exp_ne_zero _)

private theorem modeGrad_zero_of_shift {G : ℝ → Space → (Space →L[ℝ] Space)} (hG : IsTimePeriodic G) {y : Space}
    (hGy : Integrable (fun q : ℝ × ℝ => G q.1 (axialRot q.2 y)) boxMeasure) (η : ℤ × ℤ) (s : ℝ × ℝ)
    (hs : modeGrad η G s.1 (axialRot s.2 y) = 0) : modeGrad η G 0 y = 0 := by
  have hGy0 : Integrable (fun q : ℝ × ℝ => G (0 + q.1) (axialRot q.2 y)) boxMeasure := by
    simpa only [zero_add] using hGy
  have h := Bridge.modeShiftRotateTensor.1 G hG η 0 s.1 s.2 y
    (fun j => integrableOn_Icc_of_box (integrable_apply_rot hGy0 j))
  rw [zero_add, hs] at h
  have hrow : ∀ a b : Fin 3, ∑ c : Fin 3, ((axialRot s.2 (unitVector c) b : ℝ) : ℂ) * modeGrad η G 0 y (a, c) = 0 := by
    intro a b
    have hvec := rotC_eq_zero s.2 (c := fun a => ∑ c : Fin 3,
      ((axialRot s.2 (unitVector c) b : ℝ) : ℂ) * modeGrad η G 0 y (a, c)) (fun i => by
        have hk := congrFun h (i, b)
        rw [Pi.zero_apply] at hk
        have hk' := (mul_eq_zero.1 hk.symm).resolve_left (Complex.exp_ne_zero _)
        rw [← hk']
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        push_cast
        ring)
    exact congrFun hvec a
  funext ab
  obtain ⟨a, b⟩ := ab
  have hvec := rotC_eq_zero s.2 (c := fun c => modeGrad η G 0 y (a, c)) (fun i => hrow a i)
  exact congrFun hvec b

private theorem curlComp_gradArray (m : ℕ) (κ : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) (j : Fin 3) :
    curlComp (gradArray m κ G p) j = curlOfGrad (modeGrad (labelHarmonic m κ) G 0 (planePoint p)) j := by
  simp only [curlComp, curlOfGrad, gradArray, gradAt, labelGrad, permSign_eq_alternatingSymbol]

private theorem sliceMeasure_nonzero : _root_.Breakdown.CertCell.Instance.Internal.MomentUpper.sliceMeasure ≠ 0 := by
  intro h0
  have h1 : _root_.Breakdown.CertCell.Instance.Internal.MomentUpper.sliceMeasure univ = 0 := by
    rw [h0]
    rfl
  rw [_root_.Breakdown.CertCell.Instance.Internal.MomentUpper.sliceMeasure, ← univ_prod_univ, Measure.prod_prod,
    Measure.restrict_apply_univ, Measure.restrict_apply_univ, Real.volume_Ioc, Real.volume_Ioc] at h1
  simp at h1
  linarith [Real.pi_pos]


theorem labelVel_coupling_plane {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {m : ℕ} (hclass : Bridge.IsModeClass Γ m)
    {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) {S : Finset (ℤ × ℤ)} (hS : Bridge.IsHarmonicExpansion S W HW)
    (L : Finset (ℤ × ℤ)) (hL : ∀ α, α ∈ L ↔ labelHarmonic m α ∈ S) (ι : ℤ × ℤ) :
    ∀ᵐ p : ℝ × ℝ, 0 < p.1 → ∀ i : Fin 3,
      labelVel m ι (couplingField W v G) p i = ∑ α ∈ L, ∑ j : Fin 3, ∑ l : Fin 3, (alternatingSymbol i j l : ℂ) *
        (curlComp (gradArray m (ι - α) G p) j * labelVel m α W p l
          + labelVel m α (vorticityOf W) p j * velAt m (ι - α) v l p) := by
  obtain ⟨hlv, hlG, -⟩ := _root_.Breakdown.Coercive.perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv
  have hsv := ae_slice_integrable hlv
  have hsG := ae_slice_integrable hlG
  have hCS := Bridge.classSupport (Bridge.modeOffLattice Bridge.modeShiftRotate Bridge.modeShiftRotateTensor)
    Bridge.labelArithmetic
  have hinj := (Bridge.labelArithmetic m hclass.order_pos).1
  have hz : ∀ η : ℤ × ℤ, ∀ᵐ p : ℝ × ℝ, 0 < p.1 → ∀ᵐ s ∂_root_.Breakdown.CertCell.Instance.Internal.MomentUpper.sliceMeasure,
      (¬ IsLatticeHarmonic m η → modeVel η v s.1 (axialRot s.2 (planePoint p)) = 0 ∧
        modeGrad η G s.1 (axialRot s.2 (planePoint p)) = 0) := by
    intro η
    refine ae_slice_of_ae (Q := fun z => ¬ IsLatticeHarmonic m η → modeVel η v z.1 z.2 = 0 ∧
      modeGrad η G z.1 z.2 = 0) ?_
    by_cases hη : IsLatticeHarmonic m η
    · exact Filter.Eventually.of_forall fun z h => absurd hη h
    · filter_upwards [hCS Γ m P v G H g hclass hv η hη] with z hz' _ using ⟨hz'.1, hz'.2.1⟩
  have := ae_neBot.2 sliceMeasure_nonzero
  filter_upwards [hsv, hsG, ae_all_iff.2 hz] with p h1 h2 h3
  intro hp i
  have hvy : Integrable (fun q : ℝ × ℝ => v q.1 (axialRot q.2 (planePoint p))) boxMeasure := h1 hp
  have hGy : Integrable (fun q : ℝ × ℝ => G q.1 (axialRot q.2 (planePoint p))) boxMeasure := h2 hp
  have hoff : ∀ η, ¬ IsLatticeHarmonic m η →
      modeVel η v 0 (planePoint p) = 0 ∧ modeGrad η G 0 (planePoint p) = 0 := by
    intro η hη
    obtain ⟨s, hs⟩ := (h3 η hp).exists
    exact ⟨modeVel_zero_of_shift hv.periodic_velocity hvy η s (hs hη).1,
      modeGrad_zero_of_shift hv.periodic_gradient hGy η s (hs hη).2⟩
  have hpt := coupling_at_point hW hS (planePoint p) hvy hGy (labelHarmonic m ι) i
  change modeVel (labelHarmonic m ι) (couplingField W v G) 0 (planePoint p) i = _
  rw [hpt]
  have hsub : L.image (labelHarmonic m) ⊆ S := by
    intro β hβ
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hβ
    exact (hL α).1 hα
  rw [← Finset.sum_subset hsub ?_, Finset.sum_image fun a _ b _ hab => hinj hab]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [labelHarmonic_sub]
    simp only [curlComp_gradArray]
    rfl
  · intro β hβS hβ
    have hnl : ¬ IsLatticeHarmonic m β := by
      rintro ⟨α, rfl⟩
      exact hβ (Finset.mem_image.2 ⟨α, (hL α).2 hβS, rfl⟩)
    have hnl' : ¬ IsLatticeHarmonic m (labelHarmonic m ι - β) := by
      rintro ⟨γ, hγ⟩
      refine hnl ⟨ι - γ, ?_⟩
      rw [← labelHarmonic_sub, hγ]
      abel
    obtain ⟨h0v, h0G⟩ := hoff _ hnl'
    simp [h0v, h0G, curlOfGrad]

end Breakdown.CertCell.Assembly.Internal.RowIdentity
