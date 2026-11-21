import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.HeldWeakEquation
import Breakdown.Cert.FreeTransportMild

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ExtendedHeldWeakEquation

open Internal.HeldWeakEquation
open Internal.Convection

theorem profile_joint {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    (q : Fin k → ℝ) : ContDiff ℝ 1 (fun z : ℝ × Space => d.profile q z.1 z.2) :=
  hd.profile_smooth.comp (contDiff_const.prodMk contDiff_id)

theorem joint_deriv_Y {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (z : ℝ × Space) (i : Fin 3) :
    fderiv ℝ (fun z : ℝ × Space => z.2 i • W z.1 z.2) z (0, unitVector i) =
      W z.1 z.2 + z.2 i • fderiv ℝ (W z.1) z.2 (unitVector i) := by
  have hWd : Differentiable ℝ (fun z : ℝ × Space => W z.1 z.2) := hW.differentiable one_ne_zero
  have hp : HasFDerivAt (fun z : ℝ × Space => z.2 i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Space)) z :=
    ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Space)).hasFDerivAt
  have h1 : (unitVector i) i = 1 := by simp [unitVector]
  rw [(show HasFDerivAt (fun z : ℝ × Space => z.2 i • W z.1 z.2) _ z from
    hp.smul (hWd z).hasFDerivAt).fderiv, bar_inr hWd z]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', PiLp.proj_apply, h1, one_smul]
  abel

theorem joint_deriv_A {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (z : ℝ × Space) (i : Fin 3) :
    fderiv ℝ (fun z : ℝ × Space => (W z.1 z.2) i • W z.1 z.2) z (0, unitVector i) =
      (fderiv ℝ (W z.1) z.2 (unitVector i)) i • W z.1 z.2
        + (W z.1 z.2) i • fderiv ℝ (W z.1) z.2 (unitVector i) := by
  have hWd : Differentiable ℝ (fun z : ℝ × Space => W z.1 z.2) := hW.differentiable one_ne_zero
  have hp : HasFDerivAt (fun z : ℝ × Space => (W z.1 z.2) i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z)) z :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp z (hWd z).hasFDerivAt
  rw [(show HasFDerivAt (fun z : ℝ × Space => (W z.1 z.2) i • W z.1 z.2) _ z from
    hp.smul (hWd z).hasFDerivAt).fderiv, bar_inr hWd z]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  abel

theorem flux_time_zero {W φ : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (hφ : IsSpaceTimeTestField φ) :
    Integrable (barT W φ) ∧ ∫ z, barT W φ z = 0 := by
  have hWd : Differentiable ℝ (fun z : ℝ × Space => W z.1 z.2) := hW.differentiable one_ne_zero
  have hΦd : Differentiable ℝ (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.differentiable (by simp)
  exact bar_parts_zero hφ (1, 0) hW (fun z => (bar_inl hWd z).symm) (fun z => (bar_inl hΦd z).symm)

def spaceFlux (W φ : ℝ → Space → Space) (i : Fin 3) (z : ℝ × Space) : ℝ :=
  -(1 / 2 : ℝ) * barY W φ i z - barA W φ i z

theorem flux_space_zero {W φ : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (hφ : IsSpaceTimeTestField φ) (i : Fin 3) :
    Integrable (spaceFlux W φ i) ∧ ∫ z, spaceFlux W φ i z = 0 := by
  have hΦd : Differentiable ℝ (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.differentiable (by simp)
  have gφ : ∀ z : ℝ × Space, fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z (0, unitVector i) =
      fderiv ℝ (φ z.1) z.2 (unitVector i) := fun z => (bar_inr hΦd z _).symm
  have hpr : ContDiff ℝ 1 (fun z : ℝ × Space => z.2 i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
  have hpW : ContDiff ℝ 1 (fun z : ℝ × Space => (W z.1 z.2) i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hW
  obtain ⟨iY, eY⟩ : Integrable (barY W φ i) volume ∧ ∫ z, barY W φ i z = 0 :=
    bar_parts_zero hφ (0, unitVector i) (f := fun z => z.2 i • W z.1 z.2) (hpr.smul hW)
      (fun z => joint_deriv_Y hW z i) gφ
  obtain ⟨iA, eA⟩ : Integrable (barA W φ i) volume ∧ ∫ z, barA W φ i z = 0 :=
    bar_parts_zero hφ (0, unitVector i) (f := fun z => (W z.1 z.2) i • W z.1 z.2) (hpW.smul hW)
      (fun z => joint_deriv_A hW z i) gφ
  have j1 : Integrable (fun z => -(1 / 2 : ℝ) * barY W φ i z) := iY.const_mul _
  refine ⟨j1.sub iA, ?_⟩
  show ∫ z, (-(1 / 2 : ℝ) * barY W φ i z - barA W φ i z) = 0
  rw [integral_sub j1 iA, integral_const_mul, eY, eA]
  ring

def restSmooth (P : ℝ) (W : ℝ → Space → Space) (z : ℝ × Space) : Space :=
  (1 / P) • deriv (fun s => W s z.2) z.1 + (1 / 2 : ℝ) • W z.1 z.2
    + (1 / 2 : ℝ) • fderiv ℝ (W z.1) z.2 z.2 + advectionAt (W z.1) z.2

def gradPair (W φ : ℝ → Space → Space) (z : ℝ × Space) : ℝ :=
  ∑ i : Fin 3, inner ℝ (fderiv ℝ (W z.1) z.2 (unitVector i)) (fderiv ℝ (φ z.1) z.2 (unitVector i))

def secondDerivPair (φ : ℝ → Space → Space) (Hs : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (z : ℝ × Space) : ℝ :=
  inner ℝ (secondDerivTrace (Hs z.1 z.2)) (φ z.1 z.2)

theorem bar_rest_split (P : ℝ) {W φ : ℝ → Space → Space}
    (hdivW : ∀ σ y, divergenceAt (W σ) y = 0) (z : ℝ × Space) :
    barPart P W φ z = inner ℝ (restSmooth P W z) (φ z.1 z.2)
      + (-(1 / P) * barT W φ z + ∑ i : Fin 3, spaceFlux W φ i z) + gradPair W φ z := by
  have h1 := hdivW z.1 z.2
  simp only [divergenceAt, Fin.sum_univ_three] at h1
  simp only [barPart, sigmaSimilarityIntegrand, restSmooth, spaceFlux, gradPair, barT, barY, barA,
    barFlux, advectionAt]
  rw [apply_eq_sum_unitVector (fderiv ℝ (φ z.1) z.2) z.2,
    apply_eq_sum_unitVector (fderiv ℝ (W z.1) z.2) z.2,
    apply_eq_sum_unitVector (fderiv ℝ (W z.1) z.2) (W z.1 z.2)]
  simp only [Fin.sum_univ_three, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  linear_combination (inner ℝ (W z.1 z.2) (φ z.1 z.2)) * h1

theorem restSmooth_continuous (P : ℝ) {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) : Continuous (restSmooth P W) := by
  have hWd : Differentiable ℝ (fun z : ℝ × Space => W z.1 z.2) := hW.differentiable one_ne_zero
  have eW : ∀ z : ℝ × Space, ∀ w, fderiv ℝ (W z.1) z.2 w =
      fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z (0, w) := fun z w => bar_inr hWd z w
  have et : ∀ z : ℝ × Space, deriv (fun s => W s z.2) z.1 =
      fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z (1, 0) := fun z => bar_inl hWd z
  have e : restSmooth P W = fun z => (1 / P) • fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z (1, 0)
      + (1 / 2 : ℝ) • W z.1 z.2 + (1 / 2 : ℝ) • fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z (0, z.2)
      + fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z (0, W z.1 z.2) := by
    funext z
    simp only [restSmooth, advectionAt, et z, eW z]
  have hWc : Continuous (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z) :=
    hW.continuous_fderiv one_ne_zero
  have h0 : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  rw [e]
  exact ((((hWc.clm_apply continuous_const).const_smul (1 / P)).add (h0.const_smul (1 / 2 : ℝ))).add
    ((hWc.clm_apply (continuous_const.prodMk continuous_snd)).const_smul (1 / 2 : ℝ))).add
    (hWc.clm_apply (continuous_const.prodMk h0))

theorem slice_column_continuous {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (i : Fin 3) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (unitVector i)) := by
  have hWd : Differentiable ℝ (fun z : ℝ × Space => W z.1 z.2) := hW.differentiable one_ne_zero
  have hWc : Continuous (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z) :=
    hW.continuous_fderiv one_ne_zero
  have e : (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (unitVector i)) =
      fun z => fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z (0, unitVector i) :=
    funext fun z => bar_inr hWd z _
  rw [e]
  exact hWc.clm_apply continuous_const

theorem gradPair_integrable {W φ : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (hφ : IsSpaceTimeTestField φ) :
    Integrable (gradPair W φ) := by
  show Integrable (fun z : ℝ × Space => ∑ i : Fin 3,
    inner ℝ (fderiv ℝ (W z.1) z.2 (unitVector i)) (fderiv ℝ (φ z.1) z.2 (unitVector i)))
  refine integrable_finsetSum _ fun i _ => ?_
  exact ((slice_column_continuous hW i).inner (quad_column hφ i).1).integrable_of_hasCompactSupport
    (bar_cst_inner_right (quad_column hφ i).2)

theorem bar_rest_identity (P : ℝ) {W φ : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (hdivW : ∀ σ y, divergenceAt (W σ) y = 0) (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (restSmooth P W z) (φ z.1 z.2)) ∧
    Integrable (barPart P W φ) ∧
    ∫ z, barPart P W φ z = (∫ z : ℝ × Space, inner ℝ (restSmooth P W z) (φ z.1 z.2))
      + ∫ z, gradPair W φ z := by
  have iS : Integrable (fun z : ℝ × Space => inner ℝ (restSmooth P W z) (φ z.1 z.2)) :=
    ((restSmooth_continuous P hW).inner hφ.1.continuous).integrable_of_hasCompactSupport
      (bar_cst_inner_right hφ.2.1)
  obtain ⟨iT, eT⟩ := flux_time_zero hW hφ
  have iE : Integrable (fun z => ∑ i : Fin 3, spaceFlux W φ i z) :=
    integrable_finsetSum _ fun i _ => (flux_space_zero hW hφ i).1
  have eE : ∫ z, ∑ i : Fin 3, spaceFlux W φ i z = 0 := by
    rw [integral_finsetSum _ fun i _ => (flux_space_zero hW hφ i).1]
    exact Finset.sum_eq_zero fun i _ => (flux_space_zero hW hφ i).2
  have iT' : Integrable (fun z => -(1 / P) * barT W φ z) := iT.const_mul _
  have iR : Integrable (fun z => -(1 / P) * barT W φ z + ∑ i : Fin 3, spaceFlux W φ i z) :=
    iT'.add iE
  have eR : ∫ z, (-(1 / P) * barT W φ z + ∑ i : Fin 3, spaceFlux W φ i z) = 0 := by
    rw [integral_add iT' iE, integral_const_mul, eT, eE]
    ring
  have iG := gradPair_integrable hW hφ
  have hfun : barPart P W φ = fun z => inner ℝ (restSmooth P W z) (φ z.1 z.2)
      + (-(1 / P) * barT W φ z + ∑ i : Fin 3, spaceFlux W φ i z) + gradPair W φ z :=
    funext (bar_rest_split P hdivW)
  have iSR : Integrable (fun z => inner ℝ (restSmooth P W z) (φ z.1 z.2)
      + (-(1 / P) * barT W φ z + ∑ i : Fin 3, spaceFlux W φ i z)) := iS.add iR
  refine ⟨iS, by rw [hfun]; exact iSR.add iG, ?_⟩
  rw [hfun, integral_add iSR iG, integral_add iS iR, eR, add_zero]

theorem secondDerivTrace_norm_le (H : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖secondDerivTrace H‖ ≤ 3 * ‖H‖ := by
  unfold secondDerivTrace
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ j : Fin 3, ‖H (unitVector j) (unitVector j)‖ ≤ ‖H‖ := fun j => by
    have h1 := H.le_opNorm₂ (unitVector j) (unitVector j)
    have h2 : ‖unitVector j‖ = 1 := by simp [unitVector]
    rw [h2, mul_one, mul_one] at h1
    exact h1
  calc ∑ j : Fin 3, ‖H (unitVector j) (unitVector j)‖ ≤ ∑ _j : Fin 3, ‖H‖ :=
        Finset.sum_le_sum fun j _ => h j
    _ = 3 * ‖H‖ := by simp

theorem secondDerivTrace_continuous :
    Continuous (fun H : Space →L[ℝ] Space →L[ℝ] Space => secondDerivTrace H) := by
  unfold secondDerivTrace
  exact continuous_finsetSum _ fun j _ =>
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem decay_nonneg {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    {q : Fin k → ℝ} (hq : q ∈ d.params) : 0 ≤ d.decay := by
  have h := (hd.profile_decay q hq 0 0).1
  rw [norm_zero, add_zero, div_one] at h
  exact (norm_nonneg _).trans h

theorem secondDerivPair_integrable {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    {q : Fin k → ℝ} (hq : q ∈ d.params) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (secondDerivPair φ (d.profileSecondDeriv q)) := by
  have hφc : Continuous (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.continuous
  have hdec := decay_nonneg hd hq
  have iN : Integrable (fun z : ℝ × Space => (3 * d.decay) * ‖φ z.1 z.2‖) :=
    (hφc.norm.integrable_of_hasCompactSupport hφ.2.1.norm).const_mul _
  have hm : AEStronglyMeasurable (secondDerivPair φ (d.profileSecondDeriv q)) volume :=
    (secondDerivTrace_continuous.comp_aestronglyMeasurable
      (hd.profileSecondDeriv_measurable q hq)).inner hφc.aestronglyMeasurable
  refine iN.mono' hm (ae_of_all _ fun z => ?_)
  have hH : ‖d.profileSecondDeriv q z.1 z.2‖ ≤ d.decay := by
    refine ((hd.profile_decay q hq z.1 z.2).2.2).trans (div_le_self hdec ?_)
    exact one_le_pow₀ (by linarith [norm_nonneg z.2])
  calc ‖secondDerivPair φ (d.profileSecondDeriv q) z‖
        ≤ ‖secondDerivTrace (d.profileSecondDeriv q z.1 z.2)‖ * ‖φ z.1 z.2‖ := norm_inner_le_norm _ _
    _ ≤ (3 * d.decay) * ‖φ z.1 z.2‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (secondDerivTrace_norm_le _).trans (by linarith)

theorem ssp_slice {W : ℝ → Space → Space} {Hs : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {φ : ℝ → Space → Space} (σ : ℝ)
    (hw : ∀ j : Fin 3, IsWeakGradient (fun y => fderiv ℝ (W σ) y (unitVector j))
      (fun y => (Hs σ y).flip (unitVector j)))
    (hφ : IsSpaceTimeTestField φ) :
    ∫ y, gradPair W φ (σ, y) = -∫ y, secondDerivPair φ Hs (σ, y) := by
  obtain ⟨R, -, hR⟩ := Internal.TestPairing.exists_bound hφ.2.1
  have hψ := Internal.TestPairing.slice_contDiff hφ.1 σ
  have hψs := Internal.TestPairing.slice_hasCompactSupport hR σ
  have hI := fun j k => Internal.FreePerturbation.slice_column_velocity (hw j) hψ hψs j k
  have eG : (fun y => gradPair W φ (σ, y)) = fun y => ∑ j : Fin 3, ∑ k : Fin 3,
      fderiv ℝ (φ σ) y (unitVector j) k * fderiv ℝ (W σ) y (unitVector j) k := by
    funext y
    simp only [gradPair, Internal.FreePerturbation.inner_eq_sum_coord, mul_comm]
  have eH : (fun y => secondDerivPair φ Hs (σ, y)) = fun y => ∑ j : Fin 3, ∑ k : Fin 3,
      φ σ y k * ((Hs σ y).flip (unitVector j) (unitVector j)) k := by
    funext y
    simp only [secondDerivPair, secondDerivTrace, ContinuousLinearMap.flip_apply, sum_inner,
      Internal.FreePerturbation.inner_eq_sum_coord, mul_comm]
  rw [eG, eH, integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => (hI j k).2.1),
    integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => (hI j k).1),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ (fun k _ => (hI j k).2.1), integral_finsetSum _ (fun k _ => (hI j k).1),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  linarith [(hI j k).2.2]

theorem ssp_zero {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    {q : Fin k → ℝ} (hq : q ∈ d.params) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (secondDerivPair φ (d.profileSecondDeriv q)) ∧
    ∫ z, gradPair (d.profile q) φ z = -∫ z, secondDerivPair φ (d.profileSecondDeriv q) z := by
  have iG := gradPair_integrable (profile_joint hd q) hφ
  have iH := secondDerivPair_integrable hd hq hφ
  refine ⟨iH, ?_⟩
  have iG' : Integrable (gradPair (d.profile q) φ) ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    rw [← Measure.volume_eq_prod]; exact iG
  have iH' : Integrable (secondDerivPair φ (d.profileSecondDeriv q))
      ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    rw [← Measure.volume_eq_prod]; exact iH
  rw [Measure.volume_eq_prod, integral_prod _ iG', integral_prod _ iH', ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun σ => ?_)
  exact ssp_slice σ (fun j => hd.profileSecondDeriv_weak q hq σ j) hφ

theorem defect_parts {k : ℕ} (d : ExtendedCertificateData k) (q : Fin k → ℝ) (z : ℝ × Space) :
    d.defect q z.1 z.2 = restSmooth (d.period q) (d.profile q) z
      - secondDerivTrace (d.profileSecondDeriv q z.1 z.2)
      + ∑ i, d.multiplier q i • d.actuator i z.1 z.2 + d.pressureGrad q z.1 z.2 := by
  simp only [ExtendedCertificateData.defect, weakDefectField, restSmooth]
  abel

theorem actuator_field {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    (i : Fin k) : IsPeriodicField (d.actuator i) := by
  refine ⟨hd.actuator_measurable i, hd.actuator_periodic i, lt_of_le_of_lt ?_
    (lt_of_le_of_lt hd.actuator_norm ENNReal.ofReal_lt_top)⟩
  exact Finset.single_le_sum (f := fun j => periodLIntegral (fun σ y => ‖d.actuator j σ y‖ ^ 2))
    (fun j _ => bot_le) (Finset.mem_univ i)

theorem actuator_pair_integrable {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) (m : Fin k → ℝ) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (∑ i, m i • d.actuator i z.1 z.2) (φ z.1 z.2)) := by
  have hφc : Continuous (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.continuous
  have he : (fun z : ℝ × Space => inner ℝ (∑ i, m i • d.actuator i z.1 z.2) (φ z.1 z.2)) =
      fun z => ∑ i, m i * inner ℝ (d.actuator i z.1 z.2) (φ z.1 z.2) := by
    funext z
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _
  rw [he]
  exact integrable_finsetSum _ fun i _ =>
    (pairing_integrable (actuator_field hd i) hφc hφ.2.1).const_mul (m i)

theorem cross_pair_integrable {W : ℝ → Space → Space}
    (hW : Continuous (fun z : ℝ × Space => W z.1 z.2)) {u : XX} {v : VelField} {G : GradField}
    {H : SecondField} (hr : IsReadingOf u v G H) (hsup : supGrad u < ⊤) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) : Integrable (crossPart W v φ) := by
  obtain ⟨hc, hs⟩ := test_fderiv hφ
  have hcont : Continuous (crossTest W φ) := by
    refine continuous_finsetSum _ fun i _ => ?_
    have h1 : Continuous (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 (unitVector i)) :=
      hc.clm_apply continuous_const
    have h2 : Continuous (fun z : ℝ × Space =>
        inner ℝ (W z.1 z.2) (fderiv ℝ (φ z.1) z.2 (unitVector i))) := hW.inner h1
    exact ((((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hW)).smul h1).add
      (h2.smul continuous_const)
  have hsupp : HasCompactSupport (crossTest W φ) := by
    refine hs.mono fun z hz => ?_
    intro h0
    apply hz
    simp only [crossTest, h0, ContinuousLinearMap.zero_apply, smul_zero, inner_zero_right,
      zero_smul, add_zero, Finset.sum_const_zero]
  have h := (velocity_local hr hsup hcont hsupp).1.neg
  refine h.congr (ae_of_all _ fun z => ?_)
  exact (cross_eq_inner _ _ _ z).symm

theorem conv_point (A B : Space →L[ℝ] Space) (w x ψ : Space) :
    ∑ j : Fin 3, inner ℝ (A (unitVector j)) (w j • ψ)
      + inner ℝ x (∑ j : Fin 3, inner ℝ (B (unitVector j)) ψ • unitVector j) =
      inner ℝ (A w + B x) ψ := by
  rw [apply_eq_sum_unitVector A w, apply_eq_sum_unitVector B x]
  simp only [Fin.sum_univ_three, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, cross_inner_unit]
  ring

theorem conv_pair_integrable {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) {u : XX} {v : VelField} {G : GradField}
    {H : SecondField} (hr : IsReadingOf u v G H) (hsup : supGrad u < ⊤) {Γ : Set Symmetry} {P : ℝ}
    {g : ℝ → Space → Space} (hg : IsPerturbation Γ P v G H g) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ
      (G z.1 z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2)) (φ z.1 z.2)) := by
  have hφc : Continuous (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.continuous
  have hW0 : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  have i1 : ∀ j : Fin 3, Integrable (fun z : ℝ × Space =>
      inner ℝ (G z.1 z.2 (unitVector j)) ((W z.1 z.2) j • φ z.1 z.2)) := by
    intro j
    have hc1 : Continuous (fun z : ℝ × Space => (W z.1 z.2) j • φ z.1 z.2) :=
      ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp hW0).smul hφc
    have hs1 : HasCompactSupport (fun z : ℝ × Space => (W z.1 z.2) j • φ z.1 z.2) := by
      refine hφ.2.1.mono fun z hz => ?_
      intro h0
      apply hz
      have h0' : φ z.1 z.2 = 0 := h0
      simp only [h0', smul_zero]
    exact pairing_integrable (column_periodic hg j) hc1 hs1
  have hc2 : Continuous (fun z : ℝ × Space => ∑ j : Fin 3,
      inner ℝ (fderiv ℝ (W z.1) z.2 (unitVector j)) (φ z.1 z.2) • unitVector j) :=
    by
    refine continuous_finsetSum _ fun j _ => ?_
    have hcj : Continuous (fun z : ℝ × Space =>
        inner ℝ (fderiv ℝ (W z.1) z.2 (unitVector j)) (φ z.1 z.2)) :=
      (slice_column_continuous hW j).inner hφc
    exact hcj.smul continuous_const
  have hs2 : HasCompactSupport (fun z : ℝ × Space => ∑ j : Fin 3,
      inner ℝ (fderiv ℝ (W z.1) z.2 (unitVector j)) (φ z.1 z.2) • unitVector j) := by
    refine hφ.2.1.mono fun z hz => ?_
    intro h0
    apply hz
    have h0' : φ z.1 z.2 = 0 := h0
    simp only [h0', inner_zero_right, zero_smul, Finset.sum_const_zero]
  have i2 : Integrable (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (∑ j : Fin 3,
      inner ℝ (fderiv ℝ (W z.1) z.2 (unitVector j)) (φ z.1 z.2) • unitVector j)) :=
    (velocity_local hr hsup hc2 hs2).1
  have i12 : Integrable (fun z : ℝ × Space =>
      ∑ j : Fin 3, inner ℝ (G z.1 z.2 (unitVector j)) ((W z.1 z.2) j • φ z.1 z.2)
        + inner ℝ (v z.1 z.2) (∑ j : Fin 3,
          inner ℝ (fderiv ℝ (W z.1) z.2 (unitVector j)) (φ z.1 z.2) • unitVector j)) :=
    (integrable_finsetSum _ fun j _ => i1 j).add i2
  have e : (fun z : ℝ × Space =>
      ∑ j : Fin 3, inner ℝ (G z.1 z.2 (unitVector j)) ((W z.1 z.2) j • φ z.1 z.2)
        + inner ℝ (v z.1 z.2) (∑ j : Fin 3,
          inner ℝ (fderiv ℝ (W z.1) z.2 (unitVector j)) (φ z.1 z.2) • unitVector j)) =
      fun z : ℝ × Space => inner ℝ
        (G z.1 z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2)) (φ z.1 z.2) :=
    funext fun z => conv_point _ _ _ _ _
  rw [← e]
  exact i12

theorem slice_weak_profile {W : ℝ → Space → Space} {c : ℝ}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (σ : ℝ)
    (hdiv : ∀ y, divergenceAt (W σ) y = 0) (hb0 : ∀ y, ‖W σ y‖ ≤ c / (1 + ‖y‖))
    (hb1 : ∀ y, ‖fderiv ℝ (W σ) y‖ ≤ c / (1 + ‖y‖) ^ 2) :
    ∃ C, WeakProfile.IsSlice (W σ) (fun y => fderiv ℝ (W σ) y) C := by
  have hs : ContDiff ℝ 1 (W σ) := bar_slice_contDiff hW σ
  have hc : Continuous (W σ) := hs.continuous
  have hdc : Continuous (fun y => fderiv ℝ (W σ) y) := hs.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ (W σ) := hs.differentiable one_ne_zero
  have hfin6 : (Module.finrank ℝ Space : ℝ) < 6 := by
    simp only [finrank_euclideanSpace, Fintype.card_fin]; norm_num
  have hfin4 : (Module.finrank ℝ Space : ℝ) < 4 := by
    simp only [finrank_euclideanSpace, Fintype.card_fin]; norm_num
  have i6 : Integrable (fun y : Space => c ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ))) :=
    (integrable_one_add_norm hfin6).const_mul _
  have i4 : Integrable (fun y : Space => c ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ))) :=
    (integrable_one_add_norm hfin4).const_mul _
  have b6 : ∀ y, ‖W σ y‖ ^ 6 ≤ c ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ)) := by
    intro y
    have hpos : 0 < 1 + ‖y‖ := by positivity
    calc ‖W σ y‖ ^ 6 ≤ (c / (1 + ‖y‖)) ^ 6 :=
          pow_le_pow_left₀ (norm_nonneg _) (hb0 y) 6
      _ = c ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ)) := by
          rw [div_pow, Real.rpow_neg hpos.le, div_eq_mul_inv]
          norm_cast
  have b2 : ∀ y, ‖fderiv ℝ (W σ) y‖ ^ 2 ≤ c ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
    intro y
    have hpos : 0 < 1 + ‖y‖ := by positivity
    calc ‖fderiv ℝ (W σ) y‖ ^ 2 ≤ (c / (1 + ‖y‖) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hb1 y) 2
      _ = c ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
          rw [div_pow, ← pow_mul, Real.rpow_neg hpos.le, div_eq_mul_inv]
          norm_num
  have n6 : 0 ≤ ∫ y : Space, c ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ)) :=
    integral_nonneg fun y => by positivity
  have n4 : 0 ≤ ∫ y : Space, c ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) :=
    integral_nonneg fun y => by positivity
  refine ⟨(∫ y : Space, c ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ)))
    + ∫ y : Space, c ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)), ⟨⟨hc.locallyIntegrable, hdc.locallyIntegrable,
      fun ψ hψ i => ?_⟩, ae_of_all _ fun y => hdiv y, ?_, ?_⟩⟩
  · have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
    have hψc : Continuous (fun y => fderiv ℝ ψ y (unitVector i)) :=
      (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have h1 : Integrable (fun y => fderiv ℝ ψ y (unitVector i) • W σ y) :=
      (hψc.smul hc).integrable_of_hasCompactSupport
        ((hψ.2.fderiv_apply (𝕜 := ℝ) (unitVector i)).smul_right)
    have h2 : Integrable (fun y => ψ y • fderiv ℝ (W σ) y (unitVector i)) :=
      (hψ.1.continuous.smul (hdc.clm_apply continuous_const)).integrable_of_hasCompactSupport
        hψ.2.smul_right
    have h3 : Integrable (fun y => ψ y • W σ y) :=
      (hψ.1.continuous.smul hc).integrable_of_hasCompactSupport hψ.2.smul_right
    exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h1 h2 h3 (fun y _ => hψd y)
      (fun y _ => hdiff y)
  · refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right n4))
    rw [ofReal_integral_eq_lintegral_ofReal i6 (ae_of_all _ fun y => by positivity)]
    exact lintegral_mono fun y => ENNReal.ofReal_le_ofReal (b6 y)
  · refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left n6))
    rw [ofReal_integral_eq_lintegral_ofReal i4 (ae_of_all _ fun y => by positivity)]
    exact lintegral_mono fun y => ENNReal.ofReal_le_ofReal (b2 y)

theorem slice_embed {W : ℝ → Space → Space} {c : ℝ}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (σ : ℝ)
    (hdiv : ∀ y, divergenceAt (W σ) y = 0) (hb0 : ∀ y, ‖W σ y‖ ≤ c / (1 + ‖y‖))
    (hb1 : ∀ y, ‖fderiv ℝ (W σ) y‖ ≤ c / (1 + ‖y‖) ^ 2) :
    ∃ w : X, (velocity w : Space → Space) =ᵐ[volume] W σ ∧
      ∀ j : Fin 3, (partialX j w : Space → Space) =ᵐ[volume]
        fun y => fderiv ℝ (W σ) y (unitVector j) := by
  obtain ⟨C, hC⟩ := slice_weak_profile hW σ hdiv hb0 hb1
  obtain ⟨w, e1, e2, -⟩ := WeakProfile.sliceEmbedding_holds WeakProfile.pairingVelocity_holds
    WeakProfile.velocityWeakGradient_holds WeakProfile.zeroGradientSix_holds
    WeakProfile.gradientFreqTr_holds _ _ C hC
  exact ⟨w, e1, e2⟩

theorem slice_cross {W : ℝ → Space → Space} {c : ℝ}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (hdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hb : ∀ σ y, ‖W σ y‖ ≤ c / (1 + ‖y‖) ∧ ‖fderiv ℝ (W σ) y‖ ≤ c / (1 + ‖y‖) ^ 2)
    {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    ∀ᵐ σ : ℝ, ∫ y, crossPart W v φ (σ, y) = ∫ y, inner ℝ
      (G σ y (W σ y) + fderiv ℝ (W σ) y (v σ y)) (φ σ y) := by
  obtain ⟨R, -, hR⟩ := Internal.TestPairing.exists_bound hφ.2.1
  obtain ⟨C, hC⟩ := trilinear_holds
  filter_upwards [hr.velocity_eq, hr.weak_gradient] with σ h1 h2
  obtain ⟨w, hw1, hw2⟩ := slice_embed hW σ (hdiv σ) (fun y => (hb σ y).1) (fun y => (hb σ y).2)
  have hψ : IsTestField (φ σ) := ⟨Internal.TestPairing.slice_contDiff hφ.1 σ,
    Internal.TestPairing.slice_hasCompactSupport hR σ, hφ.2.2 σ⟩
  have hψ2 : MemLp (φ σ) 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1
  have hψ6 : MemLp (φ σ) 6 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1
  have hG : ∀ᵐ y, ∀ j : Fin 3, G σ y (unitVector j) =
      (partialX j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) y :=
    ae_all_iff.2 fun j => partialX_ae_of_weakGradient h2 _ h1 j
  have hW2 : ∀ᵐ y, ∀ j : Fin 3, (partialX j w : Space → Space) y =
      fderiv ℝ (W σ) y (unitVector j) := ae_all_iff.2 hw2
  have key := cross_polarize w (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) hψ
  obtain ⟨K, hK⟩ := WeakProfile.Internal.AdvectionByParts.pairForm_bound hψ
  have eL : ∫ y, crossPart W v φ (σ, y) =
      -((∫ y, WeakProfile.Internal.AdvectionByParts.pairForm (φ σ) (velocity w)
          (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))) y)
        + ∫ y, WeakProfile.Internal.AdvectionByParts.pairForm (φ σ)
          (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))) (velocity w) y) := by
    rw [← integral_add (hK _ _).1 (hK _ _).1, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [h1, hw1] with y hy1 hy2
    exact cross_slice_left _ _ _ σ _ _ y hy1 hy2
  have eR : ∫ y, inner ℝ (G σ y (W σ y) + fderiv ℝ (W σ) y (v σ y)) (φ σ y) =
      trilinear w (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) (φ σ)
        + trilinear (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) w (φ σ) := by
    unfold trilinear
    rw [← integral_add (hC w _ _ hψ2 hψ6).1 (hC _ w _ hψ2 hψ6).1]
    refine integral_congr_ae ?_
    filter_upwards [h1, hw1, hG, hW2] with y hy1 hy2 hy3 hy4
    exact cross_slice_right (G σ y) (fderiv ℝ (W σ) y) (W σ y) (v σ y) (φ σ y)
      _ _ (fun j => (partialX j w : Space → Space))
      (fun j => (partialX j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space))
      y hy1 hy2 hy3 hy4
  calc _ = _ := eL
    _ = _ := congrArg Neg.neg key
    _ = _ := neg_neg _
    _ = _ := eR.symm

theorem cross_pair_identity {W : ℝ → Space → Space} {c : ℝ}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (hdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hb : ∀ σ y, ‖W σ y‖ ≤ c / (1 + ‖y‖) ∧ ‖fderiv ℝ (W σ) y‖ ≤ c / (1 + ‖y‖) ^ 2)
    {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) (hsup : supGrad u < ⊤) {Γ : Set Symmetry} {P : ℝ}
    {g : ℝ → Space → Space} (hg : IsPerturbation Γ P v G H g) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) :
    Integrable (crossPart W v φ) ∧
    ∫ z, crossPart W v φ z = ∫ z : ℝ × Space, inner ℝ
      (G z.1 z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2)) (φ z.1 z.2) := by
  have h1 := cross_pair_integrable hW.continuous hr hsup hφ
  have h2 := conv_pair_integrable hW hr hsup hg hφ
  refine ⟨h1, ?_⟩
  rw [Measure.volume_eq_prod] at h1 h2 ⊢
  rw [integral_prod _ h1, integral_prod _ h2]
  exact integral_congr_ae (slice_cross hW hdiv hb hr hφ)

end Internal.ExtendedHeldWeakEquation

open Internal.HeldWeakEquation Internal.ExtendedHeldWeakEquation

theorem extendedHeldWeakEquationHolds_of (h1 : FreePerturbationHolds)
    (h2 : ExtendedConvectionHolds) (h3 : ExtendedDataHolds) (h4 : ProductPairingHolds)
    (h5 : ProductBoundHolds) (_h6 : TestPairingHolds) : ExtendedHeldWeakEquationHolds := by
  intro k d hd q hq f κ hf hκ v G H hr φ hφ
  have hP := hd.period_pos q hq
  obtain ⟨g, hg, hgφ⟩ := h1 d.symmetries (d.period q) hP f hf.invariant v G H hr
  have hsup : supGrad (freeInv (d.period q) f) < ⊤ := lt_of_le_of_lt hf.sup ENNReal.ofReal_lt_top
  have hW := profile_joint hd q
  obtain ⟨iS, iB, eB⟩ := bar_rest_identity (d.period q) hW (hd.profile_divergence q hq) hφ
  obtain ⟨iH, eSsp⟩ := ssp_zero hd hq hφ
  have iA := actuator_pair_integrable hd (d.multiplier q) hφ
  obtain ⟨iv, iG, ig⟩ := lin_integrable hr hsup hg hφ
  obtain ⟨iC, eC⟩ := cross_pair_identity hW (hd.profile_divergence q hq)
    (fun σ y => ⟨(hd.profile_decay q hq σ y).1, (hd.profile_decay q hq σ y).2.1⟩) hr hsup hg hφ
  obtain ⟨iQ, eQ⟩ := quad_identity hr hsup hφ h5
  have iL : Integrable (linPart (d.period q) v G φ) := iv.add iG
  have hsplit : sigmaSimilarityIntegrand (d.period q) (fun σ y => d.profile q σ y + v σ y)
      (fun σ y => fderiv ℝ (d.profile q σ) y + G σ y) φ = fun z =>
        barPart (d.period q) (d.profile q) φ z + linPart (d.period q) v G φ z
          + crossPart (d.profile q) v φ z + quadPart v φ z :=
    funext (integrand_split (d.period q) (d.profile q) v G φ)
  have iBL : Integrable (fun z => barPart (d.period q) (d.profile q) φ z
      + linPart (d.period q) v G φ z) := iB.add iL
  have iBLC : Integrable (fun z => barPart (d.period q) (d.profile q) φ z
      + linPart (d.period q) v G φ z + crossPart (d.profile q) v φ z) := iBL.add iC
  rw [hsplit]
  refine ⟨iBLC.add iQ, ?_⟩
  beta_reduce
  rw [integral_add iBLC iQ, integral_add iBL iC, integral_add iB iL]
  have eL : ∫ z, linPart (d.period q) v G φ z = inner ℝ f (testInHH φ) := by
    rw [← hgφ φ hφ]
    unfold linPart
    rw [integral_add iv iG, integral_add ig iG]
    congr 1
    exact hg.transport φ ⟨hφ.1, hφ.2.1⟩
  have eCv := (h2 d hd q hq).2.2 (freeInv (d.period q) f) v G H hr φ hφ
  have eD := (h3 d hd q hq).2.1 φ hφ
  have eAct := (h3 d hd q hq).2.2.2.1 κ φ hφ
  have eP := h4 (freeInv (d.period q) f) (freeInv (d.period q) f) hsup φ hφ
  have heq := congrArg (fun x => inner ℝ x (testInHH φ)) hf.equation
  simp only [inner_add_left, inner_zero_left] at heq
  have hκ' : κ = -d.multiplier q := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hκ
  have eAct' : ∫ z : ℝ × Space, inner ℝ (∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2) =
      -∫ z : ℝ × Space, inner ℝ (∑ i, d.multiplier q i • d.actuator i z.1 z.2) (φ z.1 z.2) := by
    rw [← integral_neg]
    congr 1
    funext z
    simp only [hκ', Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, inner_neg_left]
  have iD : Integrable (fun z : ℝ × Space => inner ℝ (d.defect q z.1 z.2) (φ z.1 z.2)) :=
    pairing_integrable (h3 d hd q hq).1 hφ.1.continuous hφ.2.1
  have hDs : (fun z : ℝ × Space => inner ℝ (d.defect q z.1 z.2) (φ z.1 z.2)) = fun z =>
      inner ℝ (restSmooth (d.period q) (d.profile q) z) (φ z.1 z.2)
        - secondDerivPair φ (d.profileSecondDeriv q) z
        + inner ℝ (∑ i, d.multiplier q i • d.actuator i z.1 z.2) (φ z.1 z.2)
        + inner ℝ (d.pressureGrad q z.1 z.2) (φ z.1 z.2) := by
    funext z
    rw [defect_parts d q z]
    simp only [secondDerivPair, inner_add_left, inner_sub_left]
  have iSHA : Integrable (fun z : ℝ × Space =>
      inner ℝ (restSmooth (d.period q) (d.profile q) z) (φ z.1 z.2)
        - secondDerivPair φ (d.profileSecondDeriv q) z
        + inner ℝ (∑ i, d.multiplier q i • d.actuator i z.1 z.2) (φ z.1 z.2)) :=
    (iS.sub iH).add iA
  have iPg : Integrable (fun z : ℝ × Space => inner ℝ (d.pressureGrad q z.1 z.2) (φ z.1 z.2)) := by
    refine (iD.sub iSHA).congr (ae_of_all _ fun z => ?_)
    have e := congrFun hDs z
    simp only [Pi.sub_apply] at e ⊢
    rw [e]
    ring
  have ePg : ∫ z : ℝ × Space, inner ℝ (d.pressureGrad q z.1 z.2) (φ z.1 z.2) = 0 :=
    hd.pressureGrad_orthogonal q hq φ hφ
  have eDs : ∫ z : ℝ × Space, inner ℝ (d.defect q z.1 z.2) (φ z.1 z.2) =
      (∫ z : ℝ × Space, inner ℝ (restSmooth (d.period q) (d.profile q) z) (φ z.1 z.2))
        - (∫ z, secondDerivPair φ (d.profileSecondDeriv q) z)
        + ∫ z : ℝ × Space, inner ℝ (∑ i, d.multiplier q i • d.actuator i z.1 z.2) (φ z.1 z.2) := by
    have iSH : Integrable (fun z : ℝ × Space =>
        inner ℝ (restSmooth (d.period q) (d.profile q) z) (φ z.1 z.2)
          - secondDerivPair φ (d.profileSecondDeriv q) z) := iS.sub iH
    rw [hDs, integral_add iSHA iPg, ePg, add_zero, integral_add iSH iA, integral_sub iS iH]
  linarith

end Breakdown.Cert
