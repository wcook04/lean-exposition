import Breakdown.CertCell.TailStatements
import Breakdown.FracCell.CylinderComp
import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoerciveSmoothApproxClassSixth

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

namespace Internal.FlipDecay

open CellCert.CellAnalysis.LowEntry.Internal (cylArg)
open Coercive.Internal.ModeRotation (expFactor expFactor_add_period)

theorem ae_orbit_of_ae {Q : ℝ × Space → Prop} (h : ∀ᵐ z : ℝ × Space, Q z) :
    ∀ᵐ p : ℝ × ℝ, ∀ᵐ q : ℝ × ℝ, Q (q.1, cylArg (p, q.2)) := by
  have hΦ : Measure.QuasiMeasurePreserving (Prod.map (id : ℝ → ℝ) cylArg)
      ((volume : Measure ℝ).prod (volume : Measure ((ℝ × ℝ) × ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure Space)) :=
    QuasiMeasurePreserving.prodMap (Measure.QuasiMeasurePreserving.id volume)
      CellCert.CellAnalysis.CylinderCompInternal.qmp_full
  have hs : MeasurePreserving (Prod.swap : (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ℝ × ℝ)))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ℝ × ℝ))) := Measure.measurePreserving_swap
  have ha : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ ℝ × ℝ × (ℝ × ℝ))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure (ℝ × ℝ)))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)))) :=
    measurePreserving_prodAssoc _ _ _
  have hc : MeasurePreserving (Prod.map (id : ℝ → ℝ) (Prod.swap : ℝ × (ℝ × ℝ) → (ℝ × ℝ) × ℝ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))))
      ((volume : Measure ℝ).prod ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ))) :=
    (MeasurePreserving.id _).prod Measure.measurePreserving_swap
  have he := (hc.comp ha).comp hs
  have h1 : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure Space)), Q z := h
  have h2 := (hΦ.comp he.quasiMeasurePreserving).ae h1
  exact Measure.ae_ae_of_ae_prod h2

theorem cylArg_eq (p : ℝ × ℝ) (θ : ℝ) : cylArg (p, θ) = axialRot θ (planePoint p) := by
  ext i
  fin_cases i <;>
    simp [cylArg, planePoint, CellCert.CellAnalysis.cylPoint, axialRot, unitVector] <;> ring

theorem rot_plane_flip (p : ℝ × ℝ) (φ : ℝ) :
    axialRot φ (planePoint (p.1, -p.2)) = flipPoint (axialRot (-φ) (planePoint p)) := by
  ext i
  fin_cases i <;>
    simp [planePoint, CellCert.CellAnalysis.cylPoint, axialRot, flipPoint, unitVector]

theorem rot_neg_flip (φ : ℝ) (w : Space) (a : Fin 3) :
    axialRot (-φ) (flipPoint w) a = frameSign a * axialRot φ w a := by
  fin_cases a <;>
    simp [axialRot, flipPoint, frameSign, unitVector] <;> ring

theorem axialRot_add_period (φ : ℝ) (y : Space) : axialRot (φ + 2 * Real.pi) y = axialRot φ y := by
  simp only [axialRot, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem axialRot_neg_add_period (φ : ℝ) (y : Space) :
    axialRot (-(φ + 2 * Real.pi)) y = axialRot (-φ) y := by
  rw [show -(φ + 2 * Real.pi) = -φ - 2 * Real.pi by ring]
  simp only [axialRot, Real.cos_sub_two_pi, Real.sin_sub_two_pi]

theorem expFactor_flip_neg (ξ : ℤ × ℤ) (τ φ : ℝ) : expFactor (ξ.1, -ξ.2) τ (-φ) = expFactor ξ τ φ := by
  unfold expFactor
  congr 2
  push_cast
  ring

theorem modeVel_flip_of {v : ℝ → Space → Space} (ξ : ℤ × ℤ) (p : ℝ × ℝ)
    (hp : ∀ᵐ q : ℝ × ℝ, v q.1 (flipPoint (axialRot q.2 (planePoint p)))
      = flipPoint (v q.1 (axialRot q.2 (planePoint p)))) (a : Fin 3) :
    modeVel ξ v 0 (planePoint (p.1, -p.2)) a
      = (frameSign a : ℂ) * modeVel (ξ.1, -ξ.2) v 0 (planePoint p) a := by
  have hae : ∀ᵐ τ : ℝ, ∀ᵐ φ : ℝ, v τ (flipPoint (axialRot (-φ) (planePoint p)))
      = flipPoint (v τ (axialRot (-φ) (planePoint p))) := by
    have hmp : MeasurePreserving (Prod.map (id : ℝ → ℝ) (fun φ : ℝ => -φ))
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
      (MeasurePreserving.id _).prod (Measure.measurePreserving_neg _)
    have h1 : ∀ᵐ q ∂((volume : Measure ℝ).prod (volume : Measure ℝ)), v q.1 (flipPoint (axialRot q.2 (planePoint p)))
        = flipPoint (v q.1 (axialRot q.2 (planePoint p))) := hp
    exact Measure.ae_ae_of_ae_prod (hmp.quasiMeasurePreserving.ae h1)
  set g : ℝ → ℝ → ℂ := fun τ φ => expFactor (ξ.1, -ξ.2) τ φ
    * ((axialRot (-φ) (v (0 + τ) (axialRot φ (planePoint p))) a : ℝ) : ℂ) with hg
  have hper : ∀ τ, Function.Periodic (g τ) (2 * Real.pi) := by
    intro τ φ
    simp only [hg, expFactor_add_period, axialRot_add_period, axialRot_neg_add_period]
  have hinner : ∀ τ, ∫ φ in (0 : ℝ)..(2 * Real.pi), g τ (-φ) = ∫ φ in (0 : ℝ)..(2 * Real.pi), g τ φ := by
    intro τ
    rw [intervalIntegral.integral_comp_neg, neg_zero]
    have h := (hper τ).intervalIntegral_add_eq (-(2 * Real.pi)) 0
    rw [neg_add_cancel, zero_add] at h
    exact h
  unfold modeVel modeAverage
  calc (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(((2 * Real.pi * ξ.1 * τ + ξ.2 * φ : ℝ) : ℂ) * Complex.I))
            * ((axialRot (-φ) (v (0 + τ) (axialRot φ (planePoint (p.1, -p.2)))) a : ℝ) : ℂ)
        = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1,
            (frameSign a : ℂ) * ∫ φ in (0 : ℝ)..(2 * Real.pi), g τ (-φ) := by
          congr 1
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards [hae] with τ hτ _
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards [hτ] with φ hφ _
          simp only [hg, expFactor_flip_neg, neg_neg, zero_add]
          rw [rot_plane_flip, hφ, rot_neg_flip]
          unfold expFactor
          push_cast
          ring
      _ = (frameSign a : ℂ) * ((1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1,
            ∫ φ in (0 : ℝ)..(2 * Real.pi), g τ φ) := by
          simp_rw [hinner]
          rw [intervalIntegral.integral_const_mul]
          ring
      _ = _ := by
          rfl


theorem slice_sixth_bound {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6) ≤
        ENNReal.ofReal c ^ 6 * (∫⁻ y, ENNReal.ofReal (matSq (G σ y))) ^ 3 ∧
      ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) < ⊤ := by
  have hFa : AEMeasurable (fun σ => ∫⁻ y, ENNReal.ofReal (matSq (G σ y))) volume :=
    Coercive.Internal.PerturbationFacts.aemeasurable_matNorm hv.measurable_gradient
  have hfin : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) < ⊤ :=
    ae_lt_top' hFa.restrict hv.gradient_finite.ne
  refine ⟨‖(Freq.velocity : Freq.X →L[ℝ] Freq.L6R)‖, norm_nonneg _, ?_⟩
  filter_upwards [ae_restrict_of_ae hv.weak_gradient, ae_restrict_of_ae hv.divergence_free,
    ae_restrict_of_ae hv.sixth_power, hfin] with σ h1 h2 h3 h4
  exact ⟨Coercive.Internal.SmoothApprox.slice_sixth_le h1 h2 h3 h4, h4⟩

theorem orbit_qmp :
    Measure.QuasiMeasurePreserving (fun x : Space × (ℝ × ℝ) => (x.2.1, axialRot x.2.2 x.1))
      ((volume : Measure Space).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)))
      (volume : Measure (ℝ × Space)) := by
  have hRot := Coercive.axialRotationHolds_proof
  have hΨ : Measure.QuasiMeasurePreserving (fun x : (ℝ × Space) × ℝ => (x.1.1, axialRot x.2 x.1.2))
      ((volume : Measure (ℝ × Space)).prod (volume : Measure ℝ)) (volume : Measure (ℝ × Space)) := by
    refine QuasiMeasurePreserving.prod_of_left ?_ (Filter.Eventually.of_forall fun φ => ?_)
    · have hc : Continuous (fun x : (ℝ × Space) × ℝ => (x.1.1, axialRot x.2 x.1.2)) := by
        unfold axialRot
        fun_prop
      exact hc.measurable
    · have h := (Coercive.Internal.ModeRotation.measurePreserving_orbitMap hRot (0, φ)).quasiMeasurePreserving
      have e : Coercive.Internal.ModeRotation.orbitMap (0, φ) = fun x : ℝ × Space => (x.1, axialRot φ x.2) := by
        funext x
        simp [Coercive.Internal.ModeRotation.orbitMap]
      rw [e] at h
      exact h
  have ha : MeasurePreserving (MeasurableEquiv.prodAssoc : (Space × ℝ) × ℝ ≃ᵐ Space × ℝ × ℝ)
      (((volume : Measure Space).prod (volume : Measure ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure Space).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))) :=
    measurePreserving_prodAssoc _ _ _
  have hs : MeasurePreserving (Prod.map (Prod.swap : Space × ℝ → ℝ × Space) (id : ℝ → ℝ))
      (((volume : Measure Space).prod (volume : Measure ℝ)).prod (volume : Measure ℝ))
      (((volume : Measure ℝ).prod (volume : Measure Space)).prod (volume : Measure ℝ)) :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id _)
  have he := hs.comp ha.symm
  exact hΨ.comp he.quasiMeasurePreserving

theorem rot_lintegral_sixth (τ φ : ℝ) (v : ℝ → Space → Space) :
    ∫⁻ y, ‖v τ (axialRot φ y)‖ₑ ^ 6 = ∫⁻ y, ENNReal.ofReal (‖v τ y‖ ^ 6) := by
  obtain ⟨R, hR⟩ := Coercive.axialRotationHolds_proof.1 φ
  have hf : (fun y => axialRot φ y) = ⇑R := funext fun y => (hR y).symm
  have hmp : MeasurePreserving (fun y => axialRot φ y) volume volume := by
    rw [hf]
    exact R.measurePreserving
  have hemb : MeasurableEmbedding (fun y => axialRot φ y) := by
    rw [hf]
    exact R.toHomeomorph.measurableEmbedding
  refine (hmp.lintegral_comp_emb hemb (fun x => ‖v τ x‖ₑ ^ 6)).trans (lintegral_congr fun y => ?_)
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem modeVel_enorm_le (ξ : ℤ × ℤ) (v : ℝ → Space → Space) (y : Space) (a : Fin 3) :
    ‖modeVel ξ v 0 y a‖ₑ ≤ ∫⁻ τ in Set.Ioc (0 : ℝ) 1, ∫⁻ φ in Set.Ioc (0 : ℝ) (2 * Real.pi),
      ‖v τ (axialRot φ y)‖ₑ := by
  have hc : ‖(1 / (2 * Real.pi) : ℂ)‖ₑ ≤ 1 := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [ENNReal.ofReal_le_one, div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  unfold modeVel modeAverage
  rw [enorm_mul]
  refine (mul_le_of_le_one_left zero_le hc).trans ?_
  rw [intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun τ => ?_)
  rw [intervalIntegral.integral_of_le (by positivity)]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun φ => ?_)
  rw [enorm_mul]
  have h1 : ‖Complex.exp (-(((2 * Real.pi * ξ.1 * τ + ξ.2 * φ : ℝ) : ℂ) * Complex.I))‖ₑ = 1 := by
    rw [← ofReal_norm, Complex.norm_exp, ENNReal.ofReal_eq_one]
    simp
  rw [h1, one_mul]
  beta_reduce
  rw [zero_add, ← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (PiLp.norm_apply_le _ a).trans (le_of_eq ?_)
  exact Coercive.Internal.ModeRotation.norm_axialRot Coercive.axialRotationHolds_proof _ _

theorem velocity_sixth_square {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, (∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6)) ^ (1 / 3 : ℝ) < ⊤ := by
  obtain ⟨c, -, hb⟩ := slice_sixth_bound hv
  have hle : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      (∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6)) ^ (1 / 3 : ℝ) ≤
        ENNReal.ofReal c ^ 2 * ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) := by
    filter_upwards [hb] with σ h
    refine (ENNReal.rpow_le_rpow h.1 (by norm_num)).trans (le_of_eq ?_)
    have e1 : (ENNReal.ofReal c ^ 6) ^ (1 / 3 : ℝ) = ENNReal.ofReal c ^ 2 := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast]
      norm_num
    have e2 : ((∫⁻ y, ENNReal.ofReal (matSq (G σ y))) ^ 3) ^ (1 / 3 : ℝ) =
        ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e1, e2]
  refine lt_of_le_of_lt (lintegral_mono_ae hle) ?_
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hv.gradient_finite

theorem mode_sixth_finite {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (ξ : ℤ × ℤ) :
    ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ξ v 0 y) ^ 3) < ⊤ := by
  obtain ⟨c, hc, hb⟩ := slice_sixth_bound hv
  set F : ℝ → ℝ≥0∞ := fun s => ∫⁻ y, ENNReal.ofReal (matSq (G s y)) with hFdef
  have hFa : AEMeasurable F volume := Coercive.Internal.PerturbationFacts.aemeasurable_matNorm hv.measurable_gradient
  set Fm : ℝ → ℝ≥0∞ := hFa.mk F with hFmdef
  have hFmm : Measurable Fm := hFa.measurable_mk
  have hFe : F =ᵐ[volume] Fm := hFa.ae_eq_mk
  set W : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (1 + c * (1 + (Fm s).toReal)) with hWdef
  have hWm : Measurable W :=
    (measurable_const.add (measurable_const.mul (measurable_const.add hFmm.ennreal_toReal))).ennreal_ofReal
  have hW0 : ∀ s, W s ≠ 0 := fun s => (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hWt : ∀ s, W s ≠ ⊤ := fun s => ENNReal.ofReal_ne_top
  set μ1 : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ1
  set μ2 : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)) with hμ2
  have hSW : ∀ᵐ s ∂μ1, ∫⁻ y, ENNReal.ofReal (‖v s y‖ ^ 6) ≤ W s ^ 6 := by
    have hb' := ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self hb
    filter_upwards [hb', ae_restrict_of_ae hFe] with s h h5
    refine h.1.trans ?_
    obtain ⟨f, hf0, hfF⟩ : ∃ f : ℝ, 0 ≤ f ∧ F s = ENNReal.ofReal f :=
      ⟨(F s).toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal h.2.ne).symm⟩
    have hW : W s = ENNReal.ofReal (1 + c * (1 + f)) := by
      show ENNReal.ofReal (1 + c * (1 + (Fm s).toReal)) = _
      rw [← h5, hfF, ENNReal.toReal_ofReal hf0]
    have hF' : ∫⁻ y, ENNReal.ofReal (matSq (G s y)) = ENNReal.ofReal f := hfF
    rw [hW, hF', ← ENNReal.ofReal_pow hc, ← ENNReal.ofReal_pow hf0, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h6 : f ^ 3 ≤ (1 + f) ^ 6 := by
      calc f ^ 3 ≤ ((1 + f) ^ 2) ^ 3 := pow_le_pow_left₀ hf0 (by nlinarith) 3
        _ = (1 + f) ^ 6 := by ring
    calc c ^ 6 * f ^ 3 ≤ c ^ 6 * (1 + f) ^ 6 := by gcongr
      _ = (c * (1 + f)) ^ 6 := by ring
      _ ≤ (1 + c * (1 + f)) ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
  have hFint : ∫⁻ s, Fm s ∂μ1 < ⊤ := by
    rw [← lintegral_congr_ae (ae_restrict_of_ae hFe)]
    exact lt_of_le_of_lt (lintegral_mono_set Set.Ioc_subset_Icc_self) hv.gradient_finite
  have hWint : ∫⁻ s, W s ∂μ1 < ⊤ := by
    have hle : ∀ s, W s ≤ ENNReal.ofReal (1 + c) + ENNReal.ofReal c * Fm s := by
      intro s
      calc W s = ENNReal.ofReal ((1 + c) + c * (Fm s).toReal) := by
            show ENNReal.ofReal (1 + c * (1 + (Fm s).toReal)) = _
            congr 1
            ring
        _ ≤ ENNReal.ofReal (1 + c) + ENNReal.ofReal (c * (Fm s).toReal) := ENNReal.ofReal_add_le
        _ ≤ ENNReal.ofReal (1 + c) + ENNReal.ofReal c * Fm s := by
            rw [ENNReal.ofReal_mul hc]
            gcongr
            exact ENNReal.ofReal_toReal_le
    refine lt_of_le_of_lt (lintegral_mono hle) ?_
    rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul _ hFmm]
    refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFint⟩
    rw [hμ1, Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  set β : Measure (ℝ × ℝ) := μ1.prod μ2 with hβ
  have hac : (volume : Measure Space).prod β ≪
      (volume : Measure Space).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    Measure.AbsolutelyContinuous.rfl.prod
      ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self))
  have hq : Measure.QuasiMeasurePreserving (fun x : Space × (ℝ × ℝ) => (x.2.1, axialRot x.2.2 x.1))
      ((volume : Measure Space).prod β) volume := orbit_qmp.mono_left hac
  have hV : AEStronglyMeasurable (fun x : Space × (ℝ × ℝ) => v x.2.1 (axialRot x.2.2 x.1))
      ((volume : Measure Space).prod β) :=
    hv.measurable_velocity.comp_quasiMeasurePreserving hq
  have hI : ∀ᵐ y : Space, ∀ a, ‖modeVel ξ v 0 y a‖ₑ ≤ ∫⁻ q, ‖v q.1 (axialRot q.2 y)‖ₑ ∂β := by
    filter_upwards [hV.prodMk_left] with y hy a
    refine (modeVel_enorm_le ξ v y a).trans (le_of_eq ?_)
    exact (lintegral_prod _ hy.enorm).symm
  have hpt : ∀ᵐ y : Space, ENNReal.ofReal (cnormSq (modeVel ξ v 0 y) ^ 3) ≤
      27 * (∫⁻ q, ‖v q.1 (axialRot q.2 y)‖ₑ ∂β) ^ 6 := by
    filter_upwards [hI] with y hy
    set I := ∫⁻ q, ‖v q.1 (axialRot q.2 y)‖ₑ ∂β
    have hs : ENNReal.ofReal (cnormSq (modeVel ξ v 0 y)) ≤ 3 * I ^ 2 := by
      unfold cnormSq
      rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => by positivity)]
      calc ∑ a : Fin 3, ENNReal.ofReal (‖modeVel ξ v 0 y a‖ ^ 2) ≤ ∑ _a : Fin 3, I ^ 2 := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
            exact pow_le_pow_left₀ zero_le (hy a) 2
        _ = 3 * I ^ 2 := by simp
    have hn : 0 ≤ cnormSq (modeVel ξ v 0 y) := by
      unfold cnormSq
      positivity
    calc ENNReal.ofReal (cnormSq (modeVel ξ v 0 y) ^ 3) = ENNReal.ofReal (cnormSq (modeVel ξ v 0 y)) ^ 3 :=
          ENNReal.ofReal_pow hn 3
      _ ≤ (3 * I ^ 2) ^ 3 := pow_le_pow_left₀ zero_le hs 3
      _ = 27 * I ^ 6 := by ring
  have hWfst : AEMeasurable (fun q : ℝ × ℝ => W q.1) β := (hWm.comp measurable_fst).aemeasurable
  have hH : ∀ᵐ y : Space, (∫⁻ q, ‖v q.1 (axialRot q.2 y)‖ₑ ∂β) ^ 6 ≤
      (∫⁻ q, W q.1 ∂β) ^ 5 * ∫⁻ q, (W q.1)⁻¹ ^ 5 * ‖v q.1 (axialRot q.2 y)‖ₑ ^ 6 ∂β := by
    filter_upwards [hV.prodMk_left] with y hy
    have h := Coercive.Internal.SmoothApprox.lintegral_mul_sixth_le (μ := β) (A := fun _ => 1)
      (B := fun q => ‖v q.1 (axialRot q.2 y)‖ₑ) (W := fun q => W q.1) aemeasurable_const hy.enorm hWfst
      (fun q => hW0 q.1) (fun q => hWt q.1)
    simpa only [one_mul] using h
  have hJ : AEMeasurable (Function.uncurry fun (y : Space) (q : ℝ × ℝ) =>
      (W q.1)⁻¹ ^ 5 * ‖v q.1 (axialRot q.2 y)‖ₑ ^ 6) ((volume : Measure Space).prod β) :=
    ((hWm.comp (measurable_fst.comp measurable_snd)).inv.pow_const 5).aemeasurable.mul (hV.enorm.pow_const 6)
  have hswap : ∫⁻ y, ∫⁻ q, (W q.1)⁻¹ ^ 5 * ‖v q.1 (axialRot q.2 y)‖ₑ ^ 6 ∂β =
      ∫⁻ q, (∫⁻ y, (W q.1)⁻¹ ^ 5 * ‖v q.1 (axialRot q.2 y)‖ₑ ^ 6) ∂β :=
    lintegral_lintegral_swap hJ
  have hinner : ∀ q : ℝ × ℝ, ∫⁻ y, (W q.1)⁻¹ ^ 5 * ‖v q.1 (axialRot q.2 y)‖ₑ ^ 6 =
      (W q.1)⁻¹ ^ 5 * ∫⁻ y, ENNReal.ofReal (‖v q.1 y‖ ^ 6) := by
    intro q
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (hW0 q.1))),
      rot_lintegral_sixth]
  have hfin : ∀ᵐ q ∂β, (W q.1)⁻¹ ^ 5 * ∫⁻ y, ENNReal.ofReal (‖v q.1 y‖ ^ 6) ≤ W q.1 := by
    have h := (Measure.quasiMeasurePreserving_fst (μ := μ1) (ν := μ2)).ae hSW
    filter_upwards [h] with q hq
    calc (W q.1)⁻¹ ^ 5 * ∫⁻ y, ENNReal.ofReal (‖v q.1 y‖ ^ 6) ≤ (W q.1)⁻¹ ^ 5 * W q.1 ^ 6 := by
          gcongr
      _ = W q.1 := by
          rw [show W q.1 ^ 6 = W q.1 ^ 5 * W q.1 by ring, ← mul_assoc, ← mul_pow,
            ENNReal.inv_mul_cancel (hW0 q.1) (hWt q.1), one_pow, one_mul]
  have hWβ : ∫⁻ q, W q.1 ∂β < ⊤ := by
    rw [lintegral_prod _ hWfst]
    simp only [lintegral_const]
    rw [lintegral_mul_const _ hWm]
    refine ENNReal.mul_lt_top hWint ?_
    rw [hμ2, Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  calc ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ξ v 0 y) ^ 3)
      ≤ ∫⁻ y, 27 * ((∫⁻ q, W q.1 ∂β) ^ 5 *
          ∫⁻ q, (W q.1)⁻¹ ^ 5 * ‖v q.1 (axialRot q.2 y)‖ₑ ^ 6 ∂β) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpt, hH] with y h1 h2
        exact h1.trans (mul_le_mul_of_nonneg_left h2 zero_le)
    _ = 27 * ((∫⁻ q, W q.1 ∂β) ^ 5 *
          ∫⁻ q, (W q.1)⁻¹ ^ 5 * (∫⁻ y, ENNReal.ofReal (‖v q.1 y‖ ^ 6)) ∂β) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (ENNReal.pow_ne_top hWβ.ne),
          hswap]
        simp_rw [hinner]
    _ ≤ 27 * ((∫⁻ q, W q.1 ∂β) ^ 5 * ∫⁻ q, W q.1 ∂β) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (lintegral_mono_ae hfin) zero_le) zero_le
    _ < ⊤ := ENNReal.mul_lt_top (by simp) (ENNReal.mul_lt_top (ENNReal.pow_lt_top hWβ) hWβ)

end Internal.FlipDecay

open Internal.FlipDecay in
theorem labelFlipEvenHolds : LabelFlipEvenHolds := by
  intro Γ P v G H g hv _ hflip mm ι
  obtain ⟨γ, hγ, hγ1, hγ2⟩ := hflip
  have hinv : ∀ᵐ z : ℝ × Space, v z.1 (flipPoint z.2) = flipPoint (v z.1 z.2) := by
    filter_upwards [hv.invariant γ hγ] with z hz
    rw [hγ2, add_zero, hγ1, hγ1] at hz
    exact hz
  have horb := ae_orbit_of_ae hinv
  refine ae_restrict_of_ae ?_
  filter_upwards [horb] with p hp
  have hp' : ∀ᵐ q : ℝ × ℝ, v q.1 (flipPoint (axialRot q.2 (planePoint p)))
      = flipPoint (v q.1 (axialRot q.2 (planePoint p))) := by
    filter_upwards [hp] with q hq
    rw [← cylArg_eq]
    exact hq
  funext a
  unfold labelVel
  rw [modeVel_flip_of _ p hp' a]
  congr 2
  simp [labelHarmonic, labelFlip, labelTime, labelAzimuth]
  ring


def VelocitySixthSquareIntegral : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g →
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, (∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6)) ^ (1 / 3 : ℝ) < ⊤

def ModeVelSixthFinite : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g → ∀ ξ : ℤ × ℤ,
    ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ξ v 0 y) ^ 3) < ⊤

theorem velocitySixthSquareIntegral : VelocitySixthSquareIntegral :=
  fun _ _ _ _ _ _ hv => Internal.FlipDecay.velocity_sixth_square hv

theorem modeVelSixthFinite : ModeVelSixthFinite :=
  fun _ _ _ _ _ _ hv ξ => Internal.FlipDecay.mode_sixth_finite hv ξ

end TailBand

end CertCell

end Breakdown
