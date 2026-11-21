import Breakdown.CertCell.BridgeStatements
import Breakdown.CertCell.TailFlipDecay

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.ScalarFlip

open CellCert.CellAnalysis.LowEntry.Internal (cylArg)
open Coercive.Internal.ModeRotation (expFactor expFactor_add_period)
open TailBand.Internal.FlipDecay (ae_orbit_of_ae cylArg_eq rot_plane_flip axialRot_add_period
  expFactor_flip_neg)

theorem planeScalar_neg_height {q : ℝ → Space → ℝ} (ξ : ℤ × ℤ) (p : ℝ × ℝ)
    (hp : ∀ᵐ w : ℝ × ℝ, q w.1 (flipPoint (axialRot w.2 (planePoint p))) = q w.1 (axialRot w.2 (planePoint p))) :
    planeScalar ξ q p.1 (-p.2) = planeScalar (flipLabel ξ) q p.1 p.2 := by
  have hae : ∀ᵐ τ : ℝ, ∀ᵐ φ : ℝ, q τ (flipPoint (axialRot (-φ) (planePoint p)))
      = q τ (axialRot (-φ) (planePoint p)) := by
    have hmp : MeasurePreserving (Prod.map (id : ℝ → ℝ) (fun φ : ℝ => -φ))
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
      (MeasurePreserving.id _).prod (Measure.measurePreserving_neg _)
    have h1 : ∀ᵐ w ∂((volume : Measure ℝ).prod (volume : Measure ℝ)),
        q w.1 (flipPoint (axialRot w.2 (planePoint p))) = q w.1 (axialRot w.2 (planePoint p)) := hp
    exact Measure.ae_ae_of_ae_prod (hmp.quasiMeasurePreserving.ae h1)
  set g : ℝ → ℝ → ℂ := fun τ φ => expFactor (ξ.1, -ξ.2) τ φ * ((q τ (axialRot φ (planePoint p)) : ℝ) : ℂ)
    with hg
  have hper : ∀ τ, Function.Periodic (g τ) (2 * Real.pi) := by
    intro τ φ
    simp only [hg, expFactor_add_period, axialRot_add_period]
  have hinner : ∀ τ, ∫ φ in (0 : ℝ)..(2 * Real.pi), g τ (-φ) = ∫ φ in (0 : ℝ)..(2 * Real.pi), g τ φ := by
    intro τ
    rw [intervalIntegral.integral_comp_neg, neg_zero]
    have h := (hper τ).intervalIntegral_add_eq (-(2 * Real.pi)) 0
    rw [neg_add_cancel, zero_add] at h
    exact h
  unfold planeScalar modeAverage
  calc (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(((2 * Real.pi * ξ.1 * τ + ξ.2 * φ : ℝ) : ℂ) * Complex.I))
            * ((q τ (axialRot φ (planePoint (p.1, -p.2))) : ℝ) : ℂ)
        = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), g τ (-φ) := by
          congr 1
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards [hae] with τ hτ _
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards [hτ] with φ hφ _
          simp only [hg, expFactor_flip_neg]
          rw [rot_plane_flip, hφ]
          rfl
      _ = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), g τ φ := by
          simp_rw [hinner]
      _ = _ := rfl

theorem ae_planeScalar_flip {q : ℝ → Space → ℝ}
    (hflip : ∀ᵐ z : ℝ × Space, q z.1 (flipPoint z.2) = q z.1 z.2) (ξ : ℤ × ℤ) :
    ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ᵐ z : ℝ,
      planeScalar (flipLabel ξ) q r z = planeScalar ξ q r (-z) := by
  have h := ae_orbit_of_ae hflip
  have h2 : ∀ᵐ p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)),
      planeScalar ξ q p.1 (-p.2) = planeScalar (flipLabel ξ) q p.1 p.2 := by
    rw [← Measure.volume_eq_prod]
    filter_upwards [h] with p hp
    refine planeScalar_neg_height ξ p ?_
    filter_upwards [hp] with w hw
    simpa only [cylArg_eq] using hw
  refine ae_restrict_of_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod h2] with r hr
  filter_upwards [hr] with z hz
  exact hz.symm

theorem setIntegral_symm_neg {a : ℝ} (F : ℝ → ℂ) :
    ∫ x in Set.Ioo (-a) a, F (-x) = ∫ x in Set.Ioo (-a) a, F x := by
  have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioo (-a) a = Set.Ioo (-a) a := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding F (Set.Ioo (-a) a)
  rw [hpre] at h
  exact h

theorem integrableOn_symm_neg {a : ℝ} {F : ℝ → ℂ} (hF : IntegrableOn F (Set.Ioo (-a) a)) :
    IntegrableOn (fun x => F (-x)) (Set.Ioo (-a) a) := by
  have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioo (-a) a = Set.Ioo (-a) a := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding (f := F) (s := Set.Ioo (-a) a)).2 hF
  rw [hpre] at h
  exact h

theorem weakDeriv_reflect {f fz f' fz' : ℝ → ℂ} {a : ℝ} (hf : ∀ᵐ z : ℝ, f' z = f (-z))
    (h1 : HasWeakDerivOn f fz (-a) a) (h2 : HasWeakDerivOn f' fz' (-a) a) :
    ∀ᵐ z : ℝ, z ∈ Set.Ioo (-a) a → fz' z = -fz (-z) := by
  have key : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo (-a) a →
      ∫ x in Set.Ioo (-a) a, fz (-x) * ((ψ x : ℝ) : ℂ) = -∫ x in Set.Ioo (-a) a, fz' x * ((ψ x : ℝ) : ℂ) := by
    intro ψ hψ hc hs
    set χ : ℝ → ℝ := fun x => ψ (-x) with hχdef
    have hχ : ContDiff ℝ ∞ χ := hψ.comp contDiff_neg
    have hχc : HasCompactSupport χ := hc.comp_homeomorph (Homeomorph.neg ℝ)
    have hχs : tsupport χ ⊆ Set.Ioo (-a) a := by
      have e : tsupport χ = (Homeomorph.neg ℝ) ⁻¹' tsupport ψ := tsupport_comp_eq_preimage ψ (Homeomorph.neg ℝ)
      rw [e]
      intro x hx
      have hm := hs hx
      change -a < -x ∧ -x < a at hm
      constructor <;> linarith [hm.1, hm.2]
    have hderiv : ∀ x, deriv χ x = -deriv ψ (-x) := fun x => deriv_comp_neg ψ x
    have e1 := h1.2.2 χ hχ hχc hχs
    have e2 := h2.2.2 ψ hψ hc hs
    have r1 := setIntegral_symm_neg (a := a) (fun y => fz y * ((χ y : ℝ) : ℂ))
    simp only [hχdef, neg_neg] at r1
    have r2 := setIntegral_symm_neg (a := a) (fun y => f (-y) * ((deriv ψ y : ℝ) : ℂ))
    simp only [neg_neg] at r2
    calc ∫ x in Set.Ioo (-a) a, fz (-x) * ((ψ x : ℝ) : ℂ)
          = ∫ x in Set.Ioo (-a) a, fz x * ((χ x : ℝ) : ℂ) := r1
      _ = -∫ x in Set.Ioo (-a) a, f x * ((deriv χ x : ℝ) : ℂ) := by rw [e1, neg_neg]
      _ = ∫ x in Set.Ioo (-a) a, f x * ((deriv ψ (-x) : ℝ) : ℂ) := by
          simp only [hderiv, Complex.ofReal_neg, mul_neg, integral_neg, neg_neg]
      _ = ∫ x in Set.Ioo (-a) a, f (-x) * ((deriv ψ x : ℝ) : ℂ) := r2
      _ = ∫ x in Set.Ioo (-a) a, f' x * ((deriv ψ x : ℝ) : ℂ) := by
          refine setIntegral_congr_ae measurableSet_Ioo ?_
          filter_upwards [hf] with x hx _
          rw [hx]
      _ = -∫ x in Set.Ioo (-a) a, fz' x * ((ψ x : ℝ) : ℂ) := e2
  have hint : IntegrableOn (fun x => fz' x + fz (-x)) (Set.Ioo (-a) a) :=
    h2.2.1.add (integrableOn_symm_neg h1.2.1)
  have hz := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (f := fun x => fz' x + fz (-x)) hint.locallyIntegrableOn (by
      intro ψ hψ hc hs
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioo (-a) a) (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), zero_smul])]
      obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hψ.continuous
      have hb : ∀ᵐ x ∂(volume.restrict (Set.Ioo (-a) a)), ‖((ψ x : ℝ) : ℂ)‖ ≤ C :=
        Filter.Eventually.of_forall fun x => by rw [Complex.norm_real]; exact hC x
      have hm : AEStronglyMeasurable (fun x => ((ψ x : ℝ) : ℂ)) (volume.restrict (Set.Ioo (-a) a)) :=
        (Complex.continuous_ofReal.comp hψ.continuous).aestronglyMeasurable
      have i1 : IntegrableOn (fun x => ((ψ x : ℝ) : ℂ) * fz' x) (Set.Ioo (-a) a) :=
        Integrable.bdd_mul h2.2.1 hm hb
      have i2 : IntegrableOn (fun x => ((ψ x : ℝ) : ℂ) * fz (-x)) (Set.Ioo (-a) a) :=
        Integrable.bdd_mul (integrableOn_symm_neg h1.2.1) hm hb
      simp only [Complex.real_smul, mul_add]
      rw [integral_add i1 i2]
      have k := key ψ hψ hc hs
      simp only [mul_comm (fz (-_)), mul_comm (fz' _)] at k
      rw [k, add_neg_cancel])
  filter_upwards [hz] with z hz hmem
  exact eq_neg_of_add_eq_zero_left (hz hmem)

end Internal.ScalarFlip

open Internal.ScalarFlip in
theorem scalarPlaneFlip (hF : TraceFlipHolds) (hM : TraceMatchHolds) (hD : ScalarHeightDerivHolds) :
    ScalarPlaneFlipHolds := by
  intro q dq hq hdq hpq hpdq hgrad hfin hflip ξ
  have hD1 := hD q dq hq hdq hpq hpdq hgrad hfin hflip ξ
  have hD2 := hD q dq hq hdq hpq hpdq hgrad hfin hflip (flipLabel ξ)
  have hS := ae_planeScalar_flip hflip ξ
  filter_upwards [hD1, hD2, hS] with r hr1 hr2 hrs h hh
  have h2h : 0 < 2 * h := by positivity
  have w1 := hr1 (2 * h) h2h
  have w2 := hr2 (2 * h) h2h
  have hz := weakDeriv_reflect hrs w1 w2
  have step : upperTrace (planeScalar (flipLabel ξ) q r) (planeScalarHeight (flipLabel ξ) dq r) h
      = upperTrace (fun z => 1 * planeScalar ξ q r (-z)) (fun z => -(1 * planeScalarHeight ξ dq r (-z))) h := by
    unfold upperTrace
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hrs, hz] with z e1 e2 hzI
    have hmem : z ∈ Set.Ioo (-(2 * h)) (2 * h) := by
      rw [Set.uIoc_of_le hh.le] at hzI
      exact ⟨by linarith [hzI.1], by linarith [hzI.2]⟩
    rw [e1, e2 hmem, one_mul, one_mul]
  rw [step, hF (planeScalar ξ q r) (planeScalarHeight ξ dq r) h 1, one_mul]
  exact (hM _ _ h hh w1).symm

end Bridge

end CertCell

end Breakdown
