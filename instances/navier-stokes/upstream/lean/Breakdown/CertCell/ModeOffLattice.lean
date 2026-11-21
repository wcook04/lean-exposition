import Breakdown.CertCell.BridgeStatements
import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoerciveModeDerivative
import Breakdown.Cert.CoerciveGain
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoercivePerturbationFactsProof

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.OffLattice

open Coercive Coercive.ModeDerivative.Internal

private theorem rot_coeffs_zero (α : ℝ) (m : Fin 3 → ℂ)
    (h : ∀ i : Fin 3, ∑ j : Fin 3, ((axialRot α (unitVector j) i : ℝ) : ℂ) * m j = 0) : m = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [Fin.sum_univ_three, axialRot, unitVector] at h0 h1 h2
  simp at h0 h1 h2
  have hc : Complex.cos (α : ℂ) ^ 2 + Complex.sin (α : ℂ) ^ 2 = 1 := Complex.cos_sq_add_sin_sq _
  funext i
  fin_cases i
  · show m 0 = 0
    linear_combination Complex.cos (α : ℂ) * h0 + Complex.sin (α : ℂ) * h1 - m 0 * hc
  · show m 1 = 0
    linear_combination -Complex.sin (α : ℂ) * h0 + Complex.cos (α : ℂ) * h1 - m 1 * hc
  · show m 2 = 0
    exact h2

private theorem weak_zero {f : Space → Space} {F : Space → (Space →L[ℝ] Space)} (h : IsWeakGradient f F)
    (hf : ∀ᵐ y, f y = 0) : ∀ᵐ y, F y = 0 := by
  have hcol : ∀ j : Fin 3, ∀ᵐ y, F y (unitVector j) = 0 := by
    intro j
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (Coercive.GainInternal.li_apply h.2.1 j) fun φ hφ hφc => ?_
    rw [h.2.2 φ ⟨hφ, hφc⟩ j, neg_eq_zero]
    rw [integral_congr_ae (g := fun _ => (0 : Space))]
    · simp
    · filter_upwards [hf] with y hy
      rw [hy, smul_zero]
  filter_upwards [ae_all_iff.2 hcol] with y hy
  exact clm_ext_unitVector fun j => by rw [hy j, zero_apply]

private theorem grad_zero_of {g : Fin 3 × Fin 3 → ℂ} (hr : reMat g = 0) (hi : imMat g = 0) : g = 0 := by
  funext ij
  have a := Coercive.GainInternal.reMat_apply g ij.1 ij.2
  have b := Coercive.GainInternal.imMat_apply g ij.1 ij.2
  rw [hr] at a
  rw [hi] at b
  simp only [zero_apply, PiLp.zero_apply] at a b
  exact Complex.ext a.symm b.symm

private theorem reVec_zero : reVec (0 : Fin 3 → ℂ) = 0 := by
  simp [reVec]

private theorem imVec_zero : imVec (0 : Fin 3 → ℂ) = 0 := by
  simp [imVec]

private theorem rot_comm (hRot : Coercive.AxialRotationHolds) (a b : ℝ) (y : Space) :
    axialRot a (axialRot b y) = axialRot b (axialRot a y) := by
  rw [← hRot.2.1, ← hRot.2.1, add_comm]

private theorem orbit_integrableOn {v : ℝ → Space → Space} {z : ℝ × Space}
    (hz : Integrable (fun p : ℝ × ℝ => v (z.1 + p.1) (axialRot p.2 z.2)) angleMeasure) :
    IntegrableOn (fun p : ℝ × ℝ => v (z.1 + p.1) (axialRot p.2 z.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  have e : angleMeasure = (volume : Measure (ℝ × ℝ)).restrict
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod_restrict _ _
  have h2 : IntegrableOn (fun p : ℝ × ℝ => v (z.1 + p.1) (axialRot p.2 z.2))
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
    rw [IntegrableOn, ← e]
    exact hz
  refine h2.congr_set_ae ?_
  rw [Measure.volume_eq_prod]
  exact Measure.set_prod_ae_eq Ioc_ae_eq_Icc.symm Ioc_ae_eq_Icc.symm

private theorem shifted_mode (hRot : Coercive.AxialRotationHolds) {v : ℝ → Space → Space} (ξ : ℤ × ℤ)
    (α s : ℝ) {z : ℝ × Space}
    (hz : Integrable (fun p : ℝ × ℝ => v (z.1 + p.1) (axialRot p.2 z.2)) angleMeasure)
    (ht : ∀ᵐ p ∂angleMeasure,
      v (z.1 + p.1 + s) (axialRot α (axialRot p.2 z.2)) = axialRot α (v (z.1 + p.1) (axialRot p.2 z.2)))
    (i : Fin 3) :
    modeVel ξ v (z.1 + s) (axialRot α z.2) i =
      ∑ j : Fin 3, ((axialRot α (unitVector j) i : ℝ) : ℂ) * modeVel ξ v z.1 z.2 j := by
  set E := Coercive.Internal.ModeRotation.expFactor ξ
  set a : Fin 3 → ℝ → ℝ → ℝ := fun j τ φ => axialRot (-φ) (v (z.1 + τ) (axialRot φ z.2)) j
  set r : Fin 3 → ℝ := fun j => axialRot α (unitVector j) i
  have hint : ∀ j, Integrable (fun p : ℝ × ℝ => E p.1 p.2 * ((a j p.1 p.2 : ℝ) : ℂ)) angleMeasure := by
    intro j
    have ha := Coercive.Internal.ModeRotation.integrable_velComponent hRot hz j
    refine ha.norm.mono' ((Coercive.Internal.ModeRotation.continuous_expFactor ξ).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable ha.1)) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    simp only [E, norm_mul, Coercive.Internal.ModeRotation.norm_expFactor, one_mul, Complex.norm_real]
    exact le_rfl
  have hsum : Integrable (fun p : ℝ × ℝ => E p.1 p.2 * ((∑ j, r j * a j p.1 p.2 : ℝ) : ℂ))
      angleMeasure := by
    have hf : (fun p : ℝ × ℝ => E p.1 p.2 * ((∑ j, r j * a j p.1 p.2 : ℝ) : ℂ)) =
        fun p => ∑ j, (r j : ℂ) * (E p.1 p.2 * ((a j p.1 p.2 : ℝ) : ℂ)) := by
      funext p
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hf]
    exact integrable_finsetSum _ fun j _ => (hint j).const_mul _
  have hae : (fun p : ℝ × ℝ => E p.1 p.2 *
        ((axialRot (-p.2) (v (z.1 + s + p.1) (axialRot p.2 (axialRot α z.2))) i : ℝ) : ℂ)) =ᵐ[angleMeasure]
      fun p => E p.1 p.2 * ((∑ j, r j * a j p.1 p.2 : ℝ) : ℂ) := by
    filter_upwards [ht] with p hp
    congr 2
    rw [show z.1 + s + p.1 = z.1 + p.1 + s by ring, rot_comm hRot p.2 α, hp, rot_comm hRot (-p.2) α]
    exact Coercive.Internal.ModeRotation.axialRot_apply α _ i
  have hF1 : Integrable (fun p : ℝ × ℝ => E p.1 p.2 *
      ((axialRot (-p.2) (v (z.1 + s + p.1) (axialRot p.2 (axialRot α z.2))) i : ℝ) : ℂ)) angleMeasure :=
    hsum.congr hae.symm
  have hL := iterated_intervalIntegral_eq (F := fun τ φ => E τ φ *
      ((axialRot (-φ) (v (z.1 + s + τ) (axialRot φ (axialRot α z.2))) i : ℝ) : ℂ)) hF1
  have hR := iterated_intervalIntegral_eq (F := fun τ φ => E τ φ * ((∑ j, r j * a j τ φ : ℝ) : ℂ)) hsum
  have hS := Coercive.Internal.ModeRotation.modeAverage_sum ξ r a
    (fun j => Coercive.Internal.ModeRotation.integrable_velComponent hRot hz j)
  calc modeVel ξ v (z.1 + s) (axialRot α z.2) i
      = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          E τ φ * ((axialRot (-φ) (v (z.1 + s + τ) (axialRot φ (axialRot α z.2))) i : ℝ) : ℂ) := rfl
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          E τ φ * ((∑ j, r j * a j τ φ : ℝ) : ℂ) := by
        rw [hL, hR, integral_congr_ae hae]
    _ = (1 / (2 * Real.pi) : ℂ) * ∑ j, (r j : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          E τ φ * ((a j τ φ : ℝ) : ℂ) := by
        rw [hS]
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        show _ = (r j : ℂ) * ((1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          E τ φ * ((a j τ φ : ℝ) : ℂ))
        ring

private theorem velocity_zero (hS : ModeShiftRotateHolds) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (α s : ℝ)
    (hinv : ∀ᵐ z : ℝ × Space, v (z.1 + s) (axialRot α z.2) = axialRot α (v z.1 z.2)) (ξ : ℤ × ℤ)
    (hξ : Complex.exp (((ξ.2 * α + 2 * Real.pi * ξ.1 * s : ℝ) : ℂ) * Complex.I) ≠ 1) :
    ∀ᵐ z : ℝ × Space, modeVel ξ v z.1 z.2 = 0 := by
  have hRot := Coercive.axialRotationHolds_proof
  obtain ⟨hvl, -, -⟩ := Coercive.perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv
  have hI := ae_integrable_shiftRot hRot hv.measurable_velocity hvl
  have hT : ∀ᵐ z : ℝ × Space, ∀ᵐ p ∂angleMeasure,
      v (z.1 + p.1 + s) (axialRot α (axialRot p.2 z.2)) = axialRot α (v (z.1 + p.1) (axialRot p.2 z.2)) :=
    Measure.ae_ae_of_ae_prod ((quasiMeasurePreserving_shiftRot hRot).ae hinv)
  filter_upwards [hI, hT] with z hz ht
  have e1 := hS v hv.periodic_velocity ξ z.1 s α z.2 (orbit_integrableOn hz)
  have hph : (2 * Real.pi * ξ.1 * s + ξ.2 * α : ℝ) = ξ.2 * α + 2 * Real.pi * ξ.1 * s := by ring
  rw [hph] at e1
  refine rot_coeffs_zero α _ fun i => ?_
  have e2 := congrFun e1 i
  rw [shifted_mode hRot ξ α s hz ht i] at e2
  have e3 : (Complex.exp (((ξ.2 * α + 2 * Real.pi * ξ.1 * s : ℝ) : ℂ) * Complex.I) - 1) *
      ∑ j : Fin 3, ((axialRot α (unitVector j) i : ℝ) : ℂ) * modeVel ξ v z.1 z.2 j = 0 := by
    linear_combination -e2
  rcases mul_eq_zero.1 e3 with h | h
  · exact absurd (sub_eq_zero.1 h) hξ
  · exact h

end Internal.OffLattice

open Internal.OffLattice Coercive.ModeDerivative.Internal in
theorem modeOffLattice (hS : ModeShiftRotateHolds) (_hT : ModeShiftRotateTensorHolds) :
    ModeOffLatticeHolds := by
  intro Γ P v G H g hv α s hinv ξ hξ
  have hRot := Coercive.axialRotationHolds_proof
  obtain ⟨hD1, hD2, -⟩ := Coercive.modeDerivativeHolds_of hRot Coercive.perturbationLocalIntegrabilityHolds_proof
    Γ P v G H g hv ξ
  have hV := velocity_zero hS hv α s hinv ξ hξ
  have hV' : ∀ᵐ σ, ∀ᵐ y, modeVel ξ v σ y = 0 := by
    rw [Measure.volume_eq_prod] at hV
    exact Measure.ae_ae_of_ae_prod hV
  have hG' : ∀ᵐ σ, ∀ᵐ y, modeGrad ξ G σ y = 0 := by
    filter_upwards [hV', hD1] with σ h0 h1
    have hr := weak_zero h1.1 (by filter_upwards [h0] with y hy; rw [hy, reVec_zero])
    have hi := weak_zero h1.2 (by filter_upwards [h0] with y hy; rw [hy, imVec_zero])
    filter_upwards [hr, hi] with y a b
    exact grad_zero_of a b
  have hH' : ∀ᵐ σ, ∀ᵐ y, modeSecondDeriv ξ H σ y = 0 := by
    filter_upwards [hG', hD2] with σ h0 h2
    have hl : ∀ l : Fin 3, ∀ᵐ y, (fun ij : Fin 3 × Fin 3 => modeSecondDeriv ξ H σ y (ij.1, ij.2, l)) = 0 := by
      intro l
      have hcol : ∀ᵐ y, (fun i => modeGrad ξ G σ y (i, l)) = 0 := by
        filter_upwards [h0] with y hy
        funext i
        rw [hy]
        rfl
      have hr := weak_zero (h2 l).1 (by filter_upwards [hcol] with y hy; rw [hy, reVec_zero])
      have hi := weak_zero (h2 l).2 (by filter_upwards [hcol] with y hy; rw [hy, imVec_zero])
      filter_upwards [hr, hi] with y a b
      exact grad_zero_of a b
    filter_upwards [ae_all_iff.2 hl] with y hy
    funext ijl
    exact congrFun (hy ijl.2.2) (ijl.1, ijl.2.1)
  have hG : ∀ᵐ z : ℝ × Space, modeGrad ξ G z.1 z.2 = 0 := by
    have h := ae_zero_of_ae_ae (Coercive.GainInternal.modeGrad_aesm hRot ξ G hv.measurable_gradient).norm
      (by filter_upwards [hG'] with σ hσ; filter_upwards [hσ] with y hy; rw [hy, norm_zero])
    filter_upwards [h] with z hz
    exact norm_eq_zero.1 hz
  have hH : ∀ᵐ z : ℝ × Space, modeSecondDeriv ξ H z.1 z.2 = 0 := by
    have h := ae_zero_of_ae_ae (Coercive.GainInternal.modeSecondDeriv_aesm hRot ξ H hv.measurable_secondDeriv).norm
      (by filter_upwards [hH'] with σ hσ; filter_upwards [hσ] with y hy; rw [hy, norm_zero])
    filter_upwards [h] with z hz
    exact norm_eq_zero.1 hz
  filter_upwards [hV, hG, hH] with z a b c
  exact ⟨a, b, c⟩

end Bridge

end CertCell

end Breakdown
