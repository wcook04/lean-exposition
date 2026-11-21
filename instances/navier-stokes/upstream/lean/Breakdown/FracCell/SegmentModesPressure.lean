import Breakdown.FracCell.SegmentPairDefs
import Breakdown.FracCell.MeshDataAffineModes
import Breakdown.FracCell.CylModeWeak
import Breakdown.FracCell.ModeRadialPartsA

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown.FracInternal.SegmentModes

theorem off_axis_int {F : ℝ × ℝ → ℂ} {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ p ∈ S, δ ≤ |p.1|) (hw : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) S) : IntegrableOn F S := by
  have hm : AEStronglyMeasurable F (volume.restrict S) := by
    have h2 := (Complex.measurable_ofReal.comp (measurable_fst.inv)).aestronglyMeasurable.mul hw.aestronglyMeasurable
    refine h2.congr ?_
    filter_upwards [ae_restrict_mem hS] with p hp
    have hp0 : p.1 ≠ 0 := fun h => by
      have := hd p hp
      rw [h, abs_zero] at this
      linarith
    show ((p.1⁻¹ : ℝ) : ℂ) * ((p.1 : ℂ) * F p) = F p
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hp0, Complex.ofReal_one, one_mul]
  refine Integrable.mono' (hw.norm.const_mul (1 / δ)) hm ?_
  filter_upwards [ae_restrict_mem hS] with p hp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
  refine le_mul_of_one_le_left (norm_nonneg _) ?_
  rw [div_mul_eq_mul_div, one_mul, one_le_div hδ]
  exact hd p hp

theorem deriv_integral_zero {S : Space → ℝ} (hS : ContDiff ℝ 1 S) (hc : HasCompactSupport S)
    (v : Space) : Integrable (fun x => fderiv ℝ S x v) ∧ ∫ x, fderiv ℝ S x v = 0 := by
  have hi : Integrable (fun x => fderiv ℝ S x v) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((hS.continuous_fderiv one_ne_zero).clm_apply continuous_const) ?_
    exact (hc.fderiv (𝕜 := ℝ)).mono fun x hx h0 => hx (by simp [h0])
  refine ⟨hi, ?_⟩
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Space => (1 : ℝ)) (g := S) (v := v) (by simp) (by simpa using hi)
    (by simpa using hS.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => differentiableAt_const _)
    (fun x _ => (hS.differentiable one_ne_zero).differentiableAt)
  simpa using h

end Breakdown.FracInternal.SegmentModes

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis
open Breakdown.FracInternal.SegmentModes

theorem pressure_weak {Q : Space → Space} (hQ : IsGradientField Q) (e : ℝ) :
    ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • (potentialOf Q y - e) =
        -∫ y, φ y • (innerSL ℝ (Q y) : Space →L[ℝ] ℝ) (unitVector j) := by
  intro φ hφ j
  have hq := MeshGaugeLinearPotential.potentialOf_spec Q hQ
  have hloc := Breakdown.FracInternal.MeshDataAffineModes.pot_locInt hq
  have hz := deriv_integral_zero (hφ.1.of_le (by simp)) hφ.2 (unitVector j)
  have hd : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) * potentialOf Q y) :=
    hloc.integrable_smul_left_of_hasCompactSupport hd (hφ.2.fderiv_apply (𝕜 := ℝ) _)
  have i2 : Integrable (fun y => fderiv ℝ φ y (unitVector j) * e) := hz.1.mul_const e
  have e1 : (fun y => fderiv ℝ φ y (unitVector j) • (potentialOf Q y - e)) =
      fun y => fderiv ℝ φ y (unitVector j) * potentialOf Q y - fderiv ℝ φ y (unitVector j) * e := by
    funext y; rw [smul_eq_mul]; ring
  have e2 : (fun y => φ y • (innerSL ℝ (Q y) : Space →L[ℝ] ℝ) (unitVector j)) =
      fun y => φ y * inner ℝ (Q y) (unitVector j) := by
    funext y; rw [smul_eq_mul, innerSL_apply_apply]
  rw [e1, e2, integral_sub i1 i2, integral_mul_const, hz.2, zero_mul, sub_zero]
  exact hq.2.2 φ hφ j

theorem modes_radial_pair_pressure {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (hx : IsAdmissible c x)
    (L : CellLayout) (hL : L.order = c.order) (n : ℤ) :
    IsRadialWeakPair (L.pressMode n x) (L.pressureGradMode n x 0) := by
  have hG : IsGradientField x.2.2.2.2 := hx.2.1
  have hint := fun r₁ r₂ z₁ z₂ =>
    MeshDataAffineModes.gradient_modes_integrable L.order x.2.2.2.2 hG n (L.gaugeValue x / L.gaugeUnit).re
      r₁ r₂ z₁ z₂
  refine ⟨fun R Z => ⟨(hint 0 R (-Z) Z).1, (hint 0 R (-Z) Z).2 0⟩, fun δ R Z hδ => ?_, ?_⟩
  · refine off_axis_int (measurableSet_Icc.prod measurableSet_Icc) hδ (fun p hp => ?_) ((hint δ R (-Z) Z).2 0)
    rw [abs_of_pos (hδ.trans_le hp.1.1)]
    exact hp.1.1
  · intro ψ hψ hc hpos
    have hq := MeshGaugeLinearPotential.potentialOf_spec x.2.2.2.2 hG
    obtain ⟨_, _, hQ2, hQm, _⟩ := hG
    have hQloc := Breakdown.FracInternal.MeshDataAffineModes.locInt_of_sq hQm hQ2
    have hf : LocallyIntegrable (L.pressureOf x) volume :=
      (Breakdown.FracInternal.MeshDataAffineModes.pot_locInt hq).sub (locallyIntegrable_const _)
    have hg : ∀ j : Fin 3, LocallyIntegrable
        (fun y => (innerSL ℝ (x.2.2.2.2 y) : Space →L[ℝ] ℝ) (unitVector j)) volume := by
      intro j
      refine (locallyIntegrable_iff).2 fun K hK => ?_
      refine Integrable.mono' ((hQloc.integrableOn_isCompact hK).norm)
        ((hQm.inner aestronglyMeasurable_const).restrict) (Filter.Eventually.of_forall fun y => ?_)
      rw [innerSL_apply_apply]
      refine (norm_inner_le_norm _ _).trans ?_
      simp [unitVector]
    have hw := (cylModeWeak ℝ (L.pressureOf x) (fun y => (innerSL ℝ (x.2.2.2.2 y) : Space →L[ℝ] ℝ)) hf hg
      (pressure_weak hx.2.1 _) (fun _ => ContinuousLinearMap.id ℝ ℝ) contDiff_const L.order n ψ hψ hc hpos).1
    have hpm : ∀ p : ℝ × ℝ, L.pressMode n x p = (1 / (2 * Real.pi) : ℂ) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth L.order n * θ : ℝ) * Complex.I) *
          ((ContinuousLinearMap.id ℝ ℝ (L.pressureOf x (cylPoint p.1 θ p.2)) : ℝ) : ℂ) := by
      intro p
      rfl
    have hgm : ∀ p : ℝ × ℝ, L.pressureGradMode n x 0 p = (1 / (2 * Real.pi) : ℂ) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth L.order n * θ : ℝ) * Complex.I) *
          ((ContinuousLinearMap.id ℝ ℝ ((innerSL ℝ (x.2.2.2.2 (cylPoint p.1 θ p.2)) : Space →L[ℝ] ℝ)
            (radialUnit θ)) : ℝ) : ℂ) := by
      intro p
      simp only [ContinuousLinearMap.id_apply, innerSL_apply_apply]
      rfl
    simp only [hpm, hgm]
    exact Breakdown.CellCert.CellAnalysis.ModeRadialPartsA.Internal.scale _ hw

end Breakdown.CellCert.CellFormula
