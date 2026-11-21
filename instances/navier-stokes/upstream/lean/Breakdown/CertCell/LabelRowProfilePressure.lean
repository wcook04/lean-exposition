import Breakdown.CertCell.RowProfileDefs
import Breakdown.CertCell.StripTraceParts
import Breakdown.FracCell.SegmentModesPressure
import Breakdown.FracCell.SegmentModesHeight
import Breakdown.FracCell.CircleWeak
import Breakdown.FracCell.MeshGaugeLinearPotential

open MeasureTheory Set Filter
open scoped ContDiff

noncomputable section

namespace Breakdown.CertCell.CellCalculus

namespace Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula

theorem potential_weak {Q : Space → Space} (hG : IsGradientField Q) :
    ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • potentialOf Q y =
        -∫ y, φ y • (innerSL ℝ (Q y) : Space →L[ℝ] ℝ) (unitVector j) := by
  intro φ hφ j
  have h := pressure_weak hG 0 φ hφ j
  simpa using h

theorem inner_locInt {Q : Space → Space} (hG : IsGradientField Q) (j : Fin 3) :
    LocallyIntegrable (fun y => (innerSL ℝ (Q y) : Space →L[ℝ] ℝ) (unitVector j)) volume := by
  obtain ⟨_, _, hQ2, hQm, _⟩ := hG
  have hQloc := Breakdown.FracInternal.MeshDataAffineModes.locInt_of_sq hQm hQ2
  refine (locallyIntegrable_iff).2 fun K hK => ?_
  refine Integrable.mono' ((hQloc.integrableOn_isCompact hK).norm)
    ((hQm.inner aestronglyMeasurable_const).restrict) (Eventually.of_forall fun y => ?_)
  rw [innerSL_apply_apply]
  refine (norm_inner_le_norm _ _).trans ?_
  simp [unitVector]

theorem mode_integrable {Q : Space → Space} (hG : IsGradientField Q) (m : ℕ) (n : ℤ) (r₁ r₂ z₁ z₂ : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => presMode m n (potentialOf Q) p.1 p.2) (Icc r₁ r₂ ×ˢ Icc z₁ z₂) ∧
    ∀ a : Fin 3, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeVec m n Q p.1 p.2 a) (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := by
  have h := MeshDataAffineModes.gradient_modes_integrable m Q hG n 0 r₁ r₂ z₁ z₂
  simpa using h

theorem grad_radial_pair {Q : Space → Space} (hG : IsGradientField Q) (m : ℕ) (n : ℤ) :
    IsRadialWeakPair (fun p => presMode m n (potentialOf Q) p.1 p.2) (fun p => modeVec m n Q p.1 p.2 0) := by
  have hint := fun r₁ r₂ z₁ z₂ => mode_integrable hG m n r₁ r₂ z₁ z₂
  refine ⟨fun R Z => ⟨(hint 0 R (-Z) Z).1, (hint 0 R (-Z) Z).2 0⟩, fun δ R Z hδ => ?_, ?_⟩
  · refine Breakdown.FracInternal.SegmentModes.off_axis_int (measurableSet_Icc.prod measurableSet_Icc) hδ
      (fun p hp => ?_) ((hint δ R (-Z) Z).2 0)
    rw [abs_of_pos (hδ.trans_le hp.1.1)]
    exact hp.1.1
  · intro ψ hψ hc hpos
    have hq := MeshGaugeLinearPotential.potentialOf_spec Q hG
    have hf : LocallyIntegrable (potentialOf Q) volume := Breakdown.FracInternal.MeshDataAffineModes.pot_locInt hq
    have hw := (cylModeWeak ℝ (potentialOf Q) (fun y => (innerSL ℝ (Q y) : Space →L[ℝ] ℝ)) hf (inner_locInt hG)
      (potential_weak hG) (fun _ => ContinuousLinearMap.id ℝ ℝ) contDiff_const m n ψ hψ hc hpos).1
    have hpm : ∀ p : ℝ × ℝ, presMode m n (potentialOf Q) p.1 p.2 = (1 / (2 * Real.pi) : ℂ) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          ((ContinuousLinearMap.id ℝ ℝ (potentialOf Q (cylPoint p.1 θ p.2)) : ℝ) : ℂ) := fun p => rfl
    have hgm : ∀ p : ℝ × ℝ, modeVec m n Q p.1 p.2 0 = (1 / (2 * Real.pi) : ℂ) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          ((ContinuousLinearMap.id ℝ ℝ ((innerSL ℝ (Q (cylPoint p.1 θ p.2)) : Space →L[ℝ] ℝ)
            (radialUnit θ)) : ℝ) : ℂ) := by
      intro p
      simp only [ContinuousLinearMap.id_apply, innerSL_apply_apply]
      rfl
    simp only [hpm, hgm]
    exact Breakdown.CellCert.CellAnalysis.ModeRadialPartsA.Internal.scale _ hw

theorem grad_height_pair {Q : Space → Space} (hG : IsGradientField Q) (m : ℕ) (n : ℤ) :
    IsHeightWeakPair (fun r => r) (fun p => presMode m n (potentialOf Q) p.1 p.2) (fun p => modeVec m n Q p.1 p.2 2) := by
  have hrect := fun R Z : ℝ => mode_integrable hG m n (-R) R (-Z) Z
  have hF : ∀ p : ℝ × ℝ, presMode m n (potentialOf Q) (-p.1) p.2 =
      Breakdown.FracInternal.SegmentHeight.halfTurn m n * presMode m n (potentialOf Q) p.1 p.2 :=
    fun p => Breakdown.FracInternal.SegmentHeight.pres_refl' m n _ p
  have hdF : ∀ p : ℝ × ℝ, modeVec m n Q (-p.1) p.2 2 =
      Breakdown.FracInternal.SegmentHeight.halfTurn m n * modeVec m n Q p.1 p.2 2 := by
    intro p
    have := Breakdown.FracInternal.SegmentHeight.vel_refl m n Q 2 p
    rw [Breakdown.FracInternal.SegmentHeight.sign_two, mul_one] at this
    exact this
  have hoff : ∀ δ R Z : ℝ, 0 < δ →
      IntegrableOn (fun p : ℝ × ℝ => presMode m n (potentialOf Q) p.1 p.2)
        {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} ∧
      IntegrableOn (fun p : ℝ × ℝ => modeVec m n Q p.1 p.2 2) {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} :=
    fun δ R Z hδ => ⟨(hrect R Z).1.mono_set (Breakdown.FracInternal.SegmentHeight.box_sub δ R Z),
      Breakdown.FracInternal.SegmentModes.off_axis_int (Breakdown.FracInternal.SegmentHeight.box_meas δ R Z) hδ
        (fun p hp => hp.1) (((hrect R Z).2 2).mono_set (Breakdown.FracInternal.SegmentHeight.box_sub δ R Z))⟩
  refine ⟨fun R Z => ⟨Breakdown.FracInternal.SegmentHeight.weighted_rect (hrect R Z).1, (hrect R Z).2 2⟩, hoff,
    Breakdown.FracInternal.SegmentRefl.height_ident_refl (Breakdown.FracInternal.SegmentHeight.halfTurn_ne _ _)
      hF hdF hoff ?_⟩
  intro ψ hψ hc hpos
  have hq := MeshGaugeLinearPotential.potentialOf_spec Q hG
  have hf : LocallyIntegrable (potentialOf Q) volume := Breakdown.FracInternal.MeshDataAffineModes.pot_locInt hq
  have hw := (cylModeWeak ℝ (potentialOf Q) (fun y => (innerSL ℝ (Q y) : Space →L[ℝ] ℝ)) hf (inner_locInt hG)
    (potential_weak hG) (fun _ => ContinuousLinearMap.id ℝ ℝ) contDiff_const m n ψ hψ hc hpos).2
  have hpm : ∀ p : ℝ × ℝ, presMode m n (potentialOf Q) p.1 p.2 = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        ((ContinuousLinearMap.id ℝ ℝ (potentialOf Q (cylPoint p.1 θ p.2)) : ℝ) : ℂ) := fun p => rfl
  have hgm : ∀ p : ℝ × ℝ, modeVec m n Q p.1 p.2 2 = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        ((ContinuousLinearMap.id ℝ ℝ ((innerSL ℝ (Q (cylPoint p.1 θ p.2)) : Space →L[ℝ] ℝ)
          axialUnit) : ℝ) : ℂ) := by
    intro p
    simp only [ContinuousLinearMap.id_apply, innerSL_apply_apply]
    rfl
  simp only [hpm, hgm]
  exact Breakdown.CellCert.CellAnalysis.ModeRadialPartsA.Internal.scale _ hw

theorem grad_angular {Q : Space → Space} (hG : IsGradientField Q) (m : ℕ) (n : ℤ) :
    ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (p.1 : ℂ) * modeVec m n Q p.1 p.2 1 = ((azimuth m n : ℂ) * Complex.I) * presMode m n (potentialOf Q) p.1 p.2 := by
  have hq := MeshGaugeLinearPotential.potentialOf_spec Q hG
  have hQloc : LocallyIntegrable Q volume := by
    obtain ⟨_, _, hQ2, hQm, _⟩ := hG
    exact Breakdown.FracInternal.MeshDataAffineModes.locInt_of_sq hQm hQ2
  have hf : LocallyIntegrable (potentialOf Q) volume := Breakdown.FracInternal.MeshDataAffineModes.pot_locInt hq
  set w : ℝ := azimuth m n with hwdef
  set E : ℝ → ℂ := fun θ => Complex.exp (-((w * θ : ℝ) : ℂ) * Complex.I) with hE
  have hEs : ContDiff ℝ ∞ E := by
    have h0 : ContDiff ℝ ∞ (fun θ : ℝ => (-((w * θ : ℝ) : ℂ) * Complex.I)) :=
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).neg).mul contDiff_const
    exact Complex.contDiff_exp.comp h0
  have hEp : Function.Periodic E (2 * Real.pi) := by
    intro θ
    simp only [hE]
    obtain ⟨j, hj⟩ : ∃ j : ℤ, w = j := ⟨n * m, by simp [hwdef, azimuth]⟩
    rw [show (-(((w * (θ + 2 * Real.pi)) : ℝ) : ℂ) * Complex.I) =
      (-(((w * θ) : ℝ) : ℂ) * Complex.I) + ((-j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by rw [hj]; push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hEd : ∀ θ, deriv E θ = E θ * (-(w : ℂ) * Complex.I) := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => (-((w * θ : ℝ) : ℂ) * Complex.I)) (-(w : ℂ) * Complex.I) θ := by
      have := ((hasDerivAt_id θ).const_mul w).ofReal_comp
      have h2 := (this.neg).mul_const Complex.I
      simpa using h2
    exact h1.cexp.deriv
  obtain ⟨hii, hcw⟩ := CellEnergy.circleWeak (potentialOf Q) Q hf hQloc hq.2.2
  filter_upwards [hii, hcw E hEs hEp] with p hp1 hp2 hpos
  have h := hp2 hpos
  simp only [hEd] at h
  have e1 : ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((p.1 * inner ℝ (Q (cylPoint p.1 θ p.2)) (angularUnit θ) : ℝ) : ℂ) =
      (p.1 : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((inner ℝ (Q (cylPoint p.1 θ p.2)) (angularUnit θ) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext θ; push_cast; ring
  have e2 : ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * (-(w : ℂ) * Complex.I) * (potentialOf Q (cylPoint p.1 θ p.2) : ℂ) =
      (-(w : ℂ) * Complex.I) * ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * (potentialOf Q (cylPoint p.1 θ p.2) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext θ; ring
  rw [e1, e2] at h
  have hq1 : modeVec m n Q p.1 p.2 1 = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((inner ℝ (Q (cylPoint p.1 θ p.2)) (angularUnit θ) : ℝ) : ℂ) := rfl
  have hp : presMode m n (potentialOf Q) p.1 p.2 = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * (potentialOf Q (cylPoint p.1 θ p.2) : ℂ) := rfl
  rw [hq1, hp]
  linear_combination (1 / (2 * Real.pi) : ℂ) * h

end Internal

end Breakdown.CertCell.CellCalculus

namespace Breakdown.CertCell.CellCalculus

namespace Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula

theorem supported_integrable2 {G : ℝ × ℝ → ℂ} {θ : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} (hG : IntegrableOn G S)
    (hS : MeasurableSet S) (hθ : Continuous θ) (hθc : HasCompactSupport θ) (hts : ∀ x, x ∉ S → θ x = 0) :
    Integrable (fun p => (θ p : ℂ) * G p) := by
  obtain ⟨C, hC⟩ := hθc.exists_bound_of_continuous hθ
  have h1 : Integrable (fun t => (θ t : ℂ) * S.indicator G t) :=
    ((integrable_indicator_iff hS).2 hG).bdd_mul (c := C)
      (Complex.continuous_ofReal.comp hθ).aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Complex.norm_real]; exact hC t)
  refine h1.congr (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ S
  · simp [indicator_of_mem ht]
  · simp [hts t ht]

theorem compact_box {C : Set (ℝ × ℝ)} (hC : IsCompact C) (hne : ∀ p ∈ C, p.1 ≠ 0) :
    ∃ δ > 0, ∃ R : ℝ, C ⊆ {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ R} := by
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall 0
  by_cases h : C.Nonempty
  · obtain ⟨q, hq, hmin⟩ := hC.exists_isMinOn h (continuous_abs.comp continuous_fst).continuousOn
    refine ⟨|q.1|, abs_pos.2 (hne q hq), R, fun p hp => ⟨hmin hp, ?_, ?_⟩⟩
    · have := hR hp
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact (norm_fst_le p).trans this
    · have := hR hp
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact (norm_snd_le p).trans this
  · exact ⟨1, one_pos, 0, fun p hp => absurd ⟨p, hp⟩ h⟩

theorem radial_pair_add {F1 dF1 F2 dF2 : ℝ × ℝ → ℂ} (h1 : IsRadialWeakPair F1 dF1) (h2 : IsRadialWeakPair F2 dF2)
    (c : ℂ) : IsRadialWeakPair (fun p => F1 p + c * F2 p) (fun p => dF1 p + c * dF2 p) := by
  refine ⟨fun R Z => ⟨((h1.1 R Z).1).add (((h2.1 R Z).1).const_mul c), ?_⟩,
    fun δ R Z hδ => (h1.2.1 δ R Z hδ).add ((h2.2.1 δ R Z hδ).const_mul c), ?_⟩
  · exact IntegrableOn.congr_fun (((h1.1 R Z).2).add (((h2.1 R Z).2).const_mul c))
      (fun p _ => by simp only [Pi.add_apply]; ring) (measurableSet_Icc.prod measurableSet_Icc)
  · intro ψ hψ hc hpos
    obtain ⟨δ, hδ, R, hR⟩ := compact_box hc.isCompact (fun p hp => (hpos p hp).ne')
    set S : Set (ℝ × ℝ) := Icc δ R ×ˢ Icc (-R) R with hSd
    have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
    have hsub : ∀ p ∈ tsupport ψ, p ∈ S := by
      intro p hp
      have h : δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ R := hR hp
      have hp1 : 0 < p.1 := hpos p hp
      rw [abs_of_pos hp1] at h
      exact ⟨⟨h.1, h.2.1⟩, abs_le.1 h.2.2⟩
    have hSsub : S ⊆ Icc 0 R ×ˢ Icc (-R) R := prod_mono (Icc_subset_Icc_left hδ.le) le_rfl
    have z1 : ∀ p, p ∉ S → ψ p = 0 := fun p hp => image_eq_zero_of_notMem_tsupport (fun h => hp (hsub p h))
    have z2 : ∀ p, p ∉ S → fderiv ℝ ψ p (1, 0) = 0 := by
      intro p hp
      have : fderiv ℝ ψ p = 0 := by
        by_contra hne
        exact hp (hsub p (support_fderiv_subset ℝ hne))
      rw [this]
      rfl
    have hd : Continuous (fun p => fderiv ℝ ψ p (1, 0)) := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdc : HasCompactSupport (fun p => fderiv ℝ ψ p (1, 0)) := hc.fderiv_apply (𝕜 := ℝ) _
    have i1 := supported_integrable2 (((h1.1 R R).1).mono_set hSsub) hS hd hdc z2
    have i2 := supported_integrable2 (((h2.1 R R).1).mono_set hSsub) hS hd hdc z2
    have j1 := supported_integrable2 (h1.2.1 δ R R hδ) hS hψ.continuous hc z1
    have j2 := supported_integrable2 (h2.2.1 δ R R hδ) hS hψ.continuous hc z1
    have e1 : (fun p => ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * (F1 p + c * F2 p)) =
        fun p => ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F1 p + c * (((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F2 p) := by
      funext p; ring
    have e2 : (fun p => (ψ p : ℂ) * (dF1 p + c * dF2 p)) =
        fun p => (ψ p : ℂ) * dF1 p + c * ((ψ p : ℂ) * dF2 p) := by
      funext p; ring
    rw [e1, e2, integral_add i1 (i2.const_mul c), integral_add j1 (j2.const_mul c), integral_const_mul,
      integral_const_mul, h1.2.2 ψ hψ hc hpos, h2.2.2 ψ hψ hc hpos]
    ring

theorem height_pair_add {F1 dF1 F2 dF2 : ℝ × ℝ → ℂ} (h1 : IsHeightWeakPair (fun r => r) F1 dF1)
    (h2 : IsHeightWeakPair (fun r => r) F2 dF2) (c : ℂ) :
    IsHeightWeakPair (fun r => r) (fun p => F1 p + c * F2 p) (fun p => dF1 p + c * dF2 p) := by
  have hms : ∀ δ R Z : ℝ, MeasurableSet {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} :=
    fun δ R Z => Breakdown.FracInternal.SegmentHeight.box_meas δ R Z
  refine ⟨fun R Z => ⟨?_, ?_⟩, fun δ R Z hδ => ⟨((h1.2.1 δ R Z hδ).1).add (((h2.2.1 δ R Z hδ).1).const_mul c),
    ((h1.2.1 δ R Z hδ).2).add (((h2.2.1 δ R Z hδ).2).const_mul c)⟩, ?_⟩
  · exact IntegrableOn.congr_fun (((h1.1 R Z).1).add (((h2.1 R Z).1).const_mul c))
      (fun p _ => by simp only [Pi.add_apply]; ring) (measurableSet_Icc.prod measurableSet_Icc)
  · exact IntegrableOn.congr_fun (((h1.1 R Z).2).add (((h2.1 R Z).2).const_mul c))
      (fun p _ => by simp only [Pi.add_apply]; ring) (measurableSet_Icc.prod measurableSet_Icc)
  · intro ψ hψ hc hne
    obtain ⟨δ, hδ, R, hR⟩ := compact_box hc.isCompact hne
    set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ R} with hSd
    have hS : MeasurableSet S := hms δ R R
    have z1 : ∀ p, p ∉ S → ψ p = 0 := fun p hp => image_eq_zero_of_notMem_tsupport (fun h => hp (hR h))
    have z2 : ∀ p, p ∉ S → fderiv ℝ ψ p (0, 1) = 0 := by
      intro p hp
      have : fderiv ℝ ψ p = 0 := by
        by_contra hne'
        exact hp (hR (support_fderiv_subset ℝ hne'))
      rw [this]
      rfl
    have hd : Continuous (fun p => fderiv ℝ ψ p (0, 1)) := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdc : HasCompactSupport (fun p => fderiv ℝ ψ p (0, 1)) := hc.fderiv_apply (𝕜 := ℝ) _
    have i1 := supported_integrable2 ((h1.2.1 δ R R hδ).1) hS hd hdc z2
    have i2 := supported_integrable2 ((h2.2.1 δ R R hδ).1) hS hd hdc z2
    have j1 := supported_integrable2 ((h1.2.1 δ R R hδ).2) hS hψ.continuous hc z1
    have j2 := supported_integrable2 ((h2.2.1 δ R R hδ).2) hS hψ.continuous hc z1
    have e1 : (fun p => ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * (F1 p + c * F2 p)) =
        fun p => ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F1 p + c * (((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F2 p) := by
      funext p; ring
    have e2 : (fun p => (ψ p : ℂ) * (dF1 p + c * dF2 p)) =
        fun p => (ψ p : ℂ) * dF1 p + c * ((ψ p : ℂ) * dF2 p) := by
      funext p; ring
    rw [e1, e2, integral_add i1 (i2.const_mul c), integral_add j1 (j2.const_mul c), integral_const_mul,
      integral_const_mul, h1.2.2 ψ hψ hc hne, h2.2.2 ψ hψ hc hne]
    ring

end Internal

end Breakdown.CertCell.CellCalculus

namespace Breakdown.CertCell.CellCalculus

namespace Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula

def radialFactor (K : CellBox) (P : CellPoly) (j : Fin (P.deg + 1)) (r : ℝ) : ℂ :=
  ∑ i, (starRingEnd ℂ) (P.coef i j) * ((K.refR r : ℝ) : ℂ) ^ (i : ℕ)

def heightFactor (K : CellBox) (P : CellPoly) (i : Fin (P.deg + 1)) (z : ℝ) : ℂ :=
  ∑ j, (starRingEnd ℂ) (P.coef i j) * ((K.refZ z : ℝ) : ℂ) ^ (j : ℕ)

theorem conj_eval_radial (K : CellBox) (P : CellPoly) (p : ℝ × ℝ) :
    (starRingEnd ℂ) (P.eval K p) = ∑ j, radialFactor K P j p.1 * ((K.refZ p.2 : ℝ) : ℂ) ^ (j : ℕ) := by
  simp only [CellPoly.eval, radialFactor, map_sum, map_mul, map_pow, Complex.conj_ofReal, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem conj_eval_height (K : CellBox) (P : CellPoly) (p : ℝ × ℝ) :
    (starRingEnd ℂ) (P.eval K p) = ∑ i, heightFactor K P i p.2 * ((K.refR p.1 : ℝ) : ℂ) ^ (i : ℕ) := by
  simp only [CellPoly.eval, heightFactor, map_sum, map_mul, map_pow, Complex.conj_ofReal, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem refR_contDiff (K : CellBox) : ContDiff ℝ ∞ (fun r : ℝ => ((K.refR r : ℝ) : ℂ)) := by
  unfold CellBox.refR
  exact Complex.ofRealCLM.contDiff.comp ((((contDiff_const.mul contDiff_id).sub contDiff_const).sub
    contDiff_const).div_const _)

theorem refZ_contDiff (K : CellBox) : ContDiff ℝ ∞ (fun z : ℝ => ((K.refZ z : ℝ) : ℂ)) := by
  unfold CellBox.refZ
  exact Complex.ofRealCLM.contDiff.comp ((((contDiff_const.mul contDiff_id).sub contDiff_const).sub
    contDiff_const).div_const _)

theorem radialFactor_contDiff (K : CellBox) (P : CellPoly) (j : Fin (P.deg + 1)) :
    ContDiff ℝ ∞ (radialFactor K P j) := by
  unfold radialFactor
  exact ContDiff.sum fun i _ => contDiff_const.mul ((refR_contDiff K).pow _)

theorem heightFactor_contDiff (K : CellBox) (P : CellPoly) (i : Fin (P.deg + 1)) :
    ContDiff ℝ ∞ (heightFactor K P i) := by
  unfold heightFactor
  exact ContDiff.sum fun j _ => contDiff_const.mul ((refZ_contDiff K).pow _)

theorem eval_radial_contDiff (K : CellBox) (P : CellPoly) (z : ℝ) :
    ContDiff ℝ ∞ (fun r : ℝ => P.eval K (r, z)) := by
  show ContDiff ℝ ∞ (fun r : ℝ => ∑ i, ∑ j, P.coef i j * ((K.refR r : ℝ) : ℂ) ^ (i : ℕ) * ((K.refZ z : ℝ) : ℂ) ^ (j : ℕ))
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (contDiff_const.mul ((refR_contDiff K).pow _)).mul contDiff_const

theorem eval_height_contDiff (K : CellBox) (P : CellPoly) (r : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ => P.eval K (r, z)) := by
  show ContDiff ℝ ∞ (fun z : ℝ => ∑ i, ∑ j, P.coef i j * ((K.refR r : ℝ) : ℂ) ^ (i : ℕ) * ((K.refZ z : ℝ) : ℂ) ^ (j : ℕ))
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    contDiff_const.mul ((refZ_contDiff K).pow _)

theorem eval_continuous (K : CellBox) (P : CellPoly) : Continuous (fun p : ℝ × ℝ => P.eval K p) := by
  unfold CellPoly.eval
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_const.mul (((refR_contDiff K).continuous.comp continuous_fst).pow _)).mul
    (((refZ_contDiff K).continuous.comp continuous_snd).pow _)

theorem conj_radialDeriv (K : CellBox) (P : CellPoly) (p : ℝ × ℝ) :
    (starRingEnd ℂ) (CellBox.radialDeriv (fun q => P.eval K q) p) =
      ∑ j, deriv (radialFactor K P j) p.1 * ((K.refZ p.2 : ℝ) : ℂ) ^ (j : ℕ) := by
  unfold CellBox.radialDeriv
  have e : (starRingEnd ℂ) (deriv (fun r : ℝ => P.eval K (r, p.2)) p.1) =
      deriv (fun r : ℝ => star (P.eval K (r, p.2))) p.1 := deriv.star.symm
  rw [e]
  have e2 : (fun r : ℝ => star (P.eval K (r, p.2))) =
      fun r => ∑ j, radialFactor K P j r * ((K.refZ p.2 : ℝ) : ℂ) ^ (j : ℕ) := by
    funext r
    exact conj_eval_radial K P (r, p.2)
  rw [e2, deriv_fun_sum (fun j _ => ((radialFactor_contDiff K P j).differentiable (by simp) p.1).mul_const _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact deriv_mul_const ((radialFactor_contDiff K P j).differentiable (by simp) p.1) _

theorem conj_heightDeriv (K : CellBox) (P : CellPoly) (p : ℝ × ℝ) :
    (starRingEnd ℂ) (CellBox.heightDeriv (fun q => P.eval K q) p) =
      ∑ i, deriv (heightFactor K P i) p.2 * ((K.refR p.1 : ℝ) : ℂ) ^ (i : ℕ) := by
  unfold CellBox.heightDeriv
  have e : (starRingEnd ℂ) (deriv (fun z : ℝ => P.eval K (p.1, z)) p.2) =
      deriv (fun z : ℝ => star (P.eval K (p.1, z))) p.2 := deriv.star.symm
  rw [e]
  have e2 : (fun z : ℝ => star (P.eval K (p.1, z))) =
      fun z => ∑ i, heightFactor K P i z * ((K.refR p.1 : ℝ) : ℂ) ^ (i : ℕ) := by
    funext z
    exact conj_eval_height K P (p.1, z)
  rw [e2, deriv_fun_sum (fun i _ => ((heightFactor_contDiff K P i).differentiable (by simp) p.2).mul_const _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact deriv_mul_const ((heightFactor_contDiff K P i).differentiable (by simp) p.2) _

theorem radialDeriv_weighted (K : CellBox) (P : CellPoly) (p : ℝ × ℝ) :
    CellBox.radialDeriv (fun q => (q.1 : ℂ) * P.eval K q) p =
      P.eval K p + (p.1 : ℂ) * CellBox.radialDeriv (fun q => P.eval K q) p := by
  unfold CellBox.radialDeriv
  show deriv (fun r : ℝ => (r : ℂ) * P.eval K (r, p.2)) p.1 = _
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 p.1 := by simpa using (hasDerivAt_id p.1).ofReal_comp
  have h2 := ((eval_radial_contDiff K P p.2).differentiable (by simp) p.1).hasDerivAt
  have h3 : HasDerivAt (fun r : ℝ => (r : ℂ) * P.eval K (r, p.2))
      (1 * P.eval K (p.1, p.2) + (p.1 : ℂ) * deriv (fun r => P.eval K (r, p.2)) p.1) p.1 := h1.mul h2
  rw [h3.deriv]
  simp

end Internal

end Breakdown.CertCell.CellCalculus

namespace Breakdown.CertCell.CellCalculus

namespace Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula
open Breakdown.CertCell.StripTrace

theorem radial_low_integrable {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {a b lo hi : ℝ} (ha : 0 ≤ a)
    (hab : a < b) {t : ℝ → ℂ} (ht : Continuous t) :
    IntegrableOn (fun p : ℝ × ℝ => (a : ℂ) * (((((1 / (a - b) : ℝ)) : ℂ) * F p
      + (((p.1 - b) / (a - b) : ℝ) : ℂ) * dF p) * t p.2)) (Icc a b ×ˢ Icc lo hi) := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    refine IntegrableOn.congr_fun integrableOn_zero (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    simp
  · set Z : ℝ := |lo| + |hi|
    have hsub : Icc a b ×ˢ Icc lo hi ⊆ Icc 0 (b + 1) ×ˢ Icc (-Z) Z :=
      prod_mono (Icc_subset_Icc hpos.le (by linarith)) (Breakdown.CertCell.StripTrace.Internal.sym_box lo hi)
    have hsub2 : Icc a b ×ˢ Icc lo hi ⊆ Icc a (b + 1) ×ˢ Icc (-Z) Z :=
      prod_mono (Icc_subset_Icc le_rfl (by linarith)) (Breakdown.CertCell.StripTrace.Internal.sym_box lo hi)
    have hF := ((h.1 (b + 1) Z).1).mono_set hsub
    have hdF := (h.2.1 a (b + 1) Z hpos).mono_set hsub2
    have hcpt : IsCompact (Icc a b ×ˢ Icc lo hi) := isCompact_Icc.prod isCompact_Icc
    have hramp : Continuous (fun p : ℝ × ℝ => (((p.1 - b) / (a - b) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (((continuous_fst).sub continuous_const).div_const _)
    refine IntegrableOn.congr_fun ((IntegrableOn.mul_continuousOn ((hF.const_mul ((((1 / (a - b) : ℝ)) : ℂ))).add
      (hdF.continuousOn_mul hramp.continuousOn hcpt)) (ht.comp continuous_snd).continuousOn hcpt).const_mul (a : ℂ))
      (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    simp only [Pi.add_apply, Function.comp_apply]

theorem radial_poly_parts {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {K : CellBox} (hK : IsCellBox K)
    (P : CellPoly) :
    IntegrableOn (fun p : ℝ × ℝ => dF p * ((p.1 : ℂ) * (starRingEnd ℂ) (P.eval K p))
      + F p * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * P.eval K q) p)) K.rect ∧
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (K.r₂ - K.r₁) : ℝ)) : ℂ) * F p + (((p.1 - K.r₁) / (K.r₂ - K.r₁) : ℝ) : ℂ) * dF p)
      * ((K.r₂ : ℂ) * (starRingEnd ℂ) (P.eval K (K.r₂, p.2)))) K.rect ∧
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) * F p + (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) * dF p)
      * ((K.r₁ : ℂ) * (starRingEnd ℂ) (P.eval K (K.r₁, p.2)))) K.rect ∧
    ∫ p in K.rect, (dF p * ((p.1 : ℂ) * (starRingEnd ℂ) (P.eval K p))
      + F p * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * P.eval K q) p)) =
      (∫ p in K.rect, ((((1 / (K.r₂ - K.r₁) : ℝ)) : ℂ) * F p + (((p.1 - K.r₁) / (K.r₂ - K.r₁) : ℝ) : ℂ) * dF p)
        * ((K.r₂ : ℂ) * (starRingEnd ℂ) (P.eval K (K.r₂, p.2))))
      + ∫ p in K.rect, ((((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) * F p + (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) * dF p)
        * ((K.r₁ : ℂ) * (starRingEnd ℂ) (P.eval K (K.r₁, p.2))) := by
  have ha : 0 ≤ K.r₁ := hK.r_order.1
  have hab : K.r₁ < K.r₂ := hK.r_order.2
  set k : Fin (P.deg + 1) → ℝ → ℂ := fun j => radialFactor K P j with hkd
  set t : Fin (P.deg + 1) → ℝ → ℂ := fun j z => ((K.refZ z : ℝ) : ℂ) ^ (j : ℕ) with htd
  have hkD : ∀ j x, HasDerivAt (k j) (deriv (k j) x) x := fun j x =>
    ((radialFactor_contDiff K P j).differentiable (by simp) x).hasDerivAt
  have hkD' : ∀ j, Continuous (deriv (k j)) := fun j => (radialFactor_contDiff K P j).continuous_deriv (by simp)
  have ht : ∀ j, Continuous (t j) := fun j => ((refZ_contDiff K).continuous).pow _
  have R := fun j => radial_parts h (lo := K.z₁) (hi := K.z₂) ha hab (hkD j) (hkD' j) (ht j)
  have RL := fun j => radial_low_integrable h (lo := K.z₁) (hi := K.z₂) ha hab (ht j)
  have hrect : K.rect = Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ := rfl
  rw [hrect]
  have hpt : ∀ p : ℝ × ℝ, dF p * ((p.1 : ℂ) * (starRingEnd ℂ) (P.eval K p))
      + F p * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * P.eval K q) p) =
      ∑ j, (dF p * ((p.1 : ℂ) * k j p.1) + F p * (k j p.1 + (p.1 : ℂ) * deriv (k j) p.1)) * t j p.2 := by
    intro p
    rw [radialDeriv_weighted, map_add, map_mul, Complex.conj_ofReal, conj_radialDeriv, conj_eval_radial]
    simp only [hkd, htd, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hb : ∀ z : ℝ, (K.r₂ : ℂ) * (starRingEnd ℂ) (P.eval K (K.r₂, z)) = ∑ j, ((K.r₂ : ℂ) * k j K.r₂) * t j z := by
    intro z
    rw [conj_eval_radial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hkd, htd]
    ring
  have ha' : ∀ z : ℝ, (K.r₁ : ℂ) * (starRingEnd ℂ) (P.eval K (K.r₁, z)) = ∑ j, ((K.r₁ : ℂ) * k j K.r₁) * t j z := by
    intro z
    rw [conj_eval_radial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hkd, htd]
    ring
  have hms : MeasurableSet (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) := measurableSet_Icc.prod measurableSet_Icc
  have iL : IntegrableOn (fun p : ℝ × ℝ => dF p * ((p.1 : ℂ) * (starRingEnd ℂ) (P.eval K p))
      + F p * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * P.eval K q) p)) (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) :=
    IntegrableOn.congr_fun (integrable_finsetSum _ fun j _ => (R j).1) (fun p _ => by rw [hpt p]) hms
  have iB : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (K.r₂ - K.r₁) : ℝ)) : ℂ) * F p
      + (((p.1 - K.r₁) / (K.r₂ - K.r₁) : ℝ) : ℂ) * dF p) * ((K.r₂ : ℂ) * (starRingEnd ℂ) (P.eval K (K.r₂, p.2))))
      (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) :=
    IntegrableOn.congr_fun (integrable_finsetSum _ fun j _ => ((R j).2.1).const_mul ((K.r₂ : ℂ) * k j K.r₂))
      (fun p _ => by rw [hb p.2, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring) hms
  have iA : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) * F p
      + (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) * dF p) * ((K.r₁ : ℂ) * (starRingEnd ℂ) (P.eval K (K.r₁, p.2))))
      (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) :=
    IntegrableOn.congr_fun (integrable_finsetSum _ fun j _ => (RL j).const_mul (k j K.r₁))
      (fun p _ => by rw [ha' p.2, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring) hms
  refine ⟨iL, iB, iA, ?_⟩
  rw [setIntegral_congr_fun hms (fun p _ => hpt p), integral_finsetSum _ (fun j _ => (R j).1)]
  have eB : ∫ p in Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂, ((((1 / (K.r₂ - K.r₁) : ℝ)) : ℂ) * F p
      + (((p.1 - K.r₁) / (K.r₂ - K.r₁) : ℝ) : ℂ) * dF p) * ((K.r₂ : ℂ) * (starRingEnd ℂ) (P.eval K (K.r₂, p.2))) =
      ∑ j, ((K.r₂ : ℂ) * k j K.r₂) * ∫ p in Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂, ((((1 / (K.r₂ - K.r₁) : ℝ)) : ℂ) * F p
        + (((p.1 - K.r₁) / (K.r₂ - K.r₁) : ℝ) : ℂ) * dF p) * t j p.2 := by
    rw [setIntegral_congr_fun hms (fun p _ => by rw [hb p.2, Finset.mul_sum]),
      integral_finsetSum _ (fun j _ => IntegrableOn.congr_fun (((R j).2.1).const_mul ((K.r₂ : ℂ) * k j K.r₂))
        (fun p _ => by ring) hms)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext p
    ring
  have eA : ∫ p in Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂, ((((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) * F p
      + (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) * dF p) * ((K.r₁ : ℂ) * (starRingEnd ℂ) (P.eval K (K.r₁, p.2))) =
      ∑ j, ((K.r₁ : ℂ) * k j K.r₁) * ∫ p in Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂, ((((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) * F p
        + (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) * dF p) * t j p.2 := by
    rw [setIntegral_congr_fun hms (fun p _ => by rw [ha' p.2, Finset.mul_sum]),
      integral_finsetSum _ (fun j _ => IntegrableOn.congr_fun ((RL j).const_mul (k j K.r₁))
        (fun p _ => by ring) hms)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext p
    ring
  rw [eB, eA, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => (R j).2.2

end Internal

end Breakdown.CertCell.CellCalculus

namespace Breakdown.CertCell.CellCalculus

namespace Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula
open Breakdown.CertCell.StripTrace

theorem height_poly_parts {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair (fun r => r) F dF) {K : CellBox}
    (hK : IsCellBox K) (P : CellPoly) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * (dF p * (starRingEnd ℂ) (P.eval K p)
      + F p * (starRingEnd ℂ) (CellBox.heightDeriv (fun q => P.eval K q) p))) K.rect ∧
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (K.z₂ - K.z₁) : ℝ)) : ℂ) * F p + (((p.2 - K.z₁) / (K.z₂ - K.z₁) : ℝ) : ℂ) * dF p)
      * ((p.1 : ℂ) * (starRingEnd ℂ) (P.eval K (p.1, K.z₂)))) K.rect ∧
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (K.z₁ - K.z₂) : ℝ)) : ℂ) * F p + (((p.2 - K.z₂) / (K.z₁ - K.z₂) : ℝ) : ℂ) * dF p)
      * ((p.1 : ℂ) * (starRingEnd ℂ) (P.eval K (p.1, K.z₁)))) K.rect ∧
    ∫ p in K.rect, (p.1 : ℂ) * (dF p * (starRingEnd ℂ) (P.eval K p)
      + F p * (starRingEnd ℂ) (CellBox.heightDeriv (fun q => P.eval K q) p)) =
      (∫ p in K.rect, ((((1 / (K.z₂ - K.z₁) : ℝ)) : ℂ) * F p + (((p.2 - K.z₁) / (K.z₂ - K.z₁) : ℝ) : ℂ) * dF p)
        * ((p.1 : ℂ) * (starRingEnd ℂ) (P.eval K (p.1, K.z₂))))
      + ∫ p in K.rect, ((((1 / (K.z₁ - K.z₂) : ℝ)) : ℂ) * F p + (((p.2 - K.z₂) / (K.z₁ - K.z₂) : ℝ) : ℂ) * dF p)
        * ((p.1 : ℂ) * (starRingEnd ℂ) (P.eval K (p.1, K.z₁))) := by
  have hab : K.z₁ < K.z₂ := hK.z_order.2
  set k : Fin (P.deg + 1) → ℝ → ℂ := fun i => heightFactor K P i with hkd
  set t : Fin (P.deg + 1) → ℝ → ℂ := fun i r => ((K.refR r : ℝ) : ℂ) ^ (i : ℕ) with htd
  have hkD : ∀ i x, HasDerivAt (k i) (deriv (k i) x) x := fun i x =>
    ((heightFactor_contDiff K P i).differentiable (by simp) x).hasDerivAt
  have hkD' : ∀ i, Continuous (deriv (k i)) := fun i => (heightFactor_contDiff K P i).continuous_deriv (by simp)
  have ht : ∀ i, Continuous (t i) := fun i => ((refR_contDiff K).continuous).pow _
  have R := fun i => height_parts h (lo := K.r₁) (hi := K.r₂) hab (hkD i) (hkD' i) (ht i)
  have hrect : K.rect = Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ := rfl
  rw [hrect]
  have hms : MeasurableSet (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) := measurableSet_Icc.prod measurableSet_Icc
  have hpt : ∀ p : ℝ × ℝ, (p.1 : ℂ) * (dF p * (starRingEnd ℂ) (P.eval K p)
      + F p * (starRingEnd ℂ) (CellBox.heightDeriv (fun q => P.eval K q) p)) =
      ∑ i, (p.1 : ℂ) * (dF p * k i p.2 + F p * deriv (k i) p.2) * t i p.1 := by
    intro p
    rw [conj_heightDeriv, conj_eval_height]
    simp only [hkd, htd, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hb : ∀ r : ℝ, (r : ℂ) * (starRingEnd ℂ) (P.eval K (r, K.z₂)) = ∑ i, k i K.z₂ * ((r : ℂ) * t i r) := by
    intro r
    rw [conj_eval_height, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hkd, htd]
    ring
  have ha : ∀ r : ℝ, (r : ℂ) * (starRingEnd ℂ) (P.eval K (r, K.z₁)) = ∑ i, k i K.z₁ * ((r : ℂ) * t i r) := by
    intro r
    rw [conj_eval_height, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hkd, htd]
    ring
  have iL : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * (dF p * (starRingEnd ℂ) (P.eval K p)
      + F p * (starRingEnd ℂ) (CellBox.heightDeriv (fun q => P.eval K q) p))) (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) :=
    IntegrableOn.congr_fun (integrable_finsetSum _ fun i _ => (R i).1) (fun p _ => by rw [hpt p]) hms
  have iB : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (K.z₂ - K.z₁) : ℝ)) : ℂ) * F p
      + (((p.2 - K.z₁) / (K.z₂ - K.z₁) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * (starRingEnd ℂ) (P.eval K (p.1, K.z₂))))
      (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) :=
    IntegrableOn.congr_fun (integrable_finsetSum _ fun i _ => ((R i).2.1).const_mul (k i K.z₂))
      (fun p _ => by rw [hb p.1, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring) hms
  have iA : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (K.z₁ - K.z₂) : ℝ)) : ℂ) * F p
      + (((p.2 - K.z₂) / (K.z₁ - K.z₂) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * (starRingEnd ℂ) (P.eval K (p.1, K.z₁))))
      (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) :=
    IntegrableOn.congr_fun (integrable_finsetSum _ fun i _ => ((R i).2.2.1).const_mul (k i K.z₁))
      (fun p _ => by rw [ha p.1, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring) hms
  refine ⟨iL, iB, iA, ?_⟩
  rw [setIntegral_congr_fun hms (fun p _ => hpt p), integral_finsetSum _ (fun i _ => (R i).1)]
  have eB : ∫ p in Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂, ((((1 / (K.z₂ - K.z₁) : ℝ)) : ℂ) * F p
      + (((p.2 - K.z₁) / (K.z₂ - K.z₁) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * (starRingEnd ℂ) (P.eval K (p.1, K.z₂))) =
      ∑ i, k i K.z₂ * ∫ p in Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂, ((((1 / (K.z₂ - K.z₁) : ℝ)) : ℂ) * F p
        + (((p.2 - K.z₁) / (K.z₂ - K.z₁) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * t i p.1) := by
    rw [setIntegral_congr_fun hms (fun p _ => by rw [hb p.1, Finset.mul_sum]),
      integral_finsetSum _ (fun i _ => IntegrableOn.congr_fun (((R i).2.1).const_mul (k i K.z₂))
        (fun p _ => by ring) hms)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext p
    ring
  have eA : ∫ p in Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂, ((((1 / (K.z₁ - K.z₂) : ℝ)) : ℂ) * F p
      + (((p.2 - K.z₂) / (K.z₁ - K.z₂) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * (starRingEnd ℂ) (P.eval K (p.1, K.z₁))) =
      ∑ i, k i K.z₁ * ∫ p in Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂, ((((1 / (K.z₁ - K.z₂) : ℝ)) : ℂ) * F p
        + (((p.2 - K.z₂) / (K.z₁ - K.z₂) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * t i p.1) := by
    rw [setIntegral_congr_fun hms (fun p _ => by rw [ha p.1, Finset.mul_sum]),
      integral_finsetSum _ (fun i _ => IntegrableOn.congr_fun (((R i).2.2.1).const_mul (k i K.z₁))
        (fun p _ => by ring) hms)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext p
    ring
  rw [eB, eA, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (R i).2.2.2

end Internal

end Breakdown.CertCell.CellCalculus

namespace Breakdown.CertCell.CellCalculus

namespace Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula
open Breakdown.CertCell.StripTrace

theorem radial_boundary_term {F D D' : ℝ × ℝ → ℂ} {r₁ r₂ z₁ z₂ c o : ℝ} {w : ℝ → ℂ}
    (hD : ∀ᵐ p ∂volume, p ∈ Icc r₁ r₂ ×ˢ Icc z₁ z₂ → D' p = D p)
    (hint : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * D p)
      * w p.2) (Icc r₁ r₂ ×ˢ Icc z₁ z₂))
    (hmin : min c o = r₁) (hmax : max c o = r₂) :
    ∫ z in Icc z₁ z₂, radialStripTrace c o F D' z * w z =
      edgeSign c o * ∫ p in Icc r₁ r₂ ×ˢ Icc z₁ z₂,
        ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * D p) * w p.2 := by
  have hms : MeasurableSet (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := measurableSet_Icc.prod measurableSet_Icc
  have hcongr : ∀ᵐ p ∂volume, p ∈ Icc r₁ r₂ ×ˢ Icc z₁ z₂ →
      ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * D p) * w p.2 =
      ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * D' p) * w p.2 := by
    filter_upwards [hD] with p hp hm
    rw [hp hm]
  have hint' : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * D' p)
      * w p.2) (Icc r₁ r₂ ×ˢ Icc z₁ z₂) :=
    hint.congr_fun_ae ((ae_restrict_iff' hms).2 hcongr)
  rw [setIntegral_congr_ae hms hcongr, Breakdown.CertCell.StripTrace.Internal.prod_iter_fst hint',
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [radialStripTrace, hmin, hmax]
  rw [integral_mul_const]
  ring

theorem height_boundary_term {F D D' : ℝ × ℝ → ℂ} {r₁ r₂ z₁ z₂ c o : ℝ} {w : ℝ → ℂ}
    (hD : ∀ᵐ p ∂volume, p ∈ Icc r₁ r₂ ×ˢ Icc z₁ z₂ → D' p = D p)
    (hint : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * D p)
      * w p.1) (Icc r₁ r₂ ×ˢ Icc z₁ z₂))
    (hmin : min c o = z₁) (hmax : max c o = z₂) :
    ∫ r in Icc r₁ r₂, heightStripTrace c o F D' r * w r =
      edgeSign c o * ∫ p in Icc r₁ r₂ ×ˢ Icc z₁ z₂,
        ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * D p) * w p.1 := by
  have hms : MeasurableSet (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := measurableSet_Icc.prod measurableSet_Icc
  have hcongr : ∀ᵐ p ∂volume, p ∈ Icc r₁ r₂ ×ˢ Icc z₁ z₂ →
      ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * D p) * w p.1 =
      ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * D' p) * w p.1 := by
    filter_upwards [hD] with p hp hm
    rw [hp hm]
  have hint' : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * D' p)
      * w p.1) (Icc r₁ r₂ ×ˢ Icc z₁ z₂) :=
    hint.congr_fun_ae ((ae_restrict_iff' hms).2 hcongr)
  rw [setIntegral_congr_ae hms hcongr, Breakdown.CertCell.StripTrace.Internal.prod_iter hint',
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [heightStripTrace, hmin, hmax]
  rw [integral_mul_const]
  ring

end Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField
open Internal

theorem labelRowProfile_pressure (h2 : HarmonicPressureLiftStatement) (K : CellBox) (hK : IsCellBox K) (m : ℕ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (hp : IsPeriodicPressure Pg)
    (ι : ℤ × ℤ) (hax : K.IsAxis → ι.1 = 0) (φ : Fin 3 → CellPoly)
    (hs : IsTestSolenoidal K (labelAzimuth m ι : ℝ) φ) (hφ : IsAxisRegularTest K (labelAzimuth m ι : ℝ) φ) :
    rowPairing K (labelRowProfile K m ι v G H Pg).presGrad φ = rowBoundaryPres K (labelRowProfile K m ι v G H Pg) φ := by
  obtain ⟨hgc, hgs⟩ := hp.harmonic_gradient (labelTime ι)
  set Qc := harmonicCos (labelTime ι) Pg with hQc
  set Qs := harmonicSin (labelTime ι) Pg with hQs
  set Pf : ℝ × ℝ → ℂ := labelPressure m ι Pg with hPf
  set Dt : Fin 3 → ℝ × ℝ → ℂ := fun j p => modeVec m ι.1 Qc p.1 p.2 j + Complex.I * modeVec m ι.1 Qs p.1 p.2 j
    with hDt
  have hR : IsRadialWeakPair Pf (Dt 0) :=
    radial_pair_add (grad_radial_pair hgc m ι.1) (grad_radial_pair hgs m ι.1) Complex.I
  have hZ : IsHeightWeakPair (fun r => r) Pf (Dt 2) :=
    height_pair_add (grad_height_pair hgc m ι.1) (grad_height_pair hgs m ι.1) Complex.I
  set kk : ℂ := ((labelAzimuth m ι : ℝ) : ℂ) with hkk
  have hkaz : ((azimuth m ι.1 : ℝ) : ℂ) = kk := by
    simp [hkk, azimuth, labelAzimuth]
  have hA : ∀ᵐ p : ℝ × ℝ, 0 < p.1 → (p.1 : ℂ) * Dt 1 p = (kk * Complex.I) * Pf p := by
    filter_upwards [grad_angular hgc m ι.1, grad_angular hgs m ι.1] with p h1 h2' hpos
    have e1 := h1 hpos
    have e2 := h2' hpos
    rw [hkaz] at e1 e2
    simp only [hDt, hPf, labelPressure]
    linear_combination e1 + Complex.I * e2
  have hmode : harmonicMode (labelTime ι) ι.1 = ι := by
    refine Prod.ext rfl ?_
    simp only [harmonicMode, labelTime]
    omega
  have heven : Even (ι.1 + labelTime ι) := ⟨ι.2, by simp only [labelTime]; ring⟩
  have hV : ∀ᵐ p : ℝ × ℝ, 0 < p.1 → ∀ a, velAt m ι Pg a p = Dt a p := by
    have := h2 m Pg hp (labelTime ι) ι.1 heven
    rw [hmode] at this
    exact this
  have hpos_ae : ∀ᵐ p : ℝ × ℝ, p ∈ K.rect → 0 < p.1 := by
    filter_upwards [Breakdown.FracInternal.CornerParts.ae_fst_ne 0] with p hp0 hp
    exact lt_of_le_of_ne (hK.r_order.1.trans hp.1.1) (Ne.symm hp0)
  have hVr : ∀ j, ∀ᵐ p : ℝ × ℝ, p ∈ Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ → velAt m ι Pg j p = Dt j p := by
    intro j
    filter_upwards [hpos_ae, hV] with p h1 h3 hm
    exact h3 (h1 hm) j
  obtain ⟨iR, iRb, iRa, eR⟩ := radial_poly_parts hR hK (φ 0)
  obtain ⟨iZ, iZb, iZa, eZ⟩ := height_poly_parts hZ hK (φ 2)
  have hms : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hvol : rowPairing K (labelRowProfile K m ι v G H Pg).presGrad φ =
      ∫ p in K.rect, ((Dt 0 p * ((p.1 : ℂ) * (starRingEnd ℂ) ((φ 0).eval K p))
        + Pf p * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * (φ 0).eval K q) p))
        + (p.1 : ℂ) * (Dt 2 p * (starRingEnd ℂ) ((φ 2).eval K p)
          + Pf p * (starRingEnd ℂ) (CellBox.heightDeriv (fun q => (φ 2).eval K q) p))) := by
    unfold rowPairing
    refine setIntegral_congr_ae hms ?_
    filter_upwards [hpos_ae, hV, hA] with p h0 hVp hAp hm
    have hp1 := h0 hm
    have key := hAp hp1
    have hsol := hs p hm
    have hc := congrArg (starRingEnd ℂ) hsol
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_zero] at hc
    show (p.1 : ℂ) * cdot3 (velArray m ι Pg p) (testValue K φ p) = _
    have hv := hVp hp1
    simp only [cdot3, velArray, testValue, Fin.sum_univ_three, hv]
    linear_combination (starRingEnd ℂ) ((φ 1).eval K p) * key - Pf p * hc
  rw [hvol, integral_add iR iZ, eR, eZ]
  have hab : K.r₁ < K.r₂ := hK.r_order.2
  have hcd : K.z₁ < K.z₂ := hK.z_order.2
  have es1 : edgeSign K.r₂ K.r₁ = 1 := by simp [edgeSign, hab]
  have es0 : edgeSign K.r₁ K.r₂ = -1 := by simp [edgeSign, not_lt.2 hab.le]
  have ez1 : edgeSign K.z₂ K.z₁ = 1 := by simp [edgeSign, hcd]
  have ez0 : edgeSign K.z₁ K.z₂ = -1 := by simp [edgeSign, not_lt.2 hcd.le]
  have B1 := radial_boundary_term (F := Pf) (D := Dt 0) (D' := fun p => velAt m ι Pg 0 p)
    (w := fun z => (K.r₂ : ℂ) * (starRingEnd ℂ) ((φ 0).eval K (K.r₂, z))) (hVr 0) iRb
    (min_eq_right hab.le) (max_eq_left hab.le)
  have B0 := radial_boundary_term (F := Pf) (D := Dt 0) (D' := fun p => velAt m ι Pg 0 p)
    (w := fun z => (K.r₁ : ℂ) * (starRingEnd ℂ) ((φ 0).eval K (K.r₁, z))) (hVr 0) iRa
    (min_eq_left hab.le) (max_eq_right hab.le)
  have C1 := height_boundary_term (F := Pf) (D := Dt 2) (D' := fun p => velAt m ι Pg 2 p)
    (w := fun r => (r : ℂ) * (starRingEnd ℂ) ((φ 2).eval K (r, K.z₂))) (hVr 2) iZb
    (min_eq_right hcd.le) (max_eq_left hcd.le)
  have C0 := height_boundary_term (F := Pf) (D := Dt 2) (D' := fun p => velAt m ι Pg 2 p)
    (w := fun r => (r : ℂ) * (starRingEnd ℂ) ((φ 2).eval K (r, K.z₁))) (hVr 2) iZa
    (min_eq_left hcd.le) (max_eq_right hcd.le)
  rw [es1] at B1
  rw [es0] at B0
  rw [ez1] at C1
  rw [ez0] at C0
  have hrect : K.rect = Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ := rfl
  rw [hrect]
  have s0 : sideRadius K 0 = K.r₁ := by simp [sideRadius]
  have s1 : sideRadius K 1 = K.r₂ := by simp [sideRadius]
  have o0 : otherRadius K 0 = K.r₂ := by simp [otherRadius]
  have o1 : otherRadius K 1 = K.r₁ := by simp [otherRadius]
  have t0 : sideHeight K 0 = K.z₁ := by simp [sideHeight]
  have t1 : sideHeight K 1 = K.z₂ := by simp [sideHeight]
  have u0 : otherHeight K 0 = K.z₂ := by simp [otherHeight]
  have u1 : otherHeight K 1 = K.z₁ := by simp [otherHeight]
  have g0 : sideSign 0 = -1 := by simp [sideSign]
  have g1 : sideSign 1 = 1 := by simp [sideSign]
  simp only [rowBoundaryPres, labelRowProfile, Fin.sum_univ_two, s0, s1, o0, o1, t0, t1, u0, u1, g0, g1]
  have f1 : ∫ z in Icc K.z₁ K.z₂, (K.r₂ : ℂ) * radialStripTrace K.r₂ K.r₁ (labelPressure m ι Pg)
      (fun p => velAt m ι Pg 0 p) z * (starRingEnd ℂ) ((φ 0).eval K (K.r₂, z)) =
      ∫ z in Icc K.z₁ K.z₂, radialStripTrace K.r₂ K.r₁ Pf (fun p => velAt m ι Pg 0 p) z *
        ((K.r₂ : ℂ) * (starRingEnd ℂ) ((φ 0).eval K (K.r₂, z))) := by
    congr 1; funext z; ring
  have f0 : ∫ z in Icc K.z₁ K.z₂, (K.r₁ : ℂ) * radialStripTrace K.r₁ K.r₂ (labelPressure m ι Pg)
      (fun p => velAt m ι Pg 0 p) z * (starRingEnd ℂ) ((φ 0).eval K (K.r₁, z)) =
      ∫ z in Icc K.z₁ K.z₂, radialStripTrace K.r₁ K.r₂ Pf (fun p => velAt m ι Pg 0 p) z *
        ((K.r₁ : ℂ) * (starRingEnd ℂ) ((φ 0).eval K (K.r₁, z))) := by
    congr 1; funext z; ring
  have k1 : ∫ r in Icc K.r₁ K.r₂, (r : ℂ) * heightStripTrace K.z₂ K.z₁ (labelPressure m ι Pg)
      (fun p => velAt m ι Pg 2 p) r * (starRingEnd ℂ) ((φ 2).eval K (r, K.z₂)) =
      ∫ r in Icc K.r₁ K.r₂, heightStripTrace K.z₂ K.z₁ Pf (fun p => velAt m ι Pg 2 p) r *
        ((r : ℂ) * (starRingEnd ℂ) ((φ 2).eval K (r, K.z₂))) := by
    congr 1; funext r; ring
  have k0 : ∫ r in Icc K.r₁ K.r₂, (r : ℂ) * heightStripTrace K.z₁ K.z₂ (labelPressure m ι Pg)
      (fun p => velAt m ι Pg 2 p) r * (starRingEnd ℂ) ((φ 2).eval K (r, K.z₁)) =
      ∫ r in Icc K.r₁ K.r₂, heightStripTrace K.z₁ K.z₂ Pf (fun p => velAt m ι Pg 2 p) r *
        ((r : ℂ) * (starRingEnd ℂ) ((φ 2).eval K (r, K.z₁))) := by
    congr 1; funext r; ring
  rw [f1, f0, k1, k0, B1, B0, C1, C0]
  ring

end Breakdown.CertCell.CellCalculus
