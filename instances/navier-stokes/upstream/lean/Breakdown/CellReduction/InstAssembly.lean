import Breakdown.CellReduction.InstanceStatements
import Breakdown.CertCell.CellLayerClosed
import Breakdown.CellReduction.InstMovedParams
import Breakdown.CellReduction.InstAffineStructure
import Breakdown.CellReduction.InstAffineWeak
import Breakdown.CellReduction.InstAffineInvariant
import Breakdown.CellReduction.InstParamsBounded
import Breakdown.CellReduction.InstScalarGradient

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal

theorem slopeBound_of_bound {f : Space → ℝ} {s : Set Space} {L : ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ L * ‖x - y‖) : ∃ K : NNReal, LipschitzOnWith K f s :=
  ⟨_, LipschitzOnWith.of_dist_le' fun x hx y hy => by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using h x hx y hy⟩

theorem realBound_of_slopeBound {f : Space → ℝ} {s : Set Space} {K : NNReal} (h : LipschitzOnWith K f s) :
    ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ K * ‖x - y‖ := fun x hx y hy => by
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using h.dist_le_mul x hx y hy

theorem bound_sum {ι : Type*} (t : Finset ι) (f : ι → Space → ℝ) {s : Set Space} (L : ι → ℝ)
    (h : ∀ i ∈ t, ∀ x ∈ s, ∀ y ∈ s, |f i x - f i y| ≤ L i * ‖x - y‖) :
    ∀ x ∈ s, ∀ y ∈ s, |∑ i ∈ t, f i x - ∑ i ∈ t, f i y| ≤ (∑ i ∈ t, L i) * ‖x - y‖ := by
  intro x hx y hy
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => h i hi x hx y hy)

theorem bound_const_mul (c : ℝ) {f : Space → ℝ} {s : Set Space} {L : ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ L * ‖x - y‖) :
    ∀ x ∈ s, ∀ y ∈ s, |c * f x - c * f y| ≤ (|c| * L) * ‖x - y‖ := by
  intro x hx y hy
  rw [← mul_sub, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x hx y hy) (abs_nonneg c)

theorem paramsAt_valid {k : ℕ} (R : ProfileShapeEntry k) (hmoved : MovedParamsValidHolds)
    (hP : IsShapeParams R.params) (hm : IsRadialPhase R.moving) (q : Fin k → ℝ) :
    IsShapeParams (R.paramsAt q) :=
  hmoved R.params R.moving (phaseRate R.rate q) hP hm

theorem pressure_regular {k : ℕ} (R : ProfileShapeEntry k) (Pr : PressureShapeEntry k)
    (hpreg : PressureFieldRegularHolds) (q : Fin k → ℝ) (hPq : IsShapeParams (R.paramsAt q))
    (hc : IsPressureFieldData Pr.centre) (ht : ∀ i, IsPressureFieldData (Pr.tangent i)) :
    Continuous (fun z : ℝ × Space => Pr.pressure R q z.1 z.2) ∧
    (∀ σ y, Pr.pressure R q (σ + 1) y = Pr.pressure R q σ y) ∧
    ∀ r : ℝ, ∃ L : ℝ, ∀ σ, ∀ x ∈ Metric.closedBall (0 : Space) r, ∀ y ∈ Metric.closedBall (0 : Space) r,
      |Pr.pressure R q σ x - Pr.pressure R q σ y| ≤ L * ‖x - y‖ := by
  obtain ⟨c0, p0, l0⟩ := hpreg _ _ hPq hc
  have hi := fun i => hpreg _ _ hPq (ht i)
  refine ⟨?_, ?_, ?_⟩
  · exact c0.add (continuous_finsetSum _ fun i _ => continuous_const.mul (hi i).1)
  · intro σ y
    simp only [PressureShapeEntry.pressure, p0 σ y, fun i => (hi i).2.1 σ y]
  · intro r
    obtain ⟨L0, hL0⟩ := l0 r
    choose Li hLi using fun i => (hi i).2.2 r
    refine ⟨L0 + ∑ i, |q i| * Li i, fun σ x hx y hy => ?_⟩
    have b0 := realBound_of_slopeBound (hL0 σ) x hx y hy
    have bs := bound_sum Finset.univ
      (fun i y' => q i * shapePressure (R.paramsAt q) (Pr.tangent i) σ y') (fun i => |q i| * Li i)
      (fun i _ => bound_const_mul (q i) (realBound_of_slopeBound (hLi i σ))) x hx y hy
    simp only [PressureShapeEntry.pressure]
    rw [show shapePressure (R.paramsAt q) Pr.centre σ x + ∑ i, q i * shapePressure (R.paramsAt q) (Pr.tangent i) σ x
        - (shapePressure (R.paramsAt q) Pr.centre σ y + ∑ i, q i * shapePressure (R.paramsAt q) (Pr.tangent i) σ y)
        = (shapePressure (R.paramsAt q) Pr.centre σ x - shapePressure (R.paramsAt q) Pr.centre σ y)
          + ((∑ i, q i * shapePressure (R.paramsAt q) (Pr.tangent i) σ x)
            - ∑ i, q i * shapePressure (R.paramsAt q) (Pr.tangent i) σ y) by ring]
    calc _ ≤ |shapePressure (R.paramsAt q) Pr.centre σ x - shapePressure (R.paramsAt q) Pr.centre σ y|
          + |(∑ i, q i * shapePressure (R.paramsAt q) (Pr.tangent i) σ x)
            - ∑ i, q i * shapePressure (R.paramsAt q) (Pr.tangent i) σ y| := abs_add_le _ _
      _ ≤ (L0 + ∑ i, |q i| * Li i) * ‖x - y‖ := by rw [add_mul]; exact add_le_add b0 bs

theorem kinetic_bound (W : Space → Space) (hW : ContDiff ℝ 1 W) (r : ℝ) :
    ∃ L : ℝ, ∀ x ∈ Metric.closedBall (0 : Space) r, ∀ y ∈ Metric.closedBall (0 : Space) r,
      |‖W x‖ ^ 2 / 2 - ‖W y‖ ^ 2 / 2| ≤ L * ‖x - y‖ := by
  have hg : ContDiff ℝ 1 (fun y => ‖W y‖ ^ 2 / 2) := (hW.norm_sq ℝ).div_const 2
  obtain ⟨K, hK⟩ := hg.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall 0 r)
    (isCompact_closedBall 0 r)
  exact ⟨K, realBound_of_slopeBound hK⟩

end Internal

theorem instantiation_holds_of (hmoved : MovedParamsValidHolds) (hstep : StepPhaseHolds)
    (hstruct : AffineFieldStructureHolds) (hweak : AffineFieldWeakSecondDerivHolds)
    (hinv : AffineFieldInvariantHolds) (hsmooth : MovedFieldJointSmoothHolds)
    (hdecay : MovedFieldUniformDecayHolds) (hbound : ParamsBoundedHolds)
    (hpin : PinValueContinuousHolds) (hpreg : PressureFieldRegularHolds)
    (hpgrad : ScalarGradientOrthogonalHolds) : InstantiationHolds := by
  intro k C nE nM D R Pr Z hgen hscale hpinm hpinl hcert
  obtain ⟨hR, hPr, hZ⟩ := hcert
  have hm : IsRadialPhase R.moving :=
    (hstep R.params.chartLength R.stepEdge R.step hR.params_valid.chartLength_pos hR.step_valid).1
  have hPq : ∀ q, IsShapeParams (R.paramsAt q) := Internal.paramsAt_valid R hmoved hR.params_valid hm
  have hWeq : D.cert.profile = R.field := funext hR.profile_eq
  have hHeq : D.cert.profileSecondDeriv = R.secondDeriv := funext hR.profileSecondDeriv_eq
  have hst := fun q => hstruct (R.paramsAt q) R.centreOrigin R.centre R.tangentOrigin R.tangent q (hPq q)
    hR.centreOrigin_valid hR.tangentOrigin_valid hR.centre_valid hR.tangent_valid
  have hsm : ContDiff ℝ 1 (fun z : (Fin k → ℝ) × ℝ × Space => D.cert.profile z.1 z.2.1 z.2.2) := by
    rw [hWeq]
    exact hsmooth R.params R.moving R.rate R.centreOrigin R.centre R.tangentOrigin R.tangent hR.params_valid hm
      hR.centreOrigin_valid hR.tangentOrigin_valid hR.centre_valid hR.tangent_valid
  obtain ⟨M, hM⟩ := hbound D.cert hscale
  obtain ⟨B, hB⟩ := hdecay R.params R.moving R.rate R.centreOrigin R.centre R.tangentOrigin R.tangent M
    hR.params_valid hm hR.centreOrigin_valid hR.tangentOrigin_valid hR.centre_valid hR.tangent_valid
  have hdec : ∀ q ∈ D.cert.params, ∀ σ y, ‖D.cert.profile q σ y‖ ≤ B / (1 + ‖y‖) ∧
      ‖fderiv ℝ (D.cert.profile q σ) y‖ ≤ B / (1 + ‖y‖) ^ 2 ∧
      ‖D.cert.profileSecondDeriv q σ y‖ ≤ B / (1 + ‖y‖) ^ 3 := by
    intro q hq σ y
    rw [hWeq, hHeq]
    exact hB q (hM q hq) σ y
  have hWq : ∀ q, ContDiff ℝ 1 (fun z : ℝ × Space => D.cert.profile q z.1 z.2) := fun q =>
    hsm.comp (contDiff_const.prodMk contDiff_id)
  have hWqσ : ∀ q σ, ContDiff ℝ 1 (fun y => D.cert.profile q σ y) := fun q σ =>
    (hWq q).comp (contDiff_const.prodMk contDiff_id)
  have htarget : ContinuousOn D.cert.target D.cert.params := by
    have ht : D.cert.target = fun q i => pinValue (D.cert.pin i) (fun σ y => fderiv ℝ (D.cert.profile q σ) y) := by
      funext q i
      exact hR.target_eq q i
    rw [ht]
    exact continuousOn_pi.2 fun i => hpin D.cert.profile (D.cert.pin i) D.cert.params B hsm
      (fun q hq σ y => (hdec q hq σ y).2.1) (hpinm i) (hpinl i)
  have hpress : ∀ q, AEStronglyMeasurable (fun z : ℝ × Space => D.cert.pressureGrad q z.1 z.2) volume ∧
      IsTimePeriodic (D.cert.pressureGrad q) ∧ ∀ φ, IsSpaceTimeTestField φ →
        ∫ z : ℝ × Space, inner ℝ (D.cert.pressureGrad q z.1 z.2) (φ z.1 z.2) = 0 := by
    intro q
    obtain ⟨pc, pp, pl⟩ := Internal.pressure_regular R Pr hpreg q (hPq q) hPr.centre_valid hPr.tangent_valid
    have hPG : D.cert.pressureGrad q = fun σ y =>
        gradient (fun y' => Pr.pressure R q σ y' - ‖D.cert.profile q σ y'‖ ^ 2 / 2) y := by
      funext σ y
      exact hPr.pressureGrad_eq q σ y
    have hcont : Continuous (fun z : ℝ × Space => Pr.pressure R q z.1 z.2 - ‖D.cert.profile q z.1 z.2‖ ^ 2 / 2) :=
      pc.sub (((hWq q).continuous.norm.pow 2).div_const 2)
    have hslope : ∀ σ, ∀ r : ℝ, ∃ L : NNReal, LipschitzOnWith L
        (fun y' => Pr.pressure R q σ y' - ‖D.cert.profile q σ y'‖ ^ 2 / 2) (Metric.closedBall 0 r) := by
      intro σ r
      obtain ⟨L1, h1⟩ := pl r
      obtain ⟨L3, h3⟩ := Internal.kinetic_bound (D.cert.profile q σ) (hWqσ q σ) r
      refine Internal.slopeBound_of_bound (L := L1 + L3) fun x hx y hy => ?_
      have b1 := h1 σ x hx y hy
      have b3 := h3 x hx y hy
      rw [show Pr.pressure R q σ x - ‖D.cert.profile q σ x‖ ^ 2 / 2
          - (Pr.pressure R q σ y - ‖D.cert.profile q σ y‖ ^ 2 / 2)
          = (Pr.pressure R q σ x - Pr.pressure R q σ y)
            - (‖D.cert.profile q σ x‖ ^ 2 / 2 - ‖D.cert.profile q σ y‖ ^ 2 / 2) by ring]
      calc _ ≤ |Pr.pressure R q σ x - Pr.pressure R q σ y|
            + |‖D.cert.profile q σ x‖ ^ 2 / 2 - ‖D.cert.profile q σ y‖ ^ 2 / 2| := abs_sub _ _
        _ ≤ (L1 + L3) * ‖x - y‖ := by rw [add_mul]; exact add_le_add b1 b3
    obtain ⟨hmeas, horth⟩ := hpgrad _ hcont hslope
    refine ⟨?_, ?_, ?_⟩
    · rw [hPG]
      exact hmeas
    · intro σ y
      rw [hPG]
      have hper : (fun y' => Pr.pressure R q (σ + 1) y' - ‖D.cert.profile q (σ + 1) y'‖ ^ 2 / 2) =
          fun y' => Pr.pressure R q σ y' - ‖D.cert.profile q σ y'‖ ^ 2 / 2 := by
        funext y'
        rw [pp σ y', hWeq, show R.field q (σ + 1) y' = R.field q σ y' from (hst q).1 σ y']
      simp only [hper]
    · rw [hPG]
      exact horth
  refine ⟨B, ?_⟩
  exact
    { target_continuous := htarget
      profile_smooth := hsm
      profile_periodic := fun q => by rw [hWeq]; exact (hst q).1
      profile_divergence := fun q _ σ y => by rw [hWeq]; exact (hst q).2.1 σ y
      profile_decay := hdec
      profileSecondDeriv_measurable := fun q _ => by rw [hHeq]; exact (hst q).2.2.1
      profileSecondDeriv_periodic := fun q _ => by rw [hHeq]; exact (hst q).2.2.2
      profileSecondDeriv_weak := fun q _ σ j => by
        rw [hWeq, hHeq]
        exact hweak (R.paramsAt q) R.centreOrigin R.centre R.tangentOrigin R.tangent q (hPq q)
          hR.centreOrigin_valid hR.tangentOrigin_valid hR.centre_valid hR.tangent_valid σ j
      profile_invariant := fun q _ γ hγ σ y => by
        rw [hWeq]
        exact hinv D (R.paramsAt q) R.centreOrigin R.centre R.tangentOrigin R.tangent q hgen hR.azimuth_eq (hPq q)
          hR.centreOrigin_valid hR.tangentOrigin_valid hR.centre_valid hR.tangent_valid γ hγ σ y
      pressureGrad_measurable := fun q _ => (hpress q).1
      pressureGrad_periodic := fun q _ => (hpress q).2.1
      pressureGrad_orthogonal := fun q _ => (hpress q).2.2
      adjoint_measurable := fun j hj q _ => by
        rw [hZ.adjoint_eq j hj q]
        exact (shapeParts_closed.field_smooth _ _ hZ.params_valid (hZ.field_valid j hj)).1.continuous.aestronglyMeasurable
      adjoint_periodic := fun j hj q _ => by
        rw [hZ.adjoint_eq j hj q]
        exact (shapeParts_closed.field_smooth _ _ hZ.params_valid (hZ.field_valid j hj)).2.1 }

theorem instantiation_holds_of_open (hstep : StepPhaseHolds) (hsmooth : MovedFieldJointSmoothHolds)
    (hdecay : MovedFieldUniformDecayHolds) (hpin : PinValueContinuousHolds)
    (hpreg : PressureFieldRegularHolds) : InstantiationHolds :=
  instantiation_holds_of movedParamsValid_holds hstep affineFieldStructure_holds affineFieldWeakSecondDeriv_holds
    affineFieldInvariant_holds hsmooth hdecay paramsBounded_holds hpin hpreg scalarGradientOrthogonal_holds

end Instantiation

end CellReduction

end Breakdown
