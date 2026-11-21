import Breakdown.CertTorus.Defs
import Breakdown.Defs
import Breakdown.Weak.Main
import Breakdown.Torus.Main

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

open Freq

theorem isRegularOrbitField_of_smooth {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {P : ℝ}
    {R : Space ≃ₗᵢ[ℝ] Space} (h : IsSmoothOrbitField W q P R) (hI : ∀ s y, W s y = profileBilin W W s y) :
    IsRegularOrbitField W q P R :=
  { h with integral_eq := hI }

theorem periodicLerayProfileExists_of_regular {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {P : ℝ}
    {R : Space ≃ₗᵢ[ℝ] Space} {C : ℝ} (h : IsRegularOrbitField W q P R) (hC : DecayBounds W q C) :
    PeriodicSimilarityProfileExists :=
  ⟨W, q, P, R, C, h.period_pos, h.smooth_field, h.smooth_pressure, h.residual, h.divergence, h.periodic,
    h.nonzero, fun s y j hj => hC.1 s y j hj, hC.2⟩

theorem periodicLerayProfileExists_of_orbit (hA : SmoothFieldOfOrbit) (hK : IntegralEquationOfOrbit)
    (hB : FarFieldDecay)
    (h : ∃ (w : ℝ → X) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space), realization.F.IsOrbit (realization.rot R) w P) :
    PeriodicSimilarityProfileExists := by
  obtain ⟨w, P, R, hw⟩ := h
  obtain ⟨W, q, hS, hV⟩ := hA w P R hw
  have hR := isRegularOrbitField_of_smooth hS (hK w P R W q hw hS hV)
  obtain ⟨C, hC⟩ := hB W q P R hR
  exact periodicLerayProfileExists_of_regular hR hC

theorem periodicLerayProfileExists_of_weak_of_parts (hA : SmoothFieldOfOrbit)
    (hK : IntegralEquationOfOrbit) (hB : FarFieldDecay) :
    WeakPeriodicSimilarityProfileExists → PeriodicSimilarityProfileExists := fun h =>
  periodicLerayProfileExists_of_orbit hA hK hB
    (WeakProfile.weakOrbitOfParts_holds WeakProfile.pairingVelocity_holds
      WeakProfile.velocityWeakGradient_holds WeakProfile.zeroGradientSix_holds
      WeakProfile.gradientFreqTr_holds WeakProfile.sliceEmbedding_holds
      WeakProfile.advectionByParts_holds WeakProfile.pairingDilate_holds
      WeakProfile.trilinearDilate_holds WeakProfile.sliceMeasurable_holds
      WeakProfile.scaledTestField_holds WeakProfile.sliceIntegrand_holds
      WeakProfile.similarityIdentity_holds
      (WeakProfile.physicalIdentity_of_parts WeakProfile.pairingVelocity_holds
        WeakProfile.velocityWeakGradient_holds)
      WeakProfile.constOfWeakDeriv_holds WeakProfile.goodTimes_holds WeakProfile.bilinIntegrable_holds
      WeakProfile.varConstInner_holds WeakProfile.varConstGood_holds WeakProfile.continuousVarConst_holds
      WeakProfile.mildFromGood_holds WeakProfile.globalRepresentative_holds
      WeakProfile.timeChangeNull_holds WeakProfile.physicalCurveMeasurable_holds h)

theorem breakdownOnTorus_of_weak_of_parts (hA : SmoothFieldOfOrbit) (hK : IntegralEquationOfOrbit)
    (hB : FarFieldDecay) : WeakPeriodicSimilarityProfileExists → BreakdownOnTorus := fun h =>
  Periodic.breakdownOnTorus_of_profile (periodicLerayProfileExists_of_weak_of_parts hA hK hB h)

end Breakdown.FarField
