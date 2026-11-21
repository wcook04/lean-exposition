import Breakdown.Cert.CoerciveSmoothEpsMeasurable
import Breakdown.Cert.CoerciveSmoothEpsSummable
import Breakdown.Cert.CoerciveSmoothEpsTail
import Breakdown.Cert.CoerciveSmoothEpsPointwise
import Breakdown.Cert.CoerciveSmoothEpsSumSecondPartials
import Breakdown.Cert.CoerciveSmoothEpsIntegrable

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEpsInternal

theorem ofReal_bound_of_le {p T r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (h : p ≤ T + r) :
    ENNReal.ofReal p + ENNReal.ofReal (-T) ≤ ENNReal.ofReal T + ENNReal.ofReal r := by
  rcases le_total 0 T with hT | hT
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -T ≤ 0), add_zero, ← ENNReal.ofReal_add hT hr]
    exact ENNReal.ofReal_le_ofReal h
  · rw [ENNReal.ofReal_of_nonpos hT, zero_add, ← ENNReal.ofReal_add hp (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

theorem lintegral_slab_eq {F : ℝ → Space → ℝ≥0∞} (hF : AEMeasurable (fun z : ℝ × Space => F z.1 z.2) slabMeasure) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, F σ y) = ∫⁻ z, F z.1 z.2 ∂slabMeasure :=
  (lintegral_prod (fun z : ℝ × Space => F z.1 z.2) hF).symm

theorem integral_slab_eq {F : ℝ → Space → ℝ} (hF : Integrable (fun z : ℝ × Space => F z.1 z.2) slabMeasure) :
    (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, F σ y) = ∫ z, F z.1 z.2 ∂slabMeasure :=
  (integral_prod (fun z : ℝ × Space => F z.1 z.2) hF).symm

theorem epsMode_bound (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) (ι : ℤ × ℤ) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (modeEpsPos m P (gradField v) ι σ y))
        + ENNReal.ofReal (-epsModeTerm m v (smoothRight P W v) ι)
      ≤ ENNReal.ofReal (epsModeTerm m v (smoothRight P W v) ι)
        + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          ENNReal.ofReal (-modeEpsRest m W v (gradField v) (secondDerivField v) ι σ y) := by
  have hPm : AEMeasurable (fun z : ℝ × Space => modeEpsPos m P (gradField v) ι z.1 z.2) slabMeasure :=
    aemeasurable_modeEpsPos hS ι
  have hRm : AEMeasurable (fun z : ℝ × Space => modeEpsRest m W v (gradField v) (secondDerivField v) ι z.1 z.2)
      slabMeasure := aemeasurable_modeEpsRest hS ι
  obtain ⟨hI, hL, hE⟩ := integrable_epsTerms hPars hSP hS ι
  have hT : epsModeTerm m v (smoothRight P W v) ι =
      ∫ z, epsIntegrand m v (smoothRight P W v) ι z.1 z.2 ∂slabMeasure :=
    integral_slab_eq (F := fun σ y => epsIntegrand m v (smoothRight P W v) ι σ y) hI
  have hLE0 := integral_slab_eq (F := fun σ y => epsIntegrand m v (negSumSecondPartialsOfField v) ι σ y + epsGradTerm m v ι σ y)
    (hL.add hE)
  rw [lintegral_slab_eq (F := fun σ y => ENNReal.ofReal (modeEpsPos m P (gradField v) ι σ y))
      hPm.ennreal_ofReal,
    lintegral_slab_eq (F := fun σ y => ENNReal.ofReal (-modeEpsRest m W v (gradField v) (secondDerivField v) ι σ y))
      hRm.neg.ennreal_ofReal, hT]
  have hPer : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      0 ≤ ∫ y, (epsIntegrand m v (negSumSecondPartialsOfField v) ι σ y + epsGradTerm m v ι σ y) := by
    filter_upwards [hL.prod_right_ae, hE.prod_right_ae] with σ h1 h2
    rw [integral_add h1 h2]
    have := epsSumSecondPartials_lower hSsp hS ι σ
    linarith
  have hLE : 0 ≤ ∫ z, (epsIntegrand m v (negSumSecondPartialsOfField v) ι z.1 z.2 + epsGradTerm m v ι z.1 z.2) ∂slabMeasure := by
    rw [← hLE0]
    exact integral_nonneg_of_ae hPer
  set Ps : ℝ × Space → ℝ := fun z => modeEpsPos m P (gradField v) ι z.1 z.2 with hPs
  set Rs : ℝ × Space → ℝ := fun z => modeEpsRest m W v (gradField v) (secondDerivField v) ι z.1 z.2 with hRs
  set Is : ℝ × Space → ℝ := fun z => epsIntegrand m v (smoothRight P W v) ι z.1 z.2 with hIs
  set Ls : ℝ × Space → ℝ := fun z => epsIntegrand m v (negSumSecondPartialsOfField v) ι z.1 z.2 with hLs
  set Es : ℝ × Space → ℝ := fun z => epsGradTerm m v ι z.1 z.2 with hEs
  by_cases hB : (∫⁻ z, ENNReal.ofReal (-Rs z) ∂slabMeasure) = ⊤
  · rw [hB]
    simp
  have hRi : Integrable (fun z => -Rs z) slabMeasure :=
    (lintegral_ofReal_ne_top_iff_integrable hRm.neg.aestronglyMeasurable
      (ae_of_all _ fun z => neg_nonneg.mpr (modeEpsRest_nonpos m W v _ _ ι z.1 z.2))).1 hB
  have h1 : Integrable (fun z => Is z + -Rs z) slabMeasure := hI.add hRi
  have h2 : Integrable (fun z => Is z + -Rs z - Es z) slabMeasure := h1.sub hE
  have hg : Integrable (fun z => Is z + -Rs z - Es z - Ls z) slabMeasure := h2.sub hL
  have hPle : ∀ z, Ps z ≤ Is z + -Rs z - Es z - Ls z := fun z => by
    have := epsIntegrand_lower hS ι z.1 z.2
    simp only [hPs, hRs, hIs, hEs, hLs]
    linarith
  have hPi : Integrable Ps slabMeasure :=
    hg.mono' hPm.aestronglyMeasurable (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (modeEpsPos_nonneg m P _ ι z.1 z.2)]
      exact hPle z)
  have hmono : ∫ z, Ps z ∂slabMeasure ≤ ∫ z, (Is z + -Rs z - Es z - Ls z) ∂slabMeasure :=
    integral_mono hPi hg hPle
  have e1 := integral_sub h2 hL
  have e2 := integral_sub h1 hE
  have e3 := integral_add hI hRi
  have e4 := integral_add hL hE
  rw [← ofReal_integral_eq_lintegral_ofReal hPi (ae_of_all _ fun z => modeEpsPos_nonneg m P _ ι z.1 z.2),
    ← ofReal_integral_eq_lintegral_ofReal hRi
      (ae_of_all _ fun z => neg_nonneg.mpr (modeEpsRest_nonpos m W v _ _ ι z.1 z.2))]
  exact ofReal_bound_of_le (integral_nonneg fun z => modeEpsPos_nonneg m P _ ι z.1 z.2)
    (integral_nonneg fun z => neg_nonneg.mpr (modeEpsRest_nonpos m W v _ _ ι z.1 z.2)) (by linarith)

end SmoothEpsInternal

open SmoothEpsInternal in
theorem modeEpsEstimateSmoothHolds_of (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hSsp : WeightedSumSecondPartialsPairingHolds) :
    ModeEpsEstimateSmoothHolds := by
  intro C m P b w W w₀ epsSup epsGradSup ratio hm hb hW hWp hWdiv hWdecay hwb v hv
  have hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v := ⟨hm, hb, hW, hWp, hWdiv, hWdecay, hwb, hv⟩
  rw [epsPairing_eq_tsum]
  exact isSplitLowerBound_of_modes (fun σ y ι => modeEpsRest_nonpos m W v _ _ ι σ y)
    (aemeasurable_modeEpsPos hS) (aemeasurable_modeEpsRest hS) (summable_epsModeTerm hPars hSP hS)
    (lintegral_negRest_lt_top hPars hSP hS) (epsMode_bound hPars hSP hSsp hS)

end Coercive

end Breakdown
