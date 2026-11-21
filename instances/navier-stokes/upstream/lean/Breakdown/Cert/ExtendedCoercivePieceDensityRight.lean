import Breakdown.Cert.ExtendedCoerciveStatement
import Breakdown.Cert.CoerciveSmoothPieceDensityPairing

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.PieceDensity

open Coercive.Internal.SmoothPieceDensity

private theorem continuous_fderiv_slice_one {W : ℝ → Space → Space}
    (h : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) := by
  have h2 : ContDiff ℝ 1 (Function.uncurry fun (z : ℝ × Space) (y : Space) => W z.1 y) :=
    h.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact (h2.fderiv (g := fun z : ℝ × Space => z.2) contDiff_snd (n := 0) (by norm_num)).continuous

private theorem aesm_smoothRight_one {P : ℝ} {W v : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2)) :
    AEStronglyMeasurable (fun z : ℝ × Space => Coercive.smoothRight P W v z.1 z.2) volume := by
  have cDv := Coercive.Internal.PieceAbsorb.continuous_fderiv_slice hv2
  have cDW := continuous_fderiv_slice_one hW
  have c3 : Continuous fun z : ℝ × Space => fderiv ℝ (v z.1) z.2 (W z.1 z.2) := cDv.clm_apply hW.continuous
  have c4 : Continuous fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2) := cDW.clm_apply hv2.continuous
  have hs : AEStronglyMeasurable (fun z : ℝ × Space => Coercive.transportPart P v z.1 z.2
      - secondDerivTrace (secondDerivField v z.1 z.2) + fderiv ℝ (v z.1) z.2 (W z.1 z.2)
      + fderiv ℝ (W z.1) z.2 (v z.1 z.2)) volume :=
    (((continuous_transportPart P v hv2).aestronglyMeasurable.sub
      (measurable_sumSecondPartials v hv2).aestronglyMeasurable).add c3.aestronglyMeasurable).add c4.aestronglyMeasurable
  have e : (fun z : ℝ × Space => Coercive.smoothRight P W v z.1 z.2) = fun z => Coercive.transportPart P v z.1 z.2
      - secondDerivTrace (secondDerivField v z.1 z.2) + fderiv ℝ (v z.1) z.2 (W z.1 z.2)
      + fderiv ℝ (W z.1) z.2 (v z.1 z.2) := funext fun z => smoothRight_eq P W v z.1 z.2
  rw [e]
  exact hs

theorem right_side_sq {P : ℝ} {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {D : ℝ} {v : ℝ → Space → Space} (hW : IsWeakSecondDerivState W HW D) (hv : Coercive.IsSmoothPerturbation P v) :
    AEStronglyMeasurable (fun z : ℝ × Space => Coercive.smoothRight P W v z.1 z.2) volume ∧
      IsTimePeriodic (Coercive.smoothRight P W v) ∧
      periodLIntegral (fun σ y => ‖Coercive.smoothRight P W v σ y‖ ^ 2) < ⊤ := by
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (WithTop.coe_le_coe.2 le_top)
  refine ⟨aesm_smoothRight_one hW.smooth hv2, periodic_smoothRight P W v hW.periodic hv, ?_⟩
  have hD0 : 0 ≤ D := by
    have := (hW.decay 0 0).1
    simp only [norm_zero, add_zero, div_one] at this
    exact (norm_nonneg _).trans this
  have bW : ∀ σ y, ‖W σ y‖ ≤ D := fun σ y =>
    (hW.decay σ y).1.trans (div_le_self hD0 (by linarith [norm_nonneg y]))
  have bDW : ∀ σ y, ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) ^ 2 := fun σ y => (hW.decay σ y).2.1
  have hL : ∀ σ y, ‖secondDerivTrace (secondDerivField v σ y)‖ ≤ 3 * ‖secondDerivField v σ y‖ := by
    intro σ y
    unfold secondDerivTrace
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j : Fin 3, ‖secondDerivField v σ y (unitVector j) (unitVector j)‖ ≤ ∑ _j : Fin 3, ‖secondDerivField v σ y‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          have a := (secondDerivField v σ y).le_opNorm₂ (unitVector j) (unitVector j)
          rw [Coercive.Internal.PerturbationFacts.norm_unitVector_eq, mul_one, mul_one] at a
          exact a
      _ = 3 * ‖secondDerivField v σ y‖ := by simp
  have hHn : ∀ σ y, ‖secondDerivField v σ y‖ = ‖iteratedFDeriv ℝ 2 (v σ) y‖ := by
    intro σ y
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    rfl
  have hpt := fun σ y => smoothRight_sq_le P W v hD0 bW bDW hL σ y
  refine Coercive.Internal.SmoothWeightSplit.periodLIntegral_lt_top_of_le (by positivity) hpt ?_
  have f0 : periodLIntegral (fun σ y => ‖Coercive.transportPart P v σ y‖ ^ 2) < ⊤ := by
    have := hv.transport_finite 0
    simpa only [norm_iteratedFDeriv_zero] using this
  have f2 : periodLIntegral (fun σ y => ‖secondDerivField v σ y‖ ^ 2) < ⊤ := by
    have := hv.derivatives_finite 2 (by norm_num)
    simpa only [hHn] using this
  have f1 : periodLIntegral (fun σ y => ‖fderiv ℝ (v σ) y‖ ^ 2) < ⊤ := by
    have := hv.derivatives_finite 1 le_rfl
    simpa only [norm_iteratedFDeriv_one] using this
  have fw := hv.weighted_finite
  have mv : Measurable (fun z : ℝ × Space => ‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) := by
    have : Continuous (fun z : ℝ × Space => ‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) :=
      Continuous.div (by fun_prop) (by fun_prop) (fun z => by positivity)
    exact this.measurable
  refine period_add_lt_top (fun σ y => by positivity) (fun σ y => by positivity) ?_
    (period_add_lt_top (fun σ y => by positivity) (fun σ y => by positivity)
      ((Coercive.Internal.PieceAbsorb.measurable_secondDeriv_slice hv2).norm.pow_const 2) f0 f2)
    (period_add_lt_top (fun σ y => by positivity) (fun σ y => by positivity) mv f1 fw)
  exact (((Coercive.Internal.PieceAbsorb.continuous_fderiv_slice hv2).norm.pow 2).measurable).add mv

end Internal.PieceDensity

end CoerciveWeak

end Breakdown
