import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal

theorem formShift_gradCoeff_nonneg (w₀ : ℝ) (b : Bool) : 0 ≤ shiftGradCoeff w₀ b := by
  unfold shiftGradCoeff supBoundFactor
  split <;> positivity

theorem formShift_trace_measurable {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : ∀ j : Fin 3, AEStronglyMeasurable (fun y => (H y).flip (unitVector j)) volume) :
    AEStronglyMeasurable (fun y => secondDerivTrace (H y)) volume := by
  have h : ∀ j : Fin 3,
      AEStronglyMeasurable (fun y => H y (unitVector j) (unitVector j)) volume := by
    intro j
    have h' := (hH j).apply_continuousLinearMap (unitVector j)
    simpa only [ContinuousLinearMap.flip_apply] using h'
  unfold secondDerivTrace
  exact Finset.aestronglyMeasurable_fun_sum _ (fun j _ => h j)

theorem formShift_product_measurable {A : Space → (Space →L[ℝ] Space)} {u t : Space → Space}
    (hA : AEStronglyMeasurable A volume) (hu : AEStronglyMeasurable u volume)
    (ht : AEStronglyMeasurable t volume) :
    AEMeasurable (fun y => ENNReal.ofReal (‖A y (u y)‖ * ‖t y‖)) volume := by
  have happ : AEStronglyMeasurable (fun y => A y (u y)) volume :=
    (ContinuousLinearMap.apply ℝ Space).aestronglyMeasurable_comp₂ hu hA
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (happ.norm.aemeasurable.mul ht.norm.aemeasurable)

end Internal

theorem formShiftBridge_of (hfi : FrozenIntegrandHolds) (hsup : ShiftSupTermHolds)
    (hgrad : ShiftGradTermHolds) (hglue : PeriodGlueHolds) : FormShiftBridgeHolds := by
  obtain ⟨-, -, hpair, -⟩ := hglue
  intro k d r hst hcert q hq σ w G H hw
  have hv := hcert.valid
  have hw₀ : 0 < d.weight := hst.weight_pos
  rw [hst.weightFn_const]
  set E := stationaryEnergy (fun _ => d.weight) G H with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    unfold stationaryEnergy
    exact add_nonneg (integral_nonneg fun _ => sq_nonneg _)
      (integral_nonneg fun _ => mul_nonneg hw₀.le (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  obtain ⟨DP, hDP⟩ := hst.profile_decay q hq
  obtain ⟨HW, DM, hM⟩ := hst.model_state q hq
  have hPs : ContDiff ℝ 1 (d.profile q σ) :=
    (hst.profile_smooth q hq).comp (contDiff_const.prodMk contDiff_id)
  have hMs : ContDiff ℝ 1 (d.model q σ) :=
    hM.smooth.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨hP1, hP2⟩ := hfi d.symmetries DP (d.profile q σ) w G H hPs
    (fun y => (hDP σ y).1) (fun y => (hDP σ y).2) hw
  obtain ⟨hStrain, hM2⟩ := hfi d.symmetries DM (d.model q σ) w G H hMs
    (fun y => (hM.decay σ y).1) (fun y => (hM.decay σ y).2.1) hw
  have hIP : Integrable (fun y => inner ℝ (G y (d.profile q σ y) + fderiv ℝ (d.profile q σ) y (w y))
      (-secondDerivTrace (H y))) := by
    refine (hP1.add hP2).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, inner_add_left]
  have hIM : Integrable (fun y => inner ℝ (G y (d.model q σ y) + fderiv ℝ (d.model q σ) y (w y))
      (-secondDerivTrace (H y))) := by
    refine (hStrain.add hM2).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, inner_add_left]
  have hdiff : frozenForm (d.profile q σ) w G H - frozenForm (d.model q σ) w G H =
      ∫ y, inner ℝ (G y (∑ a, r.piece a q σ y) + (∑ a, r.pieceGrad a q σ y) (w y))
        (-secondDerivTrace (H y)) := by
    unfold frozenForm
    rw [add_sub_add_left_eq_sub, ← integral_sub hIP hIM]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [← hv.decompose q hq σ y, ← hv.decompose_grad q hq σ y, ← inner_sub_left, map_sub,
      sub_apply]
    congr 1
    abel
  have hcoef : ∀ a, 0 ≤ shiftGradCoeff d.weight (r.cubicForm a) * r.gradNum a := fun a =>
    mul_nonneg (Internal.formShift_gradCoeff_nonneg _ _) (hv.gradNum_nonneg a)
  have hsnum : ∀ a, 0 ≤ r.supNum a / (2 * Real.sqrt d.weight) := fun a =>
    div_nonneg (hv.supNum_nonneg a) (by positivity)
  have hS0 : 0 ≤ d.formShift :=
    (Finset.sum_nonneg fun a _ => add_nonneg (hcoef a) (hsnum a)).trans hcert.sum_le
  have hGm : AEStronglyMeasurable G volume := hw.weak_gradient.2.1.aestronglyMeasurable
  have hwm : AEStronglyMeasurable w volume := hw.weak_gradient.1.aestronglyMeasurable
  have hTm : AEStronglyMeasurable (fun y => secondDerivTrace (H y)) volume :=
    Internal.formShift_trace_measurable fun j => (hw.weak_secondDeriv j).2.1.aestronglyMeasurable
  have hpm : ∀ a, StronglyMeasurable (fun y => r.piece a q σ y) := fun a =>
    (hv.piece_measurable a q hq).comp_measurable (measurable_const.prodMk measurable_id)
  have hgm : ∀ a, StronglyMeasurable (fun y => r.pieceGrad a q σ y) := fun a =>
    (hv.pieceGrad_measurable a q hq).comp_measurable (measurable_const.prodMk measurable_id)
  have hlin : (∫⁻ y, ENNReal.ofReal
      (‖G y (∑ a, r.piece a q σ y) + (∑ a, r.pieceGrad a q σ y) (w y)‖ * ‖-secondDerivTrace (H y)‖)) ≤
      ENNReal.ofReal (d.formShift * E) := by
    calc (∫⁻ y, ENNReal.ofReal
          (‖G y (∑ a, r.piece a q σ y) + (∑ a, r.pieceGrad a q σ y) (w y)‖ * ‖-secondDerivTrace (H y)‖))
        ≤ ∫⁻ y, ∑ a, (ENNReal.ofReal (‖G y (r.piece a q σ y)‖ * ‖secondDerivTrace (H y)‖)
            + ENNReal.ofReal (‖r.pieceGrad a q σ y (w y)‖ * ‖secondDerivTrace (H y)‖)) := by
          refine lintegral_mono fun y => ?_
          rw [norm_neg]
          have h1 : ‖G y (∑ a, r.piece a q σ y) + (∑ a, r.pieceGrad a q σ y) (w y)‖ ≤
              ∑ a, (‖G y (r.piece a q σ y)‖ + ‖r.pieceGrad a q σ y (w y)‖) := by
            rw [map_sum, sum_apply, ← Finset.sum_add_distrib]
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_add_le _ _)
          have h2 : ‖G y (∑ a, r.piece a q σ y) + (∑ a, r.pieceGrad a q σ y) (w y)‖
              * ‖secondDerivTrace (H y)‖ ≤ ∑ a, (‖G y (r.piece a q σ y)‖ * ‖secondDerivTrace (H y)‖
                + ‖r.pieceGrad a q σ y (w y)‖ * ‖secondDerivTrace (H y)‖) := by
            refine (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans (le_of_eq ?_)
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun a _ => add_mul _ _ _
          refine (ENNReal.ofReal_le_ofReal h2).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => by positivity)]
          exact Finset.sum_congr rfl fun a _ =>
            ENNReal.ofReal_add (by positivity) (by positivity)
      _ = ∑ a, ((∫⁻ y, ENNReal.ofReal (‖G y (r.piece a q σ y)‖ * ‖secondDerivTrace (H y)‖))
            + ∫⁻ y, ENNReal.ofReal (‖r.pieceGrad a q σ y (w y)‖ * ‖secondDerivTrace (H y)‖)) := by
          have hm : ∀ a ∈ (Finset.univ : Finset (Fin r.count)), AEMeasurable (fun y =>
              ENNReal.ofReal (‖G y (r.piece a q σ y)‖ * ‖secondDerivTrace (H y)‖)
                + ENNReal.ofReal (‖r.pieceGrad a q σ y (w y)‖ * ‖secondDerivTrace (H y)‖)) volume :=
            fun a _ =>
              (Internal.formShift_product_measurable hGm (hpm a).aestronglyMeasurable hTm).add
                (Internal.formShift_product_measurable (hgm a).aestronglyMeasurable hwm hTm)
          rw [lintegral_finsetSum' _ hm]
          exact Finset.sum_congr rfl fun a _ => lintegral_add_left'
            (Internal.formShift_product_measurable hGm (hpm a).aestronglyMeasurable hTm) _
      _ ≤ ∑ a, (ENNReal.ofReal (r.supNum a / (2 * Real.sqrt d.weight) * E)
            + ENNReal.ofReal (shiftGradCoeff d.weight (r.cubicForm a) * r.gradNum a * E)) := by
          refine Finset.sum_le_sum fun a _ => add_le_add ?_ ?_
          · exact hsup d.symmetries d.weight (r.supNum a) w (fun y => r.piece a q σ y) G H hw₀
              (hv.supNum_nonneg a) hw (fun y => hv.piece_sup a q hq σ y)
          · exact hgrad d.symmetries d.weight (r.gradNum a) (r.cubicForm a) w
              (fun y => r.pieceGrad a q σ y) G H hw₀ (hv.gradNum_nonneg a) hw (hgm a)
              (hv.piece_grad a q hq σ)
      _ = ENNReal.ofReal ((∑ a, (shiftGradCoeff d.weight (r.cubicForm a) * r.gradNum a
            + r.supNum a / (2 * Real.sqrt d.weight))) * E) := by
          rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg
            (fun a _ => mul_nonneg (add_nonneg (hcoef a) (hsnum a)) hE0)]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [add_mul, ENNReal.ofReal_add (mul_nonneg (hcoef a) hE0) (mul_nonneg (hsnum a) hE0),
            add_comm]
      _ ≤ ENNReal.ofReal (d.formShift * E) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcert.sum_le hE0)
  have hb := hpair (fun y => G y (∑ a, r.piece a q σ y) + (∑ a, r.pieceGrad a q σ y) (w y))
    (fun y => -secondDerivTrace (H y)) (d.formShift * E) (mul_nonneg hS0 hE0) hlin
  rw [hdiff, neg_mul]
  exact (abs_le.mp hb).1

end CertReduction

end Breakdown
