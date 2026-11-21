import Breakdown.CertCell.ShapeScalarStatements
import Breakdown.CertCell.InstanceBasic

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace ScalarShape

open CellCert.GivenFields (ChartParams chartT heightRatio)
open Instance (StepDatum)
open Instance.BasicFactsInternal (flipPoint_third flipPoint_norm_eq axialRot_third axialRot_norm_eq
  chartT_axialRot heightRatio_axialRot chartT_flipPoint heightRatio_flipPoint chartT_measurable values_measurable)

namespace Internal.PlaneMin

theorem upperValue_measurable (P : ChartParams) (S : StepDatum) :
    Measurable (fun y : Space => StepDatum.upperValue P S y) := by
  have h := values_measurable P S.mesh S.upper 1
  simp only [one_mul] at h
  exact h

theorem lowerValue_measurable (P : ChartParams) (S : StepDatum) :
    Measurable (fun y : Space => StepDatum.lowerValue P S y) := by
  have h := values_measurable P S.mesh S.lower (-1)
  simp only [neg_one_mul] at h
  exact h

theorem upperValue_axialRot (P : ChartParams) (S : StepDatum) (φ : ℝ) (y : Space) :
    StepDatum.upperValue P S (axialRot φ y) = StepDatum.upperValue P S y := by
  simp only [StepDatum.upperValue, chartT_axialRot, heightRatio_axialRot]

theorem lowerValue_axialRot (P : ChartParams) (S : StepDatum) (φ : ℝ) (y : Space) :
    StepDatum.lowerValue P S (axialRot φ y) = StepDatum.lowerValue P S y := by
  simp only [StepDatum.lowerValue, chartT_axialRot, heightRatio_axialRot]

theorem mirror_upperValue_flip (P : ChartParams) (S : StepDatum) (y : Space) :
    StepDatum.upperValue P S.mirror (flipPoint y) = StepDatum.lowerValue P S y := by
  simp only [StepDatum.upperValue, StepDatum.lowerValue, StepDatum.mirror, chartT_flipPoint,
    heightRatio_flipPoint]

theorem mirror_lowerValue_flip (P : ChartParams) (S : StepDatum) (y : Space) :
    StepDatum.lowerValue P S.mirror (flipPoint y) = StepDatum.upperValue P S y := by
  simp only [StepDatum.upperValue, StepDatum.lowerValue, StepDatum.mirror, chartT_flipPoint,
    heightRatio_flipPoint, neg_neg]

theorem planeMinEval_measurable (P : ChartParams) (S : StepDatum) : Measurable (planeMinEval P S) := by
  have hd : Measurable (fun y : Space => (1 - chartT P y) ^ S.decay) :=
    (measurable_const.sub (chartT_measurable P)).pow_const _
  have h2 : Measurable (fun y : Space => y 2) := by fun_prop
  have hz : MeasurableSet {y : Space | y 2 = 0} := measurableSet_eq_fun h2 measurable_const
  have hp : MeasurableSet {y : Space | 0 < y 2} := measurableSet_lt measurable_const h2
  exact hd.mul (Measurable.ite hz ((upperValue_measurable P S).min (lowerValue_measurable P S))
    (Measurable.ite hp (upperValue_measurable P S) (lowerValue_measurable P S)))

theorem planeMinEval_axialRot (P : ChartParams) (S : StepDatum) (φ : ℝ) (y : Space) :
    planeMinEval P S (axialRot φ y) = planeMinEval P S y := by
  simp only [planeMinEval, chartT_axialRot, axialRot_third, upperValue_axialRot, lowerValue_axialRot]

theorem planeMinEval_flip (P : ChartParams) (S : StepDatum) (y : Space) :
    planeMinEval P S.mirror (flipPoint y) = planeMinEval P S y := by
  have hd : S.mirror.decay = S.decay := rfl
  unfold planeMinEval
  rw [hd, chartT_flipPoint, flipPoint_third, mirror_upperValue_flip, mirror_lowerValue_flip]
  congr 1
  rcases lt_trichotomy (y 2) 0 with h | h | h
  · rw [if_neg (neg_ne_zero.mpr h.ne), if_pos (neg_pos.mpr h), if_neg h.ne, if_neg (not_lt.mpr h.le)]
  · rw [if_pos (by rw [h, neg_zero]), if_pos h, min_comm]
  · rw [if_neg (neg_ne_zero.mpr h.ne'), if_neg (not_lt.mpr (neg_nonpos.mpr h.le)), if_neg h.ne', if_pos h]

theorem axialRot_eq_zero_iff (φ : ℝ) (y : Space) : axialRot φ y = 0 ↔ y = 0 := by
  rw [← norm_eq_zero, axialRot_norm_eq, norm_eq_zero]

theorem flipPoint_eq_zero_iff (y : Space) : flipPoint y = 0 ↔ y = 0 := by
  rw [← norm_eq_zero, flipPoint_norm_eq, norm_eq_zero]

end Internal.PlaneMin

open Internal.PlaneMin

theorem planeMinEvalFacts : PlaneMinEvalFacts := fun P S =>
  ⟨planeMinEval_measurable P S, fun φ y => planeMinEval_axialRot P S φ y, fun y => planeMinEval_flip P S y⟩

theorem chartBoundFacts : ChartBoundFacts := by
  intro P B
  refine ⟨?_, ?_, ?_⟩
  · have hz : MeasurableSet {y : Space | y = 0} := measurableSet_singleton 0
    exact Measurable.ite hz measurable_const
      (((chartT_measurable P).pow_const _).mul (planeMinEval_measurable P B.data))
  · intro φ y
    simp only [ChartBound.eval, axialRot_eq_zero_iff, chartT_axialRot, planeMinEval_axialRot]
  · intro y
    have hd : B.mirror.data = B.data.mirror := rfl
    have ht : B.mirror.tPower = B.tPower := rfl
    have ho : B.mirror.originValue = B.originValue := rfl
    simp only [ChartBound.eval, flipPoint_eq_zero_iff, chartT_flipPoint, hd, ht, ho, planeMinEval_flip]

end ScalarShape

end CertCell

end Breakdown
