import Breakdown.FracCell.StClauses

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

open SteadyCert

namespace ModelPinInternal

theorem entrySq_nonneg (A : Space →L[ℝ] Space) : 0 ≤ entrySq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem entrySq_continuous : Continuous entrySq :=
  continuous_finsetSum _ fun i _ => ((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.norm.pow 2)

theorem entrySq_sub_comm (A B : Space →L[ℝ] Space) : entrySq (A - B) = entrySq (B - A) := by
  simp only [entrySq, ContinuousLinearMap.sub_apply, norm_sub_rev]

theorem entrySq_sub_le (A B : Space →L[ℝ] Space) : entrySq (A - B) ≤ 2 * entrySq A + 2 * entrySq B := by
  unfold entrySq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ContinuousLinearMap.sub_apply]
  have h := norm_sub_le (A (unitVector i)) (B (unitVector i))
  nlinarith [norm_nonneg (A (unitVector i) - B (unitVector i)), norm_nonneg (A (unitVector i)),
    norm_nonneg (B (unitVector i)), sq_nonneg (‖A (unitVector i)‖ - ‖B (unitVector i)‖)]

theorem entrySq_expand (x : ℝ) (A B : Space →L[ℝ] Space) :
    entrySq (x • A + B) = x ^ 2 * entrySq A + 2 * x * entryInner A B + entrySq B := by
  unfold entrySq entryInner
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, norm_add_sq_real, norm_smul,
    real_inner_smul_left, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem integrable_entryInner {G K : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (hK : AEStronglyMeasurable K volume) (hG2 : Integrable fun y => entrySq (G y))
    (hK2 : Integrable fun y => entrySq (K y)) : Integrable fun y => entryInner (G y) (K y) := by
  unfold entryInner
  refine integrable_finsetSum _ fun i _ => ?_
  refine Integrable.mono' (hG2.add hK2)
    ((hG.apply_continuousLinearMap _).inner (hK.apply_continuousLinearMap _))
    (Filter.Eventually.of_forall fun y => ?_)
  have a1 : ‖G y (unitVector i)‖ ^ 2 ≤ entrySq (G y) :=
    Finset.single_le_sum (f := fun j => ‖G y (unitVector j)‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have a2 : ‖K y (unitVector i)‖ ^ 2 ≤ entrySq (K y) :=
    Finset.single_le_sum (f := fun j => ‖K y (unitVector j)‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have a3 : ‖inner ℝ (G y (unitVector i)) (K y (unitVector i))‖ ≤ ‖G y (unitVector i)‖ * ‖K y (unitVector i)‖ := by
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  show _ ≤ entrySq (G y) + entrySq (K y)
  nlinarith [sq_nonneg (‖G y (unitVector i)‖ - ‖K y (unitVector i)‖), norm_nonneg (G y (unitVector i)),
    norm_nonneg (K y (unitVector i))]

theorem pair_sq_le {G K : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (hK : AEStronglyMeasurable K volume) (hG2 : Integrable fun y => entrySq (G y))
    (hK2 : Integrable fun y => entrySq (K y)) :
    (∫ y, entryInner (G y) (K y)) ^ 2 ≤ (∫ y, entrySq (G y)) * ∫ y, entrySq (K y) := by
  have hI := integrable_entryInner hG hK hG2 hK2
  have key : ∀ x : ℝ, 0 ≤ (∫ y, entrySq (G y)) * (x * x) + (2 * ∫ y, entryInner (G y) (K y)) * x
      + ∫ y, entrySq (K y) := by
    intro x
    have e : (∫ y, entrySq (x • G y + K y)) = x ^ 2 * (∫ y, entrySq (G y))
        + 2 * x * (∫ y, entryInner (G y) (K y)) + ∫ y, entrySq (K y) := by
      simp_rw [entrySq_expand]
      have i1 : Integrable (fun y => x ^ 2 * entrySq (G y) + 2 * x * entryInner (G y) (K y)) :=
        (hG2.const_mul _).add (hI.const_mul _)
      rw [integral_add i1 hK2,
        integral_add (hG2.const_mul _) (hI.const_mul _), integral_const_mul, integral_const_mul]
    have h0 : 0 ≤ ∫ y, entrySq (x • G y + K y) := integral_nonneg fun y => entrySq_nonneg _
    rw [e] at h0
    nlinarith [h0]
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

end ModelPinInternal

open ModelPinInternal

theorem modelPin_of (h1 : ChosenAgreeStatement) : ModelPinStatement := by
  intro α _ _ k N c hc p _ v G H hs P _ _ κ
  have hb := hc.base
  show vecNorm (fun i => pinValue (c.modelPinField i) (FracCellData.chosenGrad c.order v) - pinValue (c.pin i) G)
    ≤ c.pinLoss * sizeNorm c.multiplierScale c.weight G H κ
  have hs' : IsSecondOrderField c.order v G H := hs
  have hagree := (h1 c.order v G H hs').1
  have hGm := hs'.measurable_gradient
  have hG2 := hs'.gradient_two
  set D : Fin k → Space → (Space →L[ℝ] Space) := fun i y => c.modelPinField i y - c.pin i y with hDdef
  have hDm : ∀ i, AEStronglyMeasurable (D i) volume := fun i =>
    (hc.modelPin_data i).1.sub (hb.pin_measurable i).1
  have hD2 : ∀ i, Integrable fun y => entrySq (D i y) := by
    intro i
    refine Integrable.mono' ((((hc.modelPin_data i).2.1).add (hb.pin_two i).1).const_mul 2)
      (entrySq_continuous.comp_aestronglyMeasurable (hDm i)) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (entrySq_nonneg _)]
    have := entrySq_sub_le (c.modelPinField i y) (c.pin i y)
    simp only [hDdef, Pi.add_apply]
    linarith
  have hdiff : ∀ i, pinValue (c.modelPinField i) (FracCellData.chosenGrad c.order v) - pinValue (c.pin i) G
      = ∫ y, entryInner (G y) (D i y) := by
    intro i
    unfold pinValue
    have hc1 : (∫ y, entryInner (FracCellData.chosenGrad c.order v y) (c.modelPinField i y))
        = ∫ y, entryInner (G y) (c.modelPinField i y) :=
      integral_congr_ae (hagree.mono fun y hy => by simp only [hy])
    rw [hc1, ← integral_sub (integrable_entryInner hGm (hc.modelPin_data i).1 hG2 (hc.modelPin_data i).2.1)
        (integrable_entryInner hGm (hb.pin_measurable i).1 hG2 (hb.pin_two i).1)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hDdef, entryInner, ContinuousLinearMap.sub_apply, inner_sub_right, Finset.sum_sub_distrib]
  rw [show (fun i => pinValue (c.modelPinField i) (FracCellData.chosenGrad c.order v) - pinValue (c.pin i) G)
    = fun i => ∫ y, entryInner (G y) (D i y) from funext hdiff]
  set A := ∫ y, entrySq (G y) with hAdef
  set L := c.pinFieldLoss with hLdef
  have hA0 : 0 ≤ A := integral_nonneg fun y => entrySq_nonneg _
  have hL0 : 0 ≤ L := hc.losses_nonneg'.2.2.2.2.2.2.2.2
  have hBeq : ∀ i, (∫ y, entrySq (D i y)) = ∫ y, entrySq (c.pin i y - c.modelPinField i y) := fun i =>
    integral_congr_ae (Filter.Eventually.of_forall fun y => entrySq_sub_comm _ _)
  have hS : ∑ i, (∫ y, entryInner (G y) (D i y)) ^ 2 ≤ A * L ^ 2 := by
    calc ∑ i, (∫ y, entryInner (G y) (D i y)) ^ 2 ≤ ∑ i, A * ∫ y, entrySq (D i y) :=
          Finset.sum_le_sum fun i _ => pair_sq_le hGm (hDm i) hG2 (hD2 i)
      _ = A * ∑ i, ∫ y, entrySq (c.pin i y - c.modelPinField i y) := by
          rw [← Finset.mul_sum]
          simp only [hBeq]
      _ ≤ A * L ^ 2 := mul_le_mul_of_nonneg_left hc.pinFieldLoss_bound hA0
  have hwmin := hb.weightMin_pos
  have hWG : Integrable fun y => c.weight y * entrySq (G y) := by
    refine hG2.bdd_mul (c := c.weightMax) hb.weight_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hwmin (hb.weight_lower y))]
    exact hb.weight_upper y
  have hWA : c.weightMin * A ≤ ∫ y, c.weight y * entrySq (G y) := by
    rw [hAdef, ← integral_const_mul]
    exact integral_mono (hG2.const_mul _) hWG fun y =>
      mul_le_mul_of_nonneg_right (hb.weight_lower y) (entrySq_nonneg _)
  have hE : c.weightMin * A ≤ weightedEnergy c.weight G H + c.multiplierScale ^ 2 * ∑ i, κ i ^ 2 := by
    have h2 : 0 ≤ ∫ y, ‖secondTrace (H y)‖ ^ 2 := integral_nonneg fun y => sq_nonneg _
    have h3 : 0 ≤ c.multiplierScale ^ 2 * ∑ i, κ i ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    unfold weightedEnergy
    linarith
  have hsize : Real.sqrt c.weightMin * Real.sqrt A ≤ sizeNorm c.multiplierScale c.weight G H κ := by
    rw [← Real.sqrt_mul hwmin.le, sizeNorm]
    exact Real.sqrt_le_sqrt hE
  have hsw : 0 < Real.sqrt c.weightMin := Real.sqrt_pos.mpr hwmin
  have hpl : L ≤ c.pinLoss * Real.sqrt c.weightMin := by
    have := hc.pinLoss_ge
    rw [div_le_iff₀ hsw] at this
    exact this
  have hpl0 : 0 ≤ c.pinLoss := hb.losses_nonneg.2.2
  calc vecNorm (fun i => ∫ y, entryInner (G y) (D i y)) ≤ Real.sqrt (A * L ^ 2) := Real.sqrt_le_sqrt hS
    _ = Real.sqrt A * L := by rw [Real.sqrt_mul hA0, Real.sqrt_sq hL0]
    _ ≤ Real.sqrt A * (c.pinLoss * Real.sqrt c.weightMin) :=
        mul_le_mul_of_nonneg_left hpl (Real.sqrt_nonneg _)
    _ = c.pinLoss * (Real.sqrt c.weightMin * Real.sqrt A) := by ring
    _ ≤ c.pinLoss * sizeNorm c.multiplierScale c.weight G H κ := mul_le_mul_of_nonneg_left hsize hpl0

end CellCert

end Breakdown
