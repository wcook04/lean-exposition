import Breakdown.FracCell.ReductionLossDefs
import Breakdown.FracCert.LinearStateClosed

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

namespace CentreLossKernelInternal

theorem apply_le (A : Space →L[ℝ] Space) (x : Space) : ‖A x‖ ≤ Real.sqrt (entrySq A) * ‖x‖ := by
  have h := LinearStateClosedInternal.clm_sq_le A x
  have h0 : 0 ≤ entrySq A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← Real.sqrt_sq (norm_nonneg (A x)), ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul h0]
  exact Real.sqrt_le_sqrt h

theorem entry_nonneg (A : Space →L[ℝ] Space) : 0 ≤ entrySq A := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sum_sq_integral_le {a b : Space → ℝ} (ha : AEStronglyMeasurable a volume)
    (hb : AEStronglyMeasurable b volume) (ha0 : ∀ y, 0 ≤ a y) (hb0 : ∀ y, 0 ≤ b y)
    (hai : Integrable (fun y => a y ^ 2)) (hbi : Integrable (fun y => b y ^ 2)) :
    Integrable (fun y => (a y + b y) ^ 2) ∧
      ∫ y, (a y + b y) ^ 2 ≤ (Real.sqrt (∫ y, a y ^ 2) + Real.sqrt (∫ y, b y ^ 2)) ^ 2 := by
  have haL : MemLp a 2 volume := (memLp_two_iff_integrable_sq ha).2 hai
  have hbL : MemLp b 2 volume := (memLp_two_iff_integrable_sq hb).2 hbi
  have hab : Integrable (fun y => a y * b y) := by
    refine (hai.add hbi).mono' (ha.mul hb) (ae_of_all _ fun y => ?_)
    change _ ≤ a y ^ 2 + b y ^ 2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 y), abs_of_nonneg (hb0 y)]
    nlinarith [sq_nonneg (a y - b y)]
  have hcs : ∫ y, a y * b y ≤ Real.sqrt (∫ y, a y ^ 2) * Real.sqrt (∫ y, b y ^ 2) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
      (ae_of_all _ ha0) (ae_of_all _ hb0) (by simpa using haL) (by simpa using hbL)
    simp only [Real.rpow_two] at h
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact h
  have hexp : (fun y => (a y + b y) ^ 2) = fun y => (a y ^ 2 + 2 * (a y * b y)) + b y ^ 2 := by
    funext y; ring
  have hint : Integrable (fun y => (a y + b y) ^ 2) := by
    rw [hexp]; exact (hai.add (hab.const_mul 2)).add hbi
  refine ⟨hint, ?_⟩
  have h1 : ∫ y, (a y ^ 2 + 2 * (a y * b y)) + b y ^ 2 =
      (∫ y, a y ^ 2 + 2 * (a y * b y)) + ∫ y, b y ^ 2 := integral_add (hai.add (hab.const_mul 2)) hbi
  have h2 : ∫ y, a y ^ 2 + 2 * (a y * b y) = (∫ y, a y ^ 2) + ∫ y, 2 * (a y * b y) :=
    integral_add hai (hab.const_mul 2)
  have h3 : ∫ y, 2 * (a y * b y) = 2 * ∫ y, a y * b y := integral_const_mul _ _
  rw [hexp, h1, h2, h3]
  have hA : 0 ≤ ∫ y, a y ^ 2 := integral_nonneg fun y => sq_nonneg _
  have hB : 0 ≤ ∫ y, b y ^ 2 := integral_nonneg fun y => sq_nonneg _
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB]

end CentreLossKernelInternal

open CentreLossKernelInternal in
theorem centreLoss_of_kernel (hK : KernelPotentialStatement) {k N : ℕ} (c : FracCellData k N)
    (hw : 0 < c.weightMin) (hlow : ∀ y, c.weightMin ≤ c.weight y)
    (hmeas : Measurable c.weight) (hhigh : ∀ y, c.weight y ≤ c.weightMax)
    (S : CentreKernelSplit k) (hS : IsCentreKernelSplit c S)
    (hbound : ∀ p ∈ box c.radius, S.supBound p + S.kernelBound ≤ c.centreLoss * Real.sqrt c.weightMin) :
    ∀ p ∈ box c.radius, ∀ v G H, IsSecondOrderField c.order v G H →
      l2Norm (fun y => (2 : ℝ) • symProduct (fun z => c.profile p z - c.centre z)
        (fun z => c.gradProfile p z - c.centreGrad z) v G y) ≤ c.centreLoss * Real.sqrt (c.energy G H) := by
  intro p hp v G H hF
  have hs0 : 0 ≤ S.supBound p := le_trans (norm_nonneg _) (hS.sup_le p hp 0)
  have hk0 : 0 ≤ S.kernelBound := hS.bound_nonneg
  have hkb := hS.kernel p hp
  have hsw : 0 < Real.sqrt c.weightMin := Real.sqrt_pos.2 hw
  have hL0 : 0 ≤ c.centreLoss := by
    have h1 := hbound p hp
    by_contra hneg
    have hneg' := not_le.mp hneg
    nlinarith [mul_neg_of_neg_of_pos hneg' hsw]
  have hpair : IsGradientPair v G := ⟨hF.measurable_velocity, hF.velocity_six, hF.measurable_gradient,
    hF.gradient_two, hF.weak_gradient⟩
  obtain ⟨hVi, hVle⟩ := hK _ _ hkb v G hpair
  have hE0 : 0 ≤ ∫ y, entrySq (G y) := integral_nonneg fun y => entry_nonneg _
  set a : Space → ℝ := fun y => S.supBound p * Real.sqrt (entrySq (G y)) with ha_def
  set b : Space → ℝ := fun y => ‖c.gradProfile p y - c.centreGrad y‖ * ‖v y‖ with hb_def
  have ha0 : ∀ y, 0 ≤ a y := fun y => mul_nonneg hs0 (Real.sqrt_nonneg _)
  have hb0 : ∀ y, 0 ≤ b y := fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hasq : (fun y => a y ^ 2) = fun y => S.supBound p ^ 2 * entrySq (G y) := by
    funext y
    simp only [ha_def]
    rw [mul_pow, Real.sq_sqrt (entry_nonneg _)]
  have hbsq : (fun y => b y ^ 2) = fun y => ‖c.gradProfile p y - c.centreGrad y‖ ^ 2 * ‖v y‖ ^ 2 := by
    funext y
    simp only [hb_def]
    rw [mul_pow]
  have ham : AEStronglyMeasurable a volume :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hF.gradient_two.aestronglyMeasurable).const_mul _
  have hnm : AEStronglyMeasurable (fun y => ‖c.gradProfile p y - c.centreGrad y‖) volume := by
    have h2 : (fun y => ‖c.gradProfile p y - c.centreGrad y‖) =
        fun y => Real.sqrt (‖c.gradProfile p y - c.centreGrad y‖ ^ 2) := by
      funext y; rw [Real.sqrt_sq (norm_nonneg _)]
    rw [h2]
    exact (Real.continuous_sqrt.measurable.comp hkb.2.1).aestronglyMeasurable
  have hbm : AEStronglyMeasurable b volume := hnm.mul hF.measurable_velocity.norm
  have hai : Integrable (fun y => a y ^ 2) := by rw [hasq]; exact hF.gradient_two.const_mul _
  have hbi : Integrable (fun y => b y ^ 2) := by rw [hbsq]; exact hVi
  obtain ⟨hint, hsum⟩ := sum_sq_integral_le ham hbm ha0 hb0 hai hbi
  have hA : ∫ y, a y ^ 2 = S.supBound p ^ 2 * ∫ y, entrySq (G y) := by
    rw [hasq, integral_const_mul]
  have hB : ∫ y, b y ^ 2 ≤ S.kernelBound ^ 2 * ∫ y, entrySq (G y) := by
    rw [hbsq]; exact hVle
  have hsA : Real.sqrt (∫ y, a y ^ 2) = S.supBound p * Real.sqrt (∫ y, entrySq (G y)) := by
    rw [hA, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs0]
  have hsB : Real.sqrt (∫ y, b y ^ 2) ≤ S.kernelBound * Real.sqrt (∫ y, entrySq (G y)) := by
    calc Real.sqrt (∫ y, b y ^ 2) ≤ Real.sqrt (S.kernelBound ^ 2 * ∫ y, entrySq (G y)) := Real.sqrt_le_sqrt hB
      _ = S.kernelBound * Real.sqrt (∫ y, entrySq (G y)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk0]
  have hpt : ∀ y, ‖(2 : ℝ) • symProduct (fun z => c.profile p z - c.centre z)
      (fun z => c.gradProfile p z - c.centreGrad z) v G y‖ ^ 2 ≤ (a y + b y) ^ 2 := by
    intro y
    have he : (2 : ℝ) • symProduct (fun z => c.profile p z - c.centre z)
        (fun z => c.gradProfile p z - c.centreGrad z) v G y =
        G y (c.profile p y - c.centre y) + (c.gradProfile p y - c.centreGrad y) (v y) := by
      simp only [symProduct, smul_smul]
      norm_num
    rw [he]
    have h1 := apply_le (G y) (c.profile p y - c.centre y)
    have h2 := ContinuousLinearMap.le_opNorm (c.gradProfile p y - c.centreGrad y) (v y)
    have h3 := hS.sup_le p hp y
    have h4 : Real.sqrt (entrySq (G y)) * ‖c.profile p y - c.centre y‖ ≤ a y := by
      simp only [ha_def]
      rw [mul_comm (S.supBound p)]
      exact mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    have h5 := norm_add_le (G y (c.profile p y - c.centre y)) ((c.gradProfile p y - c.centreGrad y) (v y))
    have h6 : ‖G y (c.profile p y - c.centre y) + (c.gradProfile p y - c.centreGrad y) (v y)‖ ≤ a y + b y := by
      simp only [hb_def] at *
      linarith
    exact pow_le_pow_left₀ (norm_nonneg _) h6 2
  have hX : (∫ y, ‖(2 : ℝ) • symProduct (fun z => c.profile p z - c.centre z)
      (fun z => c.gradProfile p z - c.centreGrad z) v G y‖ ^ 2) ≤
      ((S.supBound p + S.kernelBound) * Real.sqrt (∫ y, entrySq (G y))) ^ 2 := by
    calc _ ≤ ∫ y, (a y + b y) ^ 2 :=
          integral_mono_of_nonneg (ae_of_all _ fun y => sq_nonneg _) hint (ae_of_all _ hpt)
      _ ≤ (Real.sqrt (∫ y, a y ^ 2) + Real.sqrt (∫ y, b y ^ 2)) ^ 2 := hsum
      _ ≤ ((S.supBound p + S.kernelBound) * Real.sqrt (∫ y, entrySq (G y))) ^ 2 := by
        apply pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        rw [hsA, add_mul]
        linarith
  have hen : c.weightMin * (∫ y, entrySq (G y)) ≤ c.energy G H := by
    have hwi : Integrable (fun y => c.weight y * entrySq (G y)) := by
      refine hF.gradient_two.bdd_mul (c := c.weightMax) hmeas.aestronglyMeasurable (ae_of_all _ fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hw.le (hlow y))]
      exact hhigh y
    have h1 : c.weightMin * (∫ y, entrySq (G y)) ≤ ∫ y, c.weight y * entrySq (G y) := by
      rw [← integral_const_mul]
      exact integral_mono (hF.gradient_two.const_mul _) hwi
        fun y => mul_le_mul_of_nonneg_right (hlow y) (entry_nonneg _)
    have h2 : 0 ≤ ∫ y, ‖secondTrace (H y)‖ ^ 2 := integral_nonneg fun y => sq_nonneg _
    show c.weightMin * (∫ y, entrySq (G y)) ≤ weightedEnergy c.weight G H
    unfold weightedEnergy
    linarith
  calc l2Norm _ ≤ (S.supBound p + S.kernelBound) * Real.sqrt (∫ y, entrySq (G y)) := by
        unfold l2Norm
        calc _ ≤ Real.sqrt (((S.supBound p + S.kernelBound) * Real.sqrt (∫ y, entrySq (G y))) ^ 2) :=
              Real.sqrt_le_sqrt hX
          _ = _ := Real.sqrt_sq (mul_nonneg (add_nonneg hs0 hk0) (Real.sqrt_nonneg _))
    _ ≤ c.centreLoss * Real.sqrt c.weightMin * Real.sqrt (∫ y, entrySq (G y)) :=
        mul_le_mul_of_nonneg_right (hbound p hp) (Real.sqrt_nonneg _)
    _ = c.centreLoss * Real.sqrt (c.weightMin * ∫ y, entrySq (G y)) := by
        rw [Real.sqrt_mul hw.le, mul_assoc]
    _ ≤ c.centreLoss * Real.sqrt (c.energy G H) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hen) hL0

end Reduction

end CellCert

end Breakdown
