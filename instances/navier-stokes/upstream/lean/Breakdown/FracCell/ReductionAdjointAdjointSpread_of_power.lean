import Breakdown.FracCell.ReductionAdjointDefs
import Breakdown.FracCert.ActiveEnclosure

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

theorem adjointSpread_of_power (hP : PowerPairingStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (d : FracCertData k N) (hw : 0 < d.weightMin) (hlow : ∀ y, d.weightMin ≤ d.weight y)
    (hmeas : Measurable d.weight) (hhigh : ∀ y, d.weight y ≤ d.weightMax)
    (Dζ : Fin k → (Fin k → ℝ) → Space → (Space →L[ℝ] Space))
    (Hζ : Fin k → (Fin k → ℝ) → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hζ : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, IsAdjointRegular (d.adjoint j p) (Dζ j p) (Hζ j p) ∧
      AEStronglyMeasurable (d.adjoint j p) volume)
    (hsharp : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, MemLp (d.adjointSharp j p) 2 volume)
    (hbound : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius,
      l2Norm (fun y => lowPowerAt (α - 1) (d.adjoint j p) y - (d.splitVisc • d.adjoint j p y + d.adjointSharp j p y))
        ≤ d.adjointSpread j p) :
    ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, ∀ v G H, IsSecondOrderField d.order v G H → ∀ P,
      IsWeakFractionalPower α v P →
        |l2Pair (d.splitField P H) (d.adjoint j p) - l2Pair (negSecondTrace H) (d.adjointSharp j p)|
          ≤ d.adjointSpread j p * Real.sqrt (d.energy G H) := by
  intro j hj p hp v G H hs P hPw
  obtain ⟨hreg, hζm⟩ := hζ j hj p hp
  obtain ⟨hL, hpair⟩ := hP α hα₁ hα₂ d.order (d.adjoint j p) (Dζ j p) (Hζ j p) hreg hζm v G H P hs hPw
  have hζ2 : MemLp (d.adjoint j p) 2 volume := hreg.1
  have hS2 := hsharp j hj p hp
  have hT : MemLp (fun y => secondTrace (H y)) 2 volume := ActiveEnclosureInternal.trace_memLp hs
  have hN : MemLp (fun y => -secondTrace (H y)) 2 volume := hT.neg
  have hP2 : MemLp P 2 volume := hPw.1
  have hX : MemLp (fun y => lowPowerAt (α - 1) (d.adjoint j p) y -
      (d.splitVisc • d.adjoint j p y + d.adjointSharp j p y)) 2 volume :=
    hL.sub ((hζ2.const_smul d.splitVisc).add hS2)
  have i1 := ActiveEnclosureInternal.pair_integrable hP2 hζ2
  have i2 := ActiveEnclosureInternal.pair_integrable hT hζ2
  have i3 := ActiveEnclosureInternal.pair_integrable hN hL
  have i4 := ActiveEnclosureInternal.pair_integrable hN hS2
  have eL : l2Pair (d.splitField P H) (d.adjoint j p) =
      l2Pair P (d.adjoint j p) + d.splitVisc * ∫ y, inner ℝ (secondTrace (H y)) (d.adjoint j p y) := by
    rw [← integral_const_mul, l2Pair, l2Pair, ← integral_add i1 (i2.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [FracCertData.splitField, inner_add_left, real_inner_smul_left]
  have eR : ∫ y, inner ℝ (-secondTrace (H y)) (lowPowerAt (α - 1) (d.adjoint j p) y -
      (d.splitVisc • d.adjoint j p y + d.adjointSharp j p y)) =
      (∫ y, inner ℝ (-secondTrace (H y)) (lowPowerAt (α - 1) (d.adjoint j p) y))
        + d.splitVisc * (∫ y, inner ℝ (secondTrace (H y)) (d.adjoint j p y))
        - ∫ y, inner ℝ (-secondTrace (H y)) (d.adjointSharp j p y) := by
    have i5 : Integrable (fun y => inner ℝ (-secondTrace (H y)) (lowPowerAt (α - 1) (d.adjoint j p) y)
        + d.splitVisc * inner ℝ (secondTrace (H y)) (d.adjoint j p y)) volume := i3.add (i2.const_mul _)
    rw [← integral_const_mul, ← integral_add i3 (i2.const_mul _), ← integral_sub i5 i4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right, inner_neg_left]
    ring
  have key : l2Pair (d.splitField P H) (d.adjoint j p) - l2Pair (negSecondTrace H) (d.adjointSharp j p) =
      ∫ y, inner ℝ (-secondTrace (H y)) (lowPowerAt (α - 1) (d.adjoint j p) y -
        (d.splitVisc • d.adjoint j p y + d.adjointSharp j p y)) := by
    rw [eR, eL, hpair]
    rfl
  rw [key]
  have hE : Real.sqrt (∫ y, ‖-secondTrace (H y)‖ ^ 2) ≤ Real.sqrt (d.energy G H) := by
    apply Real.sqrt_le_sqrt
    have h0 : 0 ≤ ∫ y, d.weight y * entrySq (G y) := by
      refine integral_nonneg fun y => mul_nonneg (hw.le.trans (hlow y)) ?_
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    simp only [FracCertData.energy, weightedEnergy, norm_neg]
    linarith
  have hB := hbound j hj p hp
  calc _ ≤ Real.sqrt (∫ y, ‖-secondTrace (H y)‖ ^ 2) * Real.sqrt (∫ y, ‖lowPowerAt (α - 1) (d.adjoint j p) y -
        (d.splitVisc • d.adjoint j p y + d.adjointSharp j p y)‖ ^ 2) :=
        ActiveEnclosureInternal.abs_pair_le hN hX
    _ ≤ Real.sqrt (d.energy G H) * d.adjointSpread j p :=
        mul_le_mul hE hB (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

end Reduction

end CellCert

end Breakdown
