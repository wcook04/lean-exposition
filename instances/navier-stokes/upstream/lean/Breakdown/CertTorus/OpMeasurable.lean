import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FarField

theorem opMeasurable_of_kernel : LerayKernelMeasurable → OpMeasurable := by
  intro hKm β F hF
  have hτ : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.1.2) :=
    measurable_snd.comp measurable_fst
  have hg : Measurable (fun q : ((ℝ × Space) × ℝ) × Space =>
      ((q.1.1.1 - Real.log (1 + q.1.2), (Real.sqrt (1 + q.1.2))⁻¹ • q.2) : ℝ × Space)) := by
    refine Measurable.prodMk ?_ ?_
    · exact (measurable_fst.comp (measurable_fst.comp measurable_fst)).sub
        (Real.measurable_log.comp (measurable_const.add hτ))
    · exact ((Real.continuous_sqrt.measurable.comp (measurable_const.add hτ)).inv).smul
        measurable_snd
  have hT : Measurable (fun q : ((ℝ × Space) × ℝ) × Space =>
      tensorShift F q.1.1.1 q.1.2 q.2) := hF.comp hg
  have hin : ∀ i : Fin 3, Measurable (fun x : (ℝ × Space) × ℝ =>
      ∫ z, ∑ j : Fin 3, ∑ k : Fin 3,
        lerayKernel i j k x.2 (x.1.2 - z) * tensorShift F x.1.1 x.2 z j k) := by
    intro i
    refine (StronglyMeasurable.integral_prod_right
      (f := fun (x : (ℝ × Space) × ℝ) (z : Space) => ∑ j : Fin 3, ∑ k : Fin 3,
        lerayKernel i j k x.2 (x.1.2 - z) * tensorShift F x.1.1 x.2 z j k) ?_).measurable
    refine Measurable.stronglyMeasurable ?_
    refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
    refine Measurable.mul ?_ ?_
    · exact (hKm i j k).comp (hτ.prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).sub measurable_snd))
    · exact (measurable_pi_apply k).comp ((measurable_pi_apply j).comp hT)
  have hconv : Measurable (fun x : (ℝ × Space) × ℝ =>
      kernelConv x.2 (tensorShift F x.1.1 x.2) x.1.2) := by
    unfold kernelConv
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (continuous_id.smul continuous_const).measurable.comp (hin i)
  have hint : Measurable (fun x : (ℝ × Space) × ℝ =>
      (1 + x.2) ^ (-β) • kernelConv x.2 (tensorShift F x.1.1 x.2) x.1.2) :=
    ((measurable_const.add measurable_snd).pow_const (-β)).smul hconv
  have hout := (StronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioi (0 : ℝ)))
    (f := fun (p : ℝ × Space) (τ : ℝ) =>
      (1 + τ) ^ (-β) • kernelConv τ (tensorShift F p.1 τ) p.2)
    hint.stronglyMeasurable).measurable
  unfold profileOp
  exact hout.neg

end Breakdown.FarField
