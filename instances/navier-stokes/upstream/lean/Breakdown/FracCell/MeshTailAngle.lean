import Breakdown.FracCell.MeshTailCoef
import Breakdown.FracCell.MeshTailSlice
import Breakdown.FracCell.MeshTailEnergy

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace MeshTailAngle

theorem ii_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume a b := by
  exact ⟨integrable_finsetSum s fun i hi => (h i hi).1, integrable_finsetSum s fun i hi => (h i hi).2⟩

end MeshTailAngle

open MeshTailAngle in
theorem angleTail_of (hS : AngleSliceStatement) (hP : InputEnergyStatement) : AngleTailStatement := by
  intro K B hK hB m hm D I O _ _ T hreg hb w F
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hint : ∀ (o : O) (jl : ℕ × ℕ), IntervalIntegrable
      (fun θ => ‖B.coef K (fun p => T.angleField m B w o p θ) jl.1 jl.2‖ ^ 2) volume 0 (2 * Real.pi) := by
    intro o jl
    have hmem := (coefMode_holds K B hK m T hreg w o 0 jl.1 jl.2).2
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le]
    exact (memLp_two_iff_integrable_sq_norm hmem.1).1 hmem
  have hSo : ∀ o : O, IntervalIntegrable (fun θ => ∑ jl ∈ F,
      (if D < max jl.1 jl.2 then ‖B.coef K (fun p => T.angleField m B w o p θ) jl.1 jl.2‖ ^ 2 else 0))
      volume 0 (2 * Real.pi) := by
    intro o
    refine ii_sum F fun jl _ => ?_
    by_cases hf : D < max jl.1 jl.2
    · simpa only [hf, if_true] using hint o jl
    · simp only [hf, if_false]; exact intervalIntegrable_const
  have hPr := fun i k => (hP K B hK hB m hm T w i k).1
  have hPh := fun i k => (hP K B hK hB m hm T w i k).2
  have hR : IntervalIntegrable (fun θ => (∑ i, ∑ j ∈ Finset.range (T.inputDeg i + 1), T.radialTotal * T.radialBound i j *
                ∫ z in Set.Icc K.z₁ K.z₂, ∑ c, ‖T.radialInput m B w i j c z θ‖ ^ 2)
            + ∑ i, ∑ l ∈ Finset.range (T.inputDeg i + 1), T.heightTotal * T.heightBound i l *
                ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ∑ c, ‖T.heightInput m B w i l c r θ‖ ^ 2)
        volume 0 (2 * Real.pi) :=
    (ii_sum _ fun i _ => ii_sum _ fun j _ => (hPr i j).1.const_mul _).add
      (ii_sum _ fun i _ => ii_sum _ fun l _ => (hPh i l).1.const_mul _)
  have hall : ∀ᵐ θ ∂(volume : Measure ℝ), ∀ i o c,
      AEStronglyMeasurable (fun p => T.mult i o c p θ) (volume.restrict K.rect) := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro o; rw [ae_all_iff]; intro c
    exact (hreg.mult_measurable i o c).prodMk_right
  calc (∑ o, T.outWeight o * ((1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ jl ∈ F,
            (if D < max jl.1 jl.2 then ‖B.coef K (fun p => T.angleField m B w o p θ) jl.1 jl.2‖ ^ 2 else 0)))
        = (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ o, T.outWeight o * ∑ jl ∈ F,
            (if D < max jl.1 jl.2 then ‖B.coef K (fun p => T.angleField m B w o p θ) jl.1 jl.2‖ ^ 2 else 0) := by
          rw [intervalIntegral.integral_finsetSum (fun o _ => (hSo o).const_mul _), Finset.mul_sum]
          refine Finset.sum_congr rfl fun o _ => ?_
          rw [intervalIntegral.integral_const_mul]
          ring
    _ ≤ (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            ((∑ i, ∑ j ∈ Finset.range (T.inputDeg i + 1), T.radialTotal * T.radialBound i j *
                ∫ z in Set.Icc K.z₁ K.z₂, ∑ c, ‖T.radialInput m B w i j c z θ‖ ^ 2)
            + ∑ i, ∑ l ∈ Finset.range (T.inputDeg i + 1), T.heightTotal * T.heightBound i l *
                ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ∑ c, ‖T.heightInput m B w i l c r θ‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine intervalIntegral.integral_mono_ae hpi.le
            (ii_sum _ fun o _ => (hSo o).const_mul _) hR ?_
          filter_upwards [hall] with θ hθ
          exact hS K B hK hB m D T hreg hb w F θ hθ
    _ = T.majorant w := by
          rw [intervalIntegral.integral_add (ii_sum _ fun i _ => ii_sum _ fun j _ => (hPr i j).1.const_mul _)
            (ii_sum _ fun i _ => ii_sum _ fun l _ => (hPh i l).1.const_mul _), mul_add,
            intervalIntegral.integral_finsetSum (fun i _ => ii_sum _ fun j _ => (hPr i j).1.const_mul _),
            intervalIntegral.integral_finsetSum (fun i _ => ii_sum _ fun l _ => (hPh i l).1.const_mul _),
            Finset.mul_sum, Finset.mul_sum]
          have e1 : ∀ i, (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
              ∑ j ∈ Finset.range (T.inputDeg i + 1), T.radialTotal * T.radialBound i j *
                ∫ z in Set.Icc K.z₁ K.z₂, ∑ c, ‖T.radialInput m B w i j c z θ‖ ^ 2
              = ∑ j ∈ Finset.range (T.inputDeg i + 1), T.radialTotal * T.radialBound i j *
                  ∑ n' ∈ T.inModes, ∑ l ∈ Finset.range (T.inputDeg i + 1), ∑ c, ‖w i n' j l c‖ ^ 2 := by
            intro i
            rw [intervalIntegral.integral_finsetSum (fun j _ => (hPr i j).1.const_mul _), Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [intervalIntegral.integral_const_mul, ← (hPr i j).2]
            ring
          have e2 : ∀ i, (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
              ∑ l ∈ Finset.range (T.inputDeg i + 1), T.heightTotal * T.heightBound i l *
                ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ∑ c, ‖T.heightInput m B w i l c r θ‖ ^ 2
              = ∑ l ∈ Finset.range (T.inputDeg i + 1), T.heightTotal * T.heightBound i l *
                  ∑ n' ∈ T.inModes, ∑ j ∈ Finset.range (T.inputDeg i + 1), ∑ c, ‖w i n' j l c‖ ^ 2 := by
            intro i
            rw [intervalIntegral.integral_finsetSum (fun l _ => (hPh i l).1.const_mul _), Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [intervalIntegral.integral_const_mul, ← (hPh i l).2]
            ring
          simp only [e1, e2]
          unfold TailFamily.majorant
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          · rw [Finset.sum_comm]
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_comm]

theorem angleTail_holds : AngleTailStatement := angleTail_of angleSlice_holds inputEnergy_holds

end CellAnalysis

end CellCert

end Breakdown
