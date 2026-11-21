import Breakdown.CertCell.InstanceStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

open CellCert.CellAnalysis (CellBox)

private theorem labelFlip_labelFlip (ι : ℤ × ℤ) : labelFlip (labelFlip ι) = ι := by
  unfold labelFlip
  ext <;> simp

private theorem labelFlip_eq_iff (ι κ : ℤ × ℤ) : labelFlip ι = κ ↔ ι = labelFlip κ := by
  constructor
  · rintro rfl
    rw [labelFlip_labelFlip]
  · rintro rfl
    rw [labelFlip_labelFlip]

private theorem cellPoly_eval_zero (K : CellBox) (p : ℝ × ℝ) : CellPoly.zero.eval K p = 0 := by
  simp [CellPoly.eval, CellPoly.zero]

private theorem cellPoly_eval_scale (K : CellBox) (c : ℂ) (P : CellPoly) (p : ℝ × ℝ) :
    (P.scale c).eval K p = c * P.eval K p := by
  simp only [CellPoly.eval, CellPoly.scale, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem generator_planeValue {count rowCount : ℕ} (R : RowValues count rowCount)
    (box : Fin count → CellBox) (a : Fin rowCount) (ι : ℤ × ℤ) (c : Fin 3) (p : ℝ × ℝ) :
    (R.generator a).planeValue box (R.cellOf a) ι c p =
      if 0 ≤ p.2 then
        (if ι = R.labelOf a then rowPartFactor (R.realPart a) * R.testValue box a c p else 0)
      else
        (if ι = labelFlip (R.labelOf a) then
          (frameSign c : ℂ) * rowPartFactor (R.realPart a) * R.testValue box a c (p.1, -p.2)
        else 0) := by
  unfold CellVecField.planeValue labelValueAt
  by_cases hp : 0 ≤ p.2
  · rw [if_pos hp, if_pos hp]
    by_cases hι : ι = R.labelOf a
    · subst hι
      rw [if_pos rfl]
      simp only [RowValues.generator, and_self, if_true]
      rw [cellPoly_eval_scale]
      rfl
    · rw [if_neg hι]
      simp only [RowValues.generator, true_and, if_neg hι]
      exact cellPoly_eval_zero _ _
  · rw [if_neg hp, if_neg hp]
    by_cases hι : ι = labelFlip (R.labelOf a)
    · have hf : labelFlip ι = R.labelOf a := (labelFlip_eq_iff _ _).2 hι
      rw [if_pos hι]
      simp only [RowValues.generator, true_and, if_pos hf]
      rw [cellPoly_eval_scale, hf, mul_assoc]
      rfl
    · have hf : ¬ labelFlip ι = R.labelOf a := fun h => hι ((labelFlip_eq_iff _ _).1 h)
      rw [if_neg hι]
      simp only [RowValues.generator, true_and, if_neg hf]
      rw [cellPoly_eval_zero, mul_zero]

theorem generatorField_eq {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (a : Fin rowCount)
    (σ : ℝ) (y : Space) :
    R.generatorField M.box m a σ y = Set.indicator (M.box (R.cellOf a)).solid (fun y => ∑ c : Fin 3,
      (labelPhase m (if 0 ≤ y 2 then R.labelOf a else labelFlip (R.labelOf a)) σ (pointAngle y) *
        (if 0 ≤ y 2 then rowPartFactor (R.realPart a) * R.testValue M.box a c (pointPlane y)
          else (frameSign c : ℂ) * rowPartFactor (R.realPart a) *
            R.testValue M.box a c ((pointPlane y).1, -(pointPlane y).2))).re • frameUnit (pointAngle y) c) y := by
  classical
  unfold RowValues.generatorField CellVecField.field
  rw [Finset.sum_eq_single (R.cellOf a)]
  · congr 1
    funext z
    have hlab : (R.generator a).labels (R.cellOf a) = {R.labelOf a, labelFlip (R.labelOf a)} := by
      simp [RowValues.generator]
    have h2 : (pointPlane z).2 = z 2 := rfl
    rw [hlab]
    by_cases hz : 0 ≤ z 2
    · rw [Finset.sum_eq_single_of_mem (R.labelOf a) (Finset.mem_insert_self _ _)]
      · refine Finset.sum_congr rfl fun c _ => ?_
        rw [generator_planeValue, h2, if_pos hz, if_pos rfl, if_pos hz, if_pos hz]
      · intro ι _ hι
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [generator_planeValue, h2, if_pos hz, if_neg hι, mul_zero, Complex.zero_re, zero_smul]
    · rw [Finset.sum_eq_single_of_mem (labelFlip (R.labelOf a))
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]
      · refine Finset.sum_congr rfl fun c _ => ?_
        rw [generator_planeValue, h2, if_neg hz, if_pos rfl, if_neg hz, if_neg hz]
      · intro ι _ hι
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [generator_planeValue, h2, if_neg hz, if_neg hι, mul_zero, Complex.zero_re, zero_smul]
  · intro K _ hK
    have hlab : (R.generator a).labels K = ∅ := by
      simp [RowValues.generator, hK]
    rw [hlab]
    simp only [Finset.sum_empty]
    exact congrFun (Set.indicator_zero (M := Space) (M.box K).solid) y
  · intro h
    exact absurd (Finset.mem_univ _) h

end Instance

end CertCell

end Breakdown
