import Breakdown.FracCell.ReductionLossKernelBoundPiece
import Breakdown.FracCert.LinearSolveCore

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

private theorem mirror_mirror_aux (y : Space) : mirror (mirror y) = y := by
  ext i
  fin_cases i <;> simp [mirror]

private theorem norm_sub_mirror_aux (x y : Space) : ‖x - mirror y‖ = ‖mirror x - y‖ := by
  rw [← LinearSolveCore.norm_mirror (x - mirror y)]
  congr 1
  ext i
  fin_cases i <;> simp [mirror] <;> ring

private theorem horizontalNorm_nonneg_aux (y : Space) : 0 ≤ horizontalNorm y := Real.sqrt_nonneg _

private theorem kernel_mirror_aux {V : Space → ℝ} (hV : ∀ y, V (mirror y) = V y) (x y : Space) :
    V (mirror y) / (4 * Real.pi * ‖x - mirror y‖) = V y / (4 * Real.pi * ‖mirror x - y‖) := by
  rw [hV, norm_sub_mirror_aux]

private theorem kernel_measurable_aux {V : Space → ℝ} (hV : Measurable V) (x : Space) :
    Measurable (fun y => V y / (4 * Real.pi * ‖x - y‖)) :=
  hV.div (measurable_const.mul (continuous_const.sub continuous_id).norm.measurable)

private theorem kernel_nonneg_aux {V : Space → ℝ} (hV : ∀ y, 0 ≤ V y) (x y : Space) :
    0 ≤ V y / (4 * Real.pi * ‖x - y‖) := by
  have := hV y
  positivity

private theorem mirror_embedding_aux : MeasurableEmbedding mirror :=
  LinearSolveCore.mirrorIsometry.toHomeomorph.measurableEmbedding

private theorem comp_mirror_aux (f : Space → ℝ) :
    Integrable (fun y => f (mirror y)) ↔ Integrable f :=
  LinearSolveCore.mirror_measurePreserving.integrable_comp_emb mirror_embedding_aux

private theorem integral_comp_mirror_aux (f : Space → ℝ) :
    ∫ y, f (mirror y) = ∫ y, f y :=
  LinearSolveCore.mirror_measurePreserving.integral_comp mirror_embedding_aux f

private theorem upper_aux (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D) (Λ : ℝ)
    (hΛ : ∀ a, D.boxBound a ≤ Λ) (x : Space) (hz : 0 ≤ x 2) :
    Integrable (fun y => V y / (4 * Real.pi * ‖x - y‖)) ∧ (∫ y, V y / (4 * Real.pi * ‖x - y‖)) ≤ Λ := by
  obtain ⟨a, h1, h2, h3, h4⟩ := hD.box_cover (horizontalNorm x) (x 2) (horizontalNorm_nonneg_aux x) hz
  have hP := fun b mirrored => pieceKernel_le m V D hD a b mirrored x hz h1 h2 h3 h4
  set K : Space → Space → ℝ := fun w y => V y / (4 * Real.pi * ‖w - y‖) with hK
  have hK0 : ∀ w y, 0 ≤ K w y := fun w y => kernel_nonneg_aux hD.nonneg w y
  have hKm : ∀ w, Measurable (K w) := fun w => kernel_measurable_aux hD.measurable w
  have hPf : ∀ b, IntegrableOn (K x) (D.pieceSolid b) ∧
      (∫ y in D.pieceSolid b, K x y) ≤ D.pairTerm m a b false := by
    intro b
    simpa using hP b false
  have hPt : ∀ b, IntegrableOn (K (mirror x)) (D.pieceSolid b) ∧
      (∫ y in D.pieceSolid b, K (mirror x) y) ≤ D.pairTerm m a b true := by
    intro b
    simpa using hP b true
  have hind : ∀ b, (mirror ⁻¹' D.pieceSolid b).indicator (K x) =
      fun y => (D.pieceSolid b).indicator (K (mirror x)) (mirror y) := by
    intro b
    funext y
    by_cases hy : mirror y ∈ D.pieceSolid b
    · have hy' : y ∈ mirror ⁻¹' D.pieceSolid b := hy
      rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy]
      simp only [hK]
      rw [hD.mirror_even, norm_sub_mirror_aux, mirror_mirror_aux]
    · have hy' : y ∉ mirror ⁻¹' D.pieceSolid b := hy
      rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem hy]
  set g : Space → ℝ := fun y => ∑ b, ((D.pieceSolid b).indicator (K x) y +
    (mirror ⁻¹' D.pieceSolid b).indicator (K x) y) with hg
  have hgi : Integrable g := by
    refine integrable_finsetSum _ fun b _ => ?_
    refine Integrable.add ((integrable_indicator_iff (hD.solid_measurable b)).2 (hPf b).1) ?_
    rw [hind b]
    exact (comp_mirror_aux _).2 ((integrable_indicator_iff (hD.solid_measurable b)).2 (hPt b).1)
  have hle : ∀ y, K x y ≤ g y := by
    intro y
    have hterm : ∀ b, 0 ≤ (D.pieceSolid b).indicator (K x) y + (mirror ⁻¹' D.pieceSolid b).indicator (K x) y :=
      fun b => add_nonneg (Set.indicator_nonneg (fun y _ => hK0 x y) y)
        (Set.indicator_nonneg (fun y _ => hK0 x y) y)
    by_cases hVy : V y = 0
    · have : K x y = 0 := by simp [hK, hVy]
      rw [this]
      exact Finset.sum_nonneg fun b _ => hterm b
    · obtain ⟨b, hb⟩ := hD.support y hVy
      refine le_trans ?_ (Finset.single_le_sum (fun b _ => hterm b) (Finset.mem_univ b))
      rcases hb with hb | hb
      · rw [Set.indicator_of_mem hb]
        exact le_add_of_nonneg_right (Set.indicator_nonneg (fun y _ => hK0 x y) y)
      · have hb' : y ∈ mirror ⁻¹' D.pieceSolid b := hb
        rw [Set.indicator_of_mem hb']
        exact le_add_of_nonneg_left (Set.indicator_nonneg (fun y _ => hK0 x y) y)
  have hKi : Integrable (K x) := by
    refine hgi.mono' (hKm x).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hK0 x y)]
    exact hle y
  refine ⟨hKi, ?_⟩
  have hgint : ∫ y, g y = ∑ b, ((∫ y in D.pieceSolid b, K x y) + ∫ y in D.pieceSolid b, K (mirror x) y) := by
    rw [hg, integral_finsetSum]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_add ((integrable_indicator_iff (hD.solid_measurable b)).2 (hPf b).1)]
      · rw [integral_indicator (hD.solid_measurable b), hind b, integral_comp_mirror_aux
          ((D.pieceSolid b).indicator (K (mirror x))), integral_indicator (hD.solid_measurable b)]
      · rw [hind b]
        exact (comp_mirror_aux _).2 ((integrable_indicator_iff (hD.solid_measurable b)).2 (hPt b).1)
    · intro b _
      refine Integrable.add ((integrable_indicator_iff (hD.solid_measurable b)).2 (hPf b).1) ?_
      rw [hind b]
      exact (comp_mirror_aux _).2 ((integrable_indicator_iff (hD.solid_measurable b)).2 (hPt b).1)
  calc (∫ y, K x y) ≤ ∫ y, g y := integral_mono hKi hgi hle
    _ = ∑ b, ((∫ y in D.pieceSolid b, K x y) + ∫ y in D.pieceSolid b, K (mirror x) y) := hgint
    _ ≤ ∑ b, ∑ mirrored : Bool, D.pairTerm m a b mirrored := by
      refine Finset.sum_le_sum fun b _ => ?_
      rw [Fintype.sum_bool]
      linarith [(hPf b).2, (hPt b).2]
    _ ≤ D.boxBound a := hD.box_sum a
    _ ≤ Λ := hΛ a

theorem kernelBound_of_cellSums (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D) (Λ : ℝ)
    (hΛ : ∀ a, D.boxBound a ≤ Λ) : KernelBound V Λ := by
  refine ⟨hD.nonneg, hD.measurable, fun x => ?_⟩
  by_cases hz : 0 ≤ x 2
  · exact upper_aux m V D hD Λ hΛ x hz
  · have hz' : 0 ≤ mirror x 2 := by
      have : mirror x 2 = -(x 2) := (LinearSolveCore.mirror_apply x).2.2
      rw [this]
      linarith
    obtain ⟨hi, hb⟩ := upper_aux m V D hD Λ hΛ (mirror x) hz'
    have heq : (fun y => V y / (4 * Real.pi * ‖x - y‖)) =
        fun y => (fun w => V w / (4 * Real.pi * ‖mirror x - w‖)) (mirror y) := by
      funext y
      simp only
      rw [kernel_mirror_aux hD.mirror_even (mirror x) y, mirror_mirror_aux]
    rw [heq]
    exact ⟨(comp_mirror_aux _).2 hi, (integral_comp_mirror_aux (fun w => V w / (4 * Real.pi * ‖mirror x - w‖))).trans_le hb⟩

end Reduction

end CellCert

end Breakdown
