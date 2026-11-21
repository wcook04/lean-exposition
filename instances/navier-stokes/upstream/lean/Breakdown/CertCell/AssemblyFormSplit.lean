import Breakdown.CertCell.AssemblyStatements

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

theorem axes_null : volume (CellMesh.closedHalfPlane \ halfPlane) = 0 := by
  have hsub : CellMesh.closedHalfPlane \ halfPlane ⊆
      (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) ∪ ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)) := by
    rintro ⟨a, b⟩ ⟨⟨ha, hb⟩, hn⟩
    simp only [Set.mem_Ici] at ha hb
    simp only [halfPlane, Set.mem_prod, Set.mem_Ioi, not_and_or, not_lt] at hn
    rcases hn with h | h
    · exact Or.inl ⟨le_antisymm h ha, Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _, le_antisymm h hb⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  · rw [Measure.volume_eq_prod, Measure.prod_prod]; simp

theorem rect_sub (K : CellCert.CellAnalysis.CellBox) (hK : CellCert.CellAnalysis.IsCellBox K) :
    K.rect ⊆ CellMesh.closedHalfPlane := by
  rintro ⟨a, b⟩ ⟨⟨ha, _⟩, ⟨hb, _⟩⟩
  exact ⟨le_trans hK.r_order.1 ha, le_trans hK.z_order.1 hb⟩

theorem rect_measurable (K : CellCert.CellAnalysis.CellBox) : MeasurableSet K.rect :=
  measurableSet_Icc.prod measurableSet_Icc

theorem lintegral_halfPlane_split (M : CellMesh) (hM : IsCellMesh M) (f : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in halfPlane, f p) = (∑ K, ∫⁻ p in (M.box K).rect, f p) + ∫⁻ p in M.exterior ∩ halfPlane, f p := by
  have hR : MeasurableSet M.region := MeasurableSet.iUnion fun K => rect_measurable (M.box K)
  have hdiff : halfPlane \ M.region = M.exterior ∩ halfPlane := by
    ext p
    constructor
    · rintro ⟨hp, hn⟩
      refine ⟨⟨?_, hn⟩, hp⟩
      exact ⟨Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hp.1)), Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hp.2))⟩
    · rintro ⟨⟨_, hn⟩, hp⟩
      exact ⟨hp, hn⟩
  have hae : (halfPlane ∩ M.region : Set (ℝ × ℝ)) =ᵐ[volume] M.region := by
    rw [ae_eq_set]
    constructor
    · rw [Set.sdiff_eq_empty.mpr Set.inter_subset_right]; exact measure_empty
    · refine measure_mono_null ?_ axes_null
      rintro p ⟨hp, hn⟩
      obtain ⟨K, hK⟩ := Set.mem_iUnion.mp hp
      exact ⟨rect_sub (M.box K) (hM.box_valid K) hK, fun h => hn ⟨h, hp⟩⟩
  have hunion : (∫⁻ p in M.region, f p) = ∑ K, ∫⁻ p in (M.box K).rect, f p := by
    rw [CellMesh.region, lintegral_iUnion₀ (fun K => (rect_measurable (M.box K)).nullMeasurableSet)
      (fun K L hKL => hM.boxes_apart K L hKL), tsum_fintype]
  rw [← lintegral_inter_add_sdiff f halfPlane hR, hdiff, setLIntegral_congr hae, hunion]

theorem regroup {ι : Type} {n : ℕ} (a : ι → Fin n → ℝ≥0∞) (e : ι → ℝ≥0∞) (b : Fin n → ℝ≥0∞) (e' : ℝ≥0∞) :
    (∑' i, ((∑ K, a i K) + e i)) + ((∑ K, b K) + e') = (∑ K, ((∑' i, a i K) + b K)) + ((∑' i, e i) + e') := by
  rw [ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), Finset.sum_add_distrib,
    add_add_add_comm]

end Internal

open CellCalculus in
theorem formSplit_holds : FormSplitHolds := by
  intro k C nE nM D hM q v G H
  have hs := Internal.lintegral_halfPlane_split D.mesh hM
  constructor
  · simp only [CellLayerData.formPos, hs]
    exact Internal.regroup _ _ _ _
  · simp only [CellLayerData.formNeg, hs]
    exact Internal.regroup _ _ _ _

end Assembly

end CertCell

end Breakdown
