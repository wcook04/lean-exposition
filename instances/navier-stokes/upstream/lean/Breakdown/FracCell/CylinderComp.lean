import Breakdown.FracCell.MeshFarRegular
import Breakdown.FracCell.LowEntry

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.CylinderCompInternal

open LowEntry.Internal

theorem shift_mp (c : ℝ) :
    MeasurePreserving (Prod.map (id : ℝ × ℝ → ℝ × ℝ) (fun t : ℝ => t - c))
      (volume : Measure ((ℝ × ℝ) × ℝ)) volume :=
  (MeasurePreserving.id volume).prod (measurePreserving_sub_right volume c)

theorem flip_mp (c : ℝ) :
    MeasurePreserving (Prod.map (Prod.map (fun r : ℝ => -r) (id : ℝ → ℝ)) (fun t : ℝ => t - c))
      (volume : Measure ((ℝ × ℝ) × ℝ)) volume :=
  ((Measure.measurePreserving_neg volume).prod (MeasurePreserving.id volume)).prod
    (measurePreserving_sub_right volume c)

theorem axis_null : (volume : Measure ((ℝ × ℝ) × ℝ)) {q | q.1.1 = 0} = 0 := by
  have e : {q : (ℝ × ℝ) × ℝ | q.1.1 = 0} = ({0} ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ) := by
    ext q; simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_singleton, zero_mul, zero_mul]

theorem angle_null : (volume : Measure ((ℝ × ℝ) × ℝ)) {q | ∃ k : ℤ, q.2 = k * π} = 0 := by
  have e : {q : (ℝ × ℝ) × ℝ | ∃ k : ℤ, q.2 = k * π} =
      (univ : Set (ℝ × ℝ)) ×ˢ range (fun k : ℤ => (k : ℝ) * π) := by
    ext q; simp [eq_comm]
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, (countable_range _).measure_zero, mul_zero]

theorem qmp_full : Measure.QuasiMeasurePreserving cylArg (volume : Measure ((ℝ × ℝ) × ℝ)) volume := by
  refine ⟨cylArg_meas, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply cylArg_meas hs]
  set U : Set ((ℝ × ℝ) × ℝ) := (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-π) π with hU
  have hA : volume (cylArg ⁻¹' s ∩ U) = 0 := by
    have h1 := qmp.preimage_null h0
    rw [muU_eq, Measure.restrict_apply (cylArg_meas hs)] at h1
    exact h1
  have hAm : MeasurableSet (cylArg ⁻¹' s ∩ U) :=
    (cylArg_meas hs).inter ((measurableSet_Ioi.prod MeasurableSet.univ).prod measurableSet_Ioo)
  have hsub : cylArg ⁻¹' s ⊆ ({q | q.1.1 = 0} ∪ {q | ∃ k : ℤ, q.2 = k * π}) ∪
      ((⋃ n : ℤ, Prod.map (id : ℝ × ℝ → ℝ × ℝ) (fun t : ℝ => t - n * (2 * π)) ⁻¹' (cylArg ⁻¹' s ∩ U)) ∪
       (⋃ n : ℤ, Prod.map (Prod.map (fun r : ℝ => -r) (id : ℝ → ℝ)) (fun t : ℝ => t - (π + n * (2 * π))) ⁻¹'
          (cylArg ⁻¹' s ∩ U))) := by
    intro q hq
    obtain ⟨⟨r, z⟩, θ⟩ := q
    by_cases hr : r = 0
    · exact Or.inl (Or.inl hr)
    by_cases hk : ∃ k : ℤ, θ = k * π
    · exact Or.inl (Or.inr hk)
    push Not at hk
    refine Or.inr ?_
    rcases lt_or_gt_of_ne hr with hneg | hpos
    · refine Or.inr (mem_iUnion.2 ⟨toIocDiv two_pi_pos (-π) (θ - π), ?_⟩)
      set n := toIocDiv two_pi_pos (-π) (θ - π)
      have hm := toIocMod_mem_Ioc two_pi_pos (-π) (θ - π)
      have he := self_sub_toIocDiv_zsmul two_pi_pos (-π) (θ - π)
      rw [zsmul_eq_mul] at he
      have hlt : θ - π - n * (2 * π) < π := by
        rw [he]
        refine lt_of_le_of_ne (by linarith [hm.2]) ?_
        intro h
        apply hk (2 * n + 2)
        rw [← he] at h
        push_cast
        linarith
      refine ⟨?_, ⟨⟨?_, trivial⟩, ?_, ?_⟩⟩
      · show cylPoint (-r) (θ - (π + n * (2 * π))) z ∈ s
        have e : cylPoint (-r) (θ - (π + n * (2 * π))) z = cylPoint r θ z := by
          have e1 : θ - (π + n * (2 * π)) = (θ - n * (2 * π)) - π := by ring
          unfold cylPoint
          rw [e1, Real.cos_sub_pi, Real.sin_sub_pi, Real.cos_sub_int_mul_two_pi,
            Real.sin_sub_int_mul_two_pi, neg_mul_neg, neg_mul_neg]
        rw [e]; exact hq
      · show 0 < -r
        linarith
      · show -π < θ - (π + n * (2 * π))
        have := hm.1
        rw [← he] at this
        linarith
      · show θ - (π + n * (2 * π)) < π
        linarith
    · refine Or.inl (mem_iUnion.2 ⟨toIocDiv two_pi_pos (-π) θ, ?_⟩)
      set n := toIocDiv two_pi_pos (-π) θ
      have hm := toIocMod_mem_Ioc two_pi_pos (-π) θ
      have he := self_sub_toIocDiv_zsmul two_pi_pos (-π) θ
      rw [zsmul_eq_mul] at he
      have hlt : θ - n * (2 * π) < π := by
        rw [he]
        refine lt_of_le_of_ne (by linarith [hm.2]) ?_
        intro h
        apply hk (2 * n + 1)
        rw [← he] at h
        push_cast
        linarith
      refine ⟨?_, ⟨⟨?_, trivial⟩, ?_, hlt⟩⟩
      · show cylPoint r (θ - n * (2 * π)) z ∈ s
        have e : cylPoint r (θ - n * (2 * π)) z = cylPoint r θ z := by
          unfold cylPoint
          rw [Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]
        rw [e]; exact hq
      · exact hpos
      · show -π < θ - n * (2 * π)
        have := hm.1
        rw [← he] at this
        linarith
  refine measure_mono_null hsub (measure_union_null (measure_union_null axis_null angle_null)
    (measure_union_null (measure_iUnion_null fun n => ?_) (measure_iUnion_null fun n => ?_)))
  · rw [(shift_mp _).measure_preimage hAm.nullMeasurableSet]; exact hA
  · rw [(flip_mp _).measure_preimage hAm.nullMeasurableSet]; exact hA

end Breakdown.CellCert.CellAnalysis.CylinderCompInternal

namespace Breakdown.CellCert.CellAnalysis

theorem cylinderComp : CylinderCompStatement := by
  intro f hf
  exact hf.comp_quasiMeasurePreserving CylinderCompInternal.qmp_full
