import Breakdown.CertCell.InstanceGeneratorForm
import Breakdown.CertCell.InstanceMomentUpper

open MeasureTheory

noncomputable section

namespace Breakdown.CertCell.Instance

open Breakdown Breakdown.CertCell
open Breakdown.CellCert.CellAnalysis (CellBox IsCellBox cylRadius cylHeight)

namespace Internal.MomentLower

def lowerSet (K : CellBox) : Set (ℝ × ℝ) := {p | p.2 < 0 ∧ (p.1, -p.2) ∈ K.rect}

def lowerCoef {count rowCount : ℕ} (R : RowValues count rowCount) (box : Fin count → CellBox) (a : Fin rowCount)
    (p : ℝ × ℝ) (c : Fin 3) : ℂ :=
  (frameSign c : ℂ) * rowPartFactor (R.realPart a) * R.testValue box a c (p.1, -p.2)

theorem lower_indicator_eq {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ)
    (a : Fin rowCount) (σ : ℝ) (y : Space) :
    Set.indicator {y : Space | y 2 < 0} (R.generatorField M.box m a σ) y =
      Set.indicator {y | pointPlane y ∈ lowerSet (M.box (R.cellOf a))} (fun y => ∑ c : Fin 3,
        (labelPhase m (labelFlip (R.labelOf a)) σ (pointAngle y) *
          lowerCoef R M.box a (pointPlane y) c).re • frameUnit (pointAngle y) c) y := by
  by_cases hy : y 2 < 0
  · have hz : ¬ 0 ≤ y 2 := not_le.2 hy
    rw [Set.indicator_of_mem (show y ∈ {y : Space | y 2 < 0} from hy), generatorField_eq]
    have hmem : y ∈ (M.box (R.cellOf a)).solid ↔ pointPlane y ∈ lowerSet (M.box (R.cellOf a)) := by
      simp only [CellBox.solid, lowerSet, CellBox.rect, pointPlane, cylHeight, Set.mem_ofPred_eq,
        Set.mem_prod, Set.mem_Icc, abs_of_neg hy]
      tauto
    by_cases hs : y ∈ (M.box (R.cellOf a)).solid
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show y ∈ {y | pointPlane y ∈ lowerSet _} from hmem.1 hs)]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [if_neg hz, lowerCoef]
    · rw [Set.indicator_of_notMem hs,
        Set.indicator_of_notMem (show y ∉ {y | pointPlane y ∈ lowerSet _} from fun h => hs (hmem.2 h))]
  · rw [Set.indicator_of_notMem (show y ∉ {y : Space | y 2 < 0} from hy),
      Set.indicator_of_notMem (show y ∉ {y | pointPlane y ∈ lowerSet (M.box (R.cellOf a))} from
        fun h => hy h.1)]

theorem continuous_lowerCoef {count rowCount : ℕ} (R : RowValues count rowCount) (box : Fin count → CellBox)
    (a : Fin rowCount) (c : Fin 3) : Continuous fun p => lowerCoef R box a p c := by
  unfold lowerCoef RowValues.testValue CellPoly.eval CellBox.refR CellBox.refZ
  fun_prop

def heightFlip : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ)

theorem heightFlip_apply (q : ℝ × ℝ) : heightFlip q = (q.1, -q.2) := rfl

theorem heightFlip_mp : MeasurePreserving heightFlip volume volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg (volume : Measure ℝ))
  rw [← Measure.volume_eq_prod] at h
  exact h

theorem lowerSet_sub_image (K : CellBox) : lowerSet K ⊆ heightFlip '' K.rect := by
  intro p hp
  exact ⟨(p.1, -p.2), hp.2, by simp [heightFlip_apply]⟩

theorem isCompact_image (K : CellBox) : IsCompact (heightFlip '' K.rect) :=
  (isCompact_Icc.prod isCompact_Icc).image (by
    show Continuous fun q : ℝ × ℝ => heightFlip q
    simp only [heightFlip_apply]
    fun_prop)

theorem measurableSet_lowerSet (K : CellBox) : MeasurableSet (lowerSet K) := by
  have h1 : MeasurableSet {p : ℝ × ℝ | p.2 < 0} := measurableSet_lt measurable_snd measurable_const
  have h2 : MeasurableSet {p : ℝ × ℝ | (p.1, -p.2) ∈ K.rect} :=
    (measurableSet_Icc.prod measurableSet_Icc).preimage (by fun_prop)
  exact h1.inter h2

theorem null_height_zero : volume {q : ℝ × ℝ | q.2 = 0} = 0 := by
  have e : {q : ℝ × ℝ | q.2 = 0} = Set.univ ×ˢ {0} := by
    ext q; simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

theorem preimage_ae_rect (K : CellBox) (hK : IsCellBox K) :
    (heightFlip ⁻¹' lowerSet K : Set (ℝ × ℝ)) =ᵐ[volume] K.rect := by
  refine (ae_eq_set).2 ⟨?_, ?_⟩
  · refine measure_mono_null (fun q hq => ?_) measure_empty
    obtain ⟨⟨_, h2⟩, h3⟩ := hq
    simp only [heightFlip_apply, neg_neg] at h2
    exact absurd h2 h3
  · refine measure_mono_null (fun q hq => ?_) null_height_zero
    obtain ⟨h1, h2⟩ := hq
    have hz : 0 ≤ q.2 := le_trans hK.z_order.1 (Set.mem_prod.1 h1).2.1
    have hn : ¬ (0 < q.2) := fun h => h2 ⟨by simp [heightFlip_apply]; exact h, by simp [heightFlip_apply]; exact h1⟩
    show q.2 = 0
    linarith [not_lt.1 hn]

theorem lower_pairing {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ)
    (hM : IsCellMesh M) (F : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (a : Fin rowCount) :
    periodPairing F (fun σ y => Set.indicator {y : Space | y 2 < 0} (R.generatorField M.box m a σ) y) =
      R.lowerMoment M.box m a F := by
  set K := M.box (R.cellOf a) with hKdef
  have hK : IsCellBox K := hM.box_valid _
  have hfun : (fun σ y => Set.indicator {y : Space | y 2 < 0} (R.generatorField M.box m a σ) y) =
      fun σ y => Set.indicator {y | pointPlane y ∈ lowerSet K} (fun y => ∑ c : Fin 3,
        (labelPhase m (labelFlip (R.labelOf a)) σ (pointAngle y) *
          lowerCoef R M.box a (pointPlane y) c).re • frameUnit (pointAngle y) c) y := by
    funext σ y
    exact lower_indicator_eq M R m a σ y
  obtain ⟨C, hC⟩ := (isCompact_image K).exists_bound_of_continuousOn
    (f := fun p => ∑ c : Fin 3, ‖lowerCoef R M.box a p c‖)
    (continuous_finsetSum _ fun c _ => (continuous_lowerCoef R M.box a c).norm).continuousOn
  have hCb : ∀ p ∈ lowerSet K, ∀ c, ‖lowerCoef R M.box a p c‖ ≤ C := by
    intro p hp c
    have h1 := hC p (lowerSet_sub_image K hp)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
    exact (Finset.single_le_sum (f := fun c => ‖lowerCoef R M.box a p c‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ c)).trans h1
  have hS0 : lowerSet K ⊆ {p | 0 ≤ p.1} := fun p hp =>
    le_trans hK.r_order.1 (Set.mem_prod.1 hp.2).1.1
  rw [hfun, pairing_planeSet_moment F hFm hF2 m (labelFlip (R.labelOf a)) (lowerSet K) (measurableSet_lowerSet K)
    ((isCompact_image K).isBounded.subset (lowerSet_sub_image K)) hS0 (lowerCoef R M.box a)
    (fun c => (continuous_lowerCoef R M.box a c).measurable) C hCb]
  unfold RowValues.lowerMoment
  congr 1
  rw [← heightFlip_mp.setIntegral_preimage_emb heightFlip.measurableEmbedding, setIntegral_congr_set
    (preimage_ae_rect K hK)]
  refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) fun q _ => ?_
  simp only [heightFlip_apply, lowerCoef, neg_neg, Prod.mk.eta]
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end Internal.MomentLower

theorem generator_lower_pairing {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (tauMax : ℝ)
    (hR : IsRowValues M R m tauMax) (F : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hFp : IsTimePeriodic F) (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (a : Fin rowCount) :
    periodPairing F (fun σ y => Set.indicator {y : Space | y 2 < 0} (R.generatorField M.box m a σ) y) =
      R.lowerMoment M.box m a F :=
  Internal.MomentLower.lower_pairing M R m hR.mesh_valid F hFm hF2 a

end Breakdown.CertCell.Instance
