import Breakdown.CertCell.CreditEvalStatements
import Breakdown.CertCell.ModeConjugate

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Internal

theorem setIntegral_le_sum_inter_of_cover {ι : Type*} [Fintype ι] {s : Set (ℝ × ℝ)} {t : ι → Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (ht : ∀ i, MeasurableSet (t i)) (hcov : s ⊆ ⋃ i, t i)
    {f : ℝ × ℝ → ℝ} (hf : ∀ p ∈ s, 0 ≤ f p) :
    ∫ p in s, f p ≤ ∑ i, ∫ p in s ∩ t i, f p := by
  by_cases hint : IntegrableOn f s volume
  · have each : ∀ i, IntegrableOn f (s ∩ t i) volume := fun i => hint.mono_set Set.inter_subset_left
    have hnn : ∀ i, 0 ≤ᵐ[volume.restrict (s ∩ t i)] f := fun i =>
      ae_restrict_of_forall_mem (hs.inter (ht i)) (fun p hp => hf p hp.1)
    have hfin : ∀ i, ∫⁻ p in s ∩ t i, ENNReal.ofReal (f p) ≠ ⊤ := fun i =>
      (Integrable.lintegral_lt_top (each i)).ne
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hs hf) hint.aestronglyMeasurable]
    rw [Finset.sum_congr rfl (fun i _ => integral_eq_lintegral_of_nonneg_ae (hnn i) (each i).aestronglyMeasurable)]
    rw [← ENNReal.toReal_sum (fun i _ => hfin i)]
    apply ENNReal.toReal_mono (ENNReal.sum_ne_top.2 (fun i _ => hfin i))
    have hsub : s ⊆ ⋃ i, s ∩ t i := by
      intro p hp
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hp)
      exact Set.mem_iUnion.2 ⟨i, hp, hi⟩
    calc ∫⁻ p in s, ENNReal.ofReal (f p)
        ≤ ∫⁻ p in ⋃ i, s ∩ t i, ENNReal.ofReal (f p) := lintegral_mono_set hsub
      _ ≤ ∑' i, ∫⁻ p in s ∩ t i, ENNReal.ofReal (f p) := lintegral_iUnion_le _ _
      _ = ∑ i, ∫⁻ p in s ∩ t i, ENNReal.ofReal (f p) := tsum_fintype _
  · rw [integral_undef hint]
    exact Finset.sum_nonneg fun i _ => setIntegral_nonneg (hs.inter (ht i)) (fun p hp => hf p hp.1)

end Internal

theorem creditLeavesBound (hP : Bridge.CreditPatchBoundHolds) (hR : CreditEval.CreditEvalMatchesHolds) :
    CreditEval.CreditLeavesBoundHolds := by
  intro k C nE nM D R _hmesh hclass hchk q hq v G H g hpert Pg κ ζ η
  have hconj : ∀ (ξ : ℤ × ℤ) (p : ℝ × ℝ),
      cnormSq (modeVel (-ξ) v 0 (planePoint p)) = cnormSq (modeVel ξ v 0 (planePoint p)) := by
    intro ξ p
    rw [(Bridge.modeConjugate v G H ξ 0 (planePoint p)).1]
    unfold cnormSq
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Pi.star_apply, norm_star]
  have hbound : ∑ j, Coupling.quadForm (R.creditPatch j).credit (CreditEval.creditData D R j v G H Pg κ ζ η)
      ≤ ∑ j, ∑ K, ∫ p in (R.creditPatch j).region ∩ (D.mesh.box K).rect,
        (R.creditPatch j).charge p * cnormSq (modeVel (flipLabel (R.creditPatch j).label) v 0 (planePoint p)) * p.1 := by
    calc _ ≤ ∑ j, ∫ p in (R.creditPatch j).region,
          (R.creditPatch j).charge p * cnormSq (modeVel (flipLabel (R.creditPatch j).label) v 0 (planePoint p)) * p.1 :=
          Finset.sum_le_sum fun j _ => by
            rw [hR D R hchk q hq v G H g hpert Pg κ ζ η j]
            exact hP _ (hchk.patches_valid j) _ _ v G H g hpert hclass.flip
      _ ≤ _ :=
          Finset.sum_le_sum fun j _ => by
            have hv := hchk.patches_valid j
            apply Internal.setIntegral_le_sum_inter_of_cover
            · exact measurableSet_Icc.prod measurableSet_Icc
            · intro K
              exact measurableSet_Icc.prod measurableSet_Icc
            · exact hchk.region_in_mesh j
            · intro p hp
              have h1 : (R.creditPatch j).inner ≤ p.1 := hp.1.1
              have hc : 0 < (R.creditPatch j).charge p :=
                lt_of_lt_of_le hv.charge_lower_pos (hv.charge_between p).1
              have hn : 0 ≤ cnormSq (modeVel (flipLabel (R.creditPatch j).label) v 0 (planePoint p)) :=
                Finset.sum_nonneg fun b _ => sq_nonneg _
              have hr : 0 ≤ p.1 := le_trans hv.inner_pos.le h1
              positivity
  calc _ ≤ 2 * ∑ j, ∑ K, ∫ p in (R.creditPatch j).region ∩ (D.mesh.box K).rect,
        (R.creditPatch j).charge p * cnormSq (modeVel (flipLabel (R.creditPatch j).label) v 0 (planePoint p)) * p.1 :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = ∑ j, ∑ K, ∫ p in (R.creditPatch j).region ∩ (D.mesh.box K).rect,
        (R.creditPatch j).charge p * (cnormSq (modeVel (flipLabel (R.creditPatch j).label) v 0 (planePoint p))
          + cnormSq (modeVel (-(flipLabel (R.creditPatch j).label)) v 0 (planePoint p))) * p.1 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun K _ => ?_
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        dsimp only
        rw [hconj]
        ring
    _ = _ := by
        rw [Finset.sum_comm]
        rfl

end CertCell

end Breakdown
