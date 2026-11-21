import Breakdown.CellReduction.InstanceStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

namespace Internal

theorem columnSquares_nonneg_aux (G : Space →L[ℝ] Space) : 0 ≤ matSq G :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem continuous_columnSquares_aux : Continuous matSq :=
  continuous_finsetSum _ fun _ _ => (continuous_id.clm_apply continuous_const).norm.pow 2

theorem continuous_columnPairing_aux :
    Continuous (fun p : (Space →L[ℝ] Space) × (Space →L[ℝ] Space) => matInner p.1 p.2) :=
  continuous_finsetSum _ fun _ _ =>
    (continuous_fst.clm_apply continuous_const).inner (continuous_snd.clm_apply continuous_const)

theorem abs_columnPairing_le_half (G K : Space →L[ℝ] Space) :
    |matInner G K| ≤ (matSq G + matSq K) / 2 := by
  unfold matInner matSq
  calc |∑ i : Fin 3, inner ℝ (G (unitVector i)) (K (unitVector i))|
      ≤ ∑ i : Fin 3, |inner ℝ (G (unitVector i)) (K (unitVector i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, (‖G (unitVector i)‖ ^ 2 + ‖K (unitVector i)‖ ^ 2) / 2 := by
        gcongr with i
        have h1 := abs_real_inner_le_norm (G (unitVector i)) (K (unitVector i))
        nlinarith [sq_nonneg (‖G (unitVector i)‖ - ‖K (unitVector i)‖)]
    _ = (∑ i : Fin 3, ‖G (unitVector i)‖ ^ 2 + ∑ i : Fin 3, ‖K (unitVector i)‖ ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]

theorem columnSquares_le_three_mul (G : Space →L[ℝ] Space) : matSq G ≤ 3 * ‖G‖ ^ 2 := by
  unfold matSq
  have h : ∀ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ‖G‖ ^ 2 := fun i => by
    have h1 : ‖G (unitVector i)‖ ≤ ‖G‖ := by
      have h2 := G.le_opNorm (unitVector i)
      have hu : ‖unitVector i‖ = 1 := by simp [unitVector]
      rw [hu, mul_one] at h2
      exact h2
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ∑ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖G‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖G‖ ^ 2 := by simp

def sliceInclusion (k : ℕ) : Space →L[ℝ] (Fin k → ℝ) × ℝ × Space :=
  (ContinuousLinearMap.inr ℝ (Fin k → ℝ) (ℝ × Space)).comp (ContinuousLinearMap.inr ℝ ℝ Space)

def jointField {k : ℕ} (W : (Fin k → ℝ) → ℝ → Space → Space) : (Fin k → ℝ) × ℝ × Space → Space :=
  fun z => W z.1 z.2.1 z.2.2

def slicePairing {k : ℕ} (W : (Fin k → ℝ) → ℝ → Space → Space) (χ : ℝ → Space → (Space →L[ℝ] Space))
    (q : Fin k → ℝ) (z : ℝ × Space) : ℝ :=
  matInner ((fderiv ℝ (jointField W) (q, z)).comp (sliceInclusion k)) (χ z.1 z.2)

theorem fderiv_slice_eq {k : ℕ} (W : (Fin k → ℝ) → ℝ → Space → Space)
    (hW : ContDiff ℝ 1 (jointField W)) (q : Fin k → ℝ) (σ : ℝ) (y : Space) :
    fderiv ℝ (W q σ) y = (fderiv ℝ (jointField W) (q, σ, y)).comp (sliceInclusion k) := by
  have hd := (hW.differentiable one_ne_zero (q, σ, y)).hasFDerivAt
  have hp : HasFDerivAt (fun y' : Space => ((q, σ, y') : (Fin k → ℝ) × ℝ × Space))
      (sliceInclusion k) y :=
    (hasFDerivAt_prodMk_right q (σ, y)).comp y (hasFDerivAt_prodMk_right σ y)
  exact (hd.comp y hp).fderiv

end Internal

open Internal in
theorem pinValueContinuous_holds : PinValueContinuousHolds := by
  intro k W χ S B hW hB hχ hfin
  have hW' : ContDiff ℝ 1 (jointField W) := hW
  have hG : ∀ q σ y, fderiv ℝ (W q σ) y = (fderiv ℝ (jointField W) (q, σ, y)).comp (sliceInclusion k) :=
    fun q σ y => fderiv_slice_eq W hW' q σ y
  have hGc : Continuous (fun p : (Fin k → ℝ) × ℝ × Space =>
      (fderiv ℝ (jointField W) p).comp (sliceInclusion k)) :=
    (hW'.continuous_fderiv one_ne_zero).clm_comp continuous_const
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have hμ : (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space) =
      (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    have h := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space))
      (Set.Icc (0 : ℝ) 1) Set.univ
    rw [Measure.restrict_univ] at h
    exact h
  have hχμ : AEStronglyMeasurable (fun z : ℝ × Space => χ z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    rw [hμ]
    exact hχ.restrict
  have hsqm : AEStronglyMeasurable (fun z : ℝ × Space => matSq (χ z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    continuous_columnSquares_aux.comp_aestronglyMeasurable hχμ
  have hsq : Integrable (fun z : ℝ × Space => matSq (χ z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    have hnn : (0 : ℝ × Space → ℝ) ≤ᵐ[(volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)]
        (fun z : ℝ × Space => matSq (χ z.1 z.2)) :=
      Filter.Eventually.of_forall fun z => by
        simp only [Pi.zero_apply]
        exact columnSquares_nonneg_aux _
    refine ⟨hsqm, (hasFiniteIntegral_iff_ofReal hnn).2 ?_⟩
    rw [lintegral_prod _ hsqm.aemeasurable.ennreal_ofReal]
    unfold periodLIntegral at hfin
    exact hfin
  have hdec : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) (volume : Measure Space) :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)
  have hb : Integrable (fun z : ℝ × Space =>
      (3 * B ^ 2 * (1 + ‖z.2‖) ^ (-(4 : ℝ)) + matSq (χ z.1 z.2)) / 2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    (((hdec.comp_snd (volume.restrict (Set.Icc (0 : ℝ) 1))).const_mul (3 * B ^ 2)).add hsq).div_const 2
  have hmeas : ∀ q, AEStronglyMeasurable (slicePairing W χ q)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := fun q => by
    have hc : Continuous (fun z : ℝ × Space => (fderiv ℝ (jointField W) (q, z)).comp (sliceInclusion k)) :=
      hGc.comp (Continuous.prodMk continuous_const continuous_id)
    have h1 : AEStronglyMeasurable (fun z : ℝ × Space => (fderiv ℝ (jointField W) (q, z)).comp (sliceInclusion k))
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := hc.aestronglyMeasurable
    have h2 := continuous_columnPairing_aux.comp_aestronglyMeasurable (h1.prodMk hχμ)
    unfold slicePairing
    exact h2
  have hbound : ∀ q ∈ S, ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)),
      ‖slicePairing W χ q z‖ ≤ (3 * B ^ 2 * (1 + ‖z.2‖) ^ (-(4 : ℝ)) + matSq (χ z.1 z.2)) / 2 := by
    intro q hq
    refine Filter.Eventually.of_forall fun z => ?_
    obtain ⟨σ, y⟩ := z
    have h1 := abs_columnPairing_le_half ((fderiv ℝ (jointField W) (q, σ, y)).comp (sliceInclusion k)) (χ σ y)
    have hn := hB q hq σ y
    rw [hG q σ y] at hn
    have hpos : 0 < 1 + ‖y‖ := by positivity
    have hr : (1 + ‖y‖) ^ (-(4 : ℝ)) = ((1 + ‖y‖) ^ 4)⁻¹ := by
      rw [Real.rpow_neg hpos.le]
      norm_cast
    have hsq2 : ‖(fderiv ℝ (jointField W) (q, σ, y)).comp (sliceInclusion k)‖ ^ 2 ≤
        (B / (1 + ‖y‖) ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    have h2 : matSq ((fderiv ℝ (jointField W) (q, σ, y)).comp (sliceInclusion k)) ≤
        3 * B ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
      calc matSq ((fderiv ℝ (jointField W) (q, σ, y)).comp (sliceInclusion k))
          ≤ 3 * ‖(fderiv ℝ (jointField W) (q, σ, y)).comp (sliceInclusion k)‖ ^ 2 :=
            columnSquares_le_three_mul _
        _ ≤ 3 * (B / (1 + ‖y‖) ^ 2) ^ 2 := by gcongr
        _ = 3 * B ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by rw [hr, div_pow]; ring
    rw [Real.norm_eq_abs]
    unfold slicePairing
    dsimp only
    linarith
  have hcont : ContinuousOn (fun q => ∫ z, slicePairing W χ q z
      ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) S := by
    refine continuousOn_of_dominated (fun q _ => hmeas q) hbound hb ?_
    refine Filter.Eventually.of_forall fun z => ?_
    have hc : Continuous (fun q : Fin k → ℝ => (fderiv ℝ (jointField W) (q, z)).comp (sliceInclusion k)) :=
      hGc.comp (Continuous.prodMk continuous_id continuous_const)
    have h3 := (continuous_columnPairing_aux.comp (hc.prodMk (continuous_const (y := χ z.1 z.2)))).continuousOn (s := S)
    unfold slicePairing
    exact h3
  refine hcont.congr fun q hq => ?_
  have hint : Integrable (slicePairing W χ q)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    hb.mono' (hmeas q) (hbound q hq)
  unfold pinValue
  simp only [hG]
  rw [integral_prod _ hint]
  simp only [slicePairing]

end Instantiation

end CellReduction

end Breakdown
