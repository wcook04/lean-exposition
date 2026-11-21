import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.HeldLimit

open scoped ENNReal Topology NNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

open Internal.HeldLimit in
theorem extendedHeldLimitHolds_of (h1 : PeriodContinuityHolds) (h2 : LocalCompactnessHolds)
    (h3 : ExtendedConvectionContinuityHolds) (h4 : ExtendedDataContinuityHolds)
    (h5 : ProductPairingHolds) (h6 : ProductBoundHolds) (h9 : FreeInvHolds)
    (h11 : ExtendedDataHolds) (h12 : ReadingExistsHolds) (h13 : TestDenseHolds) :
    ExtendedHeldLimitHolds := by
  intro k d hd p q hp hq hpq f κ hsol
  have hwpos : ∀ y, 0 ≤ d.weightFn y := fun y => hd.weight_pos.le.trans (hd.weightFn_lower y)
  have hadm : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, d.weightMax, hd.weightFn_upper⟩
  have hS0 := hd.supBound_pos.le
  have hB0 := hd.sizeBound_nonneg
  have hsupfin : ∀ n, supGrad (freeInv (d.period (p n)) (f n)) < ⊤ :=
    fun n => lt_of_le_of_lt (hsol n).sup ENNReal.ofReal_lt_top
  have hsupR : ∀ n, (supGrad (freeInv (d.period (p n)) (f n))).toReal ≤ d.supBound :=
    fun n => ENNReal.toReal_le_of_le_ofReal hS0 (hsol n).sup
  have hE : ∀ n, Real.sqrt (energyW d.weightFn (freeInv (d.period (p n)) (f n))) ≤
      2 * d.sizeBound :=
    fun n => (sqrt_energyW_le_sizeZ _ _ (κ n)).trans (hsol n).size
  have hsec : ∀ n, ‖secondCLM (freeInv (d.period (p n)) (f n))‖ ≤ 2 * d.sizeBound := by
    intro n
    calc ‖secondCLM (freeInv (d.period (p n)) (f n))‖
        = Real.sqrt (‖secondCLM (freeInv (d.period (p n)) (f n))‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (energyW d.weightFn (freeInv (d.period (p n)) (f n))) :=
          Real.sqrt_le_sqrt (secondCLM_sq_le hwpos _)
      _ ≤ _ := hE n
  have hgr : ∀ n, ‖gradCLM (freeInv (d.period (p n)) (f n))‖ ≤ d.supBound :=
    fun n => (gradCLM_norm_le _ (hsupfin n)).trans (hsupR n)
  have hub : ∀ n, ‖freeInv (d.period (p n)) (f n)‖ ≤ d.supBound + 2 * d.sizeBound :=
    fun n => (norm_le_add _).trans (add_le_add (hgr n) (hsec n))
  have hvκ : ∀ n, vecNorm (κ n) ≤ 2 * d.sizeBound :=
    fun n => (vecNorm_le_sizeZ hwpos _ _).trans (hsol n).size
  have hpw : Tendsto p atTop (𝓝[d.params] q) :=
    tendsto_nhdsWithin_iff.2 ⟨hpq, Eventually.of_forall hp⟩
  have hconvT : Tendsto (fun n => convection d.toCertificateData (p n)) atTop
      (𝓝 (convection d.toCertificateData q)) :=
    ((h3 d hd) q hq).tendsto.comp hpw
  obtain ⟨Cc, hCc0, hCc⟩ := exists_bound_of_tendsto _ _ hconvT
  have hag : 0 ≤ supBoundFactor d.weight := by
    unfold supBoundFactor
    positivity
  have hfb : ∀ n, ‖f n‖ ≤ Cc * (d.supBound + 2 * d.sizeBound) + d.actuatorBound * (2 * d.sizeBound)
      + supBoundFactor d.weight * (2 * d.sizeBound) * d.supBound + d.defectMax := by
    intro n
    have hD := h11 d hd (p n) (hp n)
    have e1 : ‖convection d.toCertificateData (p n) (freeInv (d.period (p n)) (f n))‖ ≤
        Cc * (d.supBound + 2 * d.sizeBound) :=
      (hCc n _).trans (mul_le_mul_of_nonneg_left (hub n) hCc0)
    have e2 : ‖actuatorH d.toCertificateData (κ n)‖ ≤ d.actuatorBound * (2 * d.sizeBound) :=
      (hD.2.2.2.2.1 (κ n)).trans (mul_le_mul_of_nonneg_left (hvκ n) hd.actuatorBound_nonneg)
    have e3 : ‖productH (freeInv (d.period (p n)) (f n)) (freeInv (d.period (p n)) (f n))‖ ≤
        supBoundFactor d.weight * (2 * d.sizeBound) * d.supBound :=
      ((h6 _ _ hadm _ _ (hsupfin n)).2.2).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hE n) hag)
        (hsupR n) ENNReal.toReal_nonneg (mul_nonneg hag (by linarith)))
    have e4 : ‖d.defectH (p n)‖ ≤ d.defectMax := hD.2.2.1.trans (hd.defect_le _ (hp n))
    exact (norm_le_of_add_eq_zero (hsol n).equation).trans
      (add_le_add (add_le_add (add_le_add e1 e2) e3) e4)
  obtain ⟨s1, f₀, hs1, -, hw1⟩ := exists_weakly_convergent_subseq f _ hfb
  obtain ⟨κ₀, -, s2, hs2, hκ2⟩ := tendsto_subseq_of_bounded
    (Metric.isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := 2 * d.sizeBound))
    (x := fun n => κ (s1 n))
    (fun n => mem_closedBall_zero_iff.2 ((norm_le_vecNorm _).trans (hvκ (s1 n))))
  have hsub : insert q (Set.range p) ⊆ d.params :=
    Set.insert_subset_iff.2 ⟨hq, Set.range_subset_iff.2 hp⟩
  obtain ⟨pm, hpm, hmin⟩ := hpq.isCompact_insert_range.exists_isMinOn
    (Set.insert_nonempty q (Set.range p)) (hd.period_continuous.mono hsub)
  have hpa : ∀ n, d.period (p n) ∈ Set.Icc (d.period pm) d.periodMax :=
    fun n => ⟨isMinOn_iff.1 hmin _ (Set.mem_insert_of_mem _ (Set.mem_range_self n)),
      hd.period_le _ (hp n)⟩
  have hPt : Tendsto (fun n => d.period (p n)) atTop (𝓝 (d.period q)) :=
    (hd.period_continuous q hq).tendsto.comp hpw
  obtain ⟨s3, hs3, hprod⟩ := tendsto_inner_productH h1 h2 h5 h9 h12 (d.period pm) d.periodMax
    d.supBound (hd.period_pos pm (hsub hpm)) (fun n => d.period (p (s1 (s2 n)))) (d.period q)
    (fun n => f (s1 (s2 n))) f₀ (fun n => hpa _) (hPt.comp (hs1.comp hs2).tendsto_atTop) _
    (fun n => hfb _) (fun y => (hw1 y).comp hs2.tendsto_atTop) (fun n => (hsol _).sup)
  have hs : StrictMono (fun n => s1 (s2 (s3 n))) := hs1.comp (hs2.comp hs3)
  have hwf : ∀ y, Tendsto (fun n => inner ℝ (f (s1 (s2 (s3 n)))) y) atTop (𝓝 (inner ℝ f₀ y)) :=
    fun y => ((hw1 y).comp hs2.tendsto_atTop).comp hs3.tendsto_atTop
  have hκ : Tendsto (fun n => κ (s1 (s2 (s3 n)))) atTop (𝓝 κ₀) := hκ2.comp hs3.tendsto_atTop
  have hps : Tendsto (fun n => p (s1 (s2 (s3 n)))) atTop (𝓝[d.params] q) :=
    hpw.comp hs.tendsto_atTop
  have hwu : ∀ y, Tendsto (fun n => inner ℝ (freeInv (d.period (p (s1 (s2 (s3 n)))))
      (f (s1 (s2 (s3 n))))) y) atTop (𝓝 (inner ℝ (freeInv (d.period q) f₀) y)) :=
    h1 (fun n => d.period (p (s1 (s2 (s3 n))))) (d.period q) (fun n => f (s1 (s2 (s3 n)))) f₀
      (hd.period_pos q hq) (fun n => hd.period_pos _ (hp _)) (hPt.comp hs.tendsto_atTop)
      ⟨_, fun n => hfb _⟩ hwf
  refine ⟨fun n => s1 (s2 (s3 n)), hs, f₀, κ₀, ⟨?_, ?_, ?_, ?_, ?_⟩, hκ⟩
  · exact mem_of_weak_limit (invariantHH d.symmetries : Set HH) (Submodule.convex _)
      (isClosed_invariantHH _) (fun n => f (s1 (s2 (s3 n)))) (fun n => (hsol _).invariant) f₀ hwf
  · apply h13
    intro g hg
    have hA := hwf (testInHH g)
    have hB := tendsto_inner_clm_apply (fun n => convection d.toCertificateData (p (s1 (s2 (s3 n)))))
      (convection d.toCertificateData q) _ _ _ (hconvT.comp hs.tendsto_atTop) (fun n => hub _) hwu
      (testInHH g)
    have hC : Tendsto (fun n => inner ℝ (actuatorH d.toCertificateData (κ (s1 (s2 (s3 n)))))
        (testInHH g)) atTop (𝓝 (inner ℝ (actuatorH d.toCertificateData κ₀) (testInHH g))) :=
      (((actuatorH d.toCertificateData).continuous.tendsto κ₀).comp hκ).inner tendsto_const_nhds
    have hDf : Tendsto (fun n => inner ℝ (d.defectH (p (s1 (s2 (s3 n))))) (testInHH g)) atTop
        (𝓝 (inner ℝ (d.defectH q) (testInHH g))) :=
      (((h4 d hd).2 g hg) q hq).tendsto.comp hps
    exact inner_sum_eq_zero_of_tendsto (testInHH g) (fun n => f (s1 (s2 (s3 n))))
      (fun n => convection d.toCertificateData (p (s1 (s2 (s3 n))))
        (freeInv (d.period (p (s1 (s2 (s3 n))))) (f (s1 (s2 (s3 n))))))
      (fun n => actuatorH d.toCertificateData (κ (s1 (s2 (s3 n)))))
      (fun n => productH (freeInv (d.period (p (s1 (s2 (s3 n))))) (f (s1 (s2 (s3 n)))))
        (freeInv (d.period (p (s1 (s2 (s3 n))))) (f (s1 (s2 (s3 n))))))
      (fun n => d.defectH (p (s1 (s2 (s3 n))))) _ _ _ _ _ hA hB hC (hprod g hg) hDf
      (fun n => (hsol _).equation)
  · have ha := tendsto_clm_of_weak (pinMap d.toCertificateData) _ _ hwu
    have hb : Tendsto (fun n => d.targetGap (p (s1 (s2 (s3 n))))) atTop (𝓝 (d.targetGap q)) :=
      ((h4 d hd).1 q hq).tendsto.comp hps
    exact tendsto_nhds_unique ha (hb.congr fun n => (hsol _).pins.symm)
  · exact sizeZ_le_of_weak hadm _ _ _ _ hwu hκ _ (fun n => (hsol _).size)
  · exact supGrad_le_of_weak _ _ _ hwu (fun n => (hsol _).sup)

end Breakdown.Cert
