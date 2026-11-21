import Breakdown.CertCell.AssemblyPotentialSharp
import Breakdown.CertCell.AssemblyPotentialExpand
import Breakdown.CertCell.AssemblyPotentialStageCharge

open Filter Topology Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace SharpRegularity

open CellCert.CellAnalysis CellCalculus Internal.StretchPairs

theorem tsum_facts {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : ℤ × ℤ → α → ℝ}
    (hi : ∀ ι, Integrable (f ι) μ) (hs : Summable fun ι => ∫ a, ‖f ι a‖ ∂μ) :
    (∀ᵐ a ∂μ, Summable fun ι => f ι a) ∧ Integrable (fun a => ∑' ι, f ι a) μ ∧
      ∫ a, ∑' ι, f ι a ∂μ = ∑' ι, ∫ a, f ι a ∂μ := by
  have hl : ∀ ι, ∫⁻ a, ‖f ι a‖ₑ ∂μ = ENNReal.ofReal (∫ a, ‖f ι a‖ ∂μ) := fun ι =>
    (ofReal_integral_norm_eq_lintegral_enorm (hi ι)).symm
  have hfin : ∑' ι, ∫⁻ a, ‖f ι a‖ₑ ∂μ ≠ ⊤ := by
    rw [tsum_congr hl, ← ENNReal.ofReal_tsum_of_nonneg (fun ι => integral_nonneg fun a => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  have hm : ∀ ι, AEMeasurable (fun a => ‖f ι a‖ₑ) μ := fun ι => (hi ι).1.enorm
  have hlt : ∀ᵐ a ∂μ, ∑' ι, ‖f ι a‖ₑ < ⊤ := by
    refine ae_lt_top' (AEMeasurable.tsum hm) ?_
    rwa [lintegral_tsum hm]
  have hsum : ∀ᵐ a ∂μ, Summable fun ι => f ι a := by
    filter_upwards [hlt] with a ha
    exact (tsum_enorm_ne_top_iff_summable_norm.1 ha.ne).of_norm
  have hmeas : AEStronglyMeasurable (fun a => ∑' ι, f ι a) μ := by
    refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (f := fun (s : Finset (ℤ × ℤ)) a => ∑ ι ∈ s, f ι a)
      (fun s => Finset.aestronglyMeasurable_fun_sum _ fun ι _ => (hi ι).1) ?_
    filter_upwards [hsum] with a ha
    exact ha.hasSum
  refine ⟨hsum, ⟨hmeas, ?_⟩, integral_tsum (fun ι => (hi ι).1) hfin⟩
  unfold HasFiniteIntegral
  calc ∫⁻ a, ‖∑' ι, f ι a‖ₑ ∂μ ≤ ∫⁻ a, ∑' ι, ‖f ι a‖ₑ ∂μ := lintegral_mono fun a => enorm_tsum_le_tsum_enorm
    _ = ∑' ι, ∫⁻ a, ‖f ι a‖ₑ ∂μ := lintegral_tsum hm
    _ < ⊤ := lt_top_iff_ne_top.2 hfin

theorem curlSq_nonneg (s : Fin 3 → Fin 3 → ℂ) : 0 ≤ curlSq s := by
  unfold curlSq
  positivity

theorem quad_abs_le (a b c : ℝ) (U : Fin 12 → ℂ) :
    |a * curlSq (strainOfVec U) + b * sumSq (strainOfVec U) + c * vecSq (velOf U)|
      ≤ (2 * |a| + |b| + |c|) * ∑ j, ‖U j‖ ^ 2 := by
  have h1 := Internal.curlSq_le_two (strainOfVec U)
  have h2 := curlSq_nonneg (strainOfVec U)
  have h3 := Internal.sumSq_nonneg (strainOfVec U)
  have h4 := Internal.vecSq_nonneg (velOf U)
  have h5 : sumSq (strainOfVec U) + vecSq (velOf U) = ∑ j, ‖U j‖ ^ 2 := by
    have e := Internal.pairVec_sq (strainOfVec U) (velOf U)
    rw [Sharp.pairVec_strainOfVec] at e
    exact e.symm
  have ta : |a * curlSq (strainOfVec U)| ≤ |a| * (2 * sumSq (strainOfVec U)) := by
    rw [abs_mul, abs_of_nonneg h2]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
  have tb : |b * sumSq (strainOfVec U)| = |b| * sumSq (strainOfVec U) := by
    rw [abs_mul, abs_of_nonneg h3]
  have tc : |c * vecSq (velOf U)| = |c| * vecSq (velOf U) := by
    rw [abs_mul, abs_of_nonneg h4]
  calc |a * curlSq (strainOfVec U) + b * sumSq (strainOfVec U) + c * vecSq (velOf U)|
      ≤ |a * curlSq (strainOfVec U)| + |b * sumSq (strainOfVec U)| + |c * vecSq (velOf U)| :=
        (abs_add_le _ _).trans (by linarith [abs_add_le (a * curlSq (strainOfVec U)) (b * sumSq (strainOfVec U))])
    _ ≤ (2 * |a| + |b| + |c|) * (sumSq (strainOfVec U) + vecSq (velOf U)) := by
        rw [tb, tc]
        nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, mul_nonneg (abs_nonneg a) h4,
          mul_nonneg (abs_nonneg b) h4, mul_nonneg (abs_nonneg c) h3]
    _ = (2 * |a| + |b| + |c|) * ∑ j, ‖U j‖ ^ 2 := by rw [h5]

theorem aesm_of_continuous {μ : Measure (ℝ × ℝ)} {X : ℝ × ℝ → Fin 12 → ℂ}
    (h : ∀ j, AEStronglyMeasurable (fun p => X p j) μ) (Φ : (Fin 12 → ℂ) → ℝ) (hΦ : Continuous Φ) :
    AEStronglyMeasurable (fun p => Φ (X p)) μ :=
  (hΦ.measurable.comp_aemeasurable (aemeasurable_pi_iff.2 fun j => (h j).aemeasurable)).aestronglyMeasurable

theorem weighted_quad_integrable {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) {X : ℝ × ℝ → Fin 12 → ℂ}
    (hm : ∀ j, AEStronglyMeasurable (fun p => X p j) (volume.restrict S))
    (hi : IntegrableOn (fun p => p.1 * ∑ j, ‖X p j‖ ^ 2) S) {w : ℝ → ℝ} (hw : Measurable w) {κ : ℝ}
    (hwb : ∀ p ∈ S, |w p.1| ≤ κ * p.1) (a b c : ℝ) :
    IntegrableOn (fun p => w p.1 * (a * curlSq (strainOfVec (X p)) + b * sumSq (strainOfVec (X p))
      + c * vecSq (velOf (X p)))) S := by
  refine Integrable.mono' (hi.const_mul (κ * (2 * |a| + |b| + |c|))) ?_ ?_
  · have hc : Continuous (fun U : Fin 12 → ℂ => a * curlSq (strainOfVec U) + b * sumSq (strainOfVec U)
        + c * vecSq (velOf U)) :=
      ((continuous_const.mul Internal.continuous_curlSqPart).add
        (continuous_const.mul Internal.continuous_sumSqPart)).add (continuous_const.mul Internal.continuous_vecSqPart)
    exact (hw.comp measurable_fst).aestronglyMeasurable.mul (aesm_of_continuous hm _ hc)
  · filter_upwards [ae_restrict_mem hS] with p hp
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hwb p hp
    have h2 := quad_abs_le a b c (X p)
    calc |w p.1| * |a * curlSq (strainOfVec (X p)) + b * sumSq (strainOfVec (X p)) + c * vecSq (velOf (X p))|
        ≤ (κ * p.1) * ((2 * |a| + |b| + |c|) * ∑ j, ‖X p j‖ ^ 2) :=
          mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
      _ = κ * (2 * |a| + |b| + |c|) * (p.1 * ∑ j, ‖X p j‖ ^ 2) := by ring

end SharpRegularity

end Internal

end Assembly

end CertCell

end Breakdown

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace SharpRegularity

open CellCert.CellAnalysis CellCalculus Internal.StretchPairs

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem lineWeight_abs_le (B : CellBox) (hB : IsCellBox B) :
    ∃ κ : ℝ, ∀ p ∈ B.rect, |B.lineWeight p.1| ≤ κ * p.1 := by
  by_cases h : B.r₁ = 0
  · refine ⟨1, fun p hp => ?_⟩
    simp only [CellBox.lineWeight, if_pos h, one_mul]
    exact (abs_of_nonneg (hB.r_order.1.trans hp.1.1)).le
  · have hr : 0 < B.r₁ := lt_of_le_of_ne hB.r_order.1 (Ne.symm h)
    refine ⟨B.r₁⁻¹, fun p hp => ?_⟩
    simp only [CellBox.lineWeight, if_neg h, abs_one]
    rw [← div_eq_inv_mul, le_div_iff₀ hr, one_mul]
    exact hp.1.1

theorem measurable_lineWeight (B : CellBox) : Measurable B.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs
  · exact measurable_id
  · exact measurable_const

theorem leaf_coupling (hAR : AssemblyRegular D R) (K : Fin D.mesh.count) (hK : IsCellBox (D.mesh.box K))
    (ι : ℤ × ℤ) :
    CouplingOK (D.mesh.box K).rect {0} (fun _ p => (R.leaves K).localMatrix ι p) := by
  choose c hc using fun (i j : Fin 12) => (hAR.leaves K ι i j).2
  refine ⟨measurableSet_Icc.prod measurableSet_Icc, fun p hp => hK.r_order.1.trans hp.1.1,
    fun _ _ i j => (hAR.leaves K ι i j).1, fun _ _ => ⟨∑ i, ∑ j, |c i j|, fun p hp i j => ?_⟩⟩
  refine ((hc i j p hp).trans (le_abs_self _)).trans ?_
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg (c i j))
    (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => |c i j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)

theorem charge_piece (hM : IsCellMesh D.mesh) (hE : EntryChargesRegular D R) (K : Fin D.mesh.count)
    (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hreg : ∀ ι, (∀ j, AEStronglyMeasurable (fun p => bandProfile D ι v G p j) (volume.restrict (D.mesh.box K).rect)) ∧
      IntegrableOn (fun p => p.1 * ∑ j, ‖bandProfile D ι v G p j‖ ^ 2) (D.mesh.box K).rect) :
    ∃ Mc : ℝ, ∀ ι, IntegrableOn (Sharp.chargeTerm D R K q v G H ι) (D.mesh.box K).rect ∧
      ∫ p in (D.mesh.box K).rect, ‖Sharp.chargeTerm D R K q v G H ι p‖
        ≤ Mc * ∫ p in (D.mesh.box K).rect, p.1 * ∑ j, ‖bandProfile D ι v G p j‖ ^ 2 := by
  obtain ⟨c, hc⟩ := hE.bounded K
  set Mc := 14 * (|c| + |c⁻¹| + 1) ^ 3 with hMcdef
  have hMc0 : 0 ≤ Mc := by positivity
  have hS := Internal.rect_measurable (D.mesh.box K)
  have hpos : ∀ p ∈ (D.mesh.box K).rect, 0 ≤ p.1 := fun p hp => Internal.fst_nonneg_of_mem _ (hM.box_valid K) hp
  have hnn : ∀ ι, 0 ≤ ∫ p in (D.mesh.box K).rect, p.1 * ∑ j, ‖bandProfile D ι v G p j‖ ^ 2 := fun ι =>
    setIntegral_nonneg hS fun p hp => mul_nonneg (hpos p hp) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  refine ⟨Mc, fun ι => ?_⟩
  by_cases hι : ι ∈ D.mesh.resolved K
  · have e : Sharp.chargeTerm D R K q v G H ι = fun _ => 0 := funext fun p => by simp [Sharp.chargeTerm, hι]
    rw [e]
    refine ⟨integrableOn_zero, ?_⟩
    simp only [norm_zero, integral_zero]
    exact mul_nonneg hMc0 (hnn ι)
  · have e : Sharp.chargeTerm D R K q v G H ι = fun p => Internal.chargeDiff D R K ι v G p * p.1 :=
      funext fun p => by simp only [Sharp.chargeTerm, hι, if_false, Internal.chargeDiff_eq]
    rw [e]
    have hb : ∀ p ∈ (D.mesh.box K).rect, ‖Internal.chargeDiff D R K ι v G p * p.1‖
        ≤ Mc * (p.1 * ∑ j, ‖bandProfile D ι v G p j‖ ^ 2) := by
      intro p hp
      have h1 := (Internal.chargeDiff_bound D R K ι v G p (hc ι p hp)).1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpos p hp)]
      calc |Internal.chargeDiff D R K ι v G p| * p.1 ≤ (Mc * Internal.profileSq D ι v G p) * p.1 :=
            mul_le_mul_of_nonneg_right h1 (hpos p hp)
        _ = Mc * (p.1 * ∑ j, ‖bandProfile D ι v G p j‖ ^ 2) := by
            unfold Internal.profileSq
            ring
    have hint : IntegrableOn (fun p => Internal.chargeDiff D R K ι v G p * p.1) (D.mesh.box K).rect := by
      refine Integrable.mono' ((hreg ι).2.const_mul Mc)
        (Internal.chargeDiff_aemeasurable D R hE K ι v G (hreg ι).1) ?_
      filter_upwards [ae_restrict_mem hS] with p hp
      exact hb p hp
    refine ⟨hint, ?_⟩
    rw [← integral_const_mul]
    exact setIntegral_mono_on hint.norm ((hreg ι).2.const_mul Mc) hS hb

end SharpRegularity

namespace Sharp

open CellCert.CellAnalysis CellCalculus Internal.StretchPairs Internal.SharpRegularity

theorem sharpRegular : SharpRegularStatement := by
  intro k C nE nM D R A P states hAR hTF hchk hLT K q v G H g κ F Pg ht ζ η
  have hK : IsCellBox (D.mesh.box K) := hchk.mesh_valid.box_valid K
  have hS : MeasurableSet (D.mesh.box K).rect := measurableSet_Icc.prod measurableSet_Icc
  have h0 : ∀ p ∈ (D.mesh.box K).rect, 0 ≤ p.1 := fun p hp => hK.r_order.1.trans hp.1.1
  have hreg := hTF.1 K q v G H g κ F Pg ht
  have hGT := good_true D hTF.1 ht
  have hGU := good_upper D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
  set X := otherAt D R P K v G H Pg κ ζ η with hXdef
  have hGX : Good (D.mesh.box K).rect X := good_sub h0 hS hGT hGU
  have hMc := couplingOK_rect D K hK hAR.field.model_state (P.potential K).harmonicLabels
  have hnormX : ∀ ι, ∫ p in (D.mesh.box K).rect, ‖p.1 * ∑ j, ‖X ι p j‖ ^ 2‖
      = ∫ p in (D.mesh.box K).rect, p.1 * ∑ j, ‖X ι p j‖ ^ 2 := fun ι =>
    setIntegral_congr_fun hS fun p hp => Real.norm_of_nonneg
      (mul_nonneg (h0 p hp) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  obtain ⟨hX1, -, -⟩ := tsum_facts (μ := volume.restrict (D.mesh.box K).rect)
    (f := fun ι p => p.1 * ∑ j, ‖X ι p j‖ ^ 2) hGX.integ (by simpa only [hnormX] using hGX.summ)
  have hXsum : ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), Summable fun ι => cnormSq (X ι p) := by
    filter_upwards [hX1, SharpCircleStrainParts.fst_ne_ae (D.mesh.box K)] with p hp hp1
    refine (hp.mul_left p.1⁻¹).congr fun ι => ?_
    show p.1⁻¹ * (p.1 * ∑ j, ‖X ι p j‖ ^ 2) = ∑ j, ‖X ι p j‖ ^ 2
    rw [← mul_assoc, inv_mul_cancel₀ hp1, one_mul]
  obtain ⟨Mc, hMcb⟩ := charge_piece D R hchk.mesh_valid hAR.charges K q v G H hreg.1
  have hcs : Summable fun ι => ∫ p in (D.mesh.box K).rect, ‖chargeTerm D R K q v G H ι p‖ :=
    Summable.of_nonneg_of_le (fun ι => integral_nonneg fun p => norm_nonneg _) (fun ι => (hMcb ι).2)
      (hreg.2.mul_left Mc)
  obtain ⟨hC1, hC2, hC3⟩ := tsum_facts (μ := volume.restrict (D.mesh.box K).rect)
    (f := fun ι => chargeTerm D R K q v G H ι) (fun ι => (hMcb ι).1) hcs
  have hsi : ∀ ι, IntegrableOn (stretchTerm D (P.potential K).harmonicLabels X ι) (D.mesh.box K).rect := fun ι =>
    integrable_finsetSum _ fun α hα => pairTerm_integrable hMc hGX hGX hα ι
  have hss : Summable fun ι => ∫ p in (D.mesh.box K).rect, ‖stretchTerm D (P.potential K).harmonicLabels X ι p‖ := by
    refine Summable.of_nonneg_of_le (fun ι => integral_nonneg fun p => norm_nonneg _) (fun ι => ?_)
      (summable_sum fun α hα => pairTerm_normSummable hMc hGX hGX hα)
    rw [← integral_finsetSum _ fun α hα => (pairTerm_integrable hMc hGX hGX hα ι).norm]
    exact integral_mono (hsi ι).norm (integrable_finsetSum _ fun α hα => (pairTerm_integrable hMc hGX hGX hα ι).norm)
      fun p => norm_sum_le _ _
  obtain ⟨hT1, hT2, -⟩ := tsum_facts (μ := volume.restrict (D.mesh.box K).rect)
    (f := fun ι => stretchTerm D (P.potential K).harmonicLabels X ι) hsi hss
  refine ⟨?_, ?_, hC2, ?_, hT2, pairSum_integral hMc hGX hGX⟩
  · filter_upwards [hXsum, hC1, hT1] with p h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · intro ι hι
    have hlc := pairTerm_integrable (leaf_coupling D R hAR K hK ι) hGX hGX (Finset.mem_singleton_self 0) ι
    have eL : leafCore D R K X ι = pairTerm (fun _ p => (R.leaves K).localMatrix ι p) X X 0 ι := by
      funext p
      simp only [leafCore, pairTerm, sub_zero]
    refine ⟨eL ▸ hlc, ?_, ?_⟩
    · have h := weighted_quad_integrable hS (hGX.meas ι) (hGX.integ ι) (w := id) measurable_id (κ := 1)
        (fun p hp => by rw [id, one_mul, abs_of_nonneg (h0 p hp)])
        ((R.leaves K).boxPairCurl ι) ((R.leaves K).boxPairStrain ι) ((R.leaves K).boxPairVelocity ι)
      exact h
    · obtain ⟨κw, hκw⟩ := lineWeight_abs_le (D.mesh.box K) hK
      have h := weighted_quad_integrable hS (hGX.meas ι) (hGX.integ ι) (w := (D.mesh.box K).lineWeight)
        (measurable_lineWeight _) (κ := κw) hκw
        ((R.leaves K).curlAbsorb ι) ((R.leaves K).strainAbsorb ι) ((R.leaves K).velocityAbsorb ι)
      exact h
  · rw [hC3]
    unfold stretchChargeAmount
    refine tsum_congr fun ι => ?_
    by_cases hι : ι ∈ D.mesh.resolved K
    · simp [chargeTerm, hι]
    · simp [chargeTerm, hι]

end Sharp

end Internal

end Assembly

end CertCell

end Breakdown
