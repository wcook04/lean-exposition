import Breakdown.Cert.ExtendedCoerciveStatement
import Breakdown.Cert.CoerciveSmoothPieceDensity
import Breakdown.Cert.ExtendedCoercivePieceDensityEnvelope
import Breakdown.Cert.ExtendedCoercivePieceDensityRight
import Breakdown.Cert.ExtendedCoercivePieceDensityEnergy
import Breakdown.Cert.ExtendedCoercivePieceDensityMeasure
import Breakdown.Cert.ExtendedCoercivePieceDensityBase

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.PieceDensity

open Coercive Coercive.Internal.SmoothPieceDensity Coercive.Internal.PieceAbsorb

theorem split_iff_of_block_diff {X : ℝ} {Pos Rest : ℝ → Space → ℤ × ℤ → ℝ} {B B' J E : ℝ → Space → ℝ}
    (hB : ∀ σ y, B σ y ≤ 0) (hB' : ∀ σ y, B' σ y ≤ 0) (hE0 : ∀ σ y, 0 ≤ E σ y)
    (hBE : ∀ σ y, B σ y = B' σ y - E σ y)
    (hnull : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (E σ y)) = 0)
    (hm1 : AEMeasurable (fun z : ℝ × Space =>
      (∑' ι, ENNReal.ofReal (-Rest z.1 z.2 ι)) + ENNReal.ofReal (-B' z.1 z.2)) slabMeasure)
    (hm2 : AEMeasurable (fun z : ℝ × Space =>
      (∑' ι, ENNReal.ofReal (-Rest z.1 z.2 ι)) + ENNReal.ofReal (-B' z.1 z.2) + ENNReal.ofReal (-J z.1 z.2))
      slabMeasure) :
    IsSplitLowerBound X Pos Rest B J ↔ IsSplitLowerBound X Pos Rest B' J := by
  have hp : ∀ σ y, ENNReal.ofReal (B σ y) = ENNReal.ofReal (B' σ y) := fun σ y => by
    rw [ENNReal.ofReal_of_nonpos (hB σ y), ENNReal.ofReal_of_nonpos (hB' σ y)]
  have hn : ∀ σ y, ENNReal.ofReal (-B σ y) = ENNReal.ofReal (E σ y) + ENNReal.ofReal (-B' σ y) := by
    intro σ y
    rw [← ENNReal.ofReal_add (hE0 σ y) (neg_nonneg.2 (hB' σ y)), hBE σ y]
    congr 1
    ring
  have e1 : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ((∑' ι, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-B σ y)))
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ((∑' ι, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-B' σ y)) := by
    have hq : ∀ σ y, (∑' ι, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-B σ y)
        = ENNReal.ofReal (E σ y) + ((∑' ι, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-B' σ y)) := by
      intro σ y
      rw [hn]
      ring
    simp_rw [hq]
    rw [lintegral_add_iter (f := fun σ y => ENNReal.ofReal (E σ y)) hm1, hnull, zero_add]
  have e2 : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ((∑' ι, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-B σ y) + ENNReal.ofReal (-J σ y)))
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ((∑' ι, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-B' σ y) + ENNReal.ofReal (-J σ y)) := by
    have hq : ∀ σ y, (∑' ι, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-B σ y) + ENNReal.ofReal (-J σ y)
        = ENNReal.ofReal (E σ y) + ((∑' ι, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-B' σ y)
          + ENNReal.ofReal (-J σ y)) := by
      intro σ y
      rw [hn]
      ring
    simp_rw [hq]
    rw [lintegral_add_iter (f := fun σ y => ENNReal.ofReal (E σ y)) hm2, hnull, zero_add]
  unfold IsSplitLowerBound
  simp_rw [hp]
  rw [e1, e2]

theorem epsRestWith_nonpos {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds)
    (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hE : ∀ β y, 0 ≤ (m.epsP β).wt y) (β : Fin nE) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    pieceEpsRestModeWith m h W HW v G H β ι σ y ≤ 0 := by
  unfold pieceEpsRestModeWith
  refine neg_nonpos.2 (mul_nonneg (mul_nonneg (hE β y) (Real.sqrt_nonneg _)) ?_)
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_ <;>
    exact edgeSum_nonneg_of _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _) _

theorem epsBlockLower_nonpos {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W : ℝ → Space → Space)
    {s : Space → ℝ} (hs : ∀ y, 0 ≤ s y) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hE : ∀ β y, 0 ≤ (m.epsP β).wt y) (β : Fin nE) (σ : ℝ) (y : Space) :
    epsBlockLower m W s v G H β σ y ≤ 0 := by
  have hFS : ∀ a, 0 ≤ frameSpeedSup W a y := fun a => Real.iSup_nonneg fun _ => norm_nonneg _
  have hvS : 0 ≤ vortSup W y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hvGS := hs y
  have hpn : ∀ T (g : ℤ × ℤ → ℝ), 0 ≤ pieceNorm T g := fun _ _ => Real.sqrt_nonneg _
  have hwg : ∀ f, 0 ≤ PieceWeights.wtGrad f y := fun _ => norm_nonneg _
  unfold epsBlockLower
  have ha := hE β y
  have h1 := hpn (m.epsP β).modes (fun κ => vortGradAmp H κ σ y)
  have h2 := hpn (m.epsP β).modes (fun κ => vortAmp G κ σ y)
  have h3 := hpn (m.epsP β).modes (fun κ => velAmp v κ σ y)
  have h4 := hpn (m.epsP β).modes (fun κ => gradAmp G κ σ y)
  nlinarith [mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg ha (hFS (m.epsP β).frame)) (hwg (m.epsP β).wt)) h1) h2,
    mul_nonneg (mul_nonneg ha (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hvS)
      (abs_nonneg (m.epsP β).frame))) (sq_nonneg (pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y))),
    mul_nonneg (mul_nonneg (mul_nonneg ha hvGS) h3) h2, mul_nonneg (mul_nonneg (mul_nonneg ha hvS) h4) h2]

theorem epsBlockWith_eq {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (s : Space → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (β : Fin nE) (σ : ℝ) (y : Space) :
    pieceEpsBlockWith m W HW v G H β σ y = epsBlockLower m W s v G H β σ y
      - (vortGradSupWith HW y - s y) * ((m.epsP β).wt y * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ σ y)
        * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y)) := by
  unfold pieceEpsBlockWith epsBlockLower
  ring

theorem aem_slab {f : ℝ × Space → ℝ≥0∞} (hf : AEMeasurable f volume) : AEMeasurable f slabMeasure := by
  rw [slabMeasure_eq]
  exact hf.restrict

end Internal.PieceDensity

set_option maxHeartbeats 1600000 in
open Internal.PieceDensity Internal.PieceDensityBase Coercive Coercive.Internal.SmoothPieceDensity
  Coercive.Internal.PieceAbsorb in
theorem pieceDensitySmoothWeakHolds_of (hP : ModeSquareSumHolds) (hSplit : PiecePairingSplitSmoothWeakHolds)
    (hI1 : EnergyIdentitySmoothWeakHolds) (hBase : BaseDensitySmoothHolds)
    (hEps : PieceEpsEstimateSmoothWeakHolds) (hMu : PieceMuEstimateSmoothWeakHolds)
    (hSolenoidal : SolenoidalModeHolds) : PieceDensitySmoothWeakHolds := by
  intro C nE nM m P h w k W HW D act w₀ epsSup epsGradSup ratio hm hW hwb hactm hactp hact2 v hv κ M hM
  obtain ⟨hRm, hRp, hR2⟩ := right_side_sq hW hv
  obtain ⟨Q, hQ, -⟩ := hSolenoidal _ hRm hRp hR2
  have hsplit := hSplit m P h w W HW D hm hW hwb v hv M Q hM hQ
  have hI := hI1 P W HW D v hm.period_pos hW hv
  have hB := hBase P m.classOf m.convD m.convZ m.c w w₀ hm.finite_classes hm.weight_pos hm.weight_lower hwb
    hm.weight_measurable hm.weight_axi hm.convD_smooth hm.convZ_smooth hm.convD_axi hm.convZ_axi hm.convD_decay
    hm.convZ_decay v hv
  have hE := fun β => hEps m P h w W HW D hm hW hwb v hv β
  have hMu' := fun β => hMu m P h w W HW D hm hW hwb v hv Q hQ β
  obtain ⟨mSp, mSn, hSp, hSn, hSeq⟩ := energy_split hW hv
  obtain ⟨c', hc'm, hc'0, hc'le, henv⟩ :=
    exists_lower_envelope (vortGradSupWith_nonneg HW) (vortGradSupWith_le hW)
  obtain ⟨aEP, aMP, aB, aER, aMR, aEB, aMB, aG⟩ := parts_measurable m P h w W HW D v hm hW hv hc'm
  have hpart : ∀ β, pieceSeminormPart m P β v ≠ ⊤ := fun β => (part_finite m P v hm.cμ_lt_one β (hMu' β)).ne
  have hlin := pairing_linear (smoothRight P W v) M act κ hRm hR2 hactm hact2 hM.1 hM.2.2.1
  set g : Fin nE → ℝ → Space → ℝ := fun β σ y => (m.epsP β).wt y
    * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ σ y)
    * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ σ y) with hg
  have hg0 : ∀ β σ y, 0 ≤ g β σ y := fun β σ y =>
    mul_nonneg (mul_nonneg (hm.eps_wt_nonneg β y) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hd0 : ∀ y, 0 ≤ vortGradSupWith HW y - c' y := fun y => sub_nonneg.2 (hc'le y)
  have hid := fun β σ y => epsBlockWith_eq m W HW c' v (gradField v) (secondDerivField v) β σ y
  have hEL := fun β σ y => epsBlockLower_nonpos m W hc'0 v (gradField v) (secondDerivField v) hm.eps_wt_nonneg β σ y
  have hEW : ∀ β σ y, pieceEpsBlockWith m W HW v (gradField v) (secondDerivField v) β σ y ≤ 0 := by
    intro β σ y
    rw [hid]
    nlinarith [hEL β σ y, mul_nonneg (hd0 y) (hg0 β σ y)]
  have hER := fun β ι σ y => epsRestWith_nonpos m h W HW v (gradField v) (secondDerivField v) hm.eps_wt_nonneg β ι σ y
  have tER : ∀ β, AEMeasurable (fun z : ℝ × Space =>
      ∑' ι, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι z.1 z.2)) volume :=
    fun β => AEMeasurable.ennreal_tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (aER β ι).neg
  have tMR : ∀ β, AEMeasurable (fun z : ℝ × Space =>
      ∑' ι, ENNReal.ofReal (-pieceMuRestMode m h W v (gradField v) β ι z.1 z.2)) volume :=
    fun β => AEMeasurable.ennreal_tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (aMR β ι).neg
  have mEn : ∀ β, AEMeasurable (fun z : ℝ × Space =>
      (∑' ι, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι z.1 z.2))
        + ENNReal.ofReal (-epsBlockLower m W c' v (gradField v) (secondDerivField v) β z.1 z.2)) slabMeasure :=
    fun β => aem_slab ((tER β).add (ENNReal.measurable_ofReal.comp_aemeasurable (aEB β).neg))
  have mMn : ∀ β, AEMeasurable (fun z : ℝ × Space =>
      (∑' ι, ENNReal.ofReal (-pieceMuRestMode m h W v (gradField v) β ι z.1 z.2))
        + ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β z.1 z.2)) slabMeasure :=
    fun β => aem_slab ((tMR β).add (ENNReal.measurable_ofReal.comp_aemeasurable (aMB β).neg))
  have mEp : ∀ β, AEMeasurable (fun z : ℝ × Space =>
      ∑' ι, ENNReal.ofReal (pieceEpsPos m P (gradField v) β ι z.1 z.2)) slabMeasure :=
    fun β => aem_slab (AEMeasurable.ennreal_tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (aEP β ι))
  have mMp : ∀ β, AEMeasurable (fun z : ℝ × Space =>
      ∑' ι, ENNReal.ofReal (pieceMuPos m P v β ι z.1 z.2)) slabMeasure :=
    fun β => aem_slab (AEMeasurable.ennreal_tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (aMP β ι))
  have mBp : AEMeasurable (fun z : ℝ × Space => ∑' ι, ENNReal.ofReal
      (modeVals v (gradField v) (secondDerivField v) ι z.1 z.2 (baseDensity m.convD m.convZ (m.classOf ι) m.c w z.2)))
      slabMeasure :=
    aem_slab (AEMeasurable.ennreal_tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (aB ι))
  have gslab : ∀ β, AEMeasurable (fun z : ℝ × Space => g β z.1 z.2) slabMeasure := fun β => by
    rw [slabMeasure_eq]
    exact (aG β).restrict
  have hE' : ∀ β, IsSplitLowerBound
      (epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v (smoothRight P W v))
      (fun σ y ι => pieceEpsPos m P (gradField v) β ι σ y)
      (fun σ y ι => pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y)
      (fun σ y => epsBlockLower m W c' v (gradField v) (secondDerivField v) β σ y) (fun _ _ => 0) := by
    intro β
    refine (split_iff_of_block_diff (hEW β) (hEL β)
      (E := fun σ y => (vortGradSupWith HW y - c' y) * g β σ y)
      (fun σ y => mul_nonneg (hd0 y) (hg0 β σ y)) (hid β)
      (lintegral_iter_envelope_eq_zero henv (gslab β)) (mEn β) ?_).1 (hE β)
    simp only [neg_zero, ENNReal.ofReal_zero, add_zero]
    exact mEn β
  have hA := assemble
    (Xb := vorticityEnergy v - m.c * weightedEnergy w (gradField v) (secondDerivField v))
    (Xe := fun β => epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v
      (smoothRight P W v))
    (Xm := fun β => muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Q
      - m.cμ * (pieceSeminormPart m P β v).toReal)
    (X := m.multiplierGap P w act v (gradField v) (secondDerivField v) κ
          (fun σ y => smoothRight P W v σ y + ∑ i, κ i • act i σ y) M)
    (fun σ y ι => modeVals v (gradField v) (secondDerivField v) ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y))
    (fun β σ y ι => pieceEpsPos m P (gradField v) β ι σ y)
    (fun β σ y ι => pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y)
    (fun β σ y => epsBlockLower m W c' v (gradField v) (secondDerivField v) β σ y)
    (fun β σ y ι => pieceMuPos m P v β ι σ y)
    (fun β σ y ι => pieceMuRestMode m h W v (gradField v) β ι σ y)
    (fun β σ y => pieceMuBlock m W v (gradField v) β σ y)
    (stretchFormWith W HW v (gradField v))
    (fun β σ y ι => ?_) (fun β σ y ι => hER β ι σ y) hEL
    (fun β σ y ι => ?_) (fun β σ y ι => muRest_nonpos m h W v _ hm.mu_wt_nonneg hm.mu_eta_pos β ι σ y)
    (fun β σ y => muBlock_nonpos m W v _ hm.mu_wt_nonneg β σ y)
    hE' hMu' hB (base_neg_finite m P h w W v HW hP hm hwb hv) mEp mMp mBp mEn mMn mSp mSn hSp hSn rfl ?_
  · have hRest : AEMeasurable (fun z : ℝ × Space =>
        ∑' ι, ENNReal.ofReal (-pieceRestWith m h w W HW v (gradField v) (secondDerivField v) ι z.1 z.2)) volume := by
      refine AEMeasurable.ennreal_tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable ?_
      unfold pieceRestWith
      exact (((aB ι).add (Finset.aemeasurable_fun_sum _ fun β _ => aER β ι)).add
        (Finset.aemeasurable_fun_sum _ fun β _ => aMR β ι)).neg
    have hBlk : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal
        (-(∑ β, epsBlockLower m W c' v (gradField v) (secondDerivField v) β z.1 z.2
          + ∑ β, pieceMuBlock m W v (gradField v) β z.1 z.2))) volume :=
      ENNReal.measurable_ofReal.comp_aemeasurable ((Finset.aemeasurable_fun_sum _ fun β _ => aEB β).add
        (Finset.aemeasurable_fun_sum _ fun β _ => aMB β)).neg
    have hm1 := aem_slab (hRest.add hBlk)
    refine (split_iff_of_block_diff (B' := fun σ y => ∑ β, epsBlockLower m W c' v (gradField v) (secondDerivField v) β σ y
        + ∑ β, pieceMuBlock m W v (gradField v) β σ y)
      (E := fun σ y => (vortGradSupWith HW y - c' y) * ∑ β, g β σ y) ?_ ?_ ?_ ?_ ?_ hm1 (hm1.add mSn)).2 hA
    · intro σ y
      unfold pieceBlockWith
      exact add_nonpos (Finset.sum_nonpos fun β _ => hEW β σ y)
        (Finset.sum_nonpos fun β _ => muBlock_nonpos m W v _ hm.mu_wt_nonneg β σ y)
    · intro σ y
      exact add_nonpos (Finset.sum_nonpos fun β _ => hEL β σ y)
        (Finset.sum_nonpos fun β _ => muBlock_nonpos m W v _ hm.mu_wt_nonneg β σ y)
    · intro σ y
      exact mul_nonneg (hd0 y) (Finset.sum_nonneg fun β _ => hg0 β σ y)
    · intro σ y
      unfold pieceBlockWith
      simp only [hid, Finset.sum_sub_distrib, Finset.mul_sum]
      ring
    · exact lintegral_iter_envelope_eq_zero henv (g := fun σ y => ∑ β, g β σ y)
        (Finset.aemeasurable_fun_sum _ fun β _ => gslab β)
  · unfold pieceEpsPos
    exact mul_nonneg (mul_nonneg (mul_nonneg (ind_nonneg _) (hm.eps_wt_nonneg β y)) (abs_nonneg _)) (sq_nonneg _)
  · unfold pieceMuPos
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (ind_nonneg _) (sub_nonneg.2 hm.cμ_lt_one.le))
      (hm.mu_wt_nonneg β y)) (abs_nonneg _)) (sq_nonneg _)
  · unfold PieceWeights.multiplierGap
    rw [hlin, hsplit, hI, hSeq]
    have hsn : (m.seminormSq P v).toReal = ∑ β, (pieceSeminormPart m P β v).toReal := by
      rw [show m.seminormSq P v = ∑ β, pieceSeminormPart m P β v from rfl,
        ENNReal.toReal_sum fun β _ => hpart β]
    rw [hsn, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring

end CoerciveWeak

end Breakdown
