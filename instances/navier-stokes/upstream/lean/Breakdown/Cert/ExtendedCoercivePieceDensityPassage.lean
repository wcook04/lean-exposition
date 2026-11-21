import Breakdown.Cert.ExtendedCoerciveMinorant
import Breakdown.Cert.ExtendedCoercivePassageBlockDefs
import Breakdown.Cert.ExtendedCoerciveAbsorbStep
import Breakdown.Cert.CoercivePieceDensityPassageLimit
import Breakdown.Cert.ExtendedCoercivePieceDensityMeasure
import Breakdown.Cert.CoerciveSmoothPieceDensityBlock
import Breakdown.Cert.CoercivePieceDensityPassageMultiplier
import Breakdown.Cert.CoerciveDensityPassageEnergy
import Breakdown.Cert.CoerciveFrequencySeminormBound
import Breakdown.Cert.ExtendedCoerciveZeroFlow
import Breakdown.Cert.ExtendedCoercivePassageRight
import Breakdown.Cert.ExtendedCoercivePassageStretch
import Breakdown.Cert.ExtendedCoercivePassageRest
import Breakdown.Cert.ExtendedCoercivePassageDiff
import Breakdown.Cert.ExtendedCoercivePieceDensityEnvelope
import Breakdown.Cert.CoercivePieceDensityPassageSubsequence
import Breakdown.Cert.CoerciveDensityPassageLiminf
import Breakdown.Cert.CoercivePieceDensityPassageRest
import Breakdown.Cert.CoerciveDensityPassageNegative

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CoerciveWeak

open PieceWeights

namespace Internal.PieceDensityPassageWeak

open Internal.Minorant


theorem lintegral_block_minorant (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (A : ℝ → Space → ℝ≥0∞) (a b : ℝ → Space → ℝ) (ha0 : ∀ σ y, 0 ≤ a σ y) (hb0 : ∀ σ y, 0 ≤ b σ y)
    (hm : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), AEMeasurable (A σ) ∧ AEMeasurable (a σ) ∧ AEMeasurable (b σ)) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, A σ y + ENNReal.ofReal (-(-(a σ y + vortGradSupWith HW y * b σ y)))
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, A σ y + ENNReal.ofReal (-(-(a σ y + vortGradSupLower HW y * b σ y))) := by
  have p : ∀ s : Space → ℝ, (∀ y, 0 ≤ s y) → ∀ σ y, A σ y + ENNReal.ofReal (-(-(a σ y + s y * b σ y)))
      = (A σ y + ENNReal.ofReal (a σ y)) + ENNReal.ofReal (s y * b σ y) := fun s hs σ y => by
    rw [neg_neg, ENNReal.ofReal_add (ha0 σ y) (mul_nonneg (hs y) (hb0 σ y)), add_assoc]
  simp only [p _ (Internal.Minorant.vortGradSupWith_nonneg HW), p _ (vortGradSupLower_nonneg HW)]
  exact setLIntegral_lintegral_add_ofReal_mul_vortGradSupLower HW
    (hm.mono fun σ hσ => ⟨hσ.1.add (ENNReal.measurable_ofReal.comp_aemeasurable hσ.2.1), hσ.2.2⟩)

theorem split_of_block_minorant (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (X : ℝ)
    (Pos Rest : ℝ → Space → ℤ × ℤ → ℝ) (J : ℝ → Space → ℝ) (a b : ℝ → Space → ℝ)
    (ha0 : ∀ σ y, 0 ≤ a σ y) (hb0 : ∀ σ y, 0 ≤ b σ y)
    (hm : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      AEMeasurable (fun y => ∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) ∧
      AEMeasurable (fun y => ENNReal.ofReal (-J σ y)) ∧ AEMeasurable (a σ) ∧ AEMeasurable (b σ)) :
    Coercive.IsSplitLowerBound X Pos Rest (fun σ y => -(a σ y + vortGradSupWith HW y * b σ y)) J ↔
      Coercive.IsSplitLowerBound X Pos Rest (fun σ y => -(a σ y + vortGradSupLower HW y * b σ y)) J := by
  have p2 : ∀ s : Space → ℝ, (∀ y, 0 ≤ s y) → ∀ σ y,
      ENNReal.ofReal (-(a σ y + s y * b σ y)) = 0 := fun s hs σ y =>
    ENNReal.ofReal_of_nonpos (neg_nonpos.2 (add_nonneg (ha0 σ y) (mul_nonneg (hs y) (hb0 σ y))))
  have E1 := lintegral_block_minorant HW (fun σ y => ∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) a b ha0 hb0
    (hm.mono fun σ hσ => ⟨hσ.1, hσ.2.2⟩)
  have E3 := lintegral_block_minorant HW
    (fun σ y => (∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-J σ y)) a b ha0 hb0
    (hm.mono fun σ hσ => ⟨hσ.1.add hσ.2.1, hσ.2.2⟩)
  have r3 : ∀ s : Space → ℝ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-(-(a σ y + s y * b σ y)))
        + ENNReal.ofReal (-J σ y))
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-J σ y))
          + ENNReal.ofReal (-(-(a σ y + s y * b σ y))) := fun s =>
    lintegral_congr fun σ => lintegral_congr fun y => add_right_comm _ _ _
  unfold Coercive.IsSplitLowerBound
  simp only [p2 _ (Internal.Minorant.vortGradSupWith_nonneg HW), p2 _ (vortGradSupLower_nonneg HW), add_zero]
  rw [r3, r3, E1, E3]

section Measurable

open Coercive Coercive.Internal.PieceAbsorb Coercive.Internal.SmoothPieceDensity
open CoerciveWeak.Internal.PieceDensity

theorem joint_parts_aemeasurable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (Γ : Set Symmetry) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) :
    (∀ ι, AEMeasurable (fun z : ℝ × Space => pieceRestWith m h w W HW v G H ι z.1 z.2) volume) ∧
    AEMeasurable (fun z : ℝ × Space => stretchFormWith W HW v G z.1 z.2) volume ∧
    AEMeasurable (fun z : ℝ × Space => pieceBlockWith m W 0 v G H z.1 z.2) volume ∧
    AEMeasurable (fun z : ℝ × Space => blockGain m v G z.1 z.2) volume := by
  have hWc : AEStronglyMeasurable (fun z : ℝ × Space => W z.1 z.2) volume :=
    hW.smooth.continuous.aestronglyMeasurable
  have hgW : AEStronglyMeasurable (fun z : ℝ × Space => gradField W z.1 z.2) volume :=
    (continuous_fderiv_slice_one hW.smooth).aestronglyMeasurable
  have hhW : AEStronglyMeasurable (fun z : ℝ × Space => HW z.1 z.2) volume := hW.secondDeriv_measurable
  have hvm := hv.measurable_velocity
  have hGm := hv.measurable_gradient
  have hHm := hv.measurable_secondDeriv
  have hwE : ∀ β, AEMeasurable (fun z : ℝ × Space => (m.epsP β).wt z.2) volume := fun β => by
    obtain ⟨K, hK⟩ := hm.eps_increment β
    exact (hK.continuous.measurable.comp measurable_snd).aemeasurable
  have hwM : ∀ β, AEMeasurable (fun z : ℝ × Space => (m.muP β).wt z.2) volume := fun β => by
    obtain ⟨K, hK⟩ := hm.mu_increment β
    exact (hK.continuous.measurable.comp measurable_snd).aemeasurable
  have hvS : AEMeasurable (fun z : ℝ × Space => vortSup W z.2) volume :=
    ((measurable_vortSup_one hW.smooth hm.supVort_ge).comp measurable_snd).aemeasurable
  have hvGS : AEMeasurable (fun z : ℝ × Space =>
      vortGradSupWith (0 : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) z.2) volume := by
    simp only [vortGradSupWith_zero]
    exact aemeasurable_const
  have hG3 := fun κ => aem_gradAmp hGm κ
  have hV3 := fun κ => aem_velAmp hvm κ
  refine ⟨fun ι => ?_, Internal.AbsorbStep.aem_stretchFormWith W v G HW hW hvm hGm, ?_, ?_⟩
  · have a0 := aem_velAmp hvm ι
    have hD : Measurable (m.convD (m.classOf ι)) := (hm.convD_smooth _).continuous.measurable
    have hZ : Measurable (m.convZ (m.classOf ι)) := (hm.convZ_smooth _).continuous.measurable
    have hDD : Measurable (ModeWeights.secondDerivNorm (m.convD (m.classOf ι))) :=
      ((hm.convD_smooth _).continuous_iteratedFDeriv le_rfl).norm.measurable
    have hZZ : Measurable (ModeWeights.secondDerivNorm (m.convZ (m.classOf ι))) :=
      ((hm.convZ_smooth _).continuous_iteratedFDeriv le_rfl).norm.measurable
    have a2 := aem_secondDerivAmp hHm ι
    have ac := aem_vortGradAmp hHm ι
    have a1 := aem_gradAmp hGm ι
    have ao := aem_vortAmp hGm ι
    have hw := hm.weight_measurable
    unfold pieceRestWith modeVals baseDensity pieceEpsRestModeWith pieceMuRestMode
    refine AEMeasurable.add (AEMeasurable.add ?_ (Finset.aemeasurable_fun_sum _ fun β _ => ?_))
      (Finset.aemeasurable_fun_sum _ fun β _ => ?_)
    · fun_prop
    · have e1 := aem_edgeSum h (m.epsP β).modes (X := fun z α => velAmp W α z.1 z.2)
        (g := fun z κ => vortGradAmp H κ z.1 z.2) (fun α => aem_velAmp hWc α)
        (fun κ => aem_vortGradAmp hHm κ) ι
      have e2 := aem_edgeSum h (m.epsP β).modes (X := fun z α => gradAmp (gradField W) α z.1 z.2)
        (g := fun z κ => vortAmp G κ z.1 z.2) (fun α => aem_gradAmp hgW α)
        (fun κ => aem_vortAmp hGm κ) ι
      have e3 := aem_edgeSum h (m.epsP β).modes (X := fun z α => vortGradAmp HW α z.1 z.2)
        (g := fun z κ => velAmp v κ z.1 z.2) (fun α => aem_vortGradAmp hhW α)
        (fun κ => aem_velAmp hvm κ) ι
      have e4 := aem_edgeSum h (m.epsP β).modes (X := fun z α => vortAmp (gradField W) α z.1 z.2)
        (g := fun z κ => gradAmp G κ z.1 z.2) (fun α => aem_vortAmp hgW α)
        (fun κ => aem_gradAmp hGm κ) ι
      exact (((hwE β).mul ao).mul (((e1.add e2).add e3).add e4)).neg
    · have e1 := aem_edgeSum h (m.muP β).modes (X := fun z α => velAmp W α z.1 z.2)
        (g := fun z κ => gradAmp G κ z.1 z.2) (fun α => aem_velAmp hWc α)
        (fun κ => aem_gradAmp hGm κ) ι
      have s1 : AEMeasurable (fun z : ℝ × Space =>
          ∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) volume :=
        Finset.aemeasurable_fun_sum _ fun α _ => (aem_gradAmp hgW α).mul (aem_velAmp hvm _)
      have q1 : AEMeasurable (fun z : ℝ × Space =>
          (∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) ^ 2
              / (2 * (m.muP β).eta)
            + (1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2) volume :=
        ((s1.pow_const 2).div_const _).add ((aemeasurable_const.mul ((hwM β).pow_const 2)).mul (a0.pow_const 2))
      exact ((((hwM β).mul a0).mul e1).neg).sub
        (q1.const_mul (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)))
  · have hE : ∀ β, AEMeasurable (fun z : ℝ × Space => pieceEpsBlockWith m W 0 v G H β z.1 z.2) volume := by
      intro β
      have hwg : AEMeasurable (fun z : ℝ × Space => PieceWeights.wtGrad (m.epsP β).wt z.2) volume :=
        (((measurable_fderiv ℝ (m.epsP β).wt).norm).comp measurable_snd).aemeasurable
      have hfs : AEMeasurable (fun z : ℝ × Space => frameSpeedSup W (m.epsP β).frame z.2) volume :=
        ((measurable_frameSpeedSup_one hW.smooth (hm.epsSpeed_ge β)).comp measurable_snd).aemeasurable
      have p1 := aemeasurable_pieceNorm (m.epsP β).modes
        (g := fun κ z => vortGradAmp H κ z.1 z.2) fun κ => aem_vortGradAmp hHm κ
      have p2 := aemeasurable_pieceNorm (m.epsP β).modes
        (g := fun κ z => vortAmp G κ z.1 z.2) fun κ => aem_vortAmp hGm κ
      have p3 := aemeasurable_pieceNorm (m.epsP β).modes (g := fun κ z => velAmp v κ z.1 z.2) hV3
      have p4 := aemeasurable_pieceNorm (m.epsP β).modes
        (g := fun κ z => gradAmp G κ z.1 z.2) hG3
      beta_reduce at p1 p2 p3 p4
      have t1 := (((((hwE β).mul hfs).add hwg).mul p1).mul p2).neg
      have t2 := ((hwE β).mul ((aemeasurable_const (b := (1 / 2 : ℝ))).mul hvS |>.add
        (aemeasurable_const (b := |(m.epsP β).frame|)))).mul (p2.pow_const 2)
      have t3 := (((hwE β).mul hvGS).mul p3).mul p2
      have t4 := (((hwE β).mul hvS).mul p4).mul p2
      exact (((t1.sub t2).sub t3).sub t4)
    have hM : ∀ β, AEMeasurable (fun z : ℝ × Space => pieceMuBlock m W v G β z.1 z.2) volume := by
      intro β
      have hwg : AEMeasurable (fun z : ℝ × Space => PieceWeights.wtGrad (m.muP β).wt z.2) volume :=
        (((measurable_fderiv ℝ (m.muP β).wt).norm).comp measurable_snd).aemeasurable
      have hfs : AEMeasurable (fun z : ℝ × Space => frameSpeedSup W (m.muP β).frame z.2) volume :=
        ((measurable_frameSpeedSup_one hW.smooth (hm.muSpeed_ge β)).comp measurable_snd).aemeasurable
      have p3 := aemeasurable_pieceNorm (m.muP β).modes (g := fun κ z => velAmp v κ z.1 z.2) hV3
      have p4 := aemeasurable_pieceNorm (m.muP β).modes
        (g := fun κ z => gradAmp G κ z.1 z.2) hG3
      beta_reduce at p3 p4
      have t1 := (((((hwM β).mul hfs).add hwg).mul p4).mul p3).neg
      have t2 := ((hwM β).mul (aemeasurable_const (b := |(m.muP β).frame|))).mul (p3.pow_const 2)
      exact t1.sub t2
    unfold pieceBlockWith
    exact (Finset.aemeasurable_fun_sum _ fun β _ => hE β).add (Finset.aemeasurable_fun_sum _ fun β _ => hM β)
  · have p2 := fun β => aemeasurable_pieceNorm (m.epsP β).modes
      (g := fun κ z => vortAmp G κ z.1 z.2) fun κ => aem_vortAmp hGm κ
    have p3 := fun β => aemeasurable_pieceNorm (m.epsP β).modes (g := fun κ z => velAmp v κ z.1 z.2) hV3
    unfold blockGain
    exact Finset.aemeasurable_fun_sum _ fun β _ => ((hwE β).mul (p3 β)).mul (p2 β)

theorem piecePos_aemeasurable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (Γ : Set Symmetry) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => piecePos m P v G ι z.1 z.2) volume := by
  have hwE : ∀ β, Measurable (m.epsP β).wt := fun β => by
    obtain ⟨K, hK⟩ := hm.eps_increment β
    exact hK.continuous.measurable
  have hwM : ∀ β, Measurable (m.muP β).wt := fun β => by
    obtain ⟨K, hK⟩ := hm.mu_increment β
    exact hK.continuous.measurable
  unfold piecePos pieceEpsPos pieceMuPos
  refine AEMeasurable.add (Finset.aemeasurable_fun_sum _ fun β _ => ?_)
    (Finset.aemeasurable_fun_sum _ fun β _ => ?_)
  · have h1 := hwE β
    have h2 := aem_vortAmp hv.measurable_gradient ι
    fun_prop
  · have h1 := hwM β
    have h2 := aem_velAmp hv.measurable_velocity ι
    fun_prop

theorem aemeasurable_slab {f : ℝ × Space → ℝ≥0∞} (hf : AEMeasurable f (volume.prod volume)) :
    AEMeasurable f ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  have := hf.restrict (s := Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)
  rwa [← Measure.prod_restrict, Measure.restrict_univ] at this

end Measurable

theorem slice_parts_aemeasurable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (Γ : Set Symmetry) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      AEMeasurable (fun y => ∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceRestWith m h w W HW v G H ι σ y)) ∧
      AEMeasurable (fun y => ENNReal.ofReal (-stretchFormWith W HW v G σ y)) ∧
      AEMeasurable (fun y => -pieceBlockWith m W 0 v G H σ y) ∧ AEMeasurable (blockGain m v G σ) := by
  obtain ⟨hR, hJ, hB, hG⟩ := joint_parts_aemeasurable m P h w Γ W HW D hm hW v G H g hv
  have hR' : AEMeasurable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ,
      ENNReal.ofReal (-pieceRestWith m h w W HW v G H ι z.1 z.2)) (volume.prod volume) :=
    AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (hR ι).neg
  have hJ' : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (-stretchFormWith W HW v G z.1 z.2))
      (volume.prod volume) := ENNReal.measurable_ofReal.comp_aemeasurable hJ.neg
  have hB' : AEMeasurable (fun z : ℝ × Space => -pieceBlockWith m W 0 v G H z.1 z.2) (volume.prod volume) :=
    hB.neg
  have hG' : AEMeasurable (fun z : ℝ × Space => blockGain m v G z.1 z.2) (volume.prod volume) := hG
  refine ae_restrict_of_ae ?_
  filter_upwards [Internal.Minorant.ae_aemeasurable_slice
      (g := fun σ y => ∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceRestWith m h w W HW v G H ι σ y)) hR',
    Internal.Minorant.ae_aemeasurable_slice (g := fun σ y => ENNReal.ofReal (-stretchFormWith W HW v G σ y)) hJ',
    Internal.Minorant.ae_aemeasurable_slice_real (g := fun σ y => -pieceBlockWith m W 0 v G H σ y) hB',
    Internal.Minorant.ae_aemeasurable_slice_real (g := blockGain m v G) hG']
    with σ h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

theorem split_lower_iff {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (X : ℝ) :
    Coercive.IsSplitLowerBound X (fun σ y ι => Coercive.piecePos m P v G ι σ y) (fun σ y ι => pieceRestWith m h w W HW v G H ι σ y)
        (fun σ y => pieceBlockWith m W HW v G H σ y) (stretchFormWith W HW v G) ↔
      Coercive.IsSplitLowerBound X (fun σ y ι => Coercive.piecePos m P v G ι σ y) (fun σ y ι => pieceRestWith m h w W HW v G H ι σ y)
        (fun σ y => pieceBlockLower m W HW v G H σ y) (stretchFormWith W HW v G) := by
  have hB : (fun σ y => pieceBlockWith m W HW v G H σ y) = fun σ y =>
      -(-pieceBlockWith m W 0 v G H σ y + vortGradSupWith HW y * blockGain m v G σ y) :=
    funext fun σ => funext fun y => pieceBlockWith_eq m W HW v G H σ y
  have hL : (fun σ y => pieceBlockLower m W HW v G H σ y) = fun σ y =>
      -(-pieceBlockWith m W 0 v G H σ y + vortGradSupLower HW y * blockGain m v G σ y) :=
    funext fun σ => funext fun y => by unfold pieceBlockLower; ring
  rw [hB, hL]
  exact split_of_block_minorant HW X _ _ _ _ _
    (fun σ y => neg_nonneg.2 (Internal.AbsorbStep.pieceBlockWith_nonpos m W v G H 0 hm.eps_wt_nonneg
      hm.mu_wt_nonneg σ y))
    (blockGain_nonneg m hm.eps_wt_nonneg v G)
    (slice_parts_aemeasurable m P h w Γ W HW D hm hW v G H g hv)

section Gap

open Coercive Coercive.Internal Coercive.Internal.PassageLimit Coercive.Internal.PieceDensityPassageMultiplier
open Coercive.PairingSplitInternal Coercive.ModeL2Internal

theorem multiplier_tendsto_weak (hPars : Coercive.ModeSquareSumHolds) (hDer : Coercive.ModeDerivativeHolds)
    (hRot : Coercive.ModeRotationHolds) (hField : PieceFieldExistsWeakHolds) (hSolenoidal : Coercive.SolenoidalModeHolds)
    (hSP : Coercive.SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : Coercive.IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M)
    (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n)) :
    Tendsto (fun n => periodLIntegral (fun σ y => ‖Mn n σ y - M σ y‖ ^ 2)) atTop (𝓝 0) := by
  have hpd := fun n => PassageCommon.difference_isPerturbation hSP hv hu n
  have hex := fun n => (hField m P h w ∅ W HW D hm hwb _ _ _ _ (hpd n)).2
  choose M' hM' hMb using hex
  have hsub := fun n => multiplier_sub hPars hDer hRot hSP (zeroFlowWeights m) P h w (fun _ _ => 0)
    (zeroFlowAdmissibleHolds_proof m P h w W HW hm) hv (hu.1 n) (hMn n) hMF
  have heq : ∀ n, periodNorm (fun σ y => Mn n σ y - M σ y) = periodNorm (M' n) := fun n =>
    multiplier_norm_eq hSolenoidal (hsub n) (hM' n)
  set K : ℝ := Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt w₀) ^ 2 / m.c + ratio / m.cμ) with hK
  set e : ℕ → ℝ := fun n => m.c * weightedEnergy w (fun σ y => gradField (u n) σ y - G σ y)
      (fun σ y => secondDerivField (u n) σ y - H σ y) + m.cμ * (m.seminormSq P (fun σ y => u n σ y - v σ y)).toReal with he
  have he0 : ∀ n, 0 ≤ e n := fun n =>
    add_nonneg (mul_nonneg hm.c_pos.le ENNReal.toReal_nonneg) (mul_nonneg hm.cμ_pos.le ENNReal.toReal_nonneg)
  have hb : ∀ n, periodNorm (fun σ y => Mn n σ y - M σ y) ^ 2 ≤ K ^ 2 * e n := fun n => by
    rw [heq n]
    have h1 := hMb n
    have h0 : 0 ≤ periodNorm (M' n) := Real.sqrt_nonneg _
    calc periodNorm (M' n) ^ 2 ≤ (K * Real.sqrt (e n)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = K ^ 2 * e n := by rw [mul_pow, Real.sq_sqrt (he0 n)]
  obtain ⟨Bw, hBw⟩ := hwb
  have hw0 : ∀ y, 0 ≤ w y := fun y => hm.weight_pos.le.trans (hm.weight_lower y)
  have hBw0 : 0 ≤ Bw := (hw0 0).trans (hBw 0)
  have hpn := fun n => hSP P (u n) (hu.1 n)
  have hE : Tendsto (fun n => periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField (u n) σ y - H σ y)‖ ^ 2
      + w y * matSq (gradField (u n) σ y - G σ y))) atTop (𝓝 0) := by
    have hup : Tendsto (fun n => ENNReal.ofReal 3 * periodLIntegral (fun σ y => secondDerivSq (secondDerivField (u n) σ y - H σ y))
        + ENNReal.ofReal Bw * periodLIntegral (fun σ y => matSq (gradField (u n) σ y - G σ y))) atTop (𝓝 0) := by
      have := (ENNReal.Tendsto.const_mul hu.2.2.1 (Or.inr (ENNReal.ofReal_ne_top (r := 3)))).add
        (ENNReal.Tendsto.const_mul hu.2.1 (Or.inr (ENNReal.ofReal_ne_top (r := Bw))))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le) fun n => ?_
    have m1 : AEMeasurable (fun z : ℝ × Space => 3 * secondDerivSq (secondDerivField (u n) z.1 z.2 - H z.1 z.2)) volume :=
      ((PassageLimit.continuous_secondDerivSq.comp_aestronglyMeasurable
        ((hpn n).measurable_secondDeriv.sub hv.measurable_secondDeriv)).aemeasurable).const_mul 3
    have m2 : AEMeasurable (fun z : ℝ × Space => Bw * matSq (gradField (u n) z.1 z.2 - G z.1 z.2)) volume :=
      ((PassageCommon.continuous_matSq.comp_aestronglyMeasurable
        ((hpn n).measurable_gradient.sub hv.measurable_gradient)).aemeasurable).const_mul Bw
    calc periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField (u n) σ y - H σ y)‖ ^ 2
          + w y * matSq (gradField (u n) σ y - G σ y))
        ≤ periodLIntegral (fun σ y => 3 * secondDerivSq (secondDerivField (u n) σ y - H σ y)
          + Bw * matSq (gradField (u n) σ y - G σ y)) := PassageLimit.periodLIntegral_mono fun σ y =>
            add_le_add (PassageLimit.traceSq_le_three_secondDerivSq _)
              (mul_le_mul_of_nonneg_right (hBw y) (PassageCommon.matSq_nonneg _))
      _ = periodLIntegral (fun σ y => 3 * secondDerivSq (secondDerivField (u n) σ y - H σ y))
          + periodLIntegral (fun σ y => Bw * matSq (gradField (u n) σ y - G σ y)) :=
          PassageLimit.periodLIntegral_add (f := fun σ y => 3 * secondDerivSq (secondDerivField (u n) σ y - H σ y))
            (g := fun σ y => Bw * matSq (gradField (u n) σ y - G σ y)) m1 m2
            (fun σ y => mul_nonneg (by norm_num) (PassageLimit.secondDerivSq_nonneg _))
            (fun σ y => mul_nonneg hBw0 (PassageCommon.matSq_nonneg _))
      _ ≤ _ := add_le_add (PassageLimit.periodLIntegral_le_mul (by norm_num) fun σ y => le_refl _)
          (PassageLimit.periodLIntegral_le_mul hBw0 fun σ y => le_refl _)
  have hEr : Tendsto (fun n => weightedEnergy w (fun σ y => gradField (u n) σ y - G σ y)
      (fun σ y => secondDerivField (u n) σ y - H σ y)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
    simpa [Function.comp_def, weightedEnergy] using this
  obtain ⟨Bm, hBm⟩ := hm.mu_decay
  have hS := (FrequencyBound.pieceSeminormSq_tendsto_of_approximation m hPars hDer hRot hSP hv
    hm.period_pos hm.mu_wt_nonneg (fun β y => ⟨(hBm β y).1, (hBm β y).2.1⟩)
    (fun β => let ⟨_, hK⟩ := hm.mu_increment β; hK.continuous.measurable) hu).1
  have hSr : Tendsto (fun n => (m.seminormSq P (fun σ y => u n σ y - v σ y)).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hS
    simpa [Function.comp_def] using this
  have hEt : Tendsto e atTop (𝓝 0) := by
    have := (hEr.const_mul m.c).add (hSr.const_mul m.cμ)
    simpa [he] using this
  have hKt : Tendsto (fun n => ENNReal.ofReal (K ^ 2 * e n)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (hEt.const_mul (K ^ 2))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hKt (fun _ => zero_le) fun n => ?_
  have hfin := (hsub n).2.2.1
  have hL : periodLIntegral (fun σ y => ‖Mn n σ y - M σ y‖ ^ 2) =
      ENNReal.ofReal (periodNorm (fun σ y => Mn n σ y - M σ y) ^ 2) := by
    unfold periodNorm
    rw [Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne]
  rw [hL]
  exact ENNReal.ofReal_le_ofReal (hb n)

theorem decay_one_of {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (hW : IsWeakSecondDerivState W HW D) :
    ∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1) := by
  intro σ y j hj
  interval_cases j
  · rw [norm_iteratedFDeriv_zero, zero_add, pow_one]
    exact (hW.decay σ y).1
  · rw [norm_iteratedFDeriv_one, show (1 : ℕ) + 1 = 2 from rfl]
    exact (hW.decay σ y).2.1

theorem decay_one {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (hW : IsWeakSecondDerivState W HW D) :
    ∃ D', ∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D' / (1 + ‖y‖) ^ (j + 1) :=
  ⟨D, decay_one_of hW⟩

theorem rightSide_pairing_eq_weak (hPars : Coercive.ModeSquareSumHolds) (hDer : Coercive.ModeDerivativeHolds)
    (hRot : Coercive.ModeRotationHolds) (hField : PieceFieldExistsWeakHolds) (hSolenoidal : Coercive.SolenoidalModeHolds)
    (hSP : Coercive.SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : Coercive.IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M) :
    periodPairing F M = periodPairing (rightSideLimit W act κ v G H g) M := by
  exact Internal.PassageRight.pairing_rightSideLimit_eq_one hSolenoidal κ hv hW.smooth hW.periodic (decay_one hW) hactm
    hactp hact2 (weightedVelocity_lt_top hv hu) hFm hFp hF2 hR hMF.1 hMF.2.1 hMF.2.2.1 hMF.2.2.2.1

theorem right_pairing_tendsto_weak (hPars : Coercive.ModeSquareSumHolds) (hDer : Coercive.ModeDerivativeHolds)
    (hRot : Coercive.ModeRotationHolds) (hField : PieceFieldExistsWeakHolds) (hSolenoidal : Coercive.SolenoidalModeHolds)
    (hSP : Coercive.SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : Coercive.IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M)
    (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n)) :
    Tendsto (fun n => periodPairing (fun σ y => smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y) (Mn n)) atTop
      (𝓝 (periodPairing F M)) := by
  rw [rightSide_pairing_eq_weak hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act hm hW hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF]
  have hL := Internal.PassageRight.rightSideLimit_memL2_one κ hv hW.smooth (decay_one hW) hactm hact2
    (weightedVelocity_lt_top hv hu)
  have hS := fun n => Internal.PassageRight.smoothRight_memL2_one κ hSP (hu.1 n) hW.smooth (decay_one hW)
    hactm hact2
  exact periodPairing_tendsto (fun n => (hS n).1) (fun n => (hS n).2) hL.1 hL.2
    (fun n => (hMn n).1) (fun n => (hMn n).2.2.1) hMF.1 hMF.2.2.1
    (Internal.PassageRight.smoothRight_tendsto_one κ hSP hv hu (decay_one hW))
    (multiplier_tendsto_weak hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act hm hW hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF Mn hMn)

end Gap

theorem gap_tendsto_weak (hPars : Coercive.ModeSquareSumHolds) (hDer : Coercive.ModeDerivativeHolds)
    (hRot : Coercive.ModeRotationHolds) (hField : PieceFieldExistsWeakHolds) (hSolenoidal : Coercive.SolenoidalModeHolds)
    (hSP : Coercive.SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : Coercive.IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M)
    (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n)) :
    Tendsto (fun n => m.multiplierGap P w act (u n) (gradField (u n)) (secondDerivField (u n)) κ
        (fun σ y => Coercive.smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y) (Mn n)) atTop
      (𝓝 (m.multiplierGap P w act v G H κ F M)) := by
  have hE : Tendsto (fun n => weightedEnergy w (gradField (u n)) (secondDerivField (u n))) atTop
      (𝓝 (weightedEnergy w G H)) := by
    obtain ⟨B, hB⟩ := hwb
    exact Breakdown.Coercive.weightedEnergy_tendsto (B := B) hm.weight_measurable
      (fun y => hm.weight_pos.le.trans (hm.weight_lower y)) hB hv.measurable_gradient hv.measurable_secondDeriv
      (fun n => (hSP P (u n) (hu.1 n)).measurable_gradient) (fun n => (hSP P (u n) (hu.1 n)).measurable_secondDeriv)
      hv.gradient_finite hv.sumSecondPartials_finite hu.2.1 hu.2.2.1
  have hS : Tendsto (fun n => (m.seminormSq P (u n)).toReal) atTop (𝓝 (m.seminormSq P v).toReal) := by
    obtain ⟨B, hB⟩ := hm.mu_decay
    exact (Breakdown.Coercive.FrequencyBound.pieceSeminormSq_tendsto_of_approximation m hPars hDer hRot hSP hv
      hm.period_pos hm.mu_wt_nonneg (fun β y => ⟨(hB β y).1, (hB β y).2.1⟩)
      (fun β => let ⟨_, hK⟩ := hm.mu_increment β; hK.continuous.measurable) hu).2
  have hMt := multiplier_tendsto_weak hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act hm hW hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF Mn hMn
  unfold PieceWeights.multiplierGap
  exact (((right_pairing_tendsto_weak hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act hm hW hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF Mn hMn).sub (hE.const_mul m.c)).sub (hS.const_mul m.cμ)).sub
    (tendsto_finsetSum _ fun i _ => (Coercive.Internal.PassageLimit.periodPairing_tendsto_right (hactm i) (hact2 i)
      (fun n => (hMn n).1) (fun n => (hMn n).2.2.1) hMF.1 hMF.2.2.1 hMt).const_mul (κ i))

theorem rest_negative_finite_weak (hPars : Coercive.ModeSquareSumHolds) (hDer : Coercive.ModeDerivativeHolds)
    (hRot : Coercive.ModeRotationHolds) (hField : PieceFieldExistsWeakHolds) (hSolenoidal : Coercive.SolenoidalModeHolds)
    (hSP : Coercive.SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : Coercive.IsSmoothApproximation P v G H g u) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
      ENNReal.ofReal (-pieceRestWith m h w W HW v G H ι σ y)) < ⊤ := by
  obtain ⟨K, hK, hb⟩ := Internal.PassageRest.rest_tsum_le_one m P h w W hm
    ⟨D, decay_one_of hW, fun σ y => (hW.decay σ y).2.2⟩ hwb
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
        ENNReal.ofReal (-pieceRestWith m h w W HW v G H ι σ y))
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, K * Coercive.Internal.DensityPassageRest.ampTot v G H σ y :=
        lintegral_mono fun σ => lintegral_mono fun y => le_trans (ENNReal.tsum_le_tsum fun ι =>
          ENNReal.ofReal_le_ofReal (neg_le_abs _)) (hb v G H σ y)
    _ = K * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, Coercive.Internal.DensityPassageRest.ampTot v G H σ y := by
        rw [← lintegral_const_mul' _ _ hK]
        refine lintegral_congr fun σ => ?_
        rw [← lintegral_const_mul' _ _ hK]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK)
        (Coercive.Internal.DensityPassageRest.ampTot_finite hPars hv hu)

theorem block_lower_negative_finite (hPars : Coercive.ModeSquareSumHolds) (hDer : Coercive.ModeDerivativeHolds)
    (hRot : Coercive.ModeRotationHolds) (hField : PieceFieldExistsWeakHolds) (hSolenoidal : Coercive.SolenoidalModeHolds)
    (hSP : Coercive.SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : Coercive.IsSmoothApproximation P v G H g u) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-pieceBlockLower m W HW v G H σ y)) < ⊤ := by
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (by simpa using (hW.decay 0 0).1)
  have hS81 : ∀ y, vortGradSupWith HW y ≤ 81 * (D / (1 + ‖y‖) ^ 3) := fun y => by
    unfold vortGradSupWith
    refine Real.iSup_le (fun p => ?_) (by positivity)
    refine (Internal.PieceDensity.norm_vortGradMap_le _).trans ?_
    have h1 := (hW.decay p.1 (axialRot p.2 y)).2.2
    rw [Coercive.RotationInternal.axialRot_norm] at h1
    linarith
  have hD' : ∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ (3 * D) / (1 + ‖y‖) ^ (j + 1) :=
    fun σ y j hj => (decay_one_of hW σ y j hj).trans
      (div_le_div_of_nonneg_right (by linarith) (by positivity))
  have hS' : ∀ y, vortGradSupWith HW y ≤ 27 * ((3 * D) / (1 + ‖y‖) ^ 3) := fun y => by
    have := hS81 y
    rw [show 27 * ((3 * D) / (1 + ‖y‖) ^ 3) = 81 * (D / (1 + ‖y‖) ^ 3) by ring]
    exact this
  obtain ⟨K, hK, hb⟩ := Internal.PassageRest.block_le_one m P h w W hm ⟨3 * D, hD', hS'⟩
  have hpt : ∀ σ y, -pieceBlockLower m W HW v G H σ y ≤ |pieceBlockWith m W HW v G H σ y| := fun σ y => by
    have e := pieceBlockWith_eq m W HW v G H σ y
    have hl := mul_le_mul_of_nonneg_right (vortGradSupLower_le HW y)
      (blockGain_nonneg m hm.eps_wt_nonneg v G σ y)
    have ha := neg_le_abs (pieceBlockWith m W HW v G H σ y)
    unfold pieceBlockLower
    linarith
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-pieceBlockLower m W HW v G H σ y))
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, K * Coercive.Internal.DensityPassageRest.ampTot v G H σ y :=
        lintegral_mono fun σ => lintegral_mono fun y =>
          le_trans (ENNReal.ofReal_le_ofReal (hpt σ y)) (hb v G H σ y)
    _ = K * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, Coercive.Internal.DensityPassageRest.ampTot v G H σ y := by
        rw [← lintegral_const_mul' _ _ hK]
        refine lintegral_congr fun σ => ?_
        rw [← lintegral_const_mul' _ _ hK]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK)
        (Coercive.Internal.DensityPassageRest.ampTot_finite hPars hv hu)

theorem right_finite_lower (hPars : Coercive.ModeSquareSumHolds) (hDer : Coercive.ModeDerivativeHolds)
    (hRot : Coercive.ModeRotationHolds) (hField : PieceFieldExistsWeakHolds) (hSolenoidal : Coercive.SolenoidalModeHolds)
    (hSP : Coercive.SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : Coercive.IsSmoothApproximation P v G H g u) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, Coercive.splitRight (fun σ y ι => pieceRestWith m h w W HW v G H ι σ y) (fun σ y => pieceBlockLower m W HW v G H σ y)
      (stretchFormWith W HW v G) σ y) < ⊤ := by
  have hR := rest_negative_finite_weak hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act hm hW hwb hactm hactp hact2 v G H g u hv hu
  have hB := block_lower_negative_finite hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act hm hW hwb hactm hactp hact2 v G H g u hv hu
  have hJ := Internal.PassageStretch.stretchFormWith_finite hv hW (Coercive.Internal.PassageLimit.weightedVelocity_lt_top hv hu)
  have hJ' : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-stretchFormWith W HW v G σ y)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal (neg_le_abs _)) hJ
  obtain ⟨hRj, -, hBj, hGj⟩ := joint_parts_aemeasurable m P h w Γ W HW D hm hW v G H g hv
  have hRm : AEMeasurable (fun z : ℝ × Space =>
      ∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceRestWith m h w W HW v G H ι z.1 z.2))
      Coercive.PairingSplitInternal.periodMeasure := by
    rw [Coercive.PairingSplitInternal.periodMeasure_eq]
    exact (AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (hRj ι).neg).restrict
  have hBm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (-pieceBlockLower m W HW v G H z.1 z.2))
      Coercive.PairingSplitInternal.periodMeasure := by
    rw [Coercive.PairingSplitInternal.periodMeasure_eq]
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (hBj.sub (((measurable_vortGradSupLower HW).comp measurable_snd).aemeasurable.mul hGj)).neg).restrict
  have e : ∀ σ y, Coercive.splitRight (fun σ y ι => pieceRestWith m h w W HW v G H ι σ y)
      (fun σ y => pieceBlockLower m W HW v G H σ y) (stretchFormWith W HW v G) σ y =
        ENNReal.ofReal (-stretchFormWith W HW v G σ y) + ((∑' ι : ℤ × ℤ,
          ENNReal.ofReal (-pieceRestWith m h w W HW v G H ι σ y))
          + ENNReal.ofReal (-pieceBlockLower m W HW v G H σ y)) := fun σ y => by
    unfold Coercive.splitRight
    rw [add_comm]
  simp only [e]
  rw [Coercive.Internal.DensityPassage.iterated_lintegral_add_right _ (hRm.add hBm),
    Coercive.Internal.DensityPassage.iterated_lintegral_add_right _ hBm]
  exact ENNReal.add_lt_top.2 ⟨hJ', ENNReal.add_lt_top.2 ⟨hR, hB⟩⟩

theorem left_measurable_lower (hPars : Coercive.ModeSquareSumHolds) (hDer : Coercive.ModeDerivativeHolds)
    (hRot : Coercive.ModeRotationHolds) (hField : PieceFieldExistsWeakHolds) (hSolenoidal : Coercive.SolenoidalModeHolds)
    (hSP : Coercive.SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (u₀ : ℝ → Space → Space) (hu₀ : Coercive.IsSmoothPerturbation P u₀) :
    (∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      AEMeasurable (fun y => Coercive.splitLeft (fun σ y ι => Coercive.piecePos m P u₀ (gradField u₀) ι σ y) (fun σ y ι => pieceRestWith m h w W HW u₀ (gradField u₀) (secondDerivField u₀) ι σ y)
        (fun σ y => pieceBlockLower m W HW u₀ (gradField u₀) (secondDerivField u₀) σ y) (stretchFormWith W HW u₀ (gradField u₀)) σ y) volume) ∧
    AEMeasurable (fun σ => ∫⁻ y, Coercive.splitLeft (fun σ y ι => Coercive.piecePos m P u₀ (gradField u₀) ι σ y) (fun σ y ι => pieceRestWith m h w W HW u₀ (gradField u₀) (secondDerivField u₀) ι σ y)
        (fun σ y => pieceBlockLower m W HW u₀ (gradField u₀) (secondDerivField u₀) σ y) (stretchFormWith W HW u₀ (gradField u₀)) σ y)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hv₀ := hSP P u₀ hu₀
  obtain ⟨hR, hJ, hB, hG⟩ := joint_parts_aemeasurable m P h w ∅ W HW D hm hW u₀ (gradField u₀) (secondDerivField u₀)
    (Coercive.transportPart P u₀) hv₀
  have hP := piecePos_aemeasurable m P h w ∅ W HW hm u₀ (gradField u₀) (secondDerivField u₀)
    (Coercive.transportPart P u₀) hv₀
  have hBl : ∀ σ y, ENNReal.ofReal (pieceBlockLower m W HW u₀ (gradField u₀) (secondDerivField u₀) σ y) = 0 :=
    fun σ y => ENNReal.ofReal_of_nonpos (by
      unfold pieceBlockLower
      have h1 := Internal.AbsorbStep.pieceBlockWith_nonpos m W u₀ (gradField u₀) (secondDerivField u₀) 0
        hm.eps_wt_nonneg hm.mu_wt_nonneg σ y
      have h2 := mul_nonneg (vortGradSupLower_nonneg HW y)
        (blockGain_nonneg m hm.eps_wt_nonneg u₀ (gradField u₀) σ y)
      linarith)
  have hf : AEMeasurable (fun z : ℝ × Space => Coercive.splitLeft
      (fun σ y ι => Coercive.piecePos m P u₀ (gradField u₀) ι σ y)
      (fun σ y ι => pieceRestWith m h w W HW u₀ (gradField u₀) (secondDerivField u₀) ι σ y)
      (fun σ y => pieceBlockLower m W HW u₀ (gradField u₀) (secondDerivField u₀) σ y)
      (stretchFormWith W HW u₀ (gradField u₀)) z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    unfold Coercive.splitLeft
    simp only [hBl, add_zero]
    refine Internal.PieceDensityPassageWeak.aemeasurable_slab ?_
    exact (AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (hP ι)).add
      (AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (hR ι))
      |>.add (ENNReal.measurable_ofReal.comp_aemeasurable hJ)
  refine ⟨?_, hf.lintegral_prod_right'⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk] with σ hσ
  exact ⟨fun y => hf.mk _ (σ, y), hf.measurable_mk.comp measurable_prodMk_left, hσ⟩

theorem pieceBlockLower_nonpos {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ)
    (h : HarmonicBounds) (w : Space → ℝ) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (σ : ℝ) (y : Space) : pieceBlockLower m W HW v G H σ y ≤ 0 := by
  have h1 := Internal.AbsorbStep.pieceBlockWith_nonpos m W v G H 0 hm.eps_wt_nonneg hm.mu_wt_nonneg σ y
  have h2 := mul_nonneg (vortGradSupLower_nonneg HW y) (blockGain_nonneg m hm.eps_wt_nonneg v G σ y)
  unfold pieceBlockLower
  linarith

theorem period_parts_aemeasurable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ)
    (h : HarmonicBounds) (w : Space → ℝ) (Γ : Set Symmetry) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) :
    AEMeasurable (fun z : ℝ × Space =>
      ∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceRestWith m h w W HW v G H ι z.1 z.2))
      Coercive.PairingSplitInternal.periodMeasure ∧
    AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (-pieceBlockLower m W HW v G H z.1 z.2))
      Coercive.PairingSplitInternal.periodMeasure ∧
    AEMeasurable (fun z : ℝ × Space => stretchFormWith W HW v G z.1 z.2)
      Coercive.PairingSplitInternal.periodMeasure := by
  obtain ⟨hRj, hJj, hBj, hGj⟩ := joint_parts_aemeasurable m P h w Γ W HW D hm hW v G H g hv
  rw [Coercive.PairingSplitInternal.periodMeasure_eq]
  exact ⟨(AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (hRj ι).neg).restrict,
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (hBj.sub (((measurable_vortGradSupLower HW).comp measurable_snd).aemeasurable.mul hGj)).neg).restrict,
    hJj.restrict⟩

theorem pieces_converge_ae_weak (hPars : Coercive.ModeSquareSumHolds) (hDer : Coercive.ModeDerivativeHolds)
    (hRot : Coercive.ModeRotationHolds) (hField : PieceFieldExistsWeakHolds) (hSolenoidal : Coercive.SolenoidalModeHolds)
    (hSP : Coercive.SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : Coercive.IsSmoothApproximation P v G H g u) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y,
      (∀ ι, Tendsto (fun n => Coercive.piecePos m P (u (φ n)) (gradField (u (φ n))) ι σ y) atTop
        (𝓝 (Coercive.piecePos m P v G ι σ y))) ∧
      (∀ ι, Tendsto (fun n => pieceRestWith m h w W HW (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y)
        atTop (𝓝 (pieceRestWith m h w W HW v G H ι σ y))) ∧
      Tendsto (fun n => stretchFormWith W HW (u (φ n)) (gradField (u (φ n))) σ y) atTop
        (𝓝 (stretchFormWith W HW v G σ y)) := by
  obtain ⟨φ, hφ, hae⟩ := Coercive.Internal.PiecePassageModes.ae_subseq_modes hPars hSP hv hu
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae] with σ hσ
  filter_upwards [hσ] with y hy
  obtain ⟨hV, hG, hH, hu0, hg0⟩ := hy
  exact Internal.PassageStretch.piece_limits_weak m P h w W HW (U := fun n => u (φ n)) hV hG hH hu0 hg0

theorem rest_negative_tendsto_weak (hPars : Coercive.ModeSquareSumHolds) (hDer : Coercive.ModeDerivativeHolds)
    (hRot : Coercive.ModeRotationHolds) (hField : PieceFieldExistsWeakHolds) (hSolenoidal : Coercive.SolenoidalModeHolds)
    (hSP : Coercive.SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : Coercive.IsSmoothApproximation P v G H g u) :
    Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
        ENNReal.ofReal (-pieceRestWith m h w W HW (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y)) atTop
      (𝓝 (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
        ENNReal.ofReal (-pieceRestWith m h w W HW v G H ι σ y))) := by
  have hpn := fun n => hSP P (u n) (hu.1 n)
  have hdec : ∃ D', (∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D' / (1 + ‖y‖) ^ (j + 1)) ∧
      ∀ σ y, ‖HW σ y‖ ≤ D' / (1 + ‖y‖) ^ 3 := ⟨D, decay_one_of hW, fun σ y => (hW.decay σ y).2.2⟩
  obtain ⟨K, -, -, hb⟩ := Internal.PassageDiff.rest_diff_bound_with hm hdec hwb v G H
  have habs : Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
      ENNReal.ofReal |pieceRestWith m h w W HW (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y
        - pieceRestWith m h w W HW v G H ι σ y|) atTop (𝓝 0) :=
    Coercive.Internal.PiecePassageModes.tendsto_of_absorb_bound (K := K)
      (fun n => Coercive.Internal.DensityPassageRest.diffTot_aemeasurable (hpn n).measurable_velocity
        (hpn n).measurable_gradient (hpn n).measurable_secondDeriv hv.measurable_velocity hv.measurable_gradient
        hv.measurable_secondDeriv)
      (Coercive.Internal.DensityPassageRest.ampTot_aemeasurable hv.measurable_velocity hv.measurable_gradient
        hv.measurable_secondDeriv)
      (Coercive.Internal.DensityPassageRest.ampTot_finite hPars hv hu)
      (Coercive.Internal.DensityPassageRest.diffTot_tendsto hPars hSP hv hu)
      (fun t ht n σ y => hb t ht (u n) (gradField (u n)) (secondDerivField (u n)) σ y)
  obtain ⟨K', hK', hb'⟩ := Internal.PassageRest.rest_tsum_le_one m P h w W hm hdec hwb
  have hfin : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
      ENNReal.ofReal |pieceRestWith m h w W HW v G H ι σ y|) < ⊤ := by
    calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
          ENNReal.ofReal |pieceRestWith m h w W HW v G H ι σ y|)
        ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, K' * Coercive.Internal.DensityPassageRest.ampTot v G H σ y :=
          lintegral_mono fun σ => lintegral_mono fun y => hb' v G H σ y
      _ = K' * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, Coercive.Internal.DensityPassageRest.ampTot v G H σ y := by
          rw [← lintegral_const_mul' _ _ hK']
          refine lintegral_congr fun σ => ?_
          rw [← lintegral_const_mul' _ _ hK']
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK')
          (Coercive.Internal.DensityPassageRest.ampTot_finite hPars hv hu)
  have hR0 := (joint_parts_aemeasurable m P h w Γ W HW D hm hW v G H g hv).1
  have hm' : ∀ n, AEMeasurable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ,
      ENNReal.ofReal |pieceRestWith m h w W HW (u n) (gradField (u n)) (secondDerivField (u n)) ι z.1 z.2
        - pieceRestWith m h w W HW v G H ι z.1 z.2|) Coercive.PairingSplitInternal.periodMeasure := fun n => by
    have hRn := (joint_parts_aemeasurable m P h w ∅ W HW D hm hW (u n) (gradField (u n)) (secondDerivField (u n))
      (Coercive.transportPart P (u n)) (hpn n)).1
    rw [Coercive.PairingSplitInternal.periodMeasure_eq]
    exact (AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_abs.measurable.comp_aemeasurable ((hRn ι).sub (hR0 ι)))).restrict
  exact (Coercive.Internal.DensityPassage.tsum_negPart_tendsto
    (R := fun n σ y ι => pieceRestWith m h w W HW (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y)
    (R₀ := fun σ y ι => pieceRestWith m h w W HW v G H ι σ y) hm' hfin habs).2

theorem block_lower_negative_tendsto (hPars : Coercive.ModeSquareSumHolds) (hDer : Coercive.ModeDerivativeHolds)
    (hRot : Coercive.ModeRotationHolds) (hField : PieceFieldExistsWeakHolds) (hSolenoidal : Coercive.SolenoidalModeHolds)
    (hSP : Coercive.SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : Coercive.IsSmoothApproximation P v G H g u) :
    Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ENNReal.ofReal (-pieceBlockLower m W HW (u n) (gradField (u n)) (secondDerivField (u n)) σ y)) atTop
      (𝓝 (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-pieceBlockLower m W HW v G H σ y))) := by
  have hpn := fun n => hSP P (u n) (hu.1 n)
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (by simpa using (hW.decay 0 0).1)
  have hS81 : ∀ y, vortGradSupWith HW y ≤ 81 * (D / (1 + ‖y‖) ^ 3) := fun y => by
    unfold vortGradSupWith
    refine Real.iSup_le (fun p => ?_) (by positivity)
    refine (Internal.PieceDensity.norm_vortGradMap_le _).trans ?_
    have h1 := (hW.decay p.1 (axialRot p.2 y)).2.2
    rw [Coercive.RotationInternal.axialRot_norm] at h1
    linarith
  have hD' : ∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ (3 * D) / (1 + ‖y‖) ^ (j + 1) :=
    fun σ y j hj => (decay_one_of hW σ y j hj).trans
      (div_le_div_of_nonneg_right (by linarith) (by positivity))
  have hS' : ∀ y, vortGradSupLower HW y * (1 + ‖y‖) ≤ 27 * (3 * D) := fun y => by
    have h1 := (vortGradSupLower_le HW y).trans (hS81 y)
    have hp : 0 < 1 + ‖y‖ := by positivity
    have h2 : 81 * (D / (1 + ‖y‖) ^ 3) * (1 + ‖y‖) = 81 * (D / (1 + ‖y‖) ^ 2) := by
      field_simp
    have h3 : D / (1 + ‖y‖) ^ 2 ≤ D := div_le_self hD0 (one_le_pow₀ (by linarith [norm_nonneg y]))
    nlinarith [mul_le_mul_of_nonneg_right h1 hp.le]
  obtain ⟨K, -, -, hb'⟩ := Internal.PassageDiff.block_lower_diff_bound hm ⟨3 * D, hD', hS'⟩ v G H
  have hb : ∀ t : ℝ, 0 < t → ∀ (u' : ℝ → Space → Space) (Gu : ℝ → Space → (Space →L[ℝ] Space))
      (Hu : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space),
      ENNReal.ofReal |pieceBlockLower m W HW u' Gu Hu σ y - pieceBlockLower m W HW v G H σ y|
        ≤ ENNReal.ofReal (K * (1 + 1 / t)) * Coercive.Internal.DensityPassageRestBound.diffTotal u' Gu Hu v G H σ y
          + ENNReal.ofReal (K * t) * Coercive.Internal.DensityPassageRestBound.ampTotal v G H σ y := by
    intro t ht u' Gu Hu σ y
    have e := hb' t ht u' Gu Hu σ y
    simp only [Coercive.Internal.PiecePassageDiffBound.atOrigin] at e
    rwa [Coercive.Internal.PiecePassageDiffBound.tsum_atOrigin_sub] at e
  have habs : Tendsto (fun n => periodLIntegral (fun σ y =>
      |pieceBlockLower m W HW (u n) (gradField (u n)) (secondDerivField (u n)) σ y - pieceBlockLower m W HW v G H σ y|))
      atTop (𝓝 0) := by
    unfold periodLIntegral
    exact Coercive.Internal.PiecePassageModes.tendsto_of_absorb_bound (K := K)
      (fun n => Coercive.Internal.DensityPassageRest.diffTot_aemeasurable (hpn n).measurable_velocity
        (hpn n).measurable_gradient (hpn n).measurable_secondDeriv hv.measurable_velocity hv.measurable_gradient
        hv.measurable_secondDeriv)
      (Coercive.Internal.DensityPassageRest.ampTot_aemeasurable hv.measurable_velocity hv.measurable_gradient
        hv.measurable_secondDeriv)
      (Coercive.Internal.DensityPassageRest.ampTot_finite hPars hv hu)
      (Coercive.Internal.DensityPassageRest.diffTot_tendsto hPars hSP hv hu)
      (fun t ht n σ y => hb t ht (u n) (gradField (u n)) (secondDerivField (u n)) σ y)
  have hjoint : ∀ (Γ' : Set Symmetry) (a : ℝ → Space → Space) (A : ℝ → Space → (Space →L[ℝ] Space))
      (B : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g' : ℝ → Space → Space),
      IsPerturbation Γ' P a A B g' →
      AEMeasurable (fun z : ℝ × Space => pieceBlockLower m W HW a A B z.1 z.2)
        Coercive.PairingSplitInternal.periodMeasure := fun Γ' a A B g' ha => by
    obtain ⟨-, -, hBj, hGj⟩ := joint_parts_aemeasurable m P h w Γ' W HW D hm hW a A B g' ha
    rw [Coercive.PairingSplitInternal.periodMeasure_eq]
    exact (hBj.sub (((measurable_vortGradSupLower HW).comp measurable_snd).aemeasurable.mul hGj)).restrict
  have hf : periodLIntegral (fun σ y => |pieceBlockLower m W HW v G H σ y|) < ⊤ := by
    have e : ∀ σ y, |pieceBlockLower m W HW v G H σ y| = -pieceBlockLower m W HW v G H σ y := fun σ y =>
      abs_of_nonpos (pieceBlockLower_nonpos m P h w W HW hm v G H σ y)
    unfold periodLIntegral
    simp only [e]
    exact block_lower_negative_finite hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act hm hW hwb hactm hactp hact2 v G H g u hv hu
  exact (Coercive.Internal.DensityPassage.negPart_tendsto
    (fun n => hjoint ∅ (u n) (gradField (u n)) (secondDerivField (u n)) _ (hpn n)) (hjoint Γ v G H g hv) hf habs).2

theorem subsequence_limits_lower (hPars : Coercive.ModeSquareSumHolds) (hDer : Coercive.ModeDerivativeHolds)
    (hRot : Coercive.ModeRotationHolds) (hField : PieceFieldExistsWeakHolds) (hSolenoidal : Coercive.SolenoidalModeHolds)
    (hSP : Coercive.SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : Coercive.IsSmoothApproximation P v G H g u) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          Coercive.splitRight (fun σ y ι => pieceRestWith m h w W HW (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y) (fun σ y => pieceBlockLower m W HW (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) σ y) (stretchFormWith W HW (u (φ n)) (gradField (u (φ n)))) σ y) atTop
        (𝓝 (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          Coercive.splitRight (fun σ y ι => pieceRestWith m h w W HW v G H ι σ y) (fun σ y => pieceBlockLower m W HW v G H σ y) (stretchFormWith W HW v G) σ y)) ∧
      ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y,
        Coercive.splitLeft (fun σ y ι => Coercive.piecePos m P v G ι σ y) (fun σ y ι => pieceRestWith m h w W HW v G H ι σ y) (fun σ y => pieceBlockLower m W HW v G H σ y) (stretchFormWith W HW v G) σ y
        ≤ liminf (fun n => Coercive.splitLeft (fun σ y ι => Coercive.piecePos m P (u (φ n)) (gradField (u (φ n))) ι σ y) (fun σ y ι => pieceRestWith m h w W HW (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y) (fun σ y => pieceBlockLower m W HW (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) σ y)
          (stretchFormWith W HW (u (φ n)) (gradField (u (φ n)))) σ y) atTop := by
  obtain ⟨φ, hφ, hae⟩ := pieces_converge_ae_weak hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act hm hW hwb hactm hactp hact2 v G H g u hv hu
  have hpn := fun n => hSP P (u n) (hu.1 n)
  have hv0 := period_parts_aemeasurable m P h w Γ W HW D hm hW v G H g hv
  have hn := fun n => period_parts_aemeasurable m P h w ∅ W HW D hm hW (u n) (gradField (u n)) (secondDerivField (u n))
    (Coercive.transportPart P (u n)) (hpn n)
  have hJ := (Coercive.Internal.DensityPassage.negPart_tendsto (fun n => (hn n).2.2) hv0.2.2
    (Internal.PassageStretch.stretchFormWith_finite hv hW (Coercive.Internal.PassageLimit.weightedVelocity_lt_top hv hu))
    (Internal.PassageStretch.stretchFormWith_tendsto hSP hv hu hW)).2
  have hR := rest_negative_tendsto_weak hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act hm hW hwb hactm hactp hact2 v G H g u hv hu
  have hB := block_lower_negative_tendsto hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act hm hW hwb hactm hactp hact2 v G H g u hv hu
  have hall : Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      Coercive.splitRight (fun σ y ι => pieceRestWith m h w W HW (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y)
        (fun σ y => pieceBlockLower m W HW (u n) (gradField (u n)) (secondDerivField (u n)) σ y)
        (stretchFormWith W HW (u n) (gradField (u n))) σ y) atTop
      (𝓝 (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, Coercive.splitRight (fun σ y ι => pieceRestWith m h w W HW v G H ι σ y)
        (fun σ y => pieceBlockLower m W HW v G H σ y) (stretchFormWith W HW v G) σ y)) := by
    rw [Coercive.Internal.PieceDensityPassageSubsequence.splitRight_split _ _ _ hv0.1 hv0.2.1]
    refine (hJ.add (hR.add hB)).congr fun n => ?_
    exact (Coercive.Internal.PieceDensityPassageSubsequence.splitRight_split _ _ _ (hn n).1 (hn n).2.1).symm
  refine ⟨φ, hφ, hall.comp hφ.tendsto_atTop, ?_⟩
  filter_upwards [hae] with σ hσ
  filter_upwards [hσ] with y hy
  obtain ⟨hp, hr, hj⟩ := hy
  rw [Coercive.Internal.PieceDensityPassageSubsequence.splitLeft_block_eq _ _ _
    (fun σ y => pieceBlockLower_nonpos m P h w W HW hm _ _ _ σ y)]
  simp only [Coercive.Internal.PieceDensityPassageSubsequence.splitLeft_block_eq _ _ _
    (fun σ y => pieceBlockLower_nonpos m P h w W HW hm _ _ _ σ y)]
  exact Coercive.Internal.DensityPassage.splitLeft_le_liminf
    (Pos := fun n σ y ι => Coercive.piecePos m P (u (φ n)) (gradField (u (φ n))) ι σ y)
    (Rest := fun n σ y ι => pieceRestWith m h w W HW (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y)
    (J := fun n => stretchFormWith W HW (u (φ n)) (gradField (u (φ n)))) hp hr hj

end Internal.PieceDensityPassageWeak

open Internal.PieceDensityPassageWeak in
theorem pieceDensityPassageWeakHolds_of (hSmooth : PieceDensitySmoothWeakHolds) (hPars : Coercive.ModeSquareSumHolds) (hDer : Coercive.ModeDerivativeHolds)
    (hRot : Coercive.ModeRotationHolds) (hField : PieceFieldExistsWeakHolds) (hSolenoidal : Coercive.SolenoidalModeHolds)
    (hSP : Coercive.SmoothPerturbationIsPerturbationHolds) :
    PieceDensityPassageWeakHolds := by
  intro C nE nM m P h w k Γ W HW D act w₀ epsSup epsGradSup ratio hm hW hwb hactm hactp hact2
    v G H g hv u hu κ F hFm hFp hF2 hR M hMF
  have hex : ∀ n, ∃ Mn, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) Mn := fun n =>
    let ⟨_, Mn, hMn, _⟩ := hField m P h w ∅ W HW D hm hwb (u n) (gradField (u n)) (secondDerivField (u n))
      (Coercive.transportPart P (u n)) (hSP P (u n) (hu.1 n))
    ⟨Mn, hMn⟩
  choose Mn hMn using hex
  obtain ⟨φ, hφ, hN, hlow⟩ := subsequence_limits_lower hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act
    hm hW hwb hactm hactp hact2 v G H g u hv hu
  have hgap := gap_tendsto_weak hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act hm hW hwb hactm hactp
    hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF Mn hMn
  have hS : ∀ n, Coercive.IsSplitLowerBound
      (m.multiplierGap P w act (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) κ
        (fun σ y => Coercive.smoothRight P W (u (φ n)) σ y + ∑ i, κ i • act i σ y) (Mn (φ n)))
      (fun σ y ι => Coercive.piecePos m P (u (φ n)) (gradField (u (φ n))) ι σ y) (fun σ y ι => pieceRestWith m h w W HW (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y) (fun σ y => pieceBlockLower m W HW (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) σ y) (stretchFormWith W HW (u (φ n)) (gradField (u (φ n)))) := fun n =>
    (split_lower_iff m P h w ∅ W HW D act hm hW hwb hactm hactp hact2 (u (φ n)) (gradField (u (φ n)))
      (secondDerivField (u (φ n))) (Coercive.transportPart P (u (φ n))) (hSP P (u (φ n)) (hu.1 (φ n))) _).1
      (hSmooth m P h w W HW D act hm hW hwb hactm hactp hact2 (u (φ n)) (hu.1 (φ n)) κ (Mn (φ n)) (hMn (φ n)))
  refine (split_lower_iff m P h w Γ W HW D act hm hW hwb hactm hactp hact2 v G H g hv _).2 ?_
  exact Coercive.Internal.PassageLimit.isSplitLowerBound_of_liminf hS (hgap.comp hφ.tendsto_atTop) hN
    (right_finite_lower hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act hm hW hwb hactm hactp hact2
      v G H g u hv hu)
    (fun n => (left_measurable_lower hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act hm hW hwb hactm
      hactp hact2 (u (φ n)) (hu.1 (φ n))).1)
    (fun n => (left_measurable_lower hPars hDer hRot hField hSolenoidal hSP m P h w Γ W HW D act hm hW hwb hactm
      hactp hact2 (u (φ n)) (hu.1 (φ n))).2)
    hlow

end CoerciveWeak

end Breakdown
