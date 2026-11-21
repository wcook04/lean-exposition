import Breakdown.Cert.CoerciveSmoothPieceDensity
import Breakdown.Cert.CoerciveSmoothDensityIntegrable
import Breakdown.Cert.CoercivePieceDensityPassageLimit

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PieceDensityPassageMeasure

open Internal.SmoothPieceDensity Internal.PieceAbsorb

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {w : Space → ℝ}
  {W v : ℝ → Space → Space}

theorem pieceBlock_nonpos (hm0 : ∀ β y, 0 ≤ (m.epsP β).wt y) (hm1 : ∀ β y, 0 ≤ (m.muP β).wt y)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    pieceBlock m W v G H σ y ≤ 0 := by
  unfold pieceBlock
  have e := Finset.sum_nonpos fun β (_ : β ∈ Finset.univ) => epsBlock_nonpos m W v G H hm0 β σ y
  have u := Finset.sum_nonpos fun β (_ : β ∈ Finset.univ) => muBlock_nonpos m W v G hm1 β σ y
  linarith

theorem piece_parts_aemeasurable_of {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hvc : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => piecePos m P v G ι z.1 z.2) volume ∧
      AEMeasurable (fun z : ℝ × Space => pieceRest m h w W v G H ι z.1 z.2) volume := by
  have hWc : AEStronglyMeasurable (fun z : ℝ × Space => W z.1 z.2) volume := hW.continuous.aestronglyMeasurable
  have hgW : AEStronglyMeasurable (fun z : ℝ × Space => gradField W z.1 z.2) volume :=
    (continuous_fderiv_slice hW).aestronglyMeasurable
  have hhW : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivField W z.1 z.2) volume :=
    (measurable_secondDeriv_slice hW).aestronglyMeasurable
  have hwE : ∀ β, Measurable (m.epsP β).wt := fun β => by
    obtain ⟨K, hK⟩ := hm.eps_increment β
    exact hK.continuous.measurable
  have hwM : ∀ β, Measurable (m.muP β).wt := fun β => by
    obtain ⟨K, hK⟩ := hm.mu_increment β
    exact hK.continuous.measurable
  have hEP : ∀ β, AEMeasurable (fun z : ℝ × Space => pieceEpsPos m P G β ι z.1 z.2) volume := by
    intro β
    unfold pieceEpsPos
    have h1 := hwE β
    have h2 := aem_vortAmp hG ι
    fun_prop
  have hMP : ∀ β, AEMeasurable (fun z : ℝ × Space => pieceMuPos m P v β ι z.1 z.2) volume := by
    intro β
    unfold pieceMuPos
    have h1 := hwM β
    have h2 := aem_velAmp hvc ι
    fun_prop
  have hBase : AEMeasurable (fun z : ℝ × Space =>
      modeVals v G H ι z.1 z.2 (baseDensity m.convD m.convZ (m.classOf ι) m.c w z.2))
      volume := by
    have a2 := aem_secondDerivAmp hH ι
    have ac := aem_vortGradAmp hH ι
    have a1 := aem_gradAmp hG ι
    have ao := aem_vortAmp hG ι
    have a0 := aem_velAmp hvc ι
    have hD : Measurable (m.convD (m.classOf ι)) := (hm.convD_smooth _).continuous.measurable
    have hZ : Measurable (m.convZ (m.classOf ι)) := (hm.convZ_smooth _).continuous.measurable
    have hDD : Measurable (ModeWeights.secondDerivNorm (m.convD (m.classOf ι))) :=
      ((hm.convD_smooth _).continuous_iteratedFDeriv le_rfl).norm.measurable
    have hZZ : Measurable (ModeWeights.secondDerivNorm (m.convZ (m.classOf ι))) :=
      ((hm.convZ_smooth _).continuous_iteratedFDeriv le_rfl).norm.measurable
    have hw := hm.weight_measurable
    unfold modeVals baseDensity
    fun_prop
  have hER : ∀ β, AEMeasurable (fun z : ℝ × Space =>
      pieceEpsRestMode m h W v G H β ι z.1 z.2) volume := by
    intro β
    have h1 := hwE β
    have ao := aem_vortAmp hG ι
    have e1 := aem_edgeSum h (m.epsP β).modes (X := fun z α => velAmp W α z.1 z.2)
      (g := fun z κ => vortGradAmp H κ z.1 z.2) (fun α => aem_velAmp hWc α)
      (fun κ => aem_vortGradAmp hH κ) ι
    have e2 := aem_edgeSum h (m.epsP β).modes (X := fun z α => gradAmp (gradField W) α z.1 z.2)
      (g := fun z κ => vortAmp G κ z.1 z.2) (fun α => aem_gradAmp hgW α)
      (fun κ => aem_vortAmp hG κ) ι
    have e3 := aem_edgeSum h (m.epsP β).modes (X := fun z α => vortGradAmp (secondDerivField W) α z.1 z.2)
      (g := fun z κ => velAmp v κ z.1 z.2) (fun α => aem_vortGradAmp hhW α)
      (fun κ => aem_velAmp hvc κ) ι
    have e4 := aem_edgeSum h (m.epsP β).modes (X := fun z α => vortAmp (gradField W) α z.1 z.2)
      (g := fun z κ => gradAmp G κ z.1 z.2) (fun α => aem_vortAmp hgW α)
      (fun κ => aem_gradAmp hG κ) ι
    unfold pieceEpsRestMode
    exact (((h1.comp_aemeasurable measurable_snd.aemeasurable).mul ao).mul
      (((e1.add e2).add e3).add e4)).neg
  have hMR : ∀ β, AEMeasurable (fun z : ℝ × Space =>
      pieceMuRestMode m h W v G β ι z.1 z.2) volume := by
    intro β
    have h1 := hwM β
    have a0 := aem_velAmp hvc ι
    have e1 := aem_edgeSum h (m.muP β).modes (X := fun z α => velAmp W α z.1 z.2)
      (g := fun z κ => gradAmp G κ z.1 z.2) (fun α => aem_velAmp hWc α)
      (fun κ => aem_gradAmp hG κ) ι
    have s1 : AEMeasurable (fun z : ℝ × Space =>
        ∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) volume :=
      Finset.aemeasurable_fun_sum _ fun α _ => (aem_gradAmp hgW α).mul (aem_velAmp hvc _)
    have hw1 : AEMeasurable (fun z : ℝ × Space => (m.muP β).wt z.2) volume :=
      h1.comp_aemeasurable measurable_snd.aemeasurable
    have q1 : AEMeasurable (fun z : ℝ × Space =>
        (∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) ^ 2
            / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2) volume :=
      ((s1.pow_const 2).div_const _).add ((aemeasurable_const.mul (hw1.pow_const 2)).mul (a0.pow_const 2))
    unfold pieceMuRestMode
    exact (((hw1.mul a0).mul e1).neg).sub (q1.const_mul (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)))
  refine ⟨?_, ?_⟩
  · unfold piecePos
    exact (Finset.aemeasurable_fun_sum _ fun β _ => hEP β).add (Finset.aemeasurable_fun_sum _ fun β _ => hMP β)
  · unfold pieceRest
    exact (hBase.add (Finset.aemeasurable_fun_sum _ fun β _ => hER β)).add
      (Finset.aemeasurable_fun_sum _ fun β _ => hMR β)

theorem piece_parts_aemeasurable {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => piecePos m P v (gradField v) ι z.1 z.2) volume ∧
      AEMeasurable (fun z : ℝ × Space => pieceRest m h w W v (gradField v) (secondDerivField v) ι z.1 z.2) volume := by
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by norm_cast)
  exact piece_parts_aemeasurable_of hm hW hv2.continuous.aestronglyMeasurable
    (continuous_fderiv_slice hv2).aestronglyMeasurable (measurable_secondDeriv_slice hv2).aestronglyMeasurable ι

theorem pieceBlock_aemeasurable_of {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hGm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hHm : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) :
    AEMeasurable (fun z : ℝ × Space => pieceBlock m W v G H z.1 z.2) volume := by
  have hvS : AEMeasurable (fun z : ℝ × Space => vortSup W z.2) volume :=
    ((measurable_vortSup hW hm.supVort_ge).comp measurable_snd).aemeasurable
  have hvGS : AEMeasurable (fun z : ℝ × Space => vortGradSup W z.2) volume :=
    ((measurable_vortGradSup hW hm.supGradVort_ge).comp measurable_snd).aemeasurable
  have hG3 := fun κ => aem_gradAmp hGm κ
  have hV3 := fun κ => aem_velAmp hvm κ
  have hE : ∀ β, AEMeasurable (fun z : ℝ × Space => pieceEpsBlock m W v G H β z.1 z.2) volume := by
    intro β
    have hwt : AEMeasurable (fun z : ℝ × Space => (m.epsP β).wt z.2) volume := by
      obtain ⟨K, hK⟩ := hm.eps_increment β
      exact (hK.continuous.measurable.comp measurable_snd).aemeasurable
    have hwg : AEMeasurable (fun z : ℝ × Space => PieceWeights.wtGrad (m.epsP β).wt z.2) volume :=
      (((measurable_fderiv ℝ (m.epsP β).wt).norm).comp measurable_snd).aemeasurable
    have hfs : AEMeasurable (fun z : ℝ × Space => frameSpeedSup W (m.epsP β).frame z.2) volume :=
      ((measurable_frameSpeedSup hW (hm.epsSpeed_ge β)).comp measurable_snd).aemeasurable
    have p1 := aemeasurable_pieceNorm (m.epsP β).modes
      (g := fun κ z => vortGradAmp H κ z.1 z.2) fun κ => aem_vortGradAmp hHm κ
    have p2 := aemeasurable_pieceNorm (m.epsP β).modes
      (g := fun κ z => vortAmp G κ z.1 z.2) fun κ => aem_vortAmp hGm κ
    have p3 := aemeasurable_pieceNorm (m.epsP β).modes (g := fun κ z => velAmp v κ z.1 z.2) hV3
    have p4 := aemeasurable_pieceNorm (m.epsP β).modes
      (g := fun κ z => gradAmp G κ z.1 z.2) hG3
    beta_reduce at p1 p2 p3 p4
    have t1 := ((((hwt.mul hfs).add hwg).mul p1).mul p2).neg
    have t2 := (hwt.mul ((aemeasurable_const (b := (1 / 2 : ℝ))).mul hvS |>.add
      (aemeasurable_const (b := |(m.epsP β).frame|)))).mul (p2.pow_const 2)
    have t3 := ((hwt.mul hvGS).mul p3).mul p2
    have t4 := ((hwt.mul hvS).mul p4).mul p2
    exact (((t1.sub t2).sub t3).sub t4)
  have hM : ∀ β, AEMeasurable (fun z : ℝ × Space => pieceMuBlock m W v G β z.1 z.2) volume := by
    intro β
    have hwt : AEMeasurable (fun z : ℝ × Space => (m.muP β).wt z.2) volume := by
      obtain ⟨K, hK⟩ := hm.mu_increment β
      exact (hK.continuous.measurable.comp measurable_snd).aemeasurable
    have hwg : AEMeasurable (fun z : ℝ × Space => PieceWeights.wtGrad (m.muP β).wt z.2) volume :=
      (((measurable_fderiv ℝ (m.muP β).wt).norm).comp measurable_snd).aemeasurable
    have hfs : AEMeasurable (fun z : ℝ × Space => frameSpeedSup W (m.muP β).frame z.2) volume :=
      ((measurable_frameSpeedSup hW (hm.muSpeed_ge β)).comp measurable_snd).aemeasurable
    have p3 := aemeasurable_pieceNorm (m.muP β).modes (g := fun κ z => velAmp v κ z.1 z.2) hV3
    have p4 := aemeasurable_pieceNorm (m.muP β).modes
      (g := fun κ z => gradAmp G κ z.1 z.2) hG3
    beta_reduce at p3 p4
    have t1 := ((((hwt.mul hfs).add hwg).mul p4).mul p3).neg
    have t2 := (hwt.mul (aemeasurable_const (b := |(m.muP β).frame|))).mul (p3.pow_const 2)
    exact t1.sub t2
  unfold pieceBlock
  exact (Finset.aemeasurable_fun_sum _ fun β _ => hE β).add (Finset.aemeasurable_fun_sum _ fun β _ => hM β)

theorem pieceSplitLeft_aemeasurable {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hv : IsSmoothPerturbation P v) :
    (∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      AEMeasurable (fun y => splitLeft (fun σ y ι => piecePos m P v (gradField v) ι σ y)
        (fun σ y ι => pieceRest m h w W v (gradField v) (secondDerivField v) ι σ y)
        (fun σ y => pieceBlock m W v (gradField v) (secondDerivField v) σ y) (stretchForm W v (gradField v)) σ y) volume) ∧
    AEMeasurable (fun σ => ∫⁻ y, splitLeft (fun σ y ι => piecePos m P v (gradField v) ι σ y)
        (fun σ y ι => pieceRest m h w W v (gradField v) (secondDerivField v) ι σ y)
        (fun σ y => pieceBlock m W v (gradField v) (secondDerivField v) σ y) (stretchForm W v (gradField v)) σ y)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hJ : AEMeasurable (fun z : ℝ × Space => stretchForm W v (gradField v) z.1 z.2) slabMeasure :=
    (Internal.SmoothDensity.stretch_integrable hv hW hWdecay).aestronglyMeasurable.aemeasurable
  have hB : (fun z : ℝ × Space => ENNReal.ofReal (pieceBlock m W v (gradField v) (secondDerivField v) z.1 z.2)) =
      fun _ => 0 := by
    funext z
    exact ENNReal.ofReal_of_nonpos (pieceBlock_nonpos hm.eps_wt_nonneg hm.mu_wt_nonneg _ _ z.1 z.2)
  have hf : AEMeasurable (fun z : ℝ × Space => splitLeft (fun σ y ι => piecePos m P v (gradField v) ι σ y)
      (fun σ y ι => pieceRest m h w W v (gradField v) (secondDerivField v) ι σ y)
      (fun σ y => pieceBlock m W v (gradField v) (secondDerivField v) σ y)
      (stretchForm W v (gradField v)) z.1 z.2) slabMeasure := by
    unfold splitLeft
    have hB' : AEMeasurable (fun z : ℝ × Space =>
        ENNReal.ofReal (pieceBlock m W v (gradField v) (secondDerivField v) z.1 z.2)) slabMeasure := by
      rw [hB]; exact aemeasurable_const
    rw [slabMeasure_eq] at hJ hB' ⊢
    exact (((AEMeasurable.ennreal_tsum fun ι =>
      ENNReal.measurable_ofReal.comp_aemeasurable (piece_parts_aemeasurable hm hW hv ι).1.restrict).add
      (AEMeasurable.ennreal_tsum fun ι =>
        ENNReal.measurable_ofReal.comp_aemeasurable (piece_parts_aemeasurable hm hW hv ι).2.restrict)).add
      hB').add hJ.ennreal_ofReal
  refine ⟨?_, hf.lintegral_prod_right'⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk] with σ hσ
  exact ⟨fun y => hf.mk _ (σ, y), hf.measurable_mk.comp measurable_prodMk_left, hσ⟩

end Internal.PieceDensityPassageMeasure

end Coercive

end Breakdown
