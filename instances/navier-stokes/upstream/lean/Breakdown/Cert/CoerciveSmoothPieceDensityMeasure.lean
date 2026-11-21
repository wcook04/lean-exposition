import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoercivePieceAbsorb
import Breakdown.Cert.CoerciveSmoothPieceDensityBlock

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceDensity

open Internal.PieceAbsorb

section Pieces

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
  (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
  (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))

theorem parts_measurable {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hv : IsSmoothPerturbation P v) :
    (∀ β, AEMeasurable (fun z : ℝ × Space =>
      ∑' ι, ENNReal.ofReal (pieceEpsPos m P (gradField v) β ι z.1 z.2)) slabMeasure) ∧
    (∀ β, AEMeasurable (fun z : ℝ × Space =>
      ∑' ι, ENNReal.ofReal (pieceMuPos m P v β ι z.1 z.2)) slabMeasure) ∧
    AEMeasurable (fun z : ℝ × Space => ∑' ι, ENNReal.ofReal
      (modeVals v (gradField v) (secondDerivField v) ι z.1 z.2 (baseDensity m.convD m.convZ (m.classOf ι) m.c w z.2)))
      slabMeasure ∧
    (∀ β, AEMeasurable (fun z : ℝ × Space =>
      (∑' ι, ENNReal.ofReal (-pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι z.1 z.2))
        + ENNReal.ofReal (-pieceEpsBlock m W v (gradField v) (secondDerivField v) β z.1 z.2)) slabMeasure) ∧
    (∀ β, AEMeasurable (fun z : ℝ × Space =>
      (∑' ι, ENNReal.ofReal (-pieceMuRestMode m h W v (gradField v) β ι z.1 z.2))
        + ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β z.1 z.2)) slabMeasure) := by
  obtain ⟨hbE, hbM⟩ := aemeasurable_block_terms m P h w W v hm hW hWdecay hv
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by norm_cast)
  have hvc : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume := hv2.continuous.aestronglyMeasurable
  have hG : AEStronglyMeasurable (fun z : ℝ × Space => gradField v z.1 z.2) volume :=
    (continuous_fderiv_slice hv2).aestronglyMeasurable
  have hH : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivField v z.1 z.2) volume :=
    (measurable_secondDeriv_slice hv2).aestronglyMeasurable
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
  have hEP : ∀ β ι, AEMeasurable (fun z : ℝ × Space => pieceEpsPos m P (gradField v) β ι z.1 z.2) volume := by
    intro β ι
    unfold pieceEpsPos
    have h1 := hwE β
    have h2 := aem_vortAmp hG ι
    fun_prop
  have hMP : ∀ β ι, AEMeasurable (fun z : ℝ × Space => pieceMuPos m P v β ι z.1 z.2) volume := by
    intro β ι
    unfold pieceMuPos
    have h1 := hwM β
    have h2 := aem_velAmp hvc ι
    fun_prop
  have hBase : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      modeVals v (gradField v) (secondDerivField v) ι z.1 z.2 (baseDensity m.convD m.convZ (m.classOf ι) m.c w z.2))
      volume := by
    intro ι
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
  have hER : ∀ β ι, AEMeasurable (fun z : ℝ × Space =>
      pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι z.1 z.2) volume := by
    intro β ι
    have h1 := hwE β
    have ao := aem_vortAmp hG ι
    have e1 := aem_edgeSum h (m.epsP β).modes (X := fun z α => velAmp W α z.1 z.2)
      (g := fun z κ => vortGradAmp (secondDerivField v) κ z.1 z.2) (fun α => aem_velAmp hWc α)
      (fun κ => aem_vortGradAmp hH κ) ι
    have e2 := aem_edgeSum h (m.epsP β).modes (X := fun z α => gradAmp (gradField W) α z.1 z.2)
      (g := fun z κ => vortAmp (gradField v) κ z.1 z.2) (fun α => aem_gradAmp hgW α)
      (fun κ => aem_vortAmp hG κ) ι
    have e3 := aem_edgeSum h (m.epsP β).modes (X := fun z α => vortGradAmp (secondDerivField W) α z.1 z.2)
      (g := fun z κ => velAmp v κ z.1 z.2) (fun α => aem_vortGradAmp hhW α)
      (fun κ => aem_velAmp hvc κ) ι
    have e4 := aem_edgeSum h (m.epsP β).modes (X := fun z α => vortAmp (gradField W) α z.1 z.2)
      (g := fun z κ => gradAmp (gradField v) κ z.1 z.2) (fun α => aem_vortAmp hgW α)
      (fun κ => aem_gradAmp hG κ) ι
    unfold pieceEpsRestMode
    exact (((h1.comp_aemeasurable measurable_snd.aemeasurable).mul ao).mul
      (((e1.add e2).add e3).add e4)).neg
  have hMR : ∀ β ι, AEMeasurable (fun z : ℝ × Space =>
      pieceMuRestMode m h W v (gradField v) β ι z.1 z.2) volume := by
    intro β ι
    have h1 := hwM β
    have a0 := aem_velAmp hvc ι
    have e1 := aem_edgeSum h (m.muP β).modes (X := fun z α => velAmp W α z.1 z.2)
      (g := fun z κ => gradAmp (gradField v) κ z.1 z.2) (fun α => aem_velAmp hWc α)
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
  rw [slabMeasure_eq] at hbE hbM ⊢
  refine ⟨fun β => ?_, fun β => ?_, ?_, fun β => ?_, fun β => ?_⟩
  · exact (AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (hEP β ι)).restrict
  · exact (AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (hMP β ι)).restrict
  · exact (AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (hBase ι)).restrict
  · exact (AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (hER β ι).neg).restrict.add
      (hbE β)
  · exact (AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (hMR β ι).neg).restrict.add
      (hbM β)

theorem abs_sgn_eq (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) :
    |PieceWeights.sgn T ι| = ModeWeights.ind (PieceWeights.inPiece T ι) := by
  unfold PieceWeights.sgn ModeWeights.ind PieceWeights.inPiece
  by_cases h1 : ι ∈ T
  · simp [h1]
  · by_cases h2 : -ι ∈ T
    · simp [h1, h2]
    · simp [h1, h2]

theorem sum_le_dbl {ι : Type*} (s : Finset ι) (f : ι → ℝ → Space → ℝ≥0∞) :
    ∑ i ∈ s, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f i σ y)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑ i ∈ s, f i σ y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.sum_insert hi]
    refine (add_le_add le_rfl ih).trans ?_
    refine (le_lintegral_add_iter (fun σ y => f i σ y) (fun σ y => ∑ j ∈ s, f j σ y)).trans (le_of_eq ?_)
    simp only [Finset.sum_insert hi]

theorem part_finite (hc : m.cμ < 1) (β : Fin nM) {X : ℝ} {Rest : ℝ → Space → ℤ × ℤ → ℝ}
    {Blk : ℝ → Space → ℝ}
    (hS : IsSplitLowerBound X (fun σ y ι => pieceMuPos m P v β ι σ y) Rest Blk (fun _ _ => 0)) :
    pieceSeminormPart m P β v < ⊤ := by
  obtain ⟨h1, h2⟩ := hS
  simp only [neg_zero, ENNReal.ofReal_zero, add_zero] at h2
  have hpos : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (pieceMuPos m P v β ι σ y)) < ⊤ := by
    refine lt_of_le_of_lt (le_trans (lintegral_mono fun σ => lintegral_mono fun y => ?_) le_self_add)
      (lt_of_le_of_lt h2 (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, h1⟩))
    exact le_self_add.trans le_self_add
  have hcpos : 0 < 1 - m.cμ := sub_pos.2 hc
  have hpt : ∀ ι σ y, ENNReal.ofReal (1 - m.cμ) * ENNReal.ofReal (|PieceWeights.sgn (m.muP β).modes ι|
      * |PieceWeights.frameFreq P (m.muP β).frame ι| * (m.muP β).wt y * cnormSq (modeVel ι v σ y))
      ≤ ENNReal.ofReal (pieceMuPos m P v β ι σ y) := by
    intro ι σ y
    rw [← ENNReal.ofReal_mul hcpos.le]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    unfold pieceMuPos velAmp
    rw [abs_sgn_eq, Real.sq_sqrt (cnormSq_nonneg' _)]
    ring
  have key : ENNReal.ofReal (1 - m.cμ) * pieceSeminormPart m P β v
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (pieceMuPos m P v β ι σ y) := by
    unfold pieceSeminormPart
    rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    refine le_trans (Finset.sum_le_sum fun ι _ => ?_) ((sum_le_dbl s _).trans
      (lintegral_mono fun σ => lintegral_mono fun y => ENNReal.sum_le_tsum s))
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun σ => by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_mono fun y => hpt ι σ y
  have hne : ENNReal.ofReal (1 - m.cμ) ≠ 0 := by
    simpa using hcpos
  by_contra hT
  rw [not_lt, top_le_iff] at hT
  rw [hT, ENNReal.mul_top hne] at key
  exact (lt_of_le_of_lt key hpos).ne rfl

end Pieces

end Internal.SmoothPieceDensity

end Coercive

end Breakdown
