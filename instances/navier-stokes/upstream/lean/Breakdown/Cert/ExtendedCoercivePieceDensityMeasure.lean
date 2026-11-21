import Breakdown.Cert.ExtendedCoerciveStatement
import Breakdown.Cert.CoerciveSmoothPieceDensityMeasure

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

open PieceWeights

def epsBlockLower {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W : ℝ → Space → Space)
    (s : Space → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (β : Fin nE) (σ : ℝ) (y : Space) : ℝ :=
  -(((m.epsP β).wt y * Coercive.frameSpeedSup W (m.epsP β).frame y + wtGrad (m.epsP β).wt y)
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.vortGradAmp H κ σ y)
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.vortAmp G κ σ y))
    - (m.epsP β).wt y * ((1 / 2) * Coercive.vortSup W y + |(m.epsP β).frame|)
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.vortAmp G κ σ y) ^ 2
    - (m.epsP β).wt y * s y
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.velAmp v κ σ y)
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.vortAmp G κ σ y)
    - (m.epsP β).wt y * Coercive.vortSup W y
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.gradAmp G κ σ y)
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.vortAmp G κ σ y)

namespace Internal.PieceDensity

open Coercive Coercive.Internal.PieceAbsorb Coercive.Internal.SmoothPieceDensity Coercive.Internal.ModeRotation

theorem continuous_fderiv_slice_one {W : ℝ → Space → Space}
    (h : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) := by
  have h2 : ContDiff ℝ 1 (Function.uncurry fun (z : ℝ × Space) (y : Space) => W z.1 y) :=
    h.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact (h2.fderiv (g := fun z : ℝ × Space => z.2) contDiff_snd (n := 0) (by norm_num)).continuous

theorem measurable_frameSpeedSup_one {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) {a : ℝ} {s : Space → ℝ}
    (hb : ∀ σ φ y, ‖W σ (axialRot φ y) + (1 / 2 : ℝ) • axialRot φ y
      - a • (-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1)‖ ≤ s y) :
    Measurable (frameSpeedSup W a) := by
  unfold frameSpeedSup
  refine measurable_iSup_of (s := s) (fun p => ?_) (fun p y => hb p.1 p.2 y)
  have hR : Continuous (fun y => axialRot p.2 y) :=
    Continuous.comp (g := fun q : ℝ × Space => axialRot q.1 q.2) (f := fun y : Space => (p.2, y))
      continuous_axialRot (continuous_const.prodMk continuous_id)
  have hWc : Continuous (fun x => W p.1 x) :=
    Continuous.comp (g := fun q : ℝ × Space => W q.1 q.2) (f := fun x : Space => (p.1, x))
      hW.continuous (continuous_const.prodMk continuous_id)
  have h0 : Continuous (fun y => axialRot p.2 y 0) := (continuous_coord 0).comp hR
  have h1 : Continuous (fun y => axialRot p.2 y 1) := (continuous_coord 1).comp hR
  have hWR : Continuous (fun y => W p.1 (axialRot p.2 y)) :=
    Continuous.comp (g := fun x => W p.1 x) (f := fun y => axialRot p.2 y) hWc hR
  fun_prop

theorem measurable_vortSup_one {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    {s : Space → ℝ} (hb : ∀ σ φ y, ‖curlVec (fderiv ℝ (W σ) (axialRot φ y))‖ ≤ s y) :
    Measurable (vortSup W) := by
  unfold vortSup
  refine measurable_iSup_of (s := s) (fun p => ?_) (fun p y => hb p.1 p.2 y)
  have hR : Continuous (fun y => axialRot p.2 y) :=
    Continuous.comp (g := fun q : ℝ × Space => axialRot q.1 q.2) (f := fun y : Space => (p.2, y))
      continuous_axialRot (continuous_const.prodMk continuous_id)
  have hD : Continuous (fun y => fderiv ℝ (W p.1) (axialRot p.2 y)) :=
    Continuous.comp (g := fun q : ℝ × Space => fderiv ℝ (W q.1) q.2) (f := fun y : Space => (p.1, axialRot p.2 y))
      (continuous_fderiv_slice_one hW) (continuous_const.prodMk hR)
  exact (Continuous.comp (g := curlVec) contDiff_curlVec.continuous hD).norm

section Pieces

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
  (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
  (v : ℝ → Space → Space)

theorem parts_measurable {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hW : IsWeakSecondDerivState W HW D) (hv : Coercive.IsSmoothPerturbation P v)
    {s : Space → ℝ} (hs : Measurable s) :
    (∀ β ι, AEMeasurable (fun z : ℝ × Space => Coercive.pieceEpsPos m P (gradField v) β ι z.1 z.2) volume) ∧
    (∀ β ι, AEMeasurable (fun z : ℝ × Space => Coercive.pieceMuPos m P v β ι z.1 z.2) volume) ∧
    (∀ ι, AEMeasurable (fun z : ℝ × Space => Coercive.modeVals v (gradField v) (secondDerivField v) ι z.1 z.2
      (Coercive.baseDensity m.convD m.convZ (m.classOf ι) m.c w z.2)) volume) ∧
    (∀ β ι, AEMeasurable (fun z : ℝ × Space =>
      pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι z.1 z.2) volume) ∧
    (∀ β ι, AEMeasurable (fun z : ℝ × Space =>
      Coercive.pieceMuRestMode m h W v (gradField v) β ι z.1 z.2) volume) ∧
    (∀ β, AEMeasurable (fun z : ℝ × Space =>
      epsBlockLower m W s v (gradField v) (secondDerivField v) β z.1 z.2) volume) ∧
    (∀ β, AEMeasurable (fun z : ℝ × Space => Coercive.pieceMuBlock m W v (gradField v) β z.1 z.2) volume) ∧
    (∀ β, AEMeasurable (fun z : ℝ × Space => (m.epsP β).wt z.2
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.velAmp v κ z.1 z.2)
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.vortAmp (gradField v) κ z.1 z.2)) volume) := by
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by norm_cast)
  have hvc : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume := hv2.continuous.aestronglyMeasurable
  have hG : AEStronglyMeasurable (fun z : ℝ × Space => gradField v z.1 z.2) volume :=
    (continuous_fderiv_slice hv2).aestronglyMeasurable
  have hH : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivField v z.1 z.2) volume :=
    (measurable_secondDeriv_slice hv2).aestronglyMeasurable
  have hWc : AEStronglyMeasurable (fun z : ℝ × Space => W z.1 z.2) volume :=
    hW.smooth.continuous.aestronglyMeasurable
  have hgW : AEStronglyMeasurable (fun z : ℝ × Space => gradField W z.1 z.2) volume :=
    (continuous_fderiv_slice_one hW.smooth).aestronglyMeasurable
  have hhW : AEStronglyMeasurable (fun z : ℝ × Space => HW z.1 z.2) volume := hW.secondDeriv_measurable
  have hwE : ∀ β, Measurable (m.epsP β).wt := fun β => by
    obtain ⟨K, hK⟩ := hm.eps_increment β
    exact hK.continuous.measurable
  have hwM : ∀ β, Measurable (m.muP β).wt := fun β => by
    obtain ⟨K, hK⟩ := hm.mu_increment β
    exact hK.continuous.measurable
  have hvS : AEMeasurable (fun z : ℝ × Space => vortSup W z.2) volume :=
    ((measurable_vortSup_one hW.smooth hm.supVort_ge).comp measurable_snd).aemeasurable
  have hsS : AEMeasurable (fun z : ℝ × Space => s z.2) volume := (hs.comp measurable_snd).aemeasurable
  have hG3 := fun κ => aem_gradAmp hG κ
  have hV3 := fun κ => aem_velAmp hvc κ
  refine ⟨fun β ι => ?_, fun β ι => ?_, fun ι => ?_, fun β ι => ?_, fun β ι => ?_, fun β => ?_, fun β => ?_,
    fun β => ?_⟩
  · unfold pieceEpsPos
    have h1 := hwE β
    have h2 := aem_vortAmp hG ι
    fun_prop
  · unfold pieceMuPos
    have h1 := hwM β
    have h2 := aem_velAmp hvc ι
    fun_prop
  · have a2 := aem_secondDerivAmp hH ι
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
  · have h1 := hwE β
    have ao := aem_vortAmp hG ι
    have e1 := aem_edgeSum h (m.epsP β).modes (X := fun z α => velAmp W α z.1 z.2)
      (g := fun z κ => vortGradAmp (secondDerivField v) κ z.1 z.2) (fun α => aem_velAmp hWc α)
      (fun κ => aem_vortGradAmp hH κ) ι
    have e2 := aem_edgeSum h (m.epsP β).modes (X := fun z α => gradAmp (gradField W) α z.1 z.2)
      (g := fun z κ => vortAmp (gradField v) κ z.1 z.2) (fun α => aem_gradAmp hgW α)
      (fun κ => aem_vortAmp hG κ) ι
    have e3 := aem_edgeSum h (m.epsP β).modes (X := fun z α => vortGradAmp HW α z.1 z.2)
      (g := fun z κ => velAmp v κ z.1 z.2) (fun α => aem_vortGradAmp hhW α)
      (fun κ => aem_velAmp hvc κ) ι
    have e4 := aem_edgeSum h (m.epsP β).modes (X := fun z α => vortAmp (gradField W) α z.1 z.2)
      (g := fun z κ => gradAmp (gradField v) κ z.1 z.2) (fun α => aem_vortAmp hgW α)
      (fun κ => aem_gradAmp hG κ) ι
    unfold pieceEpsRestModeWith
    exact (((h1.comp_aemeasurable measurable_snd.aemeasurable).mul ao).mul
      (((e1.add e2).add e3).add e4)).neg
  · have h1 := hwM β
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
  · have hwt : AEMeasurable (fun z : ℝ × Space => (m.epsP β).wt z.2) volume :=
      ((hwE β).comp measurable_snd).aemeasurable
    have hwg : AEMeasurable (fun z : ℝ × Space => PieceWeights.wtGrad (m.epsP β).wt z.2) volume :=
      (((measurable_fderiv ℝ (m.epsP β).wt).norm).comp measurable_snd).aemeasurable
    have hfs : AEMeasurable (fun z : ℝ × Space => frameSpeedSup W (m.epsP β).frame z.2) volume :=
      ((measurable_frameSpeedSup_one hW.smooth (hm.epsSpeed_ge β)).comp measurable_snd).aemeasurable
    have p1 := aemeasurable_pieceNorm (m.epsP β).modes
      (g := fun κ z => vortGradAmp (secondDerivField v) κ z.1 z.2) fun κ => aem_vortGradAmp hH κ
    have p2 := aemeasurable_pieceNorm (m.epsP β).modes
      (g := fun κ z => vortAmp (gradField v) κ z.1 z.2) fun κ => aem_vortAmp hG κ
    have p3 := aemeasurable_pieceNorm (m.epsP β).modes (g := fun κ z => velAmp v κ z.1 z.2) hV3
    have p4 := aemeasurable_pieceNorm (m.epsP β).modes
      (g := fun κ z => gradAmp (gradField v) κ z.1 z.2) hG3
    beta_reduce at p1 p2 p3 p4
    have t1 := ((((hwt.mul hfs).add hwg).mul p1).mul p2).neg
    have t2 := (hwt.mul ((aemeasurable_const (b := (1 / 2 : ℝ))).mul hvS |>.add
      (aemeasurable_const (b := |(m.epsP β).frame|)))).mul (p2.pow_const 2)
    have t3 := ((hwt.mul hsS).mul p3).mul p2
    have t4 := ((hwt.mul hvS).mul p4).mul p2
    unfold epsBlockLower
    exact ((t1.sub t2).sub t3).sub t4
  · have hwt : AEMeasurable (fun z : ℝ × Space => (m.muP β).wt z.2) volume :=
      ((hwM β).comp measurable_snd).aemeasurable
    have hwg : AEMeasurable (fun z : ℝ × Space => PieceWeights.wtGrad (m.muP β).wt z.2) volume :=
      (((measurable_fderiv ℝ (m.muP β).wt).norm).comp measurable_snd).aemeasurable
    have hfs : AEMeasurable (fun z : ℝ × Space => frameSpeedSup W (m.muP β).frame z.2) volume :=
      ((measurable_frameSpeedSup_one hW.smooth (hm.muSpeed_ge β)).comp measurable_snd).aemeasurable
    have p3 := aemeasurable_pieceNorm (m.muP β).modes (g := fun κ z => velAmp v κ z.1 z.2) hV3
    have p4 := aemeasurable_pieceNorm (m.muP β).modes
      (g := fun κ z => gradAmp (gradField v) κ z.1 z.2) hG3
    beta_reduce at p3 p4
    have t1 := ((((hwt.mul hfs).add hwg).mul p4).mul p3).neg
    have t2 := (hwt.mul (aemeasurable_const (b := |(m.muP β).frame|))).mul (p3.pow_const 2)
    unfold pieceMuBlock
    exact t1.sub t2
  · have hwt : AEMeasurable (fun z : ℝ × Space => (m.epsP β).wt z.2) volume :=
      ((hwE β).comp measurable_snd).aemeasurable
    have p2 := aemeasurable_pieceNorm (m.epsP β).modes
      (g := fun κ z => vortAmp (gradField v) κ z.1 z.2) fun κ => aem_vortAmp hG κ
    have p3 := aemeasurable_pieceNorm (m.epsP β).modes (g := fun κ z => velAmp v κ z.1 z.2) hV3
    beta_reduce at p2 p3
    exact (hwt.mul p3).mul p2

end Pieces

end Internal.PieceDensity

end CoerciveWeak

end Breakdown
