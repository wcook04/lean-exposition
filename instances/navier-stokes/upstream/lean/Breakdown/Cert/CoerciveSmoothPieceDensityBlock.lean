import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoercivePieceAbsorb

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceDensity

open Internal.PieceAbsorb Internal.ModeRotation

theorem contDiff_curlVec : ContDiff ℝ 1 curlVec := by
  unfold curlVec
  fun_prop

theorem continuous_coord (i : Fin 3) : Continuous (fun x : Space => x i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous

theorem measurable_iSup_of {F : ℝ × ℝ → Space → ℝ} {s : Space → ℝ} (hc : ∀ p, Continuous (F p))
    (hb : ∀ p y, F p y ≤ s y) : Measurable (fun y => ⨆ p, F p y) :=
  (lowerSemicontinuous_ciSup (fun y => ⟨s y, by rintro _ ⟨p, rfl⟩; exact hb p y⟩)
    fun p => (hc p).lowerSemicontinuous).measurable

theorem measurable_frameSpeedSup {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    {a : ℝ} {s : Space → ℝ}
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

theorem measurable_vortSup {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    {s : Space → ℝ} (hb : ∀ σ φ y, ‖curlVec (fderiv ℝ (W σ) (axialRot φ y))‖ ≤ s y) :
    Measurable (vortSup W) := by
  unfold vortSup
  refine measurable_iSup_of (s := s) (fun p => ?_) (fun p y => hb p.1 p.2 y)
  have hR : Continuous (fun y => axialRot p.2 y) :=
    Continuous.comp (g := fun q : ℝ × Space => axialRot q.1 q.2) (f := fun y : Space => (p.2, y))
      continuous_axialRot (continuous_const.prodMk continuous_id)
  have hD : Continuous (fun y => fderiv ℝ (W p.1) (axialRot p.2 y)) :=
    Continuous.comp (g := fun q : ℝ × Space => fderiv ℝ (W q.1) q.2) (f := fun y : Space => (p.1, axialRot p.2 y))
      (continuous_fderiv_slice hW) (continuous_const.prodMk hR)
  exact (Continuous.comp (g := curlVec) contDiff_curlVec.continuous hD).norm

theorem measurable_vortGradSup {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    {s : Space → ℝ}
    (hb : ∀ σ φ y, ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (W σ) x)) (axialRot φ y)‖ ≤ s y) :
    Measurable (vortGradSup W) := by
  unfold vortGradSup
  refine measurable_iSup_of (s := s) (fun p => ?_) (fun p y => hb p.1 p.2 y)
  have hR : Continuous (fun y => axialRot p.2 y) :=
    Continuous.comp (g := fun q : ℝ × Space => axialRot q.1 q.2) (f := fun y : Space => (p.2, y))
      continuous_axialRot (continuous_const.prodMk continuous_id)
  have hWs : ContDiff ℝ 2 (fun x => W p.1 x) :=
    ContDiff.comp (g := fun q : ℝ × Space => W q.1 q.2) (f := fun x : Space => (p.1, x))
      hW (contDiff_const.prodMk contDiff_id)
  have hF : ContDiff ℝ 1 (fun x => curlVec (fderiv ℝ (W p.1) x)) :=
    contDiff_curlVec.comp (hWs.fderiv_right (m := 1) (by norm_num))
  exact (Continuous.comp (g := fderiv ℝ (fun x => curlVec (fderiv ℝ (W p.1) x))) (hF.continuous_fderiv one_ne_zero) hR).norm

theorem aemeasurable_pieceNorm (T : Set (ℤ × ℤ)) {g : ℤ × ℤ → ℝ × Space → ℝ}
    (hg : ∀ κ, AEMeasurable (g κ) volume) :
    AEMeasurable (fun z => pieceNorm T (fun κ => g κ z)) volume := by
  have he : ∀ z, pieceNorm T (fun κ => g κ z)
      = Real.sqrt (∑' κ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece T κ) * g κ z ^ 2)).toReal := by
    intro z
    unfold pieceNorm
    congr 1
    rw [ENNReal.tsum_toReal_eq fun _ => ENNReal.ofReal_ne_top]
    exact tsum_congr fun κ => (ENNReal.toReal_ofReal (mul_nonneg (ind_nonneg _) (sq_nonneg _))).symm
  simp only [he]
  exact Real.continuous_sqrt.measurable.comp_aemeasurable (AEMeasurable.ennreal_toReal
    (AEMeasurable.ennreal_tsum fun κ => ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_const.mul ((hg κ).pow_const 2))))

section Pieces

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
  (W v : ℝ → Space → Space)

theorem aemeasurable_block_terms {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (_hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hv : IsSmoothPerturbation P v) :
    (∀ β, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (-pieceEpsBlock m W v (gradField v) (secondDerivField v) β z.1 z.2)) slabMeasure) ∧
    (∀ β, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β z.1 z.2)) slabMeasure) := by
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by exact_mod_cast le_top : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  have hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume := hv2.continuous.aestronglyMeasurable
  have hGm : AEStronglyMeasurable (fun z : ℝ × Space => gradField v z.1 z.2) volume :=
    (continuous_fderiv_slice hv2).aestronglyMeasurable
  have hHm : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivField v z.1 z.2) volume :=
    (measurable_secondDeriv_slice hv2).aestronglyMeasurable
  have hvS : AEMeasurable (fun z : ℝ × Space => vortSup W z.2) volume :=
    ((measurable_vortSup hW hm.supVort_ge).comp measurable_snd).aemeasurable
  have hvGS : AEMeasurable (fun z : ℝ × Space => vortGradSup W z.2) volume :=
    ((measurable_vortGradSup hW hm.supGradVort_ge).comp measurable_snd).aemeasurable
  have hG3 := fun κ => aem_gradAmp hGm κ
  have hV3 := fun κ => aem_velAmp hvm κ
  refine ⟨fun β => ?_, fun β => ?_⟩
  · have hwt : AEMeasurable (fun z : ℝ × Space => (m.epsP β).wt z.2) volume := by
      obtain ⟨K, hK⟩ := hm.eps_increment β
      exact (hK.continuous.measurable.comp measurable_snd).aemeasurable
    have hwg : AEMeasurable (fun z : ℝ × Space => PieceWeights.wtGrad (m.epsP β).wt z.2) volume :=
      (((measurable_fderiv ℝ (m.epsP β).wt).norm).comp measurable_snd).aemeasurable
    have hfs : AEMeasurable (fun z : ℝ × Space => frameSpeedSup W (m.epsP β).frame z.2) volume :=
      ((measurable_frameSpeedSup hW (hm.epsSpeed_ge β)).comp measurable_snd).aemeasurable
    have p1 := aemeasurable_pieceNorm (m.epsP β).modes
      (g := fun κ z => vortGradAmp (secondDerivField v) κ z.1 z.2) fun κ => aem_vortGradAmp hHm κ
    have p2 := aemeasurable_pieceNorm (m.epsP β).modes
      (g := fun κ z => vortAmp (gradField v) κ z.1 z.2) fun κ => aem_vortAmp hGm κ
    have p3 := aemeasurable_pieceNorm (m.epsP β).modes (g := fun κ z => velAmp v κ z.1 z.2) hV3
    have p4 := aemeasurable_pieceNorm (m.epsP β).modes
      (g := fun κ z => gradAmp (gradField v) κ z.1 z.2) hG3
    beta_reduce at p1 p2 p3 p4
    have t1 := ((((hwt.mul hfs).add hwg).mul p1).mul p2).neg
    have t2 := (hwt.mul ((aemeasurable_const (b := (1 / 2 : ℝ))).mul hvS |>.add
      (aemeasurable_const (b := |(m.epsP β).frame|)))).mul (p2.pow_const 2)
    have t3 := ((hwt.mul hvGS).mul p3).mul p2
    have t4 := ((hwt.mul hvS).mul p4).mul p2
    have hF : AEMeasurable (fun z : ℝ × Space => -pieceEpsBlock m W v (gradField v) (secondDerivField v) β z.1 z.2)
        volume := (((t1.sub t2).sub t3).sub t4).neg
    rw [slabMeasure_eq]
    exact (ENNReal.measurable_ofReal.comp_aemeasurable hF).restrict
  · have hwt : AEMeasurable (fun z : ℝ × Space => (m.muP β).wt z.2) volume := by
      obtain ⟨K, hK⟩ := hm.mu_increment β
      exact (hK.continuous.measurable.comp measurable_snd).aemeasurable
    have hwg : AEMeasurable (fun z : ℝ × Space => PieceWeights.wtGrad (m.muP β).wt z.2) volume :=
      (((measurable_fderiv ℝ (m.muP β).wt).norm).comp measurable_snd).aemeasurable
    have hfs : AEMeasurable (fun z : ℝ × Space => frameSpeedSup W (m.muP β).frame z.2) volume :=
      ((measurable_frameSpeedSup hW (hm.muSpeed_ge β)).comp measurable_snd).aemeasurable
    have p3 := aemeasurable_pieceNorm (m.muP β).modes (g := fun κ z => velAmp v κ z.1 z.2) hV3
    have p4 := aemeasurable_pieceNorm (m.muP β).modes
      (g := fun κ z => gradAmp (gradField v) κ z.1 z.2) hG3
    beta_reduce at p3 p4
    have t1 := ((((hwt.mul hfs).add hwg).mul p4).mul p3).neg
    have t2 := (hwt.mul (aemeasurable_const (b := |(m.muP β).frame|))).mul (p3.pow_const 2)
    have hF : AEMeasurable (fun z : ℝ × Space => -pieceMuBlock m W v (gradField v) β z.1 z.2) volume :=
      (t1.sub t2).neg
    rw [slabMeasure_eq]
    exact (ENNReal.measurable_ofReal.comp_aemeasurable hF).restrict

end Pieces

end Internal.SmoothPieceDensity

end Coercive

end Breakdown
