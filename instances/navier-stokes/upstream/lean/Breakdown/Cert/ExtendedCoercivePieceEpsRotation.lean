import Breakdown.Cert.ExtendedCoercivePieceEpsSumSecondPartials
import Breakdown.Cert.CoerciveField
import Breakdown.Cert.CoerciveCurlEnergy
import Breakdown.Cert.CoerciveStretch

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.ExtendedPieceEps

open Coercive Coercive.Internal.SmoothPieceEpsCore Coercive.Internal.PieceAbsorb

def perpVec (x : Space) : Space := -(x 1) • unitVector 0 + x 0 • unitVector 1

def curlField (v : ℝ → Space → Space) : ℝ → Space → Space := fun s x => curlVec (fderiv ℝ (v s) x)

def rotationPartWith (a : ℝ) (v : ℝ → Space → Space) : ℝ → Space → Space := fun s x =>
  a • perpVec (curlField v s x)

def modePart (T : Set (ℤ × ℤ)) (wt : Space → ℝ) (v Z : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  (Complex.I * ((PieceWeights.sgn T ι * wt y : ℝ) : ℂ) * cdot (curlOfGrad (modeGrad ι (gradField v) σ y))
    (modeVel ι Z σ y)).re

namespace RotationPart

theorem slice_fderiv_continuous {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) :=
  (ContDiff.fderiv (m := 1) (n := 0) (f := fun (p : ℝ × Space) (x : Space) => F p.1 x) (g := fun p => p.2)
    (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)).continuous

theorem curlMode_eq_modeVel {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2))
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    curlOfGrad (modeGrad ι (gradField F) σ y) = modeVel ι (curlField F) σ y := by
  have hc : Continuous (fun p : ℝ × ℝ => gradField F (σ + p.1) (axialRot p.2 y)) :=
    (slice_fderiv_continuous hF).comp ((continuous_const.add continuous_fst).prodMk
      (Coercive.Internal.Field.axialRot_comp_continuous continuous_snd continuous_const))
  exact Coercive.Internal.CurlEnergy.curlOfGrad_modeGrad_eq (z := (σ, y)) ι
    (StretchInternal.integrable_box_of_continuous hc)

theorem abs_sgn_eq_ind (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) :
    |PieceWeights.sgn T ι| = ModeWeights.ind (PieceWeights.inPiece T ι) := by
  unfold PieceWeights.sgn ModeWeights.ind PieceWeights.inPiece
  split_ifs <;> simp_all

theorem rot_coord0 (ψ : ℝ) (u : Space) : axialRot ψ u 0 = Real.cos ψ * u 0 - Real.sin ψ * u 1 := by
  simp [axialRot, unitVector]

theorem rot_coord1 (ψ : ℝ) (u : Space) : axialRot ψ u 1 = Real.sin ψ * u 0 + Real.cos ψ * u 1 := by
  simp [axialRot, unitVector]

theorem rot_coord2 (ψ : ℝ) (u : Space) : axialRot ψ u 2 = u 2 := by
  simp [axialRot, unitVector]

theorem perp_coord0 (u : Space) : perpVec u 0 = -u 1 := by simp [perpVec, unitVector]

theorem perp_coord1 (u : Space) : perpVec u 1 = u 0 := by simp [perpVec, unitVector]

theorem perp_coord2 (u : Space) : perpVec u 2 = 0 := by simp [perpVec, unitVector]

theorem rot_perp (ψ : ℝ) (a : ℝ) (w : Space) :
    axialRot ψ (a • perpVec w) 0 = (-a) * axialRot ψ w 1 ∧ axialRot ψ (a • perpVec w) 1 = a * axialRot ψ w 0 ∧
      axialRot ψ (a • perpVec w) 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rot_coord0, rot_coord1]
    simp only [PiLp.smul_apply, smul_eq_mul, perp_coord0, perp_coord1]
    ring
  · rw [rot_coord1, rot_coord0]
    simp only [PiLp.smul_apply, smul_eq_mul, perp_coord0, perp_coord1]
    ring
  · rw [rot_coord2]
    simp only [PiLp.smul_apply, smul_eq_mul, perp_coord2, mul_zero]

theorem modeAverage_congr_mul {β : Type*} (ι : ℤ × ℤ) (f g : ℝ → ℝ → β → ℝ) (b b' : β) (c : ℝ)
    (h : ∀ τ φ, f τ φ b = c * g τ φ b') : modeAverage ι f b = (c : ℂ) * modeAverage ι g b' := by
  unfold modeAverage
  simp only [h]
  simp_rw [Complex.ofReal_mul, mul_left_comm _ (c : ℂ), intervalIntegral.integral_const_mul]
  ring

theorem modeVel_rotationPart (a : ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeVel ι (rotationPartWith a v) σ y 0 = ((-a : ℝ) : ℂ) * modeVel ι (curlField v) σ y 1 ∧
      modeVel ι (rotationPartWith a v) σ y 1 = (a : ℂ) * modeVel ι (curlField v) σ y 0 ∧
      modeVel ι (rotationPartWith a v) σ y 2 = 0 := by
  unfold modeVel rotationPartWith
  refine ⟨modeAverage_congr_mul ι _ _ 0 1 (-a) fun τ φ => (rot_perp _ _ _).1,
    modeAverage_congr_mul ι _ _ 1 0 a fun τ φ => (rot_perp _ _ _).2.1, ?_⟩
  have := modeAverage_congr_mul ι (fun τ φ i => axialRot (-φ) (a • perpVec (curlField v (σ + τ) (axialRot φ y))) i)
    (fun τ φ i => axialRot (-φ) (curlField v (σ + τ) (axialRot φ y)) i) 2 2 0 fun τ φ => by
      rw [(rot_perp _ _ _).2.2, zero_mul]
  rw [this, Complex.ofReal_zero, zero_mul]

theorem rotation_term_le (c a : ℝ) (x : Fin 3 → ℂ) (Z : Fin 3 → ℂ) (h0 : Z 0 = ((-a : ℝ) : ℂ) * x 1)
    (h1 : Z 1 = (a : ℂ) * x 0) (h2 : Z 2 = 0) :
    |(Complex.I * (c : ℂ) * cdot x Z).re| ≤ |c| * |a| * cnormSq x := by
  unfold cdot cnormSq
  simp only [Fin.sum_univ_three, h0, h1, h2]
  have e : (Complex.I * (c : ℂ) * (x 0 * (starRingEnd ℂ) (((-a : ℝ) : ℂ) * x 1) + x 1 * (starRingEnd ℂ) ((a : ℂ) * x 0)
      + x 2 * (starRingEnd ℂ) 0)).re = -2 * c * a * ((x 1).im * (x 0).re - (x 1).re * (x 0).im) := by
    simp only [map_mul, Complex.conj_ofReal, map_zero, mul_zero, add_zero, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [e, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
    Complex.normSq_apply]
  have hb : 2 * |(x 1).im * (x 0).re - (x 1).re * (x 0).im| ≤
      (x 0).re * (x 0).re + (x 0).im * (x 0).im + ((x 1).re * (x 1).re + (x 1).im * (x 1).im) := by
    rcases abs_cases ((x 1).im * (x 0).re - (x 1).re * (x 0).im) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      nlinarith [sq_nonneg ((x 1).im - (x 0).re), sq_nonneg ((x 1).re + (x 0).im),
        sq_nonneg ((x 1).im + (x 0).re), sq_nonneg ((x 1).re - (x 0).im)]
  have h2' : 0 ≤ (x 2).re * (x 2).re + (x 2).im * (x 2).im := by nlinarith [sq_nonneg (x 2).re, sq_nonneg (x 2).im]
  rw [show -2 * c * a * ((x 1).im * (x 0).re - (x 1).re * (x 0).im)
      = -(c * a) * (2 * ((x 1).im * (x 0).re - (x 1).re * (x 0).im)) by ring, abs_mul, abs_neg, abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hca : 0 ≤ |c| * |a| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc |c| * |a| * (2 * |(x 1).im * (x 0).re - (x 1).re * (x 0).im|)
      ≤ |c| * |a| * ((x 0).re * (x 0).re + (x 0).im * (x 0).im + ((x 1).re * (x 1).re + (x 1).im * (x 1).im)) :=
        mul_le_mul_of_nonneg_left hb hca
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hca


theorem rotation_bound_of {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
    {w : Space → ℝ} {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure,
      Summable (fun ι => modePart (m.epsP β).modes (m.epsP β).wt v (rotationPartWith (m.epsP β).frame v) ι z.1 z.2) ∧
      -(∑' ι, modePart (m.epsP β).modes (m.epsP β).wt v (rotationPartWith (m.epsP β).frame v) ι z.1 z.2)
        ≤ (m.epsP β).wt z.2 * |(m.epsP β).frame|
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2 := by
  have hp := hSP P v hv
  have hG := hp.measurable_gradient
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 1
  have hAm : AEMeasurable (fun z : ℝ × Space =>
      ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2)) slabMeasure :=
    Internal.SmoothPieceEps.slab_aem
      (AEMeasurable.ennreal_tsum fun ι => ((aem_vortAmp hG ι).pow_const 2).ennreal_ofReal)
  have hfin : ∫⁻ z, ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2) ∂slabMeasure < ⊤ := by
    refine lt_of_le_of_lt (lintegral_prod_le _) (lt_of_le_of_lt
      (lintegral_mono fun σ => lintegral_mono fun y => ?_)
      (Internal.SmoothPieceEps.amplitudeSeries_finite hPars hSP P v hv))
    exact le_trans (le_trans le_self_add le_self_add) le_self_add
  filter_upwards [ae_lt_top' hAm hfin.ne] with z hz
  have hwt0 : 0 ≤ (m.epsP β).wt z.2 := hm.eps_wt_nonneg β z.2
  have hq0 : ∀ ι, 0 ≤ vortAmp (gradField v) ι z.1 z.2 ^ 2 := fun ι => sq_nonneg _
  have hq : Summable (fun ι => vortAmp (gradField v) ι z.1 z.2 ^ 2) := by
    have := ENNReal.summable_toReal hz.ne
    simpa only [ENNReal.toReal_ofReal (hq0 _)] using this
  have hi0 : ∀ ι, 0 ≤ ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) := fun ι => by
    unfold ModeWeights.ind; split_ifs <;> norm_num
  have hi1 : ∀ ι, ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) ≤ 1 := fun ι => by
    unfold ModeWeights.ind; split_ifs <;> norm_num
  have hiq : Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι)
      * vortAmp (gradField v) ι z.1 z.2 ^ 2) :=
    hq.of_nonneg_of_le (fun ι => mul_nonneg (hi0 ι) (hq0 ι))
      (fun ι => mul_le_of_le_one_left (hq0 ι) (hi1 ι))
  have hsum := hiq.mul_left ((m.epsP β).wt z.2 * |(m.epsP β).frame|)
  have hbd : ∀ ι, |modePart (m.epsP β).modes (m.epsP β).wt v (rotationPartWith (m.epsP β).frame v) ι z.1 z.2|
      ≤ (m.epsP β).wt z.2 * |(m.epsP β).frame| * (ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι)
        * vortAmp (gradField v) ι z.1 z.2 ^ 2) := by
    intro ι
    have eq : cnormSq (modeVel ι (curlField v) z.1 z.2) = vortAmp (gradField v) ι z.1 z.2 ^ 2 := by
      rw [← curlMode_eq_modeVel hv1]
      unfold vortAmp
      rw [Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg _)]
    obtain ⟨h0, h1, h2⟩ := modeVel_rotationPart (m.epsP β).frame v ι z.1 z.2
    unfold modePart
    rw [curlMode_eq_modeVel hv1]
    refine le_trans (rotation_term_le _ _ _ _ h0 h1 h2) (le_of_eq ?_)
    rw [abs_mul, abs_sgn_eq_ind, abs_of_nonneg hwt0, eq]
    ring
  have hrs : Summable (fun ι =>
      modePart (m.epsP β).modes (m.epsP β).wt v (rotationPartWith (m.epsP β).frame v) ι z.1 z.2) :=
    (hsum.of_nonneg_of_le (fun ι => abs_nonneg _) hbd).of_abs
  refine ⟨hrs, ?_⟩
  have hn := norm_tsum_le_tsum_norm hrs.norm
  simp only [Real.norm_eq_abs] at hn
  have ht := hrs.abs.tsum_le_tsum hbd hsum
  rw [tsum_mul_left] at ht
  have hpn : pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2
      = ∑' ι, ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * vortAmp (gradField v) ι z.1 z.2 ^ 2 := by
    unfold pieceNorm
    exact Real.sq_sqrt (tsum_nonneg fun ι => mul_nonneg (hi0 ι) (hq0 ι))
  rw [hpn]
  linarith [neg_le_abs (∑' ι, modePart (m.epsP β).modes (m.epsP β).wt v (rotationPartWith (m.epsP β).frame v) ι z.1 z.2)]

end RotationPart

end Internal.ExtendedPieceEps

end CoerciveWeak

end Breakdown
