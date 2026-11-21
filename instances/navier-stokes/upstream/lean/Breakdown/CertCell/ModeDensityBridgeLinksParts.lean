import Breakdown.CertCell.BridgeStatements
import Breakdown.CertCell.PinHalfPlane
import Breakdown.CertCell.StretchMeanIntegral
import Breakdown.CertCell.ModeRotationNorms

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.ModeDensityBridge

open Coercive Coercive.Internal.ModeRotation TailBand.Internal.AngularPlane

theorem modeTerm_shift {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : IsTimePeriodic v) (hG : IsTimePeriodic G)
    (hH : IsTimePeriodic H) (ξ : ℤ × ℤ) (σ : ℝ) (y : Space) :
    m.modeTerm P h w v G H ξ σ y = m.modeTerm P h w v G H ξ 0 y := by
  unfold PieceWeights.modeTerm
  rw [FrequencySeminorm.Internal.modeVel_shift ξ hv σ y, FrequencySeminorm.Internal.modeGrad_shift ξ hG σ y,
    modeSecondDeriv_shift ξ hH σ y, curlOfGrad_phase, curlGradOfSecondDeriv_phase]
  simp only [cnormSq_phase _ (Complex.norm_exp_ofReal_mul_I _)]

theorem modeTerm_rot_of {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (ξ : ℤ × ℤ) (ψ : ℝ) {z : ℝ × Space}
    (hzv : Integrable (fun p : ℝ × ℝ => v (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure)
    (hzG : Integrable (fun p : ℝ × ℝ => G (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure)
    (hzH : Integrable (fun p : ℝ × ℝ => H (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure)
    (hcoef : ∀ x2 xc x1 xo x0 : ℝ, m.modeDensity P h w ξ (axialRot ψ z.2) x2 xc x1 xo x0
      = m.modeDensity P h w ξ z.2 x2 xc x1 xo x0) :
    m.modeTerm P h w v G H ξ z.1 (axialRot ψ z.2) = m.modeTerm P h w v G H ξ z.1 z.2 := by
  have hRot := axialRotationHolds_proof
  unfold PieceWeights.modeTerm
  rw [modeVel_rotation_of hRot ξ ψ hzv, modeGrad_rotation_of hRot ξ ψ hzG, modeSecondDeriv_rotation_of hRot ξ ψ hzH,
    curlOfGrad_phase, curlGradOfSecondDeriv_phase, curlOfGrad_rotCMat, curlGradOfSecondDeriv_rotTensor, hcoef]
  simp only [cnormSq_phase _ (Complex.norm_exp_ofReal_mul_I _), cnormSq_rotC, cnormSq_rotCMat, cnormSq_rotTensor]

theorem norm_iteratedFDeriv_rot {f : Space → ℝ} (hf : IsAxisymmetric f) (n : ℕ) (φ : ℝ) (y : Space) :
    ‖iteratedFDeriv ℝ n f (axialRot φ y)‖ = ‖iteratedFDeriv ℝ n f y‖ := by
  obtain ⟨R, hR⟩ := axialRotationHolds_proof.1 φ
  have e : f ∘ R = f := funext fun x => by simp only [Function.comp, hR, hf φ x]
  rw [← hR y, ← LinearIsometryEquiv.norm_iteratedFDeriv_comp_right R f y n, e]

theorem wtGrad_rot {f : Space → ℝ} (hf : IsAxisymmetric f) (φ : ℝ) (y : Space) :
    PieceWeights.wtGrad f (axialRot φ y) = PieceWeights.wtGrad f y := by
  unfold PieceWeights.wtGrad
  rw [← norm_iteratedFDeriv_one (𝕜 := ℝ), ← norm_iteratedFDeriv_one (𝕜 := ℝ) f, norm_iteratedFDeriv_rot hf]

theorem secondDerivNorm_rot {f : Space → ℝ} (hf : IsAxisymmetric f) (φ : ℝ) (y : Space) :
    ModeWeights.secondDerivNorm f (axialRot φ y) = ModeWeights.secondDerivNorm f y :=
  norm_iteratedFDeriv_rot hf 2 φ y

theorem modeDensity_rot {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {w₀ e₁ e₂ e₃ : ℝ} (hm : CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ e₁ e₂ e₃)
    (hf : IsFlipCompatible m h w) (ξ : ℤ × ℤ) (ψ : ℝ) (y : Space) (x2 xc x1 xo x0 : ℝ) :
    m.modeDensity P h w ξ (axialRot ψ y) x2 xc x1 xo x0 = m.modeDensity P h w ξ y x2 xc x1 xo x0 := by
  have a1 : ∀ β φ y, (m.epsP β).wt (axialRot φ y) = (m.epsP β).wt y := fun β => hm.eps_axi β
  have a2 : ∀ β φ y, (m.epsP β).share1 (axialRot φ y) = (m.epsP β).share1 y := fun β => (hm.eps_free_axi β).1
  have a3 : ∀ β φ y, (m.epsP β).share2 (axialRot φ y) = (m.epsP β).share2 y := fun β => (hm.eps_free_axi β).2.1
  have a4 : ∀ β φ y, (m.epsP β).len (axialRot φ y) = (m.epsP β).len y := fun β => (hm.eps_free_axi β).2.2.1
  have a5 : ∀ β φ y, (m.epsP β).t0 (axialRot φ y) = (m.epsP β).t0 y := fun β => (hm.eps_free_axi β).2.2.2.1
  have a6 : ∀ β φ y, (m.epsP β).t1 (axialRot φ y) = (m.epsP β).t1 y := fun β => (hm.eps_free_axi β).2.2.2.2.1
  have a7 : ∀ β φ y, (m.epsP β).t2 (axialRot φ y) = (m.epsP β).t2 y :=
    fun β => (hm.eps_free_axi β).2.2.2.2.2.1
  have a8 : ∀ β φ y, (m.epsP β).t3 (axialRot φ y) = (m.epsP β).t3 y :=
    fun β => (hm.eps_free_axi β).2.2.2.2.2.2.1
  have a9 : ∀ β φ y, (m.epsP β).scale (axialRot φ y) = (m.epsP β).scale y :=
    fun β => (hm.eps_free_axi β).2.2.2.2.2.2.2
  have a10 : ∀ β φ y, (m.epsP β).speed (axialRot φ y) = (m.epsP β).speed y := fun β => hf.eps_speed_axi β
  have a11 : ∀ β φ y, PieceWeights.wtGrad (m.epsP β).wt (axialRot φ y) = PieceWeights.wtGrad (m.epsP β).wt y :=
    fun β => wtGrad_rot (hm.eps_axi β)
  have b1 : ∀ β φ y, (m.muP β).wt (axialRot φ y) = (m.muP β).wt y := fun β => hm.mu_axi β
  have b2 : ∀ β φ y, (m.muP β).share (axialRot φ y) = (m.muP β).share y := fun β => (hm.mu_free_axi β).1
  have b3 : ∀ β φ y, (m.muP β).t4 (axialRot φ y) = (m.muP β).t4 y := fun β => (hm.mu_free_axi β).2
  have b4 : ∀ β φ y, (m.muP β).speed (axialRot φ y) = (m.muP β).speed y := fun β => hf.mu_speed_axi β
  have b5 : ∀ β φ y, PieceWeights.wtGrad (m.muP β).wt (axialRot φ y) = PieceWeights.wtGrad (m.muP β).wt y :=
    fun β => wtGrad_rot (hm.mu_axi β)
  have c1 : ∀ β φ y, h.ampW β (axialRot φ y) = h.ampW β y := fun β φ y => (hf.amplitudes_axi β φ y).1
  have c2 : ∀ β φ y, h.ampGradW β (axialRot φ y) = h.ampGradW β y := fun β φ y => (hf.amplitudes_axi β φ y).2.1
  have c3 : ∀ β φ y, h.ampVort β (axialRot φ y) = h.ampVort β y := fun β φ y => (hf.amplitudes_axi β φ y).2.2.1
  have c4 : ∀ β φ y, h.ampGradVort β (axialRot φ y) = h.ampGradVort β y :=
    fun β φ y => (hf.amplitudes_axi β φ y).2.2.2
  have c5 : ∀ φ y, h.supVort (axialRot φ y) = h.supVort y := fun φ y => (hf.sups_axi φ y).1
  have c6 : ∀ φ y, h.supGradVort (axialRot φ y) = h.supGradVort y := fun φ y => (hf.sups_axi φ y).2
  have d1 : ∀ c φ y, m.convD c (axialRot φ y) = m.convD c y := fun c => hm.convD_axi c
  have d2 : ∀ c φ y, m.convZ c (axialRot φ y) = m.convZ c y := fun c => hm.convZ_axi c
  have d3 : ∀ c φ y, ModeWeights.secondDerivNorm (m.convD c) (axialRot φ y) = ModeWeights.secondDerivNorm (m.convD c) y :=
    fun c => secondDerivNorm_rot (hm.convD_axi c)
  have d4 : ∀ c φ y, ModeWeights.secondDerivNorm (m.convZ c) (axialRot φ y) = ModeWeights.secondDerivNorm (m.convZ c) y :=
    fun c => secondDerivNorm_rot (hm.convZ_axi c)
  have d5 : ∀ φ y, w (axialRot φ y) = w y := hm.weight_axi
  simp only [PieceWeights.modeDensity, PieceWeights.shareHat, PieceWeights.coefA, PieceWeights.coefAA,
    PieceWeights.coefB, PieceWeights.outward, PieceWeights.inward, PieceWeights.fwdSum, PieceWeights.backSum,
    PieceWeights.harmonicSum, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, b1, b2, b3, b4, b5, c1, c2, c3, c4,
    c5, c6, d1, d2, d3, d4, d5]

theorem measurable_ind_pos {f : Space → ℝ} (hf : Measurable f) :
    Measurable (fun y => ModeWeights.ind (0 < f y)) := by
  unfold ModeWeights.ind
  exact Measurable.ite (measurableSet_lt measurable_const hf) measurable_const measurable_const

theorem measurable_fwdSum (h : HarmonicBounds) (T : Set (ℤ × ℤ)) {amp : ℤ × ℤ → Space → ℝ}
    (hamp : ∀ β, Measurable (amp β)) (ι : ℤ × ℤ) : Measurable (PieceWeights.fwdSum h T amp ι) := by
  unfold PieceWeights.fwdSum
  refine Finset.measurable_sum _ fun β _ => ?_
  by_cases hβ : ι + β ∈ T
  · simp only [if_pos hβ]
    exact hamp β
  · simp only [if_neg hβ]
    exact measurable_const

theorem measurable_backSum (h : HarmonicBounds) (T : Set (ℤ × ℤ)) {amp : ℤ × ℤ → Space → ℝ}
    (hamp : ∀ β, Measurable (amp β)) (ι : ℤ × ℤ) : Measurable (PieceWeights.backSum h T amp ι) := by
  unfold PieceWeights.backSum
  refine Finset.measurable_sum _ fun β _ => ?_
  by_cases hβ : ι - β ∈ T
  · simp only [if_pos hβ]
    exact measurable_const
  · simp only [if_neg hβ]
    exact hamp β

theorem measurable_inward (h : HarmonicBounds) (T : Set (ℤ × ℤ)) {amp : ℤ × ℤ → Space → ℝ}
    (hamp : ∀ β, Measurable (amp β)) (ι : ℤ × ℤ) : Measurable (PieceWeights.inward h T amp ι) := by
  unfold PieceWeights.inward
  by_cases h1 : ι ∈ T
  · simp only [if_pos h1]
    exact measurable_backSum h T hamp ι
  · by_cases h2 : -ι ∈ T
    · simp only [if_neg h1, if_pos h2]
      exact measurable_backSum h T hamp (-ι)
    · simp only [if_neg h1, if_neg h2]
      exact measurable_const

theorem measurable_outward (h : HarmonicBounds) (T : Set (ℤ × ℤ)) {amp : ℤ × ℤ → Space → ℝ}
    (hamp : ∀ β, Measurable (amp β)) (ι : ℤ × ℤ) : Measurable (PieceWeights.outward h T amp ι) := by
  unfold PieceWeights.outward
  refine Measurable.add ?_ ?_
  · by_cases h1 : ι ∈ T
    · simp only [if_pos h1]
      exact measurable_const
    · simp only [if_neg h1]
      exact measurable_fwdSum h T hamp ι
  · by_cases h1 : -ι ∈ T
    · simp only [if_pos h1]
      exact measurable_const
    · simp only [if_neg h1]
      exact measurable_fwdSum h T hamp (-ι)

theorem measurable_wtGrad (f : Space → ℝ) : Measurable (PieceWeights.wtGrad f) :=
  (measurable_fderiv ℝ f).norm

theorem measurable_secondDerivNorm {f : Space → ℝ} (hf : ContDiff ℝ 2 f) : Measurable (ModeWeights.secondDerivNorm f) :=
  (hf.continuous_iteratedFDeriv (m := 2) le_rfl).norm.measurable

theorem measurable_coefs {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {w₀ e₁ e₂ e₃ : ℝ} (hm : CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ e₁ e₂ e₃)
    (hb : HasMeasurableBoundData m h) (ξ : ℤ × ℤ) :
    Measurable (fun y => m.shareHat h ξ y) ∧ Measurable (fun y => m.coefA P h ξ y) ∧
      Measurable (fun y => m.coefAA h w ξ y) ∧ Measurable (fun y => m.coefB P h ξ y) := by
  have a1 : ∀ β, Measurable (m.epsP β).wt := fun β => by
    obtain ⟨K, hK⟩ := hm.eps_increment β
    exact hK.continuous.measurable
  have a2 : ∀ β, Measurable (m.epsP β).share1 := fun β => (hm.eps_free_measurable β).1
  have a3 : ∀ β, Measurable (m.epsP β).share2 := fun β => (hm.eps_free_measurable β).2.1
  have a4 : ∀ β, Measurable (m.epsP β).len := fun β => (hm.eps_free_measurable β).2.2.1
  have a5 : ∀ β, Measurable (m.epsP β).t0 := fun β => (hm.eps_free_measurable β).2.2.2.1
  have a6 : ∀ β, Measurable (m.epsP β).t1 := fun β => (hm.eps_free_measurable β).2.2.2.2.1
  have a7 : ∀ β, Measurable (m.epsP β).t2 := fun β => (hm.eps_free_measurable β).2.2.2.2.2.1
  have a8 : ∀ β, Measurable (m.epsP β).t3 := fun β => (hm.eps_free_measurable β).2.2.2.2.2.2.1
  have a9 : ∀ β, Measurable (m.epsP β).scale := fun β => (hm.eps_free_measurable β).2.2.2.2.2.2.2
  have a10 : ∀ β, Measurable (m.epsP β).speed := hb.eps_speed_measurable
  have a11 : ∀ β, Measurable (PieceWeights.wtGrad (m.epsP β).wt) := fun β => measurable_wtGrad _
  have a12 : ∀ β, Measurable (fun y => ModeWeights.ind (0 < (m.epsP β).wt y + PieceWeights.wtGrad (m.epsP β).wt y)) :=
    fun β => measurable_ind_pos ((a1 β).add (a11 β))
  have a13 : ∀ β, Measurable (fun y => ModeWeights.ind (0 < (m.epsP β).wt y)) :=
    fun β => measurable_ind_pos (a1 β)
  have b1 : ∀ β, Measurable (m.muP β).wt := fun β => by
    obtain ⟨K, hK⟩ := hm.mu_increment β
    exact hK.continuous.measurable
  have b2 : ∀ β, Measurable (m.muP β).share := fun β => (hm.mu_free_measurable β).1
  have b3 : ∀ β, Measurable (m.muP β).t4 := fun β => (hm.mu_free_measurable β).2
  have b4 : ∀ β, Measurable (m.muP β).speed := hb.mu_speed_measurable
  have b5 : ∀ β, Measurable (PieceWeights.wtGrad (m.muP β).wt) := fun β => measurable_wtGrad _
  have b6 : ∀ β, Measurable (fun y => ModeWeights.ind (0 < (m.muP β).wt y + PieceWeights.wtGrad (m.muP β).wt y)) :=
    fun β => measurable_ind_pos ((b1 β).add (b5 β))
  have c1 : ∀ β, Measurable (h.ampW β) := fun β => (hb.amplitudes_measurable β).1
  have c2 : ∀ β, Measurable (h.ampGradW β) := fun β => (hb.amplitudes_measurable β).2.1
  have c3 : ∀ β, Measurable (h.ampVort β) := fun β => (hb.amplitudes_measurable β).2.2.1
  have c4 : ∀ β, Measurable (h.ampGradVort β) := fun β => (hb.amplitudes_measurable β).2.2.2
  have c5 : Measurable h.supVort := hb.sups_measurable.1
  have c6 : Measurable h.supGradVort := hb.sups_measurable.2
  have e1 : ∀ T ι, Measurable (PieceWeights.outward h T h.ampW ι) := fun T => measurable_outward h T c1
  have e2 : ∀ T ι, Measurable (PieceWeights.outward h T h.ampGradW ι) := fun T => measurable_outward h T c2
  have e3 : ∀ T ι, Measurable (PieceWeights.outward h T h.ampVort ι) := fun T => measurable_outward h T c3
  have e4 : ∀ T ι, Measurable (PieceWeights.outward h T h.ampGradVort ι) := fun T => measurable_outward h T c4
  have f1 : ∀ T ι, Measurable (PieceWeights.inward h T h.ampW ι) := fun T => measurable_inward h T c1
  have f2 : ∀ T ι, Measurable (PieceWeights.inward h T h.ampGradW ι) := fun T => measurable_inward h T c2
  have f3 : ∀ T ι, Measurable (PieceWeights.inward h T h.ampVort ι) := fun T => measurable_inward h T c3
  have f4 : ∀ T ι, Measurable (PieceWeights.inward h T h.ampGradVort ι) := fun T => measurable_inward h T c4
  have g1 : Measurable (PieceWeights.harmonicSum h) := by
    unfold PieceWeights.harmonicSum
    exact Finset.measurable_sum _ fun β _ => c2 β
  have d1 : ∀ c, Measurable (m.convD c) := fun c => (hm.convD_smooth c).continuous.measurable
  have d2 : ∀ c, Measurable (m.convZ c) := fun c => (hm.convZ_smooth c).continuous.measurable
  have d3 : ∀ c, Measurable (ModeWeights.secondDerivNorm (m.convD c)) := fun c => measurable_secondDerivNorm (hm.convD_smooth c)
  have d4 : ∀ c, Measurable (ModeWeights.secondDerivNorm (m.convZ c)) := fun c => measurable_secondDerivNorm (hm.convZ_smooth c)
  have d5 : Measurable w := hm.weight_measurable
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold PieceWeights.shareHat
    refine Finset.measurable_sum _ fun β _ => ?_
    exact (((a2 β).mul measurable_const).mul (a12 β)).add ((((a3 β).mul (a13 β)).mul (e1 _ ξ)).div (a9 β))
  · unfold PieceWeights.coefA
    refine (measurable_const.add (Finset.measurable_sum _ fun β _ => measurable_const.mul ?_)).sub
      (Finset.measurable_sum _ fun β _ => ((a1 β).mul (e2 _ ξ)).div (measurable_const.mul (a6 β)))
    exact ((((a1 β).mul measurable_const).sub
      ((((a1 β).mul (a10 β)).add (a11 β)).pow_const 2 |>.div (measurable_const.mul (a2 β)))).sub
      ((((a1 β).pow_const 2).mul (a9 β)).mul (f1 _ ξ) |>.div (measurable_const.mul (a3 β)))).sub
      ((a1 β).mul (((((measurable_const.add ((measurable_const.mul (measurable_const.add (a5 β))).mul c5)).add
        ((measurable_const.mul (a4 β)).mul c6)).add ((measurable_const.mul (a6 β)).mul (f2 _ ξ))).add
        ((measurable_const.mul (a7 β)).mul (f4 _ ξ))).add ((measurable_const.mul (a8 β)).mul (f3 _ ξ))))
  · unfold PieceWeights.coefAA
    exact ((((d2 _).sub (d3 _)).sub (measurable_const.mul d5)).sub (Finset.measurable_sum _ fun β _ =>
      (a1 β).mul (((measurable_const.mul c5).div (measurable_const.mul (a5 β))).add
        ((e3 _ ξ).div (measurable_const.mul (a8 β)))))).sub (Finset.measurable_sum _ fun β _ =>
      ((measurable_const.mul (b6 β)).mul (b2 β)).add (((b1 β).mul (e1 _ ξ)).div (measurable_const.mul (b3 β))))
  · unfold PieceWeights.coefB
    refine (((d4 _).neg.sub (Finset.measurable_sum _ fun β _ =>
      (a1 β).mul (((measurable_const.mul c6).div (measurable_const.mul (a4 β))).add
        ((e4 _ ξ).div (measurable_const.mul (a7 β)))))).add
      (Finset.measurable_sum _ fun β _ => measurable_const.mul ?_)).sub
      (Finset.measurable_sum _ fun β _ => (g1.mul (e2 _ ξ)).div measurable_const)
    exact (((((measurable_const.mul (b1 β)).mul measurable_const).sub
      ((((b1 β).mul (b4 β)).add (b5 β)).pow_const 2 |>.div (measurable_const.mul (b2 β)))).sub
      ((b1 β).mul measurable_const)).sub (((measurable_const.mul (b3 β)).mul (b1 β)).mul (f1 _ ξ))).sub
      (measurable_const.mul ((b1 β).pow_const 2)) |>.sub ((g1.mul (g1.sub (f2 _ ξ))).div measurable_const)

theorem aesm_modeSecondDeriv {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (ξ : ℤ × ℤ)
    (ijl : Fin 3 × Fin 3 × Fin 3) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeSecondDeriv ξ H z.1 z.2 ijl) volume := by
  have hc : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
      axialRot (-q.1) (q.2 (axialRot q.1 (unitVector ijl.2.1)) (axialRot q.1 (unitVector ijl.2.2))) ijl.1) := by
    unfold axialRot
    fun_prop
  exact Coercive.Internal.FieldModes.aestronglyMeasurable_modeAverage_comp
    (E := Space →L[ℝ] Space →L[ℝ] Space) ξ ijl
    (fun (φ : ℝ) (A : Space →L[ℝ] Space →L[ℝ] Space) (abc : Fin 3 × Fin 3 × Fin 3) =>
      axialRot (-φ) (A (axialRot φ (unitVector abc.2.1)) (axialRot φ (unitVector abc.2.2))) abc.1) hc hH

theorem aesm_sqrt_cnormSq {β : Type*} [Fintype β] {f : ℝ × Space → β → ℂ}
    (hf : ∀ b, AEStronglyMeasurable (fun z => f z b) volume) :
    AEStronglyMeasurable (fun z => Real.sqrt (cnormSq (f z))) volume := by
  unfold cnormSq
  exact Real.continuous_sqrt.comp_aestronglyMeasurable
    (Finset.aestronglyMeasurable_fun_sum _ fun b _ => ((hf b).norm).pow 2)

theorem aesm_curlOfGrad {f : ℝ × Space → Fin 3 × Fin 3 → ℂ}
    (hf : ∀ b, AEStronglyMeasurable (fun z => f z b) volume) (i : Fin 3) :
    AEStronglyMeasurable (fun z => curlOfGrad (f z) i) volume := by
  unfold curlOfGrad
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => Finset.aestronglyMeasurable_fun_sum _ fun l _ =>
    aestronglyMeasurable_const.mul (hf (l, j))

theorem aesm_curlGradOfSecondDeriv {f : ℝ × Space → Fin 3 × Fin 3 × Fin 3 → ℂ}
    (hf : ∀ b, AEStronglyMeasurable (fun z => f z b) volume) (il : Fin 3 × Fin 3) :
    AEStronglyMeasurable (fun z => curlGradOfSecondDeriv (f z) il) volume := by
  unfold curlGradOfSecondDeriv
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => Finset.aestronglyMeasurable_fun_sum _ fun l _ =>
    aestronglyMeasurable_const.mul (hf (l, il.2, j))

theorem aesm_modeTerm {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {w₀ e₁ e₂ e₃ : ℝ} (hm : CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ e₁ e₂ e₃)
    (hb : HasMeasurableBoundData m h) {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hGm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hHm : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (ξ : ℤ × ℤ) :
    AEStronglyMeasurable (fun z : ℝ × Space => m.modeTerm P h w v G H ξ z.1 z.2) volume := by
  obtain ⟨s1, s2, s3, s4⟩ := measurable_coefs m P h w hm hb ξ
  have hD : Measurable (m.convD (m.classOf ξ)) := (hm.convD_smooth _).continuous.measurable
  have hZ : Measurable (m.convZ (m.classOf ξ)) := (hm.convZ_smooth _).continuous.measurable
  have X2 := aesm_sqrt_cnormSq (fun b => aesm_modeSecondDeriv hHm ξ b)
  have Xc := aesm_sqrt_cnormSq (fun b => aesm_curlGradOfSecondDeriv (fun c => aesm_modeSecondDeriv hHm ξ c) b)
  have X1 := aesm_sqrt_cnormSq (fun b => Coercive.Internal.FieldModes.aestronglyMeasurable_modeGrad hGm ξ b)
  have Xo := aesm_sqrt_cnormSq (fun b =>
    aesm_curlOfGrad (fun c => Coercive.Internal.FieldModes.aestronglyMeasurable_modeGrad hGm ξ c) b)
  have X0 := aesm_sqrt_cnormSq (fun b => Coercive.Internal.FieldModes.aestronglyMeasurable_modeVel hvm ξ b)
  unfold PieceWeights.modeTerm PieceWeights.modeDensity
  have T2 := ((hD.comp measurable_snd).sub (measurable_const : Measurable fun _ : ℝ × Space => m.c)).aestronglyMeasurable.mul
    (X2.pow 2)
  have Tc := (((measurable_const : Measurable fun _ : ℝ × Space => (1 : ℝ)).sub (s1.comp measurable_snd)).sub
    (hD.comp measurable_snd)).aestronglyMeasurable.mul (Xc.pow 2)
  have To := ((s2.comp measurable_snd).sub (hZ.comp measurable_snd)).aestronglyMeasurable.mul (Xo.pow 2)
  have T1 := (s3.comp measurable_snd).aestronglyMeasurable.mul (X1.pow 2)
  have T0 := (s4.comp measurable_snd).aestronglyMeasurable.mul (X0.pow 2)
  exact (((T2.add Tc).add To).add T1).add T0

theorem ae_modeTerm_zero (hC : ClassSupportHolds) {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM)
    (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {Γ : Set Symmetry} {mo : ℕ} (hclass : IsModeClass Γ mo)
    {P' : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P' v G H g) (ξ : ℤ × ℤ) (hξ : ¬ IsLatticeHarmonic mo ξ) :
    ∀ᵐ y, m.modeTerm P h w v G H ξ 0 y = 0 := by
  refine PinHalf.ae_of_snd ?_
  filter_upwards [hC Γ mo P' v G H g hclass hv ξ hξ] with z hz
  rw [← modeTerm_shift m P h w hv.periodic_velocity hv.periodic_gradient hv.periodic_secondDeriv ξ z.1 z.2]
  unfold PieceWeights.modeTerm PieceWeights.modeDensity
  rw [hz.1, hz.2.1, hz.2.2]
  simp [cnormSq, curlOfGrad, curlGradOfSecondDeriv]

theorem ae_height_ne_zero : ∀ᵐ z : ℝ × Space, z.2 2 ≠ 0 := by
  have h0 : ∀ᵐ y : Space, y 2 ≠ 0 := measure_eq_zero_iff_ae_notMem.1 StretchMeanParts.coord_two_null
  rw [Measure.volume_eq_prod]
  exact Measure.quasiMeasurePreserving_snd.ae h0

theorem ae_modeTerm_flip (hF : ModeFlipHolds) (hT : ModeTermFlipHolds) {C : Type} {nE nM : ℕ}
    (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) (hfc : IsFlipCompatible m h w)
    {Γ : Set Symmetry} {P' : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P' v G H g) (hfl : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) (ξ : ℤ × ℤ) :
    ∀ᵐ y, m.modeTerm P h w v G H (flipLabel ξ) 0 (flipPoint y) = m.modeTerm P h w v G H ξ 0 y := by
  refine PinHalf.ae_of_snd ?_
  filter_upwards [hF Γ P' v G H g hv hfl ξ, ae_height_ne_zero] with z hz hz2
  rw [← modeTerm_shift m P h w hv.periodic_velocity hv.periodic_gradient hv.periodic_secondDeriv (flipLabel ξ) z.1
    (flipPoint z.2), ← modeTerm_shift m P h w hv.periodic_velocity hv.periodic_gradient hv.periodic_secondDeriv ξ z.1 z.2]
  exact hT m P h w hfc v G H ξ z.1 z.2 hz2 hz.1 hz.2.1 hz.2.2

def goodSet {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : Set Space :=
  {y | ∀ (ξ : ℤ × ℤ) (φ : ℝ), m.modeTerm P h w v G H ξ 0 (axialRot φ y) = m.modeTerm P h w v G H ξ 0 y}

theorem goodSet_rot {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (φ : ℝ) (y : Space) :
    axialRot φ y ∈ goodSet m P h w v G H ↔ y ∈ goodSet m P h w v G H := by
  have fwd : ∀ (ψ : ℝ) (x : Space), x ∈ goodSet m P h w v G H → axialRot ψ x ∈ goodSet m P h w v G H := by
    intro ψ x hx ξ φ'
    rw [← RotationInternal.axialRot_add, hx ξ (φ' + ψ), hx ξ ψ]
  refine ⟨fun hy => ?_, fwd φ y⟩
  have h' := fwd (-φ) _ hy
  rwa [RotationInternal.axialRot_neg_self] at h'

theorem ae_goodSet {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {w₀ e₁ e₂ e₃ : ℝ} (hm : CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ e₁ e₂ e₃)
    (hfc : IsFlipCompatible m h w) {Γ : Set Symmetry} {P' : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P' v G H g) :
    ∀ᵐ y, y ∈ goodSet m P h w v G H := by
  obtain ⟨lv, lG, lH⟩ := perturbationLocalIntegrabilityHolds_proof Γ P' v G H g hv
  refine PinHalf.ae_of_snd ?_
  filter_upwards [ae_integrable_orbit axialRotationHolds_proof lv, ae_integrable_orbit axialRotationHolds_proof lG,
    ae_integrable_orbit axialRotationHolds_proof lH] with z h1 h2 h3
  intro ξ φ
  rw [← modeTerm_shift m P h w hv.periodic_velocity hv.periodic_gradient hv.periodic_secondDeriv ξ z.1
    (axialRot φ z.2), ← modeTerm_shift m P h w hv.periodic_velocity hv.periodic_gradient hv.periodic_secondDeriv ξ z.1 z.2]
  exact modeTerm_rot_of m P h w ξ φ h1 h2 h3 (modeDensity_rot m P h w hm hfc ξ φ z.2)

end Internal.ModeDensityBridge

end Bridge

end CertCell

end Breakdown
