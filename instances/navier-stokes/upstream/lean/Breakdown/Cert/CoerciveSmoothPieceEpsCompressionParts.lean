import Breakdown.Cert.CoerciveSmoothPieceEpsCompressionVector
import Breakdown.Cert.CoerciveSmoothEpsPointwiseSecondDeriv
import Breakdown.Cert.ExtendedCoercivePieceEpsStretch

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEpsCompressionParts

open Internal.SmoothPieceEpsCore Internal.PieceAbsorb Internal.SmoothPieceEpsCompression

private theorem rc0 (ψ : ℝ) (u : Space) : axialRot ψ u 0 = Real.cos ψ * u 0 - Real.sin ψ * u 1 := by
  simp [axialRot, unitVector]

private theorem rc1 (ψ : ℝ) (u : Space) : axialRot ψ u 1 = Real.sin ψ * u 0 + Real.cos ψ * u 1 := by
  simp [axialRot, unitVector]

private theorem rc2 (ψ : ℝ) (u : Space) : axialRot ψ u 2 = u 2 := by
  simp [axialRot, unitVector]

private theorem pc0 (u : Space) : axialPerp u 0 = -u 1 := by simp [axialPerp, unitVector]

private theorem pc1 (u : Space) : axialPerp u 1 = u 0 := by simp [axialPerp, unitVector]

private theorem pc2 (u : Space) : axialPerp u 2 = 0 := by simp [axialPerp, unitVector]

theorem rot_frame (φ a : ℝ) (w y : Space) (j : Fin 3) :
    axialRot (-φ) (w + (1 / 2 : ℝ) • axialRot φ y - a • axialPerp (axialRot φ y)) j
      = axialRot (-φ) w j + ((1 / 2 : ℝ) • y - a • axialPerp y) j := by
  have hs := Real.sin_sq_add_cos_sq φ
  fin_cases j
  · simp only [Fin.zero_eta, rc0, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pc0, rc1,
      Real.cos_neg, Real.sin_neg]
    simp only [pc1, rc0]
    linear_combination (y 0 / 2 + a * y 1) * hs
  · simp only [Fin.mk_one, rc1, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pc1, rc0,
      Real.cos_neg, Real.sin_neg]
    simp only [pc0, rc1]
    linear_combination (y 1 / 2 - a * y 0) * hs
  · simp only [Fin.reduceFinMk, rc2, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pc2]
    ring

theorem rot_clm_cnormSq_le (L : Space →L[ℝ] Space) (φ : ℝ) (u : Fin 3 → ℂ) :
    cnormSq (fun i => ∑ j, ((axialRot (-φ) (L (axialRot φ (unitVector j))) i : ℝ) : ℂ) * u j)
      ≤ ‖L‖ ^ 2 * cnormSq u := by
  set a : Space := ∑ j : Fin 3, (u j).re • unitVector j with hadef
  set b : Space := ∑ j : Fin 3, (u j).im • unitVector j with hbdef
  have ha : ∀ j, axialRot (-φ) (axialRot φ a) j = (u j).re := by
    intro j
    rw [RotationInternal.axialRot_neg_self, hadef, Internal.MuSmooth.space_sum_apply]
  have hb : ∀ j, axialRot (-φ) (axialRot φ b) j = (u j).im := by
    intro j
    rw [RotationInternal.axialRot_neg_self, hbdef, Internal.MuSmooth.space_sum_apply]
  have key : ∀ i, (∑ j, ((axialRot (-φ) (L (axialRot φ (unitVector j))) i : ℝ) : ℂ) * u j)
      = ((axialRot (-φ) (L (axialRot φ a)) i : ℝ) : ℂ) + ((axialRot (-φ) (L (axialRot φ b)) i : ℝ) : ℂ) * Complex.I := by
    intro i
    rw [Internal.MuSmooth.rot_apply_clm L φ (axialRot φ a) i, Internal.MuSmooth.rot_apply_clm L φ (axialRot φ b) i]
    simp only [ha, hb]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← Complex.re_add_im (u j)]
    ring
  have hsq : ∀ p q : ℝ, ‖(p : ℂ) + (q : ℂ) * Complex.I‖ ^ 2 = p ^ 2 + q ^ 2 := by
    intro p q
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have nrm : ∀ w : Space, ‖axialRot (-φ) (L (axialRot φ w))‖ ^ 2 ≤ ‖L‖ ^ 2 * ‖w‖ ^ 2 := by
    intro w
    rw [RotationInternal.axialRot_norm, ← mul_pow]
    have := L.le_opNorm (axialRot φ w)
    rw [RotationInternal.axialRot_norm] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  unfold cnormSq
  simp only [key, hsq, Finset.sum_add_distrib]
  have na := nrm a
  have nb := nrm b
  rw [SmoothBaseInternal.space_norm_sq, SmoothBaseInternal.space_norm_sq] at na nb
  have ea : ∑ i : Fin 3, a i ^ 2 = ∑ j : Fin 3, (u j).re ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [hadef, Internal.MuSmooth.space_sum_apply]
  have eb : ∑ i : Fin 3, b i ^ 2 = ∑ j : Fin 3, (u j).im ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [hbdef, Internal.MuSmooth.space_sum_apply]
  rw [ea] at na
  rw [eb] at nb
  have eu : ∑ j : Fin 3, ‖u j‖ ^ 2 = ∑ j : Fin 3, (u j).re ^ 2 + ∑ j : Fin 3, (u j).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [eu, mul_add]
  linarith

theorem summable_vel_ae {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
    {w : Space → ℝ} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) :
    ∀ᵐ z ∂slabMeasure, Summable (fun ι => velAmp v ι z.1 z.2 ^ 2) := by
  have hp := hSP P v hS.smooth
  have hV := hp.measurable_velocity
  have hden : AEMeasurable (fun z : ℝ × Space => 1 + ‖z.2‖) volume :=
    (continuous_const.add (continuous_norm.comp continuous_snd)).aemeasurable
  have m4 : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2))
      volume :=
    fun ι => (((Internal.PieceAbsorb.aem_velAmp hV ι).div hden).pow_const 2).ennreal_ofReal
  have hAm : AEMeasurable (fun z : ℝ × Space =>
      ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2)) slabMeasure :=
    Internal.SmoothPieceEps.slab_aem (AEMeasurable.ennreal_tsum m4)
  have hfin : ∫⁻ z, (∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2)) ∂slabMeasure < ⊤ := by
    refine lt_of_le_of_lt (lintegral_prod_le _) (lt_of_le_of_lt
      (lintegral_mono fun σ => lintegral_mono fun y => ?_)
      (Internal.SmoothPieceEps.amplitudeSeries_finite hPars hSP P v hS.smooth))
    exact le_add_self
  filter_upwards [ae_lt_top' hAm hfin.ne] with z hz
  have s := ENNReal.summable_toReal hz.ne
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at s
  have hpos : 0 < 1 + ‖z.2‖ := by positivity
  have e : ∀ ι, velAmp v ι z.1 z.2 ^ 2 = (1 + ‖z.2‖) ^ 2 * (velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2 := by
    intro ι
    field_simp
  simp_rw [e]
  exact s.mul_left _

theorem piece_disjoint {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
    {w : Space → ℝ} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ ι ∈ (m.epsP β).modes, -ι ∉ (m.epsP β).modes := by
  intro ι h1 h2
  obtain ⟨Ωs, hΩ, hle⟩ := hS.admissible.eps_oneSided β
  have a1 := hle ι h1
  have a2 := hle (-ι) h2
  have e : PieceWeights.frameFreq P (m.epsP β).frame (-ι) = -PieceWeights.frameFreq P (m.epsP β).frame ι := by
    unfold PieceWeights.frameFreq
    simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
    ring
  rw [e] at a2
  linarith

theorem ind_summable {p : Type} [Fintype p] (T : Set (ℤ × ℤ)) (x : ℤ × ℤ → p → ℂ)
    (hx : Summable (fun ι => Real.sqrt (cnormSq (x ι)) ^ 2)) :
    Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * cnormSq (x ι)) := by
  refine hx.of_nonneg_of_le (fun ι => mul_nonneg (ind_nonneg T ι) (Internal.FieldModes.cnormSq_nonneg _))
    (fun ι => ?_)
  rw [Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg _)]
  exact mul_le_of_le_one_left (Internal.FieldModes.cnormSq_nonneg _) (ind_le_one T ι)

theorem summable_ae {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
    {w : Space → ℝ} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) :
    ∀ᵐ z ∂slabMeasure,
      Summable (fun ι => vortAmp (gradField v) ι z.1 z.2 ^ 2) ∧
      Summable (fun ι => vortGradAmp (secondDerivField v) ι z.1 z.2 ^ 2) ∧
      Summable (fun ι => gradAmp (gradField v) ι z.1 z.2 ^ 2) := by
  have hp := hSP P v hS.smooth
  have hG := hp.measurable_gradient
  have hH := hp.measurable_secondDeriv
  have m1 : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2)) volume :=
    fun ι => ((Internal.PieceAbsorb.aem_vortAmp hG ι).pow_const 2).ennreal_ofReal
  have m2 : ∀ ι, AEMeasurable
      (fun z : ℝ × Space => ENNReal.ofReal (vortGradAmp (secondDerivField v) ι z.1 z.2 ^ 2)) volume :=
    fun ι => ((Internal.PieceAbsorb.aem_vortGradAmp hH ι).pow_const 2).ennreal_ofReal
  have m3 : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (gradAmp (gradField v) ι z.1 z.2 ^ 2)) volume :=
    fun ι => ((Internal.PieceAbsorb.aem_gradAmp hG ι).pow_const 2).ennreal_ofReal
  have hAm : AEMeasurable (fun z : ℝ × Space =>
      ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι z.1 z.2 ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι z.1 z.2 ^ 2)) slabMeasure :=
    Internal.SmoothPieceEps.slab_aem
      (((AEMeasurable.ennreal_tsum m1).add (AEMeasurable.ennreal_tsum m2)).add (AEMeasurable.ennreal_tsum m3))
  have hfin : ∫⁻ z, (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι z.1 z.2 ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι z.1 z.2 ^ 2)) ∂slabMeasure < ⊤ := by
    refine lt_of_le_of_lt (lintegral_prod_le _) (lt_of_le_of_lt
      (lintegral_mono fun σ => lintegral_mono fun y => ?_)
      (Internal.SmoothPieceEps.amplitudeSeries_finite hPars hSP P v hS.smooth))
    exact le_self_add
  filter_upwards [ae_lt_top' hAm hfin.ne] with z hz
  have f1 : (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top hz.ne (le_trans le_self_add le_self_add)
  have f2 : (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι z.1 z.2 ^ 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top hz.ne (le_trans le_add_self le_self_add)
  have f3 : (∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι z.1 z.2 ^ 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top hz.ne le_add_self
  refine ⟨?_, ?_, ?_⟩
  · have := ENNReal.summable_toReal f1
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using this
  · have := ENNReal.summable_toReal f2
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using this
  · have := ENNReal.summable_toReal f3
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using this

section Bound

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {w : Space → ℝ}
  {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}

theorem transport_compression (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeries m h W v β z.1 z.2 < ⊤ →
      ∃ c : ℤ × ℤ → Fin 3 → ℂ,
        (∀ ι, PieceWeights.inPiece (m.epsP β).modes ι →
          Real.sqrt (cnormSq (modeVel ι (transportRest (m.epsP β).frame W v) z.1 z.2 - c ι))
            ≤ edgeSum h (m.epsP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2) ι) ∧
        Summable (fun ι => (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ) * cdot (vortMode v ι z.1 z.2) (c ι)).re) ∧
        |∑' ι, (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ) * cdot (vortMode v ι z.1 z.2) (c ι)).re| ≤ (m.epsP β).wt z.2 * frameSpeedSup W (m.epsP β).frame z.2
            * pieceNorm (m.epsP β).modes (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hS.smooth.smooth 2
  have hW := hS.flow_smooth
  have hWp := hS.flow_periodic
  have hA := hS.admissible
  have h0 : (0 : ℤ × ℤ) ∈ h.harmonics := hA.harmonics_zero
  have hs : ∀ α ∈ h.harmonics.erase 0, -α ∈ h.harmonics.erase 0 := fun α hα =>
    Finset.mem_erase.mpr ⟨neg_ne_zero.mpr (Finset.ne_of_mem_erase hα),
      hA.harmonics_neg α (Finset.mem_of_mem_erase hα)⟩
  have hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ h.harmonics.erase 0, (modeVel α W σ y i).re := by
    intro σ y i
    rw [hA.harmonics_span σ y i]
    exact (Finset.add_sum_erase h.harmonics (fun α => (modeVel α W σ y i).re) h0).symm
  filter_upwards [summable_ae hPars hSP hS] with z hsum _hN
  obtain ⟨s1, s2, _⟩ := hsum
  have hUexp : ∀ τ φ : ℝ, ∀ j : Fin 3, ((axialRot (-φ) (W (z.1 + τ) (axialRot φ z.2)
        + (1 / 2 : ℝ) • axialRot φ z.2 - (m.epsP β).frame • axialPerp (axialRot φ z.2)) j : ℝ) : ℂ)
      = (((meanField W z.2 + (1 / 2 : ℝ) • z.2 - (m.epsP β).frame • axialPerp z.2) j : ℝ) : ℂ)
        + ∑ α ∈ h.harmonics.erase 0, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * modeVel α W z.1 z.2 j := by
    intro τ φ j
    rw [rot_frame, Complex.ofReal_add,
      Internal.SmoothEpsPointwise.velW_expansion hW hWp (h.harmonics.erase 0) hs hh z.1 τ φ z.2 j]
    simp only [PiLp.add_apply, PiLp.sub_apply, Complex.ofReal_add, Complex.ofReal_sub]
    ring
  have hK : Continuous (fun z : ℝ × Space => fderiv ℝ (vortField v z.1) z.2) := vortGrad_continuous hv2
  have hf : ∀ ι, modeVel ι (transportRest (m.epsP β).frame W v) z.1 z.2 = fun i => ∑ j : Fin 3,
      (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) z.1 z.2) (i, j)
          * (((meanField W z.2 + (1 / 2 : ℝ) • z.2 - (m.epsP β).frame • axialPerp z.2) j : ℝ) : ℂ)
        + ∑ α ∈ h.harmonics.erase 0, curlGradOfSecondDeriv (modeSecondDeriv (ι - α) (secondDerivField v) z.1 z.2) (i, j)
          * modeVel α W z.1 z.2 j) := by
    intro ι
    funext i
    have e := Internal.SmoothEpsPointwise.mode_product_vec (h.harmonics.erase 0)
      (fun s x => fderiv ℝ (vortField v s) x) hK
      (fun s x => W s x + (1 / 2 : ℝ) • x - (m.epsP β).frame • axialPerp x) z.1 z.2
      (fun j => (meanField W z.2 + (1 / 2 : ℝ) • z.2 - (m.epsP β).frame • axialPerp z.2) j)
      (fun α => modeVel α W z.1 z.2) hUexp ι i
    simp_rw [Internal.SmoothEpsPointwise.modeGrad_vort_eq hv2] at e
    exact e
  have hbdd : BddAbove (Set.range fun p : ℝ × ℝ => ‖W p.1 (axialRot p.2 z.2) + (1 / 2 : ℝ) • axialRot p.2 z.2
      - (m.epsP β).frame • (-(axialRot p.2 z.2 1) • unitVector 0 + axialRot p.2 z.2 0 • unitVector 1)‖) :=
    ⟨(m.epsP β).speed z.2, by rintro _ ⟨p, rfl⟩; exact hA.epsSpeed_ge β p.1 p.2 z.2⟩
  have hle : ∀ τ φ : ℝ, ‖W (z.1 + τ) (axialRot φ z.2) + (1 / 2 : ℝ) • axialRot φ z.2
      - (m.epsP β).frame • axialPerp (axialRot φ z.2)‖ ≤ frameSpeedSup W (m.epsP β).frame z.2 :=
    fun τ φ => le_ciSup hbdd (z.1 + τ, φ)
  have hS0 : 0 ≤ frameSpeedSup W (m.epsP β).frame z.2 := (norm_nonneg _).trans (hle 0 0)
  have hU : ∀ τ φ, cnormSq (fun l => (((meanField W z.2 + (1 / 2 : ℝ) • z.2 - (m.epsP β).frame • axialPerp z.2) l
      : ℝ) : ℂ) + ∑ α ∈ h.harmonics.erase 0, torusPhase α τ φ * modeVel α W z.1 z.2 l)
        ≤ frameSpeedSup W (m.epsP β).frame z.2 ^ 2 := by
    intro τ φ
    have e : (fun l => (((meanField W z.2 + (1 / 2 : ℝ) • z.2 - (m.epsP β).frame • axialPerp z.2) l : ℝ) : ℂ)
        + ∑ α ∈ h.harmonics.erase 0, torusPhase α τ φ * modeVel α W z.1 z.2 l)
        = fun l => ((axialRot (-φ) (W (z.1 + τ) (axialRot φ z.2) + (1 / 2 : ℝ) • axialRot φ z.2
          - (m.epsP β).frame • axialPerp (axialRot φ z.2)) l : ℝ) : ℂ) := by
      funext l
      rw [hUexp τ φ l]
      rfl
    rw [e, ← Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg _)]
    have hn : Real.sqrt (cnormSq (fun l => ((axialRot (-φ) (W (z.1 + τ) (axialRot φ z.2)
        + (1 / 2 : ℝ) • axialRot φ z.2 - (m.epsP β).frame • axialPerp (axialRot φ z.2)) l : ℝ) : ℂ)))
        = ‖W (z.1 + τ) (axialRot φ z.2) + (1 / 2 : ℝ) • axialRot φ z.2
          - (m.epsP β).frame • axialPerp (axialRot φ z.2)‖ :=
      (Internal.SmoothEpsPointwise.cnorm3_ofReal _).trans (RotationInternal.axialRot_norm _ _)
    rw [hn]
    exact pow_le_pow_left₀ (norm_nonneg _) (hle τ φ) 2
  have hcneg : ∀ α, cnormSq (modeVel (-α) W z.1 z.2) = cnormSq (modeVel α W z.1 z.2) := by
    intro α
    unfold cnormSq
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Internal.SmoothEpsPointwise.modeVel_neg, Complex.norm_conj]
  obtain ⟨c', h1, h2, h3⟩ := compression_vec h (m.epsP β).modes (piece_disjoint hS β) hA.harmonics_neg h0
    (fun j => (((meanField W z.2 + (1 / 2 : ℝ) • z.2 - (m.epsP β).frame • axialPerp z.2) j : ℝ) : ℂ))
    (fun α => modeVel α W z.1 z.2) (frameSpeedSup W (m.epsP β).frame z.2) hS0 hU hcneg
    (fun ι => vortMode v ι z.1 z.2) (fun ι => modeVel ι (transportRest (m.epsP β).frame W v) z.1 z.2)
    (fun κ => curlGradOfSecondDeriv (modeSecondDeriv κ (secondDerivField v) z.1 z.2)) hf
    (ind_summable _ _ s1) (ind_summable _ _ s2) ((m.epsP β).wt z.2) (hA.eps_wt_nonneg β z.2)
  exact ⟨c', h1, h2, h3⟩

open CoerciveWeak.Internal.PieceEpsStretch (stretchCoeff antiPart symbolMat_anti anti_rows_bound curl_components
  compression_self_split) in
theorem stretch_compression (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeries m h W v β z.1 z.2 < ⊤ →
      ∃ c : ℤ × ℤ → Fin 3 → ℂ,
        (∀ ι, PieceWeights.inPiece (m.epsP β).modes ι →
          Real.sqrt (cnormSq (modeVel ι (stretchRest W v) z.1 z.2 - c ι))
            ≤ edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α z.1 z.2) (fun κ => vortAmp (gradField v) κ z.1 z.2) ι) ∧
        Summable (fun ι => (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ) * cdot (vortMode v ι z.1 z.2) (c ι)).re) ∧
        |∑' ι, (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ) * cdot (vortMode v ι z.1 z.2) (c ι)).re| ≤ (m.epsP β).wt z.2 * ((1 / 2) * vortSup W z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2 := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hS.smooth.smooth 1
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hS.smooth.smooth 2
  have hW := hS.flow_smooth
  have hWp := hS.flow_periodic
  have hA := hS.admissible
  obtain ⟨B, hB⟩ := Internal.SmoothEpsPointwise.grad_bound_of_decay hS.flow_decay
  have h0 : (0 : ℤ × ℤ) ∈ h.harmonics := hA.harmonics_zero
  have hs : ∀ α ∈ h.harmonics.erase 0, -α ∈ h.harmonics.erase 0 := fun α hα =>
    Finset.mem_erase.mpr ⟨neg_ne_zero.mpr (Finset.ne_of_mem_erase hα),
      hA.harmonics_neg α (Finset.mem_of_mem_erase hα)⟩
  have hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ h.harmonics.erase 0, (modeVel α W σ y i).re := by
    intro σ y i
    rw [hA.harmonics_span σ y i]
    exact (Finset.add_sum_erase h.harmonics (fun α => (modeVel α W σ y i).re) h0).symm
  have hp0 : ∀ τ φ, torusPhase 0 τ φ = 1 := fun τ φ => by simp [torusPhase]
  filter_upwards [summable_ae hPars hSP hS] with z hsum _hN
  obtain ⟨s1, _, _⟩ := hsum
  have hE := fun τ φ i j => Internal.SmoothEpsPointwise.gradW_expansion hW hB hWp (h.harmonics.erase 0) hs hh
    z.1 τ φ z.2 i j
  have hvc : Continuous (fun z : ℝ × Space => vortField v z.1 z.2) := vortField_continuous hv2
  have hf0 : ∀ ι, modeVel ι (stretchRest W v) z.1 z.2 = fun i => ∑ j : Fin 3,
      ((((fderiv ℝ (meanField W) z.2 (unitVector j) i : ℝ)) : ℂ) * vortMode v ι z.1 z.2 j
        + ∑ α ∈ h.harmonics.erase 0, modeGrad α (gradField W) z.1 z.2 (i, j) * vortMode v (ι - α) z.1 z.2 j) := by
    intro ι
    funext i
    simp only [vortMode_eq_modeVel hv1]
    exact Internal.MuSmooth.mode_product (h.harmonics.erase 0) W (vortField v) hvc z.1 z.2
      (fun i j => fderiv ℝ (meanField W) z.2 (unitVector j) i)
      (fun α => modeGrad α (gradField W) z.1 z.2) hE ι i
  have hf : ∀ ι, modeVel ι (stretchRest W v) z.1 z.2
      = ∑ b ∈ h.harmonics, applyMat (stretchCoeff W z.1 z.2 b) (vortMode v (ι - b) z.1 z.2) := by
    intro ι
    rw [hf0 ι]
    funext i
    rw [Finset.sum_apply, ← Finset.add_sum_erase h.harmonics _ h0]
    unfold applyMat stretchCoeff
    simp only [matMat, ↓reduceIte, sub_zero, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α hα => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_neg (Finset.ne_of_mem_erase hα)]
  have hselfAdj : ∀ b i j, stretchCoeff W z.1 z.2 (-b) i j = starRingEnd ℂ (stretchCoeff W z.1 z.2 b i j) := by
    intro b i j
    unfold stretchCoeff matMat
    by_cases hb : b = 0
    · subst hb
      simp [Complex.conj_ofReal]
    · rw [if_neg (neg_ne_zero.mpr hb), if_neg hb]
      exact Internal.MuSmooth.modeGrad_neg b (gradField W) z.1 z.2 (i, j)
  have hbdd : BddAbove (Set.range fun p : ℝ × ℝ => ‖curlVec (fderiv ℝ (W p.1) (axialRot p.2 z.2))‖) :=
    ⟨h.supVort z.2, by rintro _ ⟨p, rfl⟩; exact hA.supVort_ge p.1 p.2 z.2⟩
  have hle : ∀ τ φ : ℝ, ‖curlVec (fderiv ℝ (W (z.1 + τ)) (axialRot φ z.2))‖ ≤ vortSup W z.2 :=
    fun τ φ => le_ciSup hbdd (z.1 + τ, φ)
  have hS0 : 0 ≤ vortSup W z.2 := (norm_nonneg _).trans (hle 0 0)
  have hsym : ∀ τ φ (u : Fin 3 → ℂ), cnormSq (applyMat (symbolMat h.harmonics (antiPart (stretchCoeff W z.1 z.2)) τ φ) u)
      ≤ ((1 / 2) * vortSup W z.2) ^ 2 * cnormSq u := by
    intro τ φ u
    have hM : ∀ i j, symbolMat h.harmonics (stretchCoeff W z.1 z.2) τ φ i j
        = ((axialRot (-φ) (fderiv ℝ (W (z.1 + τ)) (axialRot φ z.2) (axialRot φ (unitVector j))) i : ℝ) : ℂ) := by
      intro i j
      rw [hE τ φ i j]
      unfold symbolMat stretchCoeff
      rw [← Finset.add_sum_erase h.harmonics _ h0]
      simp only [matMat, ↓reduceIte, hp0, one_mul]
      congr 1
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [if_neg (Finset.ne_of_mem_erase hα)]
      rfl
    have happ : applyMat (symbolMat h.harmonics (antiPart (stretchCoeff W z.1 z.2)) τ φ) u
        = fun i => ∑ j, ((((axialRot (-φ) (fderiv ℝ (W (z.1 + τ)) (axialRot φ z.2) (axialRot φ (unitVector j))) i
          - axialRot (-φ) (fderiv ℝ (W (z.1 + τ)) (axialRot φ z.2) (axialRot φ (unitVector i))) j) / 2 : ℝ)) : ℂ)
            * u j := by
      funext i
      unfold applyMat
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [symbolMat_anti, hM, hM]
      push_cast
      ring
    rw [happ]
    refine (anti_rows_bound (fun i j => axialRot (-φ) (fderiv ℝ (W (z.1 + τ)) (axialRot φ z.2)
      (axialRot φ (unitVector j))) i) u).trans ?_
    have hc := curl_components φ (fderiv ℝ (W (z.1 + τ)) (axialRot φ z.2))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hle τ φ) 2
    rw [hc] at hsq
    have hu := Internal.FieldModes.cnormSq_nonneg u
    calc _ ≤ vortSup W z.2 ^ 2 / 4 * cnormSq u := mul_le_mul_of_nonneg_right (by linarith) hu
      _ = ((1 / 2) * vortSup W z.2) ^ 2 * cnormSq u := by ring
  have hcneg : ∀ b, cnormSq (modeGrad (-b) (gradField W) z.1 z.2) = cnormSq (modeGrad b (gradField W) z.1 z.2) := by
    intro b
    unfold cnormSq
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [Internal.MuSmooth.modeGrad_neg, Complex.norm_conj]
  have hX : ∀ b ∈ h.harmonics, b ≠ 0 → ∀ u, Real.sqrt (cnormSq (applyMat (stretchCoeff W z.1 z.2 b) u))
      ≤ gradAmp (gradField W) b z.1 z.2 * Real.sqrt (cnormSq u) := by
    intro b _ hb u
    have e : stretchCoeff W z.1 z.2 b = fun i j => modeGrad b (gradField W) z.1 z.2 (i, j) := by
      funext i j
      simp only [stretchCoeff, matMat, if_neg hb]
    rw [e]
    exact mat_bound _ _
  have hXneg : ∀ b ∈ h.harmonics, b ≠ 0 → ∀ u, Real.sqrt (cnormSq (applyMat (stretchCoeff W z.1 z.2 (-b)) u))
      ≤ gradAmp (gradField W) b z.1 z.2 * Real.sqrt (cnormSq u) := by
    intro b _ hb u
    have e : stretchCoeff W z.1 z.2 (-b) = fun i j => modeGrad (-b) (gradField W) z.1 z.2 (i, j) := by
      funext i j
      simp only [stretchCoeff, matMat, if_neg (neg_ne_zero.mpr hb)]
    rw [e]
    refine (mat_bound _ _).trans_eq ?_
    unfold gradAmp
    rw [hcneg]
  obtain ⟨c', h1, h2, h3⟩ := compression_self_split h (m.epsP β).modes (piece_disjoint hS β)
    hA.harmonics_neg (stretchCoeff W z.1 z.2) hselfAdj ((1 / 2) * vortSup W z.2) (by positivity) hsym
    (fun ι => vortMode v ι z.1 z.2) (fun ι => modeVel ι (stretchRest W v) z.1 z.2) hf
    (fun α => gradAmp (gradField W) α z.1 z.2) hX hXneg (ind_summable _ _ s1) ((m.epsP β).wt z.2)
    (hA.eps_wt_nonneg β z.2)
  exact ⟨c', h1, h2, h3⟩

theorem vortTransport_compression (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeries m h W v β z.1 z.2 < ⊤ →
      ∃ c : ℤ × ℤ → Fin 3 → ℂ,
        (∀ ι, PieceWeights.inPiece (m.epsP β).modes ι →
          Real.sqrt (cnormSq (modeVel ι (vortTransportRest W v) z.1 z.2 - c ι))
            ≤ edgeSum h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α z.1 z.2) (fun κ => velAmp v κ z.1 z.2) ι) ∧
        Summable (fun ι => (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ) * cdot (vortMode v ι z.1 z.2) (c ι)).re) ∧
        |∑' ι, (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ) * cdot (vortMode v ι z.1 z.2) (c ι)).re| ≤ (m.epsP β).wt z.2 * vortGradSup W z.2
            * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  have hW := hS.flow_smooth
  have hWp := hS.flow_periodic
  have hA := hS.admissible
  obtain ⟨B, hB⟩ := Internal.SmoothEpsPointwise.grad_bound_of_decay hS.flow_decay
  obtain ⟨B₂, hB₂⟩ := Internal.SmoothEpsPointwise.secondDeriv_bound_of_decay hS.flow_decay
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) :=
    (contDiff_infty.mp hS.smooth.smooth 1).continuous
  have h0 : (0 : ℤ × ℤ) ∈ h.harmonics := hA.harmonics_zero
  have hs : ∀ α ∈ h.harmonics.erase 0, -α ∈ h.harmonics.erase 0 := fun α hα =>
    Finset.mem_erase.mpr ⟨neg_ne_zero.mpr (Finset.ne_of_mem_erase hα),
      hA.harmonics_neg α (Finset.mem_of_mem_erase hα)⟩
  have hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ h.harmonics.erase 0, (modeVel α W σ y i).re := by
    intro σ y i
    rw [hA.harmonics_span σ y i]
    exact (Finset.add_sum_erase h.harmonics (fun α => (modeVel α W σ y i).re) h0).symm
  filter_upwards [summable_ae hPars hSP hS, summable_vel_ae hPars hSP hS] with z hsum hvel _hN
  obtain ⟨s1, _⟩ := hsum
  have hE := fun τ φ i j => Internal.SmoothEpsPointwise.vortGradW_expansion hW hB hB₂ hWp (h.harmonics.erase 0)
    hs hh z.1 τ φ z.2 i j
  have hf : ∀ ι, modeVel ι (vortTransportRest W v) z.1 z.2 = fun i => ∑ j : Fin 3,
      ((((fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) z.2 (unitVector j) i : ℝ)) : ℂ)
          * modeVel ι v z.1 z.2 j
        + ∑ α ∈ h.harmonics.erase 0, curlGradOfSecondDeriv (modeSecondDeriv α (secondDerivField W) z.1 z.2) (i, j)
          * modeVel (ι - α) v z.1 z.2 j) := by
    intro ι
    funext i
    exact Internal.MuSmooth.mode_product (h.harmonics.erase 0) (vortField W) v hvc z.1 z.2
      (fun i j => fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) z.2 (unitVector j) i)
      (fun α => curlGradOfSecondDeriv (modeSecondDeriv α (secondDerivField W) z.1 z.2)) hE ι i
  have hbdd : BddAbove (Set.range fun p : ℝ × ℝ =>
      ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (W p.1) x)) (axialRot p.2 z.2)‖) :=
    ⟨h.supGradVort z.2, by rintro _ ⟨p, rfl⟩; exact hA.supGradVort_ge p.1 p.2 z.2⟩
  have hle : ∀ τ φ : ℝ, ‖fderiv ℝ (vortField W (z.1 + τ)) (axialRot φ z.2)‖ ≤ vortGradSup W z.2 :=
    fun τ φ => le_ciSup hbdd (z.1 + τ, φ)
  have hS0 : 0 ≤ vortGradSup W z.2 := (norm_nonneg _).trans (hle 0 0)
  have hU : ∀ τ φ (u : Fin 3 → ℂ), cnormSq (fun i => ∑ j,
      ((((fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) z.2 (unitVector j) i : ℝ)) : ℂ)
        + ∑ α ∈ h.harmonics.erase 0, torusPhase α τ φ * curlGradOfSecondDeriv (modeSecondDeriv α (secondDerivField W) z.1 z.2) (i, j))
        * u j) ≤ vortGradSup W z.2 ^ 2 * cnormSq u := by
    intro τ φ u
    have e : (fun i => ∑ j,
        ((((fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) z.2 (unitVector j) i : ℝ)) : ℂ)
          + ∑ α ∈ h.harmonics.erase 0, torusPhase α τ φ * curlGradOfSecondDeriv (modeSecondDeriv α (secondDerivField W) z.1 z.2) (i, j))
          * u j)
        = fun i => ∑ j, ((axialRot (-φ) (fderiv ℝ (vortField W (z.1 + τ)) (axialRot φ z.2)
            (axialRot φ (unitVector j))) i : ℝ) : ℂ) * u j := by
      funext i
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hE τ φ i j]
      rfl
    rw [e]
    refine (rot_clm_cnormSq_le _ φ u).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hle τ φ) 2)
      (Internal.FieldModes.cnormSq_nonneg u)
  have hcneg : ∀ α, cnormSq (curlGradOfSecondDeriv (modeSecondDeriv (-α) (secondDerivField W) z.1 z.2))
      = cnormSq (curlGradOfSecondDeriv (modeSecondDeriv α (secondDerivField W) z.1 z.2)) := by
    intro α
    unfold cnormSq
    refine Finset.sum_congr rfl fun il _ => ?_
    have e : curlGradOfSecondDeriv (modeSecondDeriv (-α) (secondDerivField W) z.1 z.2) il
        = (starRingEnd ℂ) (curlGradOfSecondDeriv (modeSecondDeriv α (secondDerivField W) z.1 z.2) il) := by
      unfold curlGradOfSecondDeriv
      simp only [Internal.SmoothEpsPointwise.modeSecondDeriv_neg, map_sum, map_mul, Complex.conj_ofReal]
    rw [e, Complex.norm_conj]
  obtain ⟨c', h1, h2, h3⟩ := compression_mat h (m.epsP β).modes (piece_disjoint hS β) hA.harmonics_neg h0
    (fun i j => ((fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) z.2 (unitVector j) i : ℝ) : ℂ))
    (fun α => curlGradOfSecondDeriv (modeSecondDeriv α (secondDerivField W) z.1 z.2)) (vortGradSup W z.2) hS0 hU hcneg
    (fun ι => vortMode v ι z.1 z.2) (fun ι => modeVel ι (vortTransportRest W v) z.1 z.2)
    (fun ι => modeVel ι v z.1 z.2) hf
    (ind_summable _ _ s1) (ind_summable _ _ hvel) ((m.epsP β).wt z.2) (hA.eps_wt_nonneg β z.2)
  exact ⟨c', h1, h2, h3⟩

theorem vortStretch_compression (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hS : CoreSetting m P h w W w₀ epsSup epsGradSup ratio v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeries m h W v β z.1 z.2 < ⊤ →
      ∃ c : ℤ × ℤ → Fin 3 → ℂ,
        (∀ ι, PieceWeights.inPiece (m.epsP β).modes ι →
          Real.sqrt (cnormSq (modeVel ι (vortStretchRest W v) z.1 z.2 - c ι))
            ≤ edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι) ∧
        Summable (fun ι => (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ) * cdot (vortMode v ι z.1 z.2) (c ι)).re) ∧
        |∑' ι, (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ) * cdot (vortMode v ι z.1 z.2) (c ι)).re| ≤ (m.epsP β).wt z.2 * vortSup W z.2
            * pieceNorm (m.epsP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hS.smooth.smooth 1
  have hW := hS.flow_smooth
  have hWp := hS.flow_periodic
  have hA := hS.admissible
  obtain ⟨B, hB⟩ := Internal.SmoothEpsPointwise.grad_bound_of_decay hS.flow_decay
  have h0 : (0 : ℤ × ℤ) ∈ h.harmonics := hA.harmonics_zero
  have hs : ∀ α ∈ h.harmonics.erase 0, -α ∈ h.harmonics.erase 0 := fun α hα =>
    Finset.mem_erase.mpr ⟨neg_ne_zero.mpr (Finset.ne_of_mem_erase hα),
      hA.harmonics_neg α (Finset.mem_of_mem_erase hα)⟩
  have hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ h.harmonics.erase 0, (modeVel α W σ y i).re := by
    intro σ y i
    rw [hA.harmonics_span σ y i]
    exact (Finset.add_sum_erase h.harmonics (fun α => (modeVel α W σ y i).re) h0).symm
  filter_upwards [summable_ae hPars hSP hS] with z hsum _hN
  obtain ⟨s1, _, s3⟩ := hsum
  have hUexp := fun τ φ j => Internal.SmoothEpsPointwise.vortW_expansion hW hB hWp (h.harmonics.erase 0) hs hh
    z.1 τ φ z.2 j
  have hK : Continuous (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) := fderiv_slice_continuous hv1
  have hf : ∀ ι, modeVel ι (vortStretchRest W v) z.1 z.2 = fun i => ∑ j : Fin 3,
      (modeGrad ι (gradField v) z.1 z.2 (i, j) * ((curlVec (fderiv ℝ (meanField W) z.2) j : ℝ) : ℂ)
        + ∑ α ∈ h.harmonics.erase 0, modeGrad (ι - α) (gradField v) z.1 z.2 (i, j)
          * curlOfGrad (modeGrad α (gradField W) z.1 z.2) j) := by
    intro ι
    funext i
    exact Internal.SmoothEpsPointwise.mode_product_vec (h.harmonics.erase 0)
      (fun s x => fderiv ℝ (v s) x) hK (vortField W) z.1 z.2
      (fun j => curlVec (fderiv ℝ (meanField W) z.2) j)
      (fun α => curlOfGrad (modeGrad α (gradField W) z.1 z.2)) hUexp ι i
  have hbdd : BddAbove (Set.range fun p : ℝ × ℝ => ‖curlVec (fderiv ℝ (W p.1) (axialRot p.2 z.2))‖) :=
    ⟨h.supVort z.2, by rintro _ ⟨p, rfl⟩; exact hA.supVort_ge p.1 p.2 z.2⟩
  have hle : ∀ τ φ : ℝ, ‖vortField W (z.1 + τ) (axialRot φ z.2)‖ ≤ vortSup W z.2 :=
    fun τ φ => le_ciSup hbdd (z.1 + τ, φ)
  have hS0 : 0 ≤ vortSup W z.2 := (norm_nonneg _).trans (hle 0 0)
  have hU : ∀ τ φ, cnormSq (fun l => ((curlVec (fderiv ℝ (meanField W) z.2) l : ℝ) : ℂ)
      + ∑ α ∈ h.harmonics.erase 0, torusPhase α τ φ * curlOfGrad (modeGrad α (gradField W) z.1 z.2) l)
        ≤ vortSup W z.2 ^ 2 := by
    intro τ φ
    have e : (fun l => ((curlVec (fderiv ℝ (meanField W) z.2) l : ℝ) : ℂ)
        + ∑ α ∈ h.harmonics.erase 0, torusPhase α τ φ * curlOfGrad (modeGrad α (gradField W) z.1 z.2) l)
        = fun l => ((axialRot (-φ) (vortField W (z.1 + τ) (axialRot φ z.2)) l : ℝ) : ℂ) := by
      funext l
      rw [hUexp τ φ l]
      rfl
    rw [e, ← Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg _)]
    have hn : Real.sqrt (cnormSq (fun l => ((axialRot (-φ) (vortField W (z.1 + τ) (axialRot φ z.2)) l : ℝ) : ℂ)))
        = ‖vortField W (z.1 + τ) (axialRot φ z.2)‖ :=
      (Internal.SmoothEpsPointwise.cnorm3_ofReal _).trans (RotationInternal.axialRot_norm _ _)
    rw [hn]
    exact pow_le_pow_left₀ (norm_nonneg _) (hle τ φ) 2
  have hcneg : ∀ α, cnormSq (curlOfGrad (modeGrad (-α) (gradField W) z.1 z.2))
      = cnormSq (curlOfGrad (modeGrad α (gradField W) z.1 z.2)) := by
    intro α
    unfold cnormSq
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : curlOfGrad (modeGrad (-α) (gradField W) z.1 z.2) j
        = (starRingEnd ℂ) (curlOfGrad (modeGrad α (gradField W) z.1 z.2) j) := by
      unfold curlOfGrad
      simp only [Internal.MuSmooth.modeGrad_neg, map_sum, map_mul, Complex.conj_ofReal]
    rw [e, Complex.norm_conj]
  obtain ⟨c', h1, h2, h3⟩ := compression_vec h (m.epsP β).modes (piece_disjoint hS β) hA.harmonics_neg h0
    (fun j => ((curlVec (fderiv ℝ (meanField W) z.2) j : ℝ) : ℂ))
    (fun α => curlOfGrad (modeGrad α (gradField W) z.1 z.2)) (vortSup W z.2) hS0 hU hcneg
    (fun ι => vortMode v ι z.1 z.2) (fun ι => modeVel ι (vortStretchRest W v) z.1 z.2)
    (fun κ => modeGrad κ (gradField v) z.1 z.2) hf
    (ind_summable _ _ s1) (ind_summable _ _ s3) ((m.epsP β).wt z.2) (hA.eps_wt_nonneg β z.2)
  exact ⟨c', h1, h2, h3⟩

end Bound

end Internal.SmoothPieceEpsCompressionParts

end Coercive

end Breakdown
