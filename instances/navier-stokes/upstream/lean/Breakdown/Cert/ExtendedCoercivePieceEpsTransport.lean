import Breakdown.Cert.CoerciveSmoothPieceEpsCompressionVector
import Breakdown.Cert.CoerciveSmoothEpsPointwiseProduct
import Breakdown.Cert.ExtendedCoerciveStatement
import Breakdown.Cert.ExtendedCoercivePieceEpsExpansion

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.ExtendedPieceEpsTransport

open Coercive Coercive.Internal.SmoothPieceEpsCore Coercive.Internal.MuSmooth Coercive.Internal.PieceAbsorb
  Coercive.Internal.SmoothPieceEpsCompression Coercive.Internal.SmoothEpsPointwise

theorem velW_expansion_of_continuous {W : ℝ → Space → Space} (hW : Continuous (fun z : ℝ × Space => W z.1 z.2))
    (hWp : IsTimePeriodic W) (s : Finset (ℤ × ℤ)) (hs : ∀ α ∈ s, -α ∈ s)
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (y : Space) (j : Fin 3) :
    ((axialRot (-φ) (W (σ + τ) (axialRot φ y)) j : ℝ) : ℂ)
      = ((meanField W y j : ℝ) : ℂ)
        + ∑ α ∈ s, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I) * modeVel α W σ y j := by
  rw [rot_field_expansion hW hWp s hh σ τ φ y j, Complex.ofReal_add]
  congr 1
  · unfold meanField
    rw [space_sum_apply (fun k => (modeVel (0, 0) W 0 y k).re) j, modeVel_mean_shift hWp σ y j]
  · exact re_sum_sym s hs _ fun α => by rw [phase_neg, modeVel_neg, map_mul]


private theorem rc0 (ψ : ℝ) (u : Space) : axialRot ψ u 0 = Real.cos ψ * u 0 - Real.sin ψ * u 1 := by
  simp [axialRot, unitVector]

private theorem rc1 (ψ : ℝ) (u : Space) : axialRot ψ u 1 = Real.sin ψ * u 0 + Real.cos ψ * u 1 := by
  simp [axialRot, unitVector]

private theorem rc2 (ψ : ℝ) (u : Space) : axialRot ψ u 2 = u 2 := by
  simp [axialRot, unitVector]

private theorem pc0 (u : Space) : axialPerp u 0 = -u 1 := by simp [axialPerp, unitVector]

private theorem pc1 (u : Space) : axialPerp u 1 = u 0 := by simp [axialPerp, unitVector]

private theorem pc2 (u : Space) : axialPerp u 2 = 0 := by simp [axialPerp, unitVector]

theorem rot_frame_weak (φ a : ℝ) (w y : Space) (j : Fin 3) :
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


theorem piece_disjoint_weak {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
    {w : Space → ℝ} {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ ι ∈ (m.epsP β).modes, -ι ∉ (m.epsP β).modes := by
  intro ι h1 h2
  obtain ⟨Ωs, hΩ, hle⟩ := hm.eps_oneSided β
  have a1 := hle ι h1
  have a2 := hle (-ι) h2
  have e : PieceWeights.frameFreq P (m.epsP β).frame (-ι) = -PieceWeights.frameFreq P (m.epsP β).frame ι := by
    unfold PieceWeights.frameFreq
    simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
    ring
  rw [e] at a2
  linarith

theorem ind_summable_weak {p : Type} [Fintype p] (T : Set (ℤ × ℤ)) (x : ℤ × ℤ → p → ℂ)
    (hx : Summable (fun ι => Real.sqrt (cnormSq (x ι)) ^ 2)) :
    Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * cnormSq (x ι)) := by
  refine hx.of_nonneg_of_le (fun ι => mul_nonneg (ind_nonneg T ι) (Internal.FieldModes.cnormSq_nonneg _))
    (fun ι => ?_)
  rw [Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg _)]
  exact mul_le_of_le_one_left (Internal.FieldModes.cnormSq_nonneg _) (ind_le_one T ι)


theorem summable_ae_weak {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
    {w : Space → ℝ} {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hv : IsSmoothPerturbation P v) :
    ∀ᵐ z ∂slabMeasure,
      Summable (fun ι => vortAmp (gradField v) ι z.1 z.2 ^ 2) ∧
      Summable (fun ι => vortGradAmp (secondDerivField v) ι z.1 z.2 ^ 2) ∧
      Summable (fun ι => gradAmp (gradField v) ι z.1 z.2 ^ 2) := by
  have hp := hSP P v hv
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
      (Internal.SmoothPieceEps.amplitudeSeries_finite hPars hSP P v hv))
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
  {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
  {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}

theorem transport_compression_of (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure,
      ∃ c : ℤ × ℤ → Fin 3 → ℂ,
        (∀ ι, PieceWeights.inPiece (m.epsP β).modes ι →
          Real.sqrt (cnormSq (modeVel ι (transportRest (m.epsP β).frame W v) z.1 z.2 - c ι))
            ≤ edgeSum h (m.epsP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2) ι) ∧
        Summable (fun ι => (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ) * cdot (vortMode v ι z.1 z.2) (c ι)).re) ∧
        |∑' ι, (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ) * cdot (vortMode v ι z.1 z.2) (c ι)).re| ≤ (m.epsP β).wt z.2 * frameSpeedSup W (m.epsP β).frame z.2
            * pieceNorm (m.epsP β).modes (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 2
  have hWc : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.smooth.continuous
  have hWp := hW.periodic
  have hA := hm
  have h0 : (0 : ℤ × ℤ) ∈ h.harmonics := hA.harmonics_zero
  have hs : ∀ α ∈ h.harmonics.erase 0, -α ∈ h.harmonics.erase 0 := fun α hα =>
    Finset.mem_erase.mpr ⟨neg_ne_zero.mpr (Finset.ne_of_mem_erase hα),
      hA.harmonics_neg α (Finset.mem_of_mem_erase hα)⟩
  have hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ h.harmonics.erase 0, (modeVel α W σ y i).re := by
    intro σ y i
    rw [hA.harmonics_span σ y i]
    exact (Finset.add_sum_erase h.harmonics (fun α => (modeVel α W σ y i).re) h0).symm
  filter_upwards [summable_ae_weak hPars hSP hm hv] with z hsum
  obtain ⟨s1, s2, _⟩ := hsum
  have hUexp : ∀ τ φ : ℝ, ∀ j : Fin 3, ((axialRot (-φ) (W (z.1 + τ) (axialRot φ z.2)
        + (1 / 2 : ℝ) • axialRot φ z.2 - (m.epsP β).frame • axialPerp (axialRot φ z.2)) j : ℝ) : ℂ)
      = (((meanField W z.2 + (1 / 2 : ℝ) • z.2 - (m.epsP β).frame • axialPerp z.2) j : ℝ) : ℂ)
        + ∑ α ∈ h.harmonics.erase 0, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * modeVel α W z.1 z.2 j := by
    intro τ φ j
    rw [rot_frame_weak, Complex.ofReal_add,
      velW_expansion_of_continuous hWc hWp (h.harmonics.erase 0) hs hh z.1 τ φ z.2 j]
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
  obtain ⟨c', h1, h2, h3⟩ := compression_vec h (m.epsP β).modes (piece_disjoint_weak hm hv β) hA.harmonics_neg h0
    (fun j => (((meanField W z.2 + (1 / 2 : ℝ) • z.2 - (m.epsP β).frame • axialPerp z.2) j : ℝ) : ℂ))
    (fun α => modeVel α W z.1 z.2) (frameSpeedSup W (m.epsP β).frame z.2) hS0 hU hcneg
    (fun ι => vortMode v ι z.1 z.2) (fun ι => modeVel ι (transportRest (m.epsP β).frame W v) z.1 z.2)
    (fun κ => curlGradOfSecondDeriv (modeSecondDeriv κ (secondDerivField v) z.1 z.2)) hf
    (ind_summable_weak _ _ s1) (ind_summable_weak _ _ s2) ((m.epsP β).wt z.2) (hA.eps_wt_nonneg β z.2)
  exact ⟨c', h1, h2, h3⟩

theorem vortStretch_compression_of (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure,
      ∃ c : ℤ × ℤ → Fin 3 → ℂ,
        (∀ ι, PieceWeights.inPiece (m.epsP β).modes ι →
          Real.sqrt (cnormSq (modeVel ι (vortStretchRest W v) z.1 z.2 - c ι))
            ≤ edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι) ∧
        Summable (fun ι => (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ) * cdot (vortMode v ι z.1 z.2) (c ι)).re) ∧
        |∑' ι, (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ) * cdot (vortMode v ι z.1 z.2) (c ι)).re| ≤ (m.epsP β).wt z.2 * vortSup W z.2
            * pieceNorm (m.epsP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 1
  have hWs := hW.smooth
  have hWp := hW.periodic
  have hA := hm
  have hD0 : 0 ≤ D := by
    have h0 := (hW.decay 0 0).1
    rw [norm_zero, add_zero, div_one] at h0
    exact le_trans (norm_nonneg _) h0
  have hB : ∀ s x, ‖fderiv ℝ (W s) x‖ ≤ D := fun s x =>
    (hW.decay s x).2.1.trans (div_le_self hD0 (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg x))))
  have h0 : (0 : ℤ × ℤ) ∈ h.harmonics := hA.harmonics_zero
  have hs : ∀ α ∈ h.harmonics.erase 0, -α ∈ h.harmonics.erase 0 := fun α hα =>
    Finset.mem_erase.mpr ⟨neg_ne_zero.mpr (Finset.ne_of_mem_erase hα),
      hA.harmonics_neg α (Finset.mem_of_mem_erase hα)⟩
  have hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ h.harmonics.erase 0, (modeVel α W σ y i).re := by
    intro σ y i
    rw [hA.harmonics_span σ y i]
    exact (Finset.add_sum_erase h.harmonics (fun α => (modeVel α W σ y i).re) h0).symm
  filter_upwards [summable_ae_weak hPars hSP hm hv] with z hsum
  obtain ⟨s1, _, s3⟩ := hsum
  have hUexp := fun τ φ j => Internal.OnceExpansion.vortW_expansion_once hWs hB hWp (h.harmonics.erase 0) hs hh
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
  obtain ⟨c', h1, h2, h3⟩ := compression_vec h (m.epsP β).modes (piece_disjoint_weak hm hv β) hA.harmonics_neg h0
    (fun j => ((curlVec (fderiv ℝ (meanField W) z.2) j : ℝ) : ℂ))
    (fun α => curlOfGrad (modeGrad α (gradField W) z.1 z.2)) (vortSup W z.2) hS0 hU hcneg
    (fun ι => vortMode v ι z.1 z.2) (fun ι => modeVel ι (vortStretchRest W v) z.1 z.2)
    (fun κ => modeGrad κ (gradField v) z.1 z.2) hf
    (ind_summable_weak _ _ s1) (ind_summable_weak _ _ s3) ((m.epsP β).wt z.2) (hA.eps_wt_nonneg β z.2)
  exact ⟨c', h1, h2, h3⟩

end Bound

end Internal.ExtendedPieceEpsTransport

end CoerciveWeak

end Breakdown
