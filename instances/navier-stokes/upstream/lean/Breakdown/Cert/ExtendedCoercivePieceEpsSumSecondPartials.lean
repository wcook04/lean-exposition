import Breakdown.Cert.CoerciveSmoothPieceEpsCore
import Breakdown.Cert.ExtendedCoerciveStatement

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.ExtendedPieceEpsSumSecondPartials

open Coercive Internal.SmoothPieceEpsCore Internal.PieceAbsorb

section Parts

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {w : Space → ℝ}
  {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
  {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}

theorem weakPairingExchange (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hv : IsSmoothPerturbation P v) (β : Fin nE) {F : ℝ → Space → Space}
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => gradField F z.1 z.2) volume)
    (hFp : IsTimePeriodic (gradField F))
    (hF2 : periodLIntegral (fun σ y => matSq (gradField F σ y)) < ⊤) :
    (∀ᵐ z ∂slabMeasure, Summable (fun ι : ℤ × ℤ =>
        pieceTerm (m.epsP β).modes (m.epsP β).wt v F ι z.1 z.2)) ∧
      Integrable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ,
        pieceTerm (m.epsP β).modes (m.epsP β).wt v F ι z.1 z.2) slabMeasure ∧
      epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v F
        = ∫ z, (∑' ι : ℤ × ℤ,
          pieceTerm (m.epsP β).modes (m.epsP β).wt v F ι z.1 z.2) ∂slabMeasure := by
  have hp := hSP P v hv
  obtain ⟨K, hK⟩ := hm.eps_increment β
  have hwc : Continuous (m.epsP β).wt := hK.continuous
  have hwt0 : ∀ y, 0 ≤ (m.epsP β).wt y := hm.eps_wt_nonneg β
  have hwtB : ∀ y, (m.epsP β).wt y ≤ epsSup := fun y =>
    le_trans (Finset.single_le_sum (f := fun b => (m.epsP b).wt y) (fun b _ => hm.eps_wt_nonneg b y)
      (Finset.mem_univ β)) (hm.eps_sum_le y)
  set T := (m.epsP β).modes
  set wt := (m.epsP β).wt
  have hc : ∀ ι y, |PieceWeights.sgn T ι * wt y| ≤ epsSup := fun ι y => by
    rw [abs_mul, abs_of_nonneg (hwt0 y)]
    exact le_trans (mul_le_of_le_one_left (hwt0 y) (abs_sgn_le T ι)) (hwtB y)
  have hA := Internal.FieldModes.integrable_cnormSq_modeGrad hPars hp.measurable_gradient
    hp.periodic_gradient hp.gradient_finite
  have hB := Internal.FieldModes.integrable_cnormSq_modeGrad hPars hFm hFp hF2
  have sA := Internal.FieldModes.summable_integral_cnormSq_modeGrad hPars hp.measurable_gradient
    hp.periodic_gradient hp.gradient_finite
  have sB := Internal.FieldModes.summable_integral_cnormSq_modeGrad hPars hFm hFp hF2
  have hfm : ∀ ι, AEStronglyMeasurable (fun z : ℝ × Space => pieceTerm T wt v F ι z.1 z.2) slabMeasure := by
    intro ι
    have hΦ : Continuous (fun q : Space × (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ) =>
        (Complex.I * ((PieceWeights.sgn T ι * wt q.1 : ℝ) : ℂ) * cdot (curlOfGrad q.2.1) (curlOfGrad q.2.2)).re) := by
      unfold cdot curlOfGrad
      fun_prop
    have hq : AEMeasurable (fun z : ℝ × Space =>
        (z.2, modeGrad ι (gradField v) z.1 z.2, modeGrad ι (gradField F) z.1 z.2)) slabMeasure :=
      measurable_snd.aemeasurable.prodMk ((Internal.FieldModes.aemeasurable_modeGrad hp.measurable_gradient ι).prodMk
        (Internal.FieldModes.aemeasurable_modeGrad hFm ι))
    exact (hΦ.measurable.comp_aemeasurable hq).aestronglyMeasurable
  have hbound : ∀ (ι : ℤ × ℤ) (z : ℝ × Space), |pieceTerm T wt v F ι z.1 z.2| ≤ epsSup *
      (cnormSq (modeGrad ι (gradField v) z.1 z.2) + cnormSq (modeGrad ι (gradField F) z.1 z.2)) := fun ι z =>
    (Internal.FieldModes.abs_curlTerm_le _ _ _).trans (mul_le_mul_of_nonneg_right (hc ι z.2)
      (add_nonneg (Internal.FieldModes.cnormSq_nonneg _) (Internal.FieldModes.cnormSq_nonneg _)))
  have hfi : ∀ ι, Integrable (fun z : ℝ × Space => pieceTerm T wt v F ι z.1 z.2) slabMeasure := fun ι =>
    Integrable.mono' (((hA ι).add (hB ι)).const_mul epsSup) (hfm ι)
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hbound ι z)
  have hbd : ∀ ι, ∫⁻ z, ENNReal.ofReal |pieceTerm T wt v F ι z.1 z.2| ∂slabMeasure ≤
      ENNReal.ofReal (epsSup * ((∫ z, cnormSq (modeGrad ι (gradField v) z.1 z.2) ∂slabMeasure)
        + ∫ z, cnormSq (modeGrad ι (gradField F) z.1 z.2) ∂slabMeasure)) := by
    intro ι
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi ι).abs (ae_of_all _ fun _ => abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (∫ z, |pieceTerm T wt v F ι z.1 z.2| ∂slabMeasure)
        ≤ ∫ z, epsSup * (cnormSq (modeGrad ι (gradField v) z.1 z.2)
          + cnormSq (modeGrad ι (gradField F) z.1 z.2)) ∂slabMeasure :=
          integral_mono (hfi ι).abs (((hA ι).add (hB ι)).const_mul _) (fun z => hbound ι z)
      _ = _ := by rw [integral_const_mul, integral_add (hA ι) (hB ι)]
  have hs : Summable (fun ι : ℤ × ℤ => epsSup * ((∫ z, cnormSq (modeGrad ι (gradField v) z.1 z.2) ∂slabMeasure)
        + ∫ z, cnormSq (modeGrad ι (gradField F) z.1 z.2) ∂slabMeasure)) := (sA.add sB).mul_left epsSup
  have hs0 : ∀ ι : ℤ × ℤ, 0 ≤ epsSup * ((∫ z, cnormSq (modeGrad ι (gradField v) z.1 z.2) ∂slabMeasure)
        + ∫ z, cnormSq (modeGrad ι (gradField F) z.1 z.2) ∂slabMeasure) := fun ι =>
    mul_nonneg (le_trans (hwt0 0) (hwtB 0)) (add_nonneg
      (integral_nonneg fun _ => Internal.FieldModes.cnormSq_nonneg _)
      (integral_nonneg fun _ => Internal.FieldModes.cnormSq_nonneg _))
  have hfin : ∑' ι, ∫⁻ z, ENNReal.ofReal |pieceTerm T wt v F ι z.1 z.2| ∂slabMeasure ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbd)
    rw [← ENNReal.ofReal_tsum_of_nonneg hs0 hs]
    exact ENNReal.ofReal_ne_top
  obtain ⟨h1, h2, h3⟩ := exchange_of_bound (f := fun ι z => pieceTerm T wt v F ι z.1 z.2) hfm hfin
  refine ⟨h1, h2, ?_⟩
  rw [epsPairing_eq_tsum, ← h3]
  exact tsum_congr fun ι => (integral_prod _ (hfi ι)).symm


theorem weakGradPartIntegrable (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    Integrable (fun z : ℝ × Space => gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2) slabMeasure := by
  have hp := hSP P v hv
  obtain ⟨K, hK⟩ := hm.eps_increment β
  have hG := hp.measurable_gradient
  have hH := hp.measurable_secondDeriv
  have hgm : AEMeasurable (fun z : ℝ × Space => PieceWeights.wtGrad (m.epsP β).wt z.2) volume :=
    ((measurable_fderiv ℝ (m.epsP β).wt).norm.comp measurable_snd).aemeasurable
  have n1 := aem_pieceNorm (m.epsP β).modes (g := fun z κ => vortGradAmp (secondDerivField v) κ z.1 z.2)
    (fun κ => aem_vortGradAmp hH κ)
  have n2 := aem_pieceNorm (m.epsP β).modes (g := fun z κ => vortAmp (gradField v) κ z.1 z.2)
    (fun κ => aem_vortAmp hG κ)
  have hmeas : AEStronglyMeasurable (fun z : ℝ × Space => gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2)
      slabMeasure := by
    rw [slabMeasure_eq]
    unfold gradPart
    exact ((hgm.mul n1).mul n2).aestronglyMeasurable.restrict
  have hpn : ∀ (g : ℤ × ℤ → ℝ), ENNReal.ofReal (pieceNorm (m.epsP β).modes g ^ 2)
      ≤ ∑' κ, ENNReal.ofReal (g κ ^ 2) := by
    intro g
    have h0 : ∀ κ, 0 ≤ ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes κ) * g κ ^ 2 := fun κ =>
      mul_nonneg (by unfold ModeWeights.ind; split_ifs <;> norm_num) (sq_nonneg _)
    have hle : ∀ κ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes κ) * g κ ^ 2)
        ≤ ENNReal.ofReal (g κ ^ 2) := fun κ => by
      refine ENNReal.ofReal_le_ofReal ?_
      have : ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes κ) ≤ 1 := by
        unfold ModeWeights.ind; split_ifs <;> norm_num
      nlinarith [sq_nonneg (g κ)]
    unfold pieceNorm
    rw [Real.sq_sqrt (tsum_nonneg h0)]
    by_cases hs : Summable (fun κ => ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes κ) * g κ ^ 2)
    · rw [ENNReal.ofReal_tsum_of_nonneg h0 hs]
      exact ENNReal.tsum_le_tsum hle
    · rw [tsum_eq_zero_of_not_summable hs, ENNReal.ofReal_zero]
      exact zero_le
  have hwg : ∀ y, PieceWeights.wtGrad (m.epsP β).wt y ≤ K := fun y => norm_fderiv_le_of_lipschitz ℝ hK
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hpt : ∀ z : ℝ × Space, ‖gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2‖ₑ ≤
      ENNReal.ofReal (K / 2) * ((∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι z.1 z.2 ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι z.1 z.2 ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2))) := by
    intro z
    set p1 := pieceNorm (m.epsP β).modes (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2)
    set p2 := pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2)
    have hp1 : 0 ≤ p1 := Real.sqrt_nonneg _
    have hp2 : 0 ≤ p2 := Real.sqrt_nonneg _
    have hw0 : 0 ≤ PieceWeights.wtGrad (m.epsP β).wt z.2 := norm_nonneg _
    have hgp : 0 ≤ gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2 := by
      unfold gradPart; exact mul_nonneg (mul_nonneg hw0 hp1) hp2
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg hgp]
    have hb : gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2 ≤ K / 2 * p1 ^ 2 + K / 2 * p2 ^ 2 := by
      unfold gradPart
      have h1 : PieceWeights.wtGrad (m.epsP β).wt z.2 * p1 * p2 ≤ K * p1 * p2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hwg z.2) hp1) hp2
      nlinarith [sq_nonneg (p1 - p2), mul_nonneg hK0 (sq_nonneg (p1 - p2))]
    calc ENNReal.ofReal (gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2)
        ≤ ENNReal.ofReal (K / 2 * p1 ^ 2 + K / 2 * p2 ^ 2) := ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal (K / 2) * (ENNReal.ofReal (p2 ^ 2) + ENNReal.ofReal (p1 ^ 2)) := by
        rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left
          (le_trans (add_le_add (hpn _) (hpn _)) (le_trans le_self_add le_self_add)) zero_le
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt (lintegral_prod_le _) ?_)
  exact Internal.SmoothPieceEps.amplitudeSeries_finite hPars hSP P v hv

private theorem abs_sgn_eq_ind (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) :
    |PieceWeights.sgn T ι| = ModeWeights.ind (PieceWeights.inPiece T ι) := by
  unfold PieceWeights.sgn ModeWeights.ind PieceWeights.inPiece
  split_ifs <;> simp_all

private theorem norm_fderiv_const_mul_le (c : ℝ) (f : Space → ℝ) (y : Space) :
    ‖fderiv ℝ (fun x => c * f x) y‖ ≤ |c| * ‖fderiv ℝ f y‖ := by
  by_cases hd : DifferentiableAt ℝ f y
  · rw [fderiv_const_mul hd c, norm_smul, Real.norm_eq_abs]
  · by_cases hc : c = 0
    · subst hc
      simp
    · have hnd : ¬ DifferentiableAt ℝ (fun x => c * f x) y := by
        intro h
        apply hd
        have h2 := h.const_mul c⁻¹
        have e : (fun x => c⁻¹ * (c * f x)) = f := by
          funext x
          rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
        rwa [e] at h2
      rw [fderiv_zero_of_not_differentiableAt hnd, norm_zero]
      positivity

private theorem piece_sum_mul_le (T : Set (ℤ × ℤ)) {c : ℝ} (hc : 0 ≤ c) (x u : ℤ × ℤ → ℝ)
    (hx : ∀ κ, 0 ≤ x κ) (hu : ∀ κ, 0 ≤ u κ) (sx : Summable (fun κ => x κ ^ 2))
    (su : Summable (fun κ => u κ ^ 2)) :
    Summable (fun κ => ModeWeights.ind (PieceWeights.inPiece T κ) * c * x κ * u κ) ∧
      ∑' κ, ModeWeights.ind (PieceWeights.inPiece T κ) * c * x κ * u κ ≤ c * pieceNorm T x * pieceNorm T u := by
  set e : ℤ × ℤ → ℝ := fun κ => ModeWeights.ind (PieceWeights.inPiece T κ) with he
  have e0 : ∀ κ, 0 ≤ e κ := fun κ => by simp only [he]; unfold ModeWeights.ind; split_ifs <;> norm_num
  have e1 : ∀ κ, e κ ≤ 1 := fun κ => by simp only [he]; unfold ModeWeights.ind; split_ifs <;> norm_num
  have ee : ∀ κ, e κ * e κ = e κ := fun κ => by simp only [he]; unfold ModeWeights.ind; split_ifs <;> norm_num
  set X : ℤ × ℤ → ℝ := fun κ => e κ * x κ with hX
  set U : ℤ × ℤ → ℝ := fun κ => e κ * u κ with hU
  have X0 : ∀ κ, 0 ≤ X κ := fun κ => mul_nonneg (e0 κ) (hx κ)
  have U0 : ∀ κ, 0 ≤ U κ := fun κ => mul_nonneg (e0 κ) (hu κ)
  have X2 : ∀ κ, X κ ^ 2 = e κ * x κ ^ 2 := fun κ => by
    simp only [hX]
    rw [mul_pow, sq (e κ), ee]
  have U2 : ∀ κ, U κ ^ 2 = e κ * u κ ^ 2 := fun κ => by
    simp only [hU]
    rw [mul_pow, sq (e κ), ee]
  have sX : Summable (fun κ => X κ ^ 2) :=
    sx.of_nonneg_of_le (fun κ => sq_nonneg _) fun κ => by
      rw [X2]; exact mul_le_of_le_one_left (sq_nonneg _) (e1 κ)
  have sU : Summable (fun κ => U κ ^ 2) :=
    su.of_nonneg_of_le (fun κ => sq_nonneg _) fun κ => by
      rw [U2]; exact mul_le_of_le_one_left (sq_nonneg _) (e1 κ)
  have sXU : Summable (fun κ => X κ * U κ) :=
    ((sX.add sU).div_const 2).of_nonneg_of_le (fun κ => mul_nonneg (X0 κ) (U0 κ)) fun κ => by
      nlinarith [sq_nonneg (X κ - U κ)]
  have term : ∀ κ, e κ * c * x κ * u κ = c * (X κ * U κ) := fun κ => by
    simp only [hX, hU]
    have := ee κ
    calc e κ * c * x κ * u κ = c * ((e κ * e κ) * x κ * u κ) := by rw [this]; ring
      _ = c * (e κ * x κ * (e κ * u κ)) := by ring
  have hs : Summable (fun κ => e κ * c * x κ * u κ) := by
    simp_rw [term]
    exact sXU.mul_left c
  refine ⟨hs, ?_⟩
  have hle : ∑' κ, X κ * U κ ≤ Real.sqrt (∑' κ, X κ ^ 2) * Real.sqrt (∑' κ, U κ ^ 2) :=
    sXU.tsum_le_of_sum_le fun s => (Real.sum_mul_le_sqrt_mul_sqrt s X U).trans
      (mul_le_mul (Real.sqrt_le_sqrt (sX.sum_le_tsum s fun κ _ => sq_nonneg _))
        (Real.sqrt_le_sqrt (sU.sum_le_tsum s fun κ _ => sq_nonneg _)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have pX : pieceNorm T x = Real.sqrt (∑' κ, X κ ^ 2) := by
    unfold pieceNorm
    congr 1
    exact tsum_congr fun κ => (X2 κ).symm
  have pU : pieceNorm T u = Real.sqrt (∑' κ, U κ ^ 2) := by
    unfold pieceNorm
    congr 1
    exact tsum_congr fun κ => (U2 κ).symm
  calc ∑' κ, e κ * c * x κ * u κ = ∑' κ, c * (X κ * U κ) := tsum_congr term
    _ = c * ∑' κ, X κ * U κ := tsum_mul_left
    _ ≤ c * (Real.sqrt (∑' κ, X κ ^ 2) * Real.sqrt (∑' κ, U κ ^ 2)) := mul_le_mul_of_nonneg_left hle hc
    _ = c * pieceNorm T x * pieceNorm T u := by rw [pX, pU, mul_assoc]

theorem weakSumSecondPartialsPairingLower (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    0 ≤ (∫ z, gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2 ∂slabMeasure)
      + epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v (negSumSecondPartials v) := by
  have hp := hSP P v hv
  obtain ⟨K, hK⟩ := hm.eps_increment β
  have hwt0 : ∀ y, 0 ≤ (m.epsP β).wt y := hm.eps_wt_nonneg β
  have hwtB : ∀ y, (m.epsP β).wt y ≤ epsSup := fun y =>
    le_trans (Finset.single_le_sum (f := fun b => (m.epsP b).wt y) (fun b _ => hm.eps_wt_nonneg b y)
      (Finset.mem_univ β)) (hm.eps_sum_le y)
  set T := (m.epsP β).modes
  set wt := (m.epsP β).wt
  have hc : ∀ ι y, |PieceWeights.sgn T ι * wt y| ≤ epsSup := fun ι y => by
    rw [abs_mul, abs_of_nonneg (hwt0 y)]
    exact le_trans (mul_le_of_le_one_left (hwt0 y) (abs_sgn_le T ι)) (hwtB y)
  obtain ⟨hFm, hFp, hF2⟩ := negSumSecondPartials_gradient_finite hv
  have hA := Internal.FieldModes.integrable_cnormSq_modeGrad hPars hp.measurable_gradient
    hp.periodic_gradient hp.gradient_finite
  have hB := Internal.FieldModes.integrable_cnormSq_modeGrad hPars hFm hFp hF2
  have sA := Internal.FieldModes.summable_integral_cnormSq_modeGrad hPars hp.measurable_gradient
    hp.periodic_gradient hp.gradient_finite
  have sB := Internal.FieldModes.summable_integral_cnormSq_modeGrad hPars hFm hFp hF2
  have hfm : ∀ ι, AEStronglyMeasurable (fun z : ℝ × Space =>
      pieceTerm T wt v (negSumSecondPartials v) ι z.1 z.2) slabMeasure := by
    intro ι
    have hΦ : Continuous (fun q : Space × (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ) =>
        (Complex.I * ((PieceWeights.sgn T ι * wt q.1 : ℝ) : ℂ) * cdot (curlOfGrad q.2.1) (curlOfGrad q.2.2)).re) := by
      have hwc : Continuous wt := hK.continuous
      unfold cdot curlOfGrad
      fun_prop
    have hq : AEMeasurable (fun z : ℝ × Space =>
        (z.2, modeGrad ι (gradField v) z.1 z.2, modeGrad ι (gradField (negSumSecondPartials v)) z.1 z.2)) slabMeasure :=
      measurable_snd.aemeasurable.prodMk ((Internal.FieldModes.aemeasurable_modeGrad hp.measurable_gradient ι).prodMk
        (Internal.FieldModes.aemeasurable_modeGrad hFm ι))
    exact (hΦ.measurable.comp_aemeasurable hq).aestronglyMeasurable
  have hbound : ∀ (ι : ℤ × ℤ) (z : ℝ × Space), |pieceTerm T wt v (negSumSecondPartials v) ι z.1 z.2| ≤ epsSup *
      (cnormSq (modeGrad ι (gradField v) z.1 z.2) + cnormSq (modeGrad ι (gradField (negSumSecondPartials v)) z.1 z.2)) :=
    fun ι z => (Internal.FieldModes.abs_curlTerm_le _ _ _).trans (mul_le_mul_of_nonneg_right (hc ι z.2)
      (add_nonneg (Internal.FieldModes.cnormSq_nonneg _) (Internal.FieldModes.cnormSq_nonneg _)))
  have hfi : ∀ ι, Integrable (fun z : ℝ × Space => pieceTerm T wt v (negSumSecondPartials v) ι z.1 z.2) slabMeasure :=
    fun ι => Integrable.mono' (((hA ι).add (hB ι)).const_mul epsSup) (hfm ι)
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hbound ι z)
  have sF : Summable (fun ι => ∫ z, pieceTerm T wt v (negSumSecondPartials v) ι z.1 z.2 ∂slabMeasure) := by
    refine Summable.of_norm_bounded ((sA.add sB).mul_left epsSup) fun ι => ?_
    refine (norm_integral_le_of_norm_le (((hA ι).add (hB ι)).const_mul epsSup)
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hbound ι z)).trans (le_of_eq ?_)
    rw [integral_const_mul]
    congr 1
    exact integral_add (hA ι) (hB ι)
  set g : ℤ × ℤ → ℝ × Space → ℝ := fun ι z =>
    ‖fderiv ℝ (fun y => PieceWeights.sgn T ι * wt y) z.2‖ * vortGradAmp (secondDerivField v) ι z.1 z.2
      * vortAmp (gradField v) ι z.1 z.2 with hgdef
  have hg0 : ∀ ι z, 0 ≤ g ι z := fun ι z => by
    simp only [hgdef]
    unfold vortGradAmp vortAmp
    positivity
  have hgm : ∀ ι, AEStronglyMeasurable (g ι) slabMeasure := by
    intro ι
    rw [slabMeasure_eq]
    exact ((((measurable_fderiv ℝ (fun y => PieceWeights.sgn T ι * wt y)).norm.comp measurable_snd).aemeasurable.mul
      (aem_vortGradAmp hp.measurable_secondDeriv ι)).mul (aem_vortAmp hp.measurable_gradient ι)).aestronglyMeasurable.restrict
  have hAm : AEMeasurable (fun z : ℝ × Space =>
      ∑' κ : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) κ z.1 z.2 ^ 2)) slabMeasure :=
    Internal.SmoothPieceEps.slab_aem (AEMeasurable.ennreal_tsum fun κ =>
      ((aem_vortAmp hp.measurable_gradient κ).pow_const 2).ennreal_ofReal)
  have hBm : AEMeasurable (fun z : ℝ × Space =>
      ∑' κ : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) κ z.1 z.2 ^ 2)) slabMeasure :=
    Internal.SmoothPieceEps.slab_aem (AEMeasurable.ennreal_tsum fun κ =>
      ((aem_vortGradAmp hp.measurable_secondDeriv κ).pow_const 2).ennreal_ofReal)
  have hAfin : ∫⁻ z, ∑' κ : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) κ z.1 z.2 ^ 2) ∂slabMeasure < ⊤ := by
    refine lt_of_le_of_lt (lintegral_prod_le _) (lt_of_le_of_lt
      (lintegral_mono fun σ => lintegral_mono fun y => ?_)
      (Internal.SmoothPieceEps.amplitudeSeries_finite hPars hSP P v hv))
    exact le_trans (le_trans le_self_add le_self_add) le_self_add
  have hBfin : ∫⁻ z, ∑' κ : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) κ z.1 z.2 ^ 2) ∂slabMeasure < ⊤ := by
    refine lt_of_le_of_lt (lintegral_prod_le _) (lt_of_le_of_lt
      (lintegral_mono fun σ => lintegral_mono fun y => ?_)
      (Internal.SmoothPieceEps.amplitudeSeries_finite hPars hSP P v hv))
    exact le_trans (le_trans le_add_self le_self_add) le_self_add
  have hCst : ∀ᵐ z ∂slabMeasure, Summable (fun ι => g ι z) ∧
      ∑' ι, g ι z ≤ gradPart T wt v z.1 z.2 := by
    filter_upwards [ae_lt_top' hAm hAfin.ne, ae_lt_top' hBm hBfin.ne] with z hzA hzB
    have sA2 : Summable (fun κ => vortAmp (gradField v) κ z.1 z.2 ^ 2) := by
      have := ENNReal.summable_toReal hzA.ne
      simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using this
    have sB2 : Summable (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2 ^ 2) := by
      have := ENNReal.summable_toReal hzB.ne
      simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using this
    obtain ⟨hs, hle⟩ := piece_sum_mul_le T (norm_nonneg (fderiv ℝ wt z.2))
      (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2) (fun κ => vortAmp (gradField v) κ z.1 z.2)
      (fun κ => Real.sqrt_nonneg _) (fun κ => Real.sqrt_nonneg _) sB2 sA2
    have hgle : ∀ ι, g ι z ≤ ModeWeights.ind (PieceWeights.inPiece T ι) * ‖fderiv ℝ wt z.2‖
        * vortGradAmp (secondDerivField v) ι z.1 z.2 * vortAmp (gradField v) ι z.1 z.2 := by
      intro ι
      have h1 := norm_fderiv_const_mul_le (PieceWeights.sgn T ι) wt z.2
      rw [abs_sgn_eq_ind] at h1
      simp only [hgdef]
      have hv1 : 0 ≤ vortGradAmp (secondDerivField v) ι z.1 z.2 := Real.sqrt_nonneg _
      have hv2 : 0 ≤ vortAmp (gradField v) ι z.1 z.2 := Real.sqrt_nonneg _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hv1) hv2
    have sg : Summable (fun ι => g ι z) := hs.of_nonneg_of_le (fun ι => hg0 ι z) hgle
    exact ⟨sg, (sg.tsum_le_tsum hgle hs).trans hle⟩
  have hGP := weakGradPartIntegrable hPars hDer hSP hm hv β
  have hgi : ∀ ι, Integrable (g ι) slabMeasure := fun ι =>
    hGP.mono' (hgm ι) (by
      filter_upwards [hCst] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 ι z)]
      exact (hz.1.le_tsum ι fun j _ => hg0 j z).trans hz.2)
  have hfinG : ∑' ι, ∫⁻ z, ENNReal.ofReal |g ι z| ∂slabMeasure ≠ ⊤ := by
    rw [← lintegral_tsum fun ι => (hgm ι).aemeasurable.abs.ennreal_ofReal]
    refine ne_top_of_le_ne_top hGP.lintegral_lt_top.ne (lintegral_mono_ae ?_)
    filter_upwards [hCst] with z hz
    simp_rw [abs_of_nonneg (hg0 _ z)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun ι => hg0 ι z) hz.1]
    exact ENNReal.ofReal_le_ofReal hz.2
  obtain ⟨-, hGi, hGeq⟩ := exchange_of_bound hgm hfinG
  have sG : Summable (fun ι => ∫ z, g ι z ∂slabMeasure) := by
    have e : ∀ ι, ∫ z, g ι z ∂slabMeasure = (∫⁻ z, ENNReal.ofReal |g ι z| ∂slabMeasure).toReal := by
      intro ι
      simp_rw [abs_of_nonneg (hg0 ι _)]
      exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hg0 ι)) (hgm ι)
    simp_rw [e]
    exact ENNReal.summable_toReal hfinG
  have hper : ∀ ι, -(∫ z, g ι z ∂slabMeasure)
      ≤ ∫ z, pieceTerm T wt v (negSumSecondPartials v) ι z.1 z.2 ∂slabMeasure := by
    intro ι
    have hincr : LipschitzWith (‖PieceWeights.sgn T ι‖₊ * K) (fun y => PieceWeights.sgn T ι * wt y) :=
      (lipschitzWith_smul (PieceWeights.sgn T ι)).comp hK
    have hgB : ∀ y, ‖fderiv ℝ (fun y => PieceWeights.sgn T ι * wt y) y‖ ≤ (K : ℝ) := fun y =>
      (norm_fderiv_const_mul_le _ _ y).trans (le_trans (mul_le_mul (abs_sgn_le T ι)
        (norm_fderiv_le_of_lipschitz ℝ hK) (norm_nonneg _) zero_le_one) (le_of_eq (one_mul _)))
    rw [integral_prod _ (hgi ι), integral_prod _ (hfi ι), ← integral_neg]
    refine integral_mono (hgi ι).integral_prod_left.neg (hfi ι).integral_prod_left fun σ => ?_
    exact Internal.SmoothEpsSumSecondPartials.mode_lower hSsp hv hincr (hc ι) hgB ι σ
  have e2 : ∀ ι, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, pieceTerm T wt v (negSumSecondPartials v) ι σ y
      = ∫ z, pieceTerm T wt v (negSumSecondPartials v) ι z.1 z.2 ∂slabMeasure := fun ι => (integral_prod _ (hfi ι)).symm
  rw [epsPairing_eq_tsum, tsum_congr e2]
  have h1 : ∑' ι, -(∫ z, g ι z ∂slabMeasure)
      ≤ ∑' ι, ∫ z, pieceTerm T wt v (negSumSecondPartials v) ι z.1 z.2 ∂slabMeasure := sG.neg.tsum_le_tsum hper sF
  rw [tsum_neg, hGeq] at h1
  have h2 : ∫ z, ∑' ι, g ι z ∂slabMeasure ≤ ∫ z, gradPart T wt v z.1 z.2 ∂slabMeasure :=
    integral_mono_ae hGi hGP (hCst.mono fun z hz => hz.2)
  linarith

theorem weakSumSecondPartialsLower (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    (∀ᵐ z ∂slabMeasure, Summable (fun ι : ℤ × ℤ =>
        pieceTerm (m.epsP β).modes (m.epsP β).wt v (negSumSecondPartials v) ι z.1 z.2)) ∧
      Integrable (fun z : ℝ × Space => gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2
        + ∑' ι : ℤ × ℤ, pieceTerm (m.epsP β).modes (m.epsP β).wt v (negSumSecondPartials v) ι z.1 z.2) slabMeasure ∧
      0 ≤ ∫ z, (gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2
        + ∑' ι : ℤ × ℤ, pieceTerm (m.epsP β).modes (m.epsP β).wt v (negSumSecondPartials v) ι z.1 z.2) ∂slabMeasure := by
  obtain ⟨hFm, hFp, hF2⟩ := negSumSecondPartials_gradient_finite hv
  obtain ⟨h1, h2, h3⟩ := weakPairingExchange hPars hSP hm hv β hFm hFp hF2
  have hg := weakGradPartIntegrable hPars hDer hSP hm hv β
  have hl := weakSumSecondPartialsPairingLower hPars hDer hSP hSsp hm hv β
  refine ⟨h1, hg.add h2, ?_⟩
  rw [integral_add hg h2, ← h3]
  exact hl


end Parts

end Internal.ExtendedPieceEpsSumSecondPartials

end CoerciveWeak

end Breakdown
