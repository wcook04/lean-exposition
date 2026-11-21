import Breakdown.FracCert.WeakRegular
import Breakdown.FracCert.HeldWeakProfileParts
import Breakdown.FracCert.GradientOrthogonal
import Breakdown.Cert.Convection

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform SchwartzMap

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

namespace ResidualNiceInternal

theorem entrySq_le (G : Space →L[ℝ] Space) : SteadyCert.entrySq G ≤ 3 * ‖G‖ ^ 2 := by
  have h : ∀ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ‖G‖ ^ 2 := fun i => by
    have h1 : ‖G (unitVector i)‖ ≤ ‖G‖ := by
      have := G.le_opNorm (unitVector i)
      simpa [unitVector, PiLp.norm_single] using this
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  simp only [SteadyCert.entrySq, Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

theorem continuous_gradientAt {P : Space → ℝ} (hP : ContDiff ℝ ∞ P) : Continuous (gradientAt P) := by
  have hD := hP.continuous_fderiv (by simp)
  unfold gradientAt
  exact continuous_finsetSum _ fun i _ => (hD.clm_apply continuous_const).smul continuous_const

theorem isGradientField_of {P : Space → ℝ} (hP : ContDiff ℝ ∞ P) :
    SteadyCert.IsGradientField (gradientAt P) := by
  have hc := continuous_gradientAt hP
  refine ⟨P, fun K hK => ?_, fun K hK => ?_, hc.aestronglyMeasurable, fun φ hφ j => ?_⟩
  · exact (hP.continuous.pow 2).continuousOn.integrableOn_compact hK
  · exact (hc.norm.pow 2).continuousOn.integrableOn_compact hK
  · have h := SteadyCert.HeldWeakProfilePartsInternal.test_ibp hφ (hP.of_le (by simp)) (unitVector j)
    simp only [smul_eq_mul] at h
    rw [h]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only
    rw [real_inner_comm, SteadyCert.HeldWeakProfilePartsInternal.inner_gradient]
    simp [unitVector]

theorem isWeakGradient_of {v : Space → Space} (hv : ContDiff ℝ ∞ v) :
    IsWeakGradient v (fderiv ℝ v) := by
  have hw := WeakRegularInternal.weakGradient_of_smooth hv
  refine ⟨hv.continuous.locallyIntegrable, (hv.continuous_fderiv (by simp)).locallyIntegrable,
    fun φ hφ i => ?_⟩
  rw [hw φ hφ i, neg_neg]

theorem integrable_inner_pair {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun y => inner ℝ (f y) (g y)) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

end ResidualNiceInternal

open WeakRegularInternal ResidualNiceInternal in
theorem residualNice_of (h1 : SymbolL1OfMomentsStatement) (h2 : FieldSmoothOfMomentsStatement)
    (t5 : PressureGradientSquareStatement) : ResidualNiceStatement := by
  intro α hα hα2 a U hW hM φ hφ
  have hφ' := hφ
  obtain ⟨m, hm, rfl⟩ := hφ
  have hwm := (h1 U hM).1
  have hvel := (h1 U hM).2
  obtain ⟨hV, hB⟩ := h2 _ (moments_clean U hwm) (cleanSymbol_conjSym _)
  rw [physField_clean U] at hV hB
  set V := physField (symbolX U) with hVdef
  set P := profilePressure U with hPdef
  have hP : ContDiff ℝ ∞ P := pressureSmooth_of h1 U hM
  have hV6 : MemLp V 6 volume := (Lp.memLp (velocity U)).ae_eq hvel
  have hVm : AEStronglyMeasurable V volume := hV.continuous.aestronglyMeasurable
  have hDc : Continuous (fderiv ℝ V) := hV.continuous_fderiv (by simp)
  have t2 := velocityGradientSquare_of h1 U hM
  have hE : Integrable (fun y => SteadyCert.entrySq (fderiv ℝ V y)) := by
    have hs : Integrable (fun y => ‖fderiv ℝ V y‖ ^ 2) :=
      (memLp_two_iff_integrable_sq t2.aestronglyMeasurable).1 t2
    refine (hs.const_mul 3).mono' ?_ (ae_of_all _ fun y => ?_)
    · unfold SteadyCert.entrySq
      exact (continuous_finsetSum _ fun i _ =>
        ((hDc.clm_apply continuous_const).norm.pow 2)).aestronglyMeasurable
    · have h0 : 0 ≤ SteadyCert.entrySq (fderiv ℝ V y) := by
        unfold SteadyCert.entrySq; positivity
      rw [Real.norm_of_nonneg h0]
      exact entrySq_le _
  obtain ⟨-, eD⟩ := SteadyCert.driftNicePairing α a (by linarith) V (fderiv ℝ V) hVm hV6
    hDc.aestronglyMeasurable hE (weakGradient_of_smooth hV) (niceField m) hφ'
  have hS := FracInternal.NiceField.fieldS_coe hm
  obtain ⟨iA1, -, eA⟩ := symmetryRapid α hα (by linarith) V hV (fun j _ => hB j)
    (FracInternal.NiceField.fieldS hm)
  rw [hS] at iA1 eA
  have hg : ∀ j : Fin 3, (fun y => fderiv ℝ V y (unitVector j)) =ᵐ[volume]
      (partialX j U : Space → Space) := fun j =>
    Cert.Internal.Convection.partialX_ae_of_weakGradient (isWeakGradient_of hV) U hvel.symm j
  have htri : trilinear U U (niceField m) = ∫ y, inner ℝ (advectionAt V y) (niceField m y) := by
    unfold trilinear
    apply integral_congr_ae
    have hg' : ∀ᵐ y ∂volume, ∀ j, fderiv ℝ V y (unitVector j) = (partialX j U : Space → Space) y :=
      ae_all_iff.2 hg
    filter_upwards [hvel, hg'] with y h1y h2y
    simp only [h1y, ← h2y]
    exact Freq.Internal.NicePairing.sum_coord_inner _ _ _
  have hsol := SteadyCert.niceSolenoidal _ hφ'
  have hφ2 := hsol.1
  have e0 : ∫ y, inner ℝ (gradientAt P y) (niceField m y) = 0 :=
    SteadyCert.gradientOrthogonal _ _ (isGradientField_of hP) (t5 U hM) hsol
  have iAd := integrable_inner_pair
    (advectionSquare_of h1 h2 (velocityGradientSquare_of h1) U hM) hφ2
  have iG := integrable_inner_pair (t5 U hM) hφ2
  have hWt := residualWeighted_of h1 h2 (velocityInverseWeight_of h1 h2) (velocityGradientSquare_of h1)
    (powerSquare_of h1) (advectionSquare_of h1 h2 (velocityGradientSquare_of h1)) t5 α hα hα2 a U hM
  have hc := residualContinuous_of h1 h2 α hα hα2 a U hM
  let Mm := hm.2.1.toSchwartzMap hm.1
  have enf : niceField m = fun y => realVec ((𝓕⁻ Mm) y) := physField_of_rapid Mm rfl
  have iT : Integrable (fun y => inner ℝ (profileResidual α a U y) (niceField m y)) := by
    rw [enf]; exact integrable_pairing hc hWt _
  have hsplit : ∀ y, inner ℝ (profileResidual α a U y) (niceField m y) =
      inner ℝ (SteadyCert.driftField α a V (fderiv ℝ V) y) (niceField m y) +
        (inner ℝ (fractionalPowerAt α V y) (niceField m y) +
          inner ℝ (advectionAt V y) (niceField m y) + inner ℝ (gradientAt P y) (niceField m y)) := by
    intro y
    simp only [← inner_add_left]
    congr 1
    simp only [profileResidual, rotatingProfileResidual, SteadyCert.driftField, one_smul, advectionAt]
    abel
  have iR1 : Integrable (fun y => inner ℝ (fractionalPowerAt α V y) (niceField m y) +
      inner ℝ (advectionAt V y) (niceField m y)) := iA1.add iAd
  have iR : Integrable (fun y => inner ℝ (fractionalPowerAt α V y) (niceField m y) +
      inner ℝ (advectionAt V y) (niceField m y) + inner ℝ (gradientAt P y) (niceField m y)) := iR1.add iG
  have iDr : Integrable (fun y => inner ℝ (SteadyCert.driftField α a V (fderiv ℝ V) y) (niceField m y)) :=
    (iT.sub iR).congr (ae_of_all _ fun y => by simp only [Pi.sub_apply, hsplit]; ring)
  have hmain : ∫ y, inner ℝ (profileResidual α a U y) (niceField m y) =
      (∫ y, inner ℝ (V y) (driftAdjoint α a (niceField m) y)) +
        (∫ y, inner ℝ (V y) (fractionalPowerAt α (niceField m) y)) + trilinear U U (niceField m) := by
    simp_rw [hsplit]
    rw [integral_add iDr iR, integral_add iR1 iG, integral_add iA1 iAd, eD, eA, htri, e0]
    ring
  have hw := hW.2 (niceField m) hφ'
  have c1 : ∫ y, inner ℝ ((velocity U : Space → Space) y) (driftAdjoint α a (niceField m) y) =
      ∫ y, inner ℝ (V y) (driftAdjoint α a (niceField m) y) :=
    integral_congr_ae (by filter_upwards [hvel] with y hy; rw [hy])
  have c2 : ∫ y, inner ℝ ((velocity U : Space → Space) y) (fractionalPowerAt α (niceField m) y) =
      ∫ y, inner ℝ (V y) (fractionalPowerAt α (niceField m) y) :=
    integral_congr_ae (by filter_upwards [hvel] with y hy; rw [hy])
  rw [c1, c2] at hw
  rw [hmain, hw]

end Breakdown.FracCert
