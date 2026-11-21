import Breakdown.Uniqueness.RegLocalAuxCurvePart3
import Breakdown.Uniqueness.RegUniqueAux2
import Breakdown.Uniqueness.RegPersistAux

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem measurable_divFreeC_pair : Measurable (fun q : Space × CSpace => divFreeC q.1 q.2) := by
  have hf : Measurable (fun q : Space × CSpace => freqVec q.1) :=
    complexifyVec.continuous.measurable.comp measurable_fst
  have hs : Measurable (fun q : Space × CSpace => ∑ i, ((q.1 i : ℝ) : ℂ) * q.2 i) := by
    have : Continuous (fun q : Space × CSpace => ∑ i, ((q.1 i : ℝ) : ℂ) * q.2 i) := by fun_prop
    exact this.measurable
  have hi : Measurable (fun q : Space × CSpace => ((((‖q.1‖ ^ 2)⁻¹ : ℝ)) : ℂ)) :=
    Complex.measurable_ofReal.comp ((measurable_norm.comp measurable_fst).pow_const 2).inv
  have he : (fun q : Space × CSpace => divFreeC q.1 q.2) = fun q =>
      q.2 - ((((‖q.1‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ((q.1 i : ℝ) : ℂ) * q.2 i) • freqVec q.1 := rfl
  rw [he]
  exact measurable_snd.sub ((hi.mul hs).smul hf)

theorem nonlinSymbol_aestronglyMeasurable_curve {m : ℕ} (hm : 1 ≤ m) {G : ℝ → Space → CSpace} {a b : ℝ}
    (hG : IsHsCurve m G a b) :
    AEStronglyMeasurable (fun p : Space × ℝ => nonlinSymbol (G p.2) p.1)
      ((volume : Measure Space).prod (volume.restrict (Icc a b))) := by
  have hμ : (volume : Measure Space).prod (volume.restrict (Icc a b)) =
      ((volume : Measure Space).prod (volume : Measure ℝ)).restrict (univ ×ˢ Icc a b) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hA : AEStronglyMeasurable (fun p : Space × ℝ => advectionBilin (G p.2) (G p.2) p.1)
      ((volume : Measure Space).prod (volume.restrict (Icc a b))) := by
    rw [hμ]
    exact (continuousOn_advectionBilin_curve hm hG).aestronglyMeasurable
      (MeasurableSet.univ.prod measurableSet_Icc)
  have hP : AEMeasurable (fun p : Space × ℝ => (p.1, advectionBilin (G p.2) (G p.2) p.1))
      ((volume : Measure Space).prod (volume.restrict (Icc a b))) :=
    measurable_fst.aemeasurable.prodMk hA.aemeasurable
  have hL := (measurable_divFreeC_pair.comp_aemeasurable hP).neg
  exact hL.aestronglyMeasurable

private theorem hsNormSq_mono {m n : ℕ} (h : m ≤ n) (f : Space → CSpace) :
    hsNormSq m f ≤ hsNormSq n f := by
  unfold hsNormSq
  refine lintegral_mono fun ξ => ?_
  gcongr
  unfold hsWeight
  exact pow_le_pow_right₀ (by nlinarith [norm_nonneg ξ]) h

private theorem hsNormSq_nonlinSymbol_le_four (k : ℕ) (f : Space → CSpace) :
    hsNormSq k (nonlinSymbol f) ≤ 4 * hsNormSq k (advectionBilin f f) := by
  unfold hsNormSq
  rw [← lintegral_const_mul' _ _ (by norm_num)]
  refine lintegral_mono fun ξ => ?_
  have h1 : ‖nonlinSymbol f ξ‖ₑ ≤ 2 * ‖advectionBilin f f ξ‖ₑ := by
    simp only [nonlinSymbol, advectionSymbol, enorm_neg]
    rw [← ofReal_norm, ← ofReal_norm]
    calc ENNReal.ofReal ‖divFreeC ξ (advectionBilin f f ξ)‖
        ≤ ENNReal.ofReal (2 * ‖advectionBilin f f ξ‖) := ENNReal.ofReal_le_ofReal (norm_divFreeC_le ξ _)
      _ = 2 * ENNReal.ofReal ‖advectionBilin f f ξ‖ := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  have h2 : ‖nonlinSymbol f ξ‖ₑ ^ 2 ≤ 4 * ‖advectionBilin f f ξ‖ₑ ^ 2 := by
    calc ‖nonlinSymbol f ξ‖ₑ ^ 2 ≤ (2 * ‖advectionBilin f f ξ‖ₑ) ^ 2 := by gcongr
      _ = 4 * ‖advectionBilin f f ξ‖ₑ ^ 2 := by rw [mul_pow]; norm_num
  calc ENNReal.ofReal (hsWeight k ξ) * ‖nonlinSymbol f ξ‖ₑ ^ 2
      ≤ ENNReal.ofReal (hsWeight k ξ) * (4 * ‖advectionBilin f f ξ‖ₑ ^ 2) := by gcongr
    _ = 4 * (ENNReal.ofReal (hsWeight k ξ) * ‖advectionBilin f f ξ‖ₑ ^ 2) := by ring

theorem hsNormSq_nonlinSymbol_curve_le {k : ℕ} (hk : 2 ≤ k) {G : ℝ → Space → CSpace} {a b : ℝ}
    (hG : IsHsCurve (k + 1) G a b) :
    ∃ K : ℝ, ∀ s ∈ Icc a b, hsNormSq k (nonlinSymbol (G s)) ≤ ENNReal.ofReal K := by
  obtain ⟨B, hB⟩ := hsNormSq_bdd_of_curve hG
  obtain ⟨C, hC⟩ := hsNormSq_advectionBilin_le k
  obtain ⟨C₁, hC₁⟩ := freqL1Norm_le_hsNormSq
  obtain ⟨C₂, hC₂⟩ := weightedFreqL1_le 1
  set R : ℝ≥0∞ := ENNReal.ofReal B ^ (1 / 2 : ℝ) with hR
  set E : ℝ≥0∞ := 4 * (ENNReal.ofReal C * ((ENNReal.ofReal C₁ * R) ^ 2 * ENNReal.ofReal B +
    ENNReal.ofReal B * (ENNReal.ofReal C₂ * R) ^ 2)) with hE
  have hRt : R ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hEt : E ≠ ⊤ := by
    rw [hE]
    apply ENNReal.mul_ne_top (by norm_num)
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ENNReal.add_ne_top.2
    constructor
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRt))
        ENNReal.ofReal_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRt))
  refine ⟨E.toReal, fun s hs => ?_⟩
  rw [ENNReal.ofReal_toReal hEt]
  have hmeas := (hG.1 s hs).1
  have hb : hsNormSq (k + 1) (G s) ≤ ENNReal.ofReal B := hB s hs
  have hW : freqL1Norm (G s) ≤ ENNReal.ofReal C₁ * R := by
    refine (hC₁ (G s)).trans ?_
    gcongr
    rw [hR]
    exact ENNReal.rpow_le_rpow ((hsNormSq_mono (m := 2) (n := k + 1) (by omega) _).trans hb) (by norm_num)
  have hGW : gradFreqL1Norm (G s) ≤ ENNReal.ofReal C₂ * R := by
    refine (gradFreqL1Norm_le_weighted (G s)).trans ((hC₂ (G s)).trans ?_)
    gcongr
    rw [hR]
    exact ENNReal.rpow_le_rpow ((hsNormSq_mono (m := 1 + 2) (n := k + 1) (by omega) _).trans hb) (by norm_num)
  have hk' : hsNormSq k (G s) ≤ ENNReal.ofReal B := (hsNormSq_mono (by omega) _).trans hb
  refine (hsNormSq_nonlinSymbol_le_four k (G s)).trans ?_
  rw [hE]
  gcongr
  refine (hC (G s) (G s) hmeas hmeas).trans ?_
  gcongr

end Breakdown.SmoothFlow
