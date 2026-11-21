import Breakdown.FracCert.StHeldParts
import Breakdown.FracCert.StFree
import Breakdown.FreqTr.VelocityInjective

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace Internal.SplitFormBounds

theorem trace_sq_le (B : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖secondTrace B‖ ^ 2 ≤ 3 * ∑ i : Fin 3, ∑ j : Fin 3, ‖B (unitVector i) (unitVector j)‖ ^ 2 := by
  have h := norm_sum_le (Finset.univ : Finset (Fin 3)) fun j => B (unitVector j) (unitVector j)
  simp only [secondTrace, Fin.sum_univ_three] at h ⊢
  have h0 := norm_nonneg (B (unitVector 0) (unitVector 0) + B (unitVector 1) (unitVector 1) +
    B (unitVector 2) (unitVector 2))
  have hsq := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (‖B (unitVector 0) (unitVector 0)‖ - ‖B (unitVector 1) (unitVector 1)‖),
    sq_nonneg (‖B (unitVector 1) (unitVector 1)‖ - ‖B (unitVector 2) (unitVector 2)‖),
    sq_nonneg (‖B (unitVector 0) (unitVector 0)‖ - ‖B (unitVector 2) (unitVector 2)‖),
    sq_nonneg ‖B (unitVector 0) (unitVector 1)‖, sq_nonneg ‖B (unitVector 0) (unitVector 2)‖,
    sq_nonneg ‖B (unitVector 1) (unitVector 0)‖, sq_nonneg ‖B (unitVector 1) (unitVector 2)‖,
    sq_nonneg ‖B (unitVector 2) (unitVector 0)‖, sq_nonneg ‖B (unitVector 2) (unitVector 1)‖]

theorem memLp_trace {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    MemLp (negSecondTrace H) 2 volume := by
  have hc : Continuous fun B : Space →L[ℝ] Space →L[ℝ] Space => -secondTrace B := by
    unfold secondTrace
    fun_prop
  have hm : AEStronglyMeasurable (negSecondTrace H) volume :=
    hc.comp_aestronglyMeasurable hs.measurable_second
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine (hs.second_two.const_mul 3).mono' (hm.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa [negSecondTrace, norm_neg] using trace_sq_le (H y)

theorem toLpOrZero_ae {f : Space → Space} (hf : MemLp f 2 volume) :
    (Freq.toLpOrZero 2 f : Space → Space) =ᵐ[volume] f := by
  unfold Freq.toLpOrZero
  rw [dif_pos hf]
  exact hf.coeFn_toLp

theorem integrable_pair {F E : Space → Space} (hF : MemLp F 2 volume) (hE : MemLp E 2 volume) :
    Integrable (fun y => inner ℝ (F y) (E y)) volume := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hF.toLp F) (hE.toLp E)).congr ?_
  filter_upwards [hF.coeFn_toLp, hE.coeFn_toLp] with y a b
  rw [a, b]

theorem pair_symbol {F E : Space → Space} (hF : MemLp F 2 volume) (hE : MemLp E 2 volume) :
    l2Pair F E = ∫ ξ, inner ℝ ((fieldSymbol F : Space → Freq.CSpace) ξ)
      ((fieldSymbol E : Space → Freq.CSpace) ξ) := by
  rw [← L2.inner_def]
  unfold fieldSymbol
  rw [Freq.Internal.VelocityInjective.freqTrR_inner, Freq.Internal.VelocityInjective.complexify_inner,
    L2.inner_def]
  unfold l2Pair
  apply integral_congr_ae
  filter_upwards [toLpOrZero_ae hF, toLpOrZero_ae hE] with y h1 h2
  rw [h1, h2]

theorem ae_ne_zero : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
  have := (Set.countable_singleton (0 : Space)).ae_notMem volume
  filter_upwards [this] with ξ hξ
  simpa using hξ

theorem comb_le {f g h : Space → ℝ} (If : Integrable f) (Ig : Integrable g) (Ih : Integrable h)
    (c₁ c₂ c₃ : ℝ) (hpt : ∀ᵐ ξ ∂volume, c₁ * f ξ + c₂ * g ξ + c₃ * h ξ ≤ 0) :
    c₁ * (∫ ξ, f ξ) + c₂ * (∫ ξ, g ξ) + c₃ * (∫ ξ, h ξ) ≤ 0 := by
  have I12 : Integrable (fun ξ => c₁ * f ξ + c₂ * g ξ) := (If.const_mul c₁).add (Ig.const_mul c₂)
  have I123 : Integrable (fun ξ => c₁ * f ξ + c₂ * g ξ + c₃ * h ξ) := I12.add (Ih.const_mul c₃)
  have hi := integral_mono_ae (g := fun _ => (0 : ℝ)) I123 (integrable_zero Space ℝ volume) hpt
  rw [integral_add I12 (Ih.const_mul c₃), integral_add (If.const_mul c₁) (Ig.const_mul c₂),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_zero] at hi
  exact hi

theorem freqPow_eq {ξ : Space} (α : ℝ) : freqPow (2 * α - 2) ξ = (2 * π * ‖ξ‖) ^ (2 * (α - 1)) := by
  unfold freqPow
  congr 1
  ring

theorem freqPow_two_eq (ξ : Space) : freqPow 2 ξ = (2 * π * ‖ξ‖) ^ 2 := by
  unfold freqPow
  exact Real.rpow_two _

end Internal.SplitFormBounds

open Internal.SplitFormBounds in
theorem splitFormBounds_of (h1 : SecondSymbolEnergyStatement) (h2 : WeakPowerSymbolStatement)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N : ℕ} (d : FracCertData k N) (hd : IsFracCert α d)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (P : Space → Space) (hs : IsSecondOrderField d.order v G H) (hP : IsWeakFractionalPower α v P) :
    -d.lowLoss * ((∫ y, ‖secondTrace (H y)‖ ^ 2) + d.weightMin * ∫ y, entrySq (G y)) ≤
        l2Pair (d.splitField P H) (negSecondTrace H) ∧
      0 ≤ l2Pair (d.splitField P H) (negSecondTrace H) +
        d.reducedCoercivity * ((∫ y, ‖secondTrace (H y)‖ ^ 2) + d.weightMin * ∫ y, entrySq (G y)) ∧
      Real.sqrt (∫ y, ‖secondTrace (H y)‖ ^ 2) ≤ d.formScale * d.splitEnergy P G H := by
  obtain ⟨Iy, eG, -, eX⟩ := h1 d.order v G H hs
  have hsym := h2 α hα1 (by linarith) d.order v G H P hs hP
  have hw := memLp_trace hs
  have In : Integrable (fun ξ => ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2) :=
    (Lp.memLp (secondSymbol H)).integrable_norm_pow two_ne_zero
  have hpt : ∀ᵐ ξ ∂volume, inner ℝ ((fieldSymbol P : Space → Freq.CSpace) ξ)
      ((secondSymbol H : Space → Freq.CSpace) ξ) =
      freqPow (2 * α - 2) ξ * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 := by
    filter_upwards [hsym] with ξ hξ
    rw [hξ, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have IZ : Integrable (fun ξ => freqPow (2 * α - 2) ξ * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2) :=
    (L2.integrable_inner (𝕜 := ℝ) (fieldSymbol P) (secondSymbol H)).congr hpt
  have eZ : l2Pair P (negSecondTrace H) =
      ∫ ξ, freqPow (2 * α - 2) ξ * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 := by
    rw [pair_symbol hP.1 hw]
    exact integral_congr_ae hpt
  have It : Integrable (fun y => ‖secondTrace (H y)‖ ^ 2) := by
    simpa [negSecondTrace, norm_neg] using hw.integrable_norm_pow two_ne_zero
  have eB : l2Pair (d.splitField P H) (negSecondTrace H) =
      l2Pair P (negSecondTrace H) - d.splitVisc * ∫ y, ‖secondTrace (H y)‖ ^ 2 := by
    have Ip := integrable_pair hP.1 hw
    unfold l2Pair
    rw [← integral_const_mul, ← integral_sub Ip (It.const_mul _)]
    congr 1
    ext y
    simp only [FracCertData.splitField, negSecondTrace, inner_add_left, inner_neg_right,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have hA := comb_le In Iy IZ (d.splitVisc - d.lowLoss) (-(d.lowLoss * d.weightMin)) (-1) (by
    filter_upwards [ae_ne_zero] with ξ hξ
    have hκ : 0 < 2 * π * ‖ξ‖ := by have := norm_pos_iff.2 hξ; positivity
    have hb := (le_max_left _ _).trans (hd.lowLoss_bound _ hκ)
    rw [freqPow_eq, freqPow_two_eq]
    set n := ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2
    set A := (2 * π * ‖ξ‖) ^ (2 * (α - 1))
    set t := d.weightMin / (2 * π * ‖ξ‖) ^ 2
    have hn : 0 ≤ n := sq_nonneg _
    have e : d.lowLoss * d.weightMin * (n / (2 * π * ‖ξ‖) ^ 2) = d.lowLoss * t * n := by
      simp only [t]; ring
    have hm := mul_le_mul_of_nonneg_right hb hn
    nlinarith)
  have hC := comb_le In Iy IZ (1 + d.formScale ^ 2 * d.splitVisc - d.formScale ^ 2 * d.reducedCoercivity)
    (-(d.formScale ^ 2 * d.reducedCoercivity * d.weightMin)) (-(d.formScale ^ 2)) (by
    filter_upwards [ae_ne_zero] with ξ hξ
    have hκ : 0 < 2 * π * ‖ξ‖ := by have := norm_pos_iff.2 hξ; positivity
    have hb := hd.formScale_bound _ hκ
    rw [freqPow_eq, freqPow_two_eq]
    set n := ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2
    set A := (2 * π * ‖ξ‖) ^ (2 * (α - 1))
    set t := d.weightMin / (2 * π * ‖ξ‖) ^ 2
    have hn : 0 ≤ n := sq_nonneg _
    have e : d.formScale ^ 2 * d.reducedCoercivity * d.weightMin * (n / (2 * π * ‖ξ‖) ^ 2) =
        d.formScale ^ 2 * d.reducedCoercivity * t * n := by
      simp only [t]; ring
    have hm := mul_le_mul_of_nonneg_right hb hn
    nlinarith)
  beta_reduce at hA hC
  have hX0 : 0 ≤ ∫ ξ, ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 :=
    integral_nonneg fun ξ => sq_nonneg _
  have hY0 : 0 ≤ ∫ ξ, ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 / freqPow 2 ξ :=
    integral_nonneg fun ξ => div_nonneg (sq_nonneg _) (by unfold freqPow; positivity)
  have hgap := hd.reducedGap_pos
  unfold FracCertData.reducedGap at hgap
  have hw0 := hd.weightMin_pos
  have hf0 := hd.formScale_nonneg
  simp only [FracCertData.splitEnergy]
  rw [eB, eZ, eX, eG]
  generalize ∫ ξ, ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 = X at hA hC hX0 ⊢
  generalize ∫ ξ, ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 / freqPow 2 ξ = Y at hA hC hY0 ⊢
  generalize ∫ ξ, freqPow (2 * α - 2) ξ * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 = Z at hA hC ⊢
  refine ⟨by nlinarith, by nlinarith [mul_nonneg hgap.le (add_nonneg hX0 (mul_nonneg hw0.le hY0))], ?_⟩
  calc Real.sqrt X ≤ Real.sqrt (d.formScale ^ 2 *
        (Z - d.splitVisc * X + d.reducedCoercivity * (X + d.weightMin * Y))) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = d.formScale * Real.sqrt (Z - d.splitVisc * X + d.reducedCoercivity * (X + d.weightMin * Y)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hf0]

theorem splitFormBounds (h1 : SecondSymbolEnergyStatement) (h2 : WeakPowerSymbolStatement) :
    SplitFormBoundsStatement := fun α hα1 hα2 _ _ d hd v G H P hs hP =>
  splitFormBounds_of h1 h2 α hα1 hα2 d hd v G H P hs hP

end SteadyCert

end Breakdown
