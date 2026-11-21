import Breakdown.FracCert.StFree
import Breakdown.FreqTr.VelocityInjective

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

def DriftPairSymbolStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    MemLp (driftField α a v G) 2 volume →
    MemLp (fun ξ => freqPow (2 * α - 2) ξ • (secondSymbol H : Space → Freq.CSpace) ξ) 2 volume →
    ∫ ξ, inner ℝ ((fieldSymbol (driftField α a v G) : Space → Freq.CSpace) ξ)
        (freqPow (2 * α - 2) ξ • (secondSymbol H : Space → Freq.CSpace) ξ) =
      (3 / 2 - 5 / (4 * α)) * ∫ ξ, freqPow (2 * α - 4) ξ * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2

namespace Internal.DriftPower

theorem freqPow_le {α : ℝ} (h1 : 1 ≤ α) (h2 : α < 2) (ξ : Space) :
    freqPow (2 * α - 4) ξ ≤ (freqPow 2 ξ)⁻¹ + 1 := by
  unfold freqPow
  set k : ℝ := 2 * π * ‖ξ‖ with hk
  have k0 : 0 ≤ k := by positivity
  rcases k0.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow (by linarith)]
    positivity
  · rcases le_total k 1 with hk1 | hk1
    · have : k ^ (2 * α - 4) ≤ k ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge h hk1 (by linarith)
      rw [Real.rpow_neg h.le] at this
      have : 0 ≤ (1 : ℝ) := zero_le_one
      linarith
    · have : k ^ (2 * α - 4) ≤ k ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
      rw [Real.rpow_zero] at this
      have : 0 ≤ (k ^ (2 : ℝ))⁻¹ := by positivity
      linarith

theorem measurable_freqPow (s : ℝ) : Measurable (freqPow s) := by
  unfold freqPow
  exact (measurable_const.mul measurable_norm).pow_const s

theorem integrable_weighted {α : ℝ} (h1 : 1 ≤ α) (h2 : α < 2) (S : Freq.L2C)
    (hS : Integrable (fun ξ => ‖(S : Space → Freq.CSpace) ξ‖ ^ 2 / freqPow 2 ξ)) :
    Integrable (fun ξ => freqPow (2 * α - 4) ξ * ‖(S : Space → Freq.CSpace) ξ‖ ^ 2) := by
  have hS2 : Integrable (fun ξ => ‖(S : Space → Freq.CSpace) ξ‖ ^ 2) :=
    (Lp.memLp S).integrable_norm_pow two_ne_zero
  refine Integrable.mono' (hS.add hS2) ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · exact (measurable_freqPow _).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable S).norm.pow 2)
  · have h0 : 0 ≤ freqPow (2 * α - 4) ξ := by unfold freqPow; positivity
    have hs : 0 ≤ ‖(S : Space → Freq.CSpace) ξ‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 hs)]
    have := mul_le_mul_of_nonneg_right (freqPow_le h1 h2 ξ) hs
    simp only [Pi.add_apply]
    rw [div_eq_mul_inv]
    nlinarith

theorem toLpOrZero_ae' {f : Space → Space} (hf : MemLp f 2 volume) :
    (Freq.toLpOrZero 2 f : Space → Space) =ᵐ[volume] f := by
  unfold Freq.toLpOrZero
  rw [dif_pos hf]
  exact hf.coeFn_toLp

theorem l2Pair_eq {F E : Space → Space} (hF : MemLp F 2 volume) (hE : MemLp E 2 volume) :
    l2Pair F E = ∫ ξ, inner ℝ ((fieldSymbol F : Space → Freq.CSpace) ξ) ((fieldSymbol E : Space → Freq.CSpace) ξ) := by
  rw [← L2.inner_def]
  unfold fieldSymbol
  rw [Freq.Internal.VelocityInjective.freqTrR_inner, Freq.Internal.VelocityInjective.complexify_inner,
    L2.inner_def]
  unfold l2Pair
  apply integral_congr_ae
  filter_upwards [toLpOrZero_ae' hF, toLpOrZero_ae' hE] with y h1 h2
  rw [h1, h2]

end Internal.DriftPower

open Internal.DriftPower in
theorem driftPower_of (h1 : SecondSymbolEnergyStatement) (h2 : WeakPowerSymbolStatement)
    (h3 : DriftPairSymbolStatement) : DriftPowerStatement := by
  intro α hα1 hα2 a m v G H P hv hP hD
  have hint := integrable_weighted hα1.le (by linarith) (secondSymbol H) (h1 m v G H hv).1
  refine ⟨hint, ?_⟩
  have hPS := h2 α hα1 (by linarith) m v G H P hv hP
  have hmem : MemLp (fun ξ => freqPow (2 * α - 2) ξ • (secondSymbol H : Space → Freq.CSpace) ξ) 2 volume :=
    (Lp.memLp (fieldSymbol P)).ae_eq hPS
  rw [l2Pair_eq hD hP.1, ← h3 α hα1 hα2 a m v G H hv hD hmem]
  apply integral_congr_ae
  filter_upwards [hPS] with ξ hξ
  rw [hξ]


def freqTurn (z : Freq.CSpace) : Freq.CSpace :=
  EuclideanSpace.single 0 (-(z 1)) + EuclideanSpace.single 1 (z 0)

def IsFreqTest (ψ : Space → Freq.CSpace) : Prop :=
  ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (0 : Space) ∉ tsupport ψ

def flowAdjoint (α a : ℝ) (ψ : Space → Freq.CSpace) (ξ : Space) : Freq.CSpace :=
  (1 - 1 / (2 * α)) • ψ ξ + (1 / (2 * α)) • fderiv ℝ ψ ξ ξ - a • fderiv ℝ ψ ξ (axialTurn ξ)
    + a • freqTurn (ψ ξ)

def DriftSymbolWeakStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    MemLp (driftField α a v G) 2 volume → ∀ ψ : Space → Freq.CSpace, IsFreqTest ψ →
    ∫ ξ, inner ℝ ((fieldSymbol (driftField α a v G) : Space → Freq.CSpace) ξ) (ψ ξ) =
      ∫ ξ, inner ℝ ((freqPow 2 ξ)⁻¹ • (secondSymbol H : Space → Freq.CSpace) ξ) (flowAdjoint α a ψ ξ)

def FlowPairingStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (D h : Space → Freq.CSpace), MemLp D 2 volume →
    MemLp (fun ξ => freqPow 1 ξ • h ξ) 2 volume → MemLp (fun ξ => freqPow (2 * α) ξ • h ξ) 2 volume →
    (∀ ψ : Space → Freq.CSpace, IsFreqTest ψ →
      ∫ ξ, inner ℝ (D ξ) (ψ ξ) = ∫ ξ, inner ℝ (h ξ) (flowAdjoint α a ψ ξ)) →
    ∫ ξ, inner ℝ (D ξ) (freqPow (2 * α) ξ • h ξ) =
      (3 / 2 - 5 / (4 * α)) * ∫ ξ, freqPow (2 * α) ξ * ‖h ξ‖ ^ 2

namespace Internal.DriftPower

theorem freqPow_mul {ξ : Space} (hξ : ξ ≠ 0) (s t : ℝ) :
    freqPow s ξ * freqPow t ξ = freqPow (s + t) ξ := by
  unfold freqPow
  rw [Real.rpow_add (by positivity)]

theorem freqPow_inv (ξ : Space) (s : ℝ) : (freqPow s ξ)⁻¹ = freqPow (-s) ξ := by
  unfold freqPow
  rw [Real.rpow_neg (by positivity)]

theorem freqPow_nonneg (ξ : Space) (s : ℝ) : 0 ≤ freqPow s ξ := by
  unfold freqPow; positivity

theorem ae_ne_zero : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
  have := (Set.countable_singleton (0 : Space)).ae_notMem volume
  filter_upwards [this] with ξ hξ
  simpa using hξ

end Internal.DriftPower

open Internal.DriftPower in
theorem driftPairSymbol_of (h1 : SecondSymbolEnergyStatement) (hA : DriftSymbolWeakStatement)
    (hB : FlowPairingStatement) : DriftPairSymbolStatement := by
  intro α hα1 hα2 a m v G H hv hD hmem
  set S : Space → Freq.CSpace := (secondSymbol H : Space → Freq.CSpace) with hSdef
  set h : Space → Freq.CSpace := fun ξ => (freqPow 2 ξ)⁻¹ • S ξ with hhdef
  have hSm : AEStronglyMeasurable S volume := Lp.aestronglyMeasurable _
  have hhm : AEStronglyMeasurable h volume :=
    ((measurable_freqPow 2).inv.aestronglyMeasurable).smul hSm
  have hm1 : MemLp (fun ξ => freqPow 1 ξ • h ξ) 2 volume := by
    have hmeas : AEStronglyMeasurable (fun ξ => freqPow 1 ξ • h ξ) volume :=
      (measurable_freqPow 1).aestronglyMeasurable.smul hhm
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    refine (h1 m v G H hv).1.congr ?_
    filter_upwards [ae_ne_zero] with ξ hξ
    simp only [hhdef, smul_smul, norm_smul, Real.norm_eq_abs]
    have hc : freqPow 1 ξ * (freqPow 2 ξ)⁻¹ = freqPow (-1) ξ := by
      rw [freqPow_inv, freqPow_mul hξ]; norm_num
    have hsq : freqPow (-1) ξ ^ 2 = (freqPow 2 ξ)⁻¹ := by
      rw [sq, freqPow_mul hξ, freqPow_inv]; norm_num
    rw [abs_of_nonneg (mul_nonneg (freqPow_nonneg _ _) (inv_nonneg.2 (freqPow_nonneg _ _))),
      mul_pow, hc, hsq, div_eq_mul_inv, mul_comm]
  have hm2 : MemLp (fun ξ => freqPow (2 * α) ξ • h ξ) 2 volume := by
    refine hmem.ae_eq ?_
    filter_upwards [ae_ne_zero] with ξ hξ
    simp only [hhdef, smul_smul]
    rw [freqPow_inv, freqPow_mul hξ]
    congr 2
  have key := hB α hα1 hα2 a _ h (Lp.memLp _) hm1 hm2 (hA α hα1 hα2 a m v G H hv hD)
  have e1 : ∫ ξ, inner ℝ ((fieldSymbol (driftField α a v G) : Space → Freq.CSpace) ξ)
        (freqPow (2 * α - 2) ξ • S ξ) =
      ∫ ξ, inner ℝ ((fieldSymbol (driftField α a v G) : Space → Freq.CSpace) ξ)
        (freqPow (2 * α) ξ • h ξ) := by
    apply integral_congr_ae
    filter_upwards [ae_ne_zero] with ξ hξ
    simp only [hhdef, smul_smul]
    rw [freqPow_inv, freqPow_mul hξ]
    congr 3
  have e2 : ∫ ξ, freqPow (2 * α) ξ * ‖h ξ‖ ^ 2 = ∫ ξ, freqPow (2 * α - 4) ξ * ‖S ξ‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_ne_zero] with ξ hξ
    simp only [hhdef, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (inv_nonneg.2 (freqPow_nonneg _ _)), freqPow_inv, mul_pow, ← mul_assoc, sq,
      freqPow_mul hξ, freqPow_mul hξ]
    congr 2
    ring
  rw [e1, key, e2]

end SteadyCert

end Breakdown
