import Breakdown.FracCert.DecayPressureParts
import Breakdown.FracCert.DecayPower
import Breakdown.Uniqueness.RegPhysAuxPressurePart3
import Breakdown.Uniqueness.RegPhysAuxProductPart2

open MeasureTheory Set Real Filter
open scoped ENNReal ContDiff FourierTransform

noncomputable section

namespace Breakdown.FracCert.DecayPressureRep

open Breakdown.Freq Breakdown.SmoothFlow Breakdown.FracCert.WeakRegularInternal
open Breakdown.SmoothFlow.Internal.ConvProduct Breakdown.FracCert.DecayPowerInternal

private theorem multiplier_norm_le (i j : Fin 3) (ξ : Space) : ‖pressureMultiplier i j ξ‖ ≤ 1 := by
  unfold pressureMultiplier
  rw [Complex.norm_real, Real.norm_eq_abs, abs_neg]
  by_cases hξ : ξ = 0
  · subst hξ; simp
  have hn : 0 < ‖ξ‖ ^ 2 := by positivity
  rw [abs_div, abs_of_pos hn, div_le_one hn, abs_mul]
  have hi : |ξ i| ≤ ‖ξ‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ξ i
  have hj : |ξ j| ≤ ‖ξ‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ξ j
  rw [sq]
  exact mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)

private theorem multiplier_measurable (i j : Fin 3) : Measurable (pressureMultiplier i j) := by
  unfold pressureMultiplier
  fun_prop

theorem pressureRepresentation_of (h3 : SymbolL1OfMomentsStatement) :
    PressureRepresentationStatement := by
  intro α hα1 hα2 a U hU hM hD
  have hwm := (h3 U hM).1
  set f := cleanSymbol (symbolX U) with hfdef
  have hf : ∀ k, MemLp f 1 (weightL1Measure k) := memLp_clean U hwm
  have hsol : IsSolenoidalSymbol f := fun ξ => ⟨cleanSymbol_div _ ξ, cleanSymbol_conjSym _ ξ⟩
  have hfp : ∀ (k : ℕ) (l : Fin 3), MemLp (fun ξ => f ξ l) 1 (polyWeight k) :=
    fun k l => memLp_polyWeight_apply (hf k) l
  have hfi : ∀ l : Fin 3, Integrable (fun ξ => f ξ l) :=
    fun l => integrable_of_memLp_polyWeight (hfp 0 l)
  set F : Fin 3 → Fin 3 → Space → ℂ := fun i j => convC (fun ξ => f ξ i) (fun ξ => f ξ j)
    with hFdef
  have hFp : ∀ (k : ℕ) (i j : Fin 3), MemLp (F i j) 1 (polyWeight k) :=
    fun k i j => memLp_convC (hfp k i) (hfp k j)
  have hFi : ∀ i j, Integrable (F i j) := fun i j => integrable_of_memLp_polyWeight (hFp 0 i j)
  have hσFm : ∀ i j, AEStronglyMeasurable (fun ξ => pressureMultiplier i j ξ * F i j ξ) volume :=
    fun i j => (multiplier_measurable i j).aestronglyMeasurable.mul (hFi i j).aestronglyMeasurable
  have hσFi : ∀ i j, Integrable (fun ξ => pressureMultiplier i j ξ * F i j ξ) := fun i j =>
    (hFi i j).norm.mono' (hσFm i j) (Eventually.of_forall fun ξ => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (multiplier_norm_le i j ξ)))
  refine ⟨F, fun i j => ?_, fun i j => ?_, fun y => ?_⟩
  · have hre : ∀ (l : Fin 3) (y : Space),
        (((profileField U y l : ℝ)) : ℂ) = 𝓕⁻ (fun ξ => f ξ l) y := by
      intro l y
      have hconjSym : ∀ ξ, f (-ξ) l = (starRingEnd ℂ) (f ξ l) := fun ξ => by
        rw [hfdef, cleanSymbol_conjSym]
        rfl
      have hc := freqTrInv_conj_symm (g := fun ξ => f ξ l) hconjSym y
      have e1 : profileField U y l = (𝓕⁻ (fun ξ => f ξ l) y).re := by
        unfold profileField
        rw [← physField_clean U, ← freqTrInv_apply_eq (Breakdown.SmoothFlow.Internal.integrable_of_weight (hf 0))]
        rfl
      rw [e1]
      exact Complex.conj_eq_iff_re.1 hc
    have e : (fun y => ((profileField U y i * profileField U y j : ℝ) : ℂ)) = 𝓕⁻ (F i j) := by
      funext y
      rw [hFdef]
      simp only
      rw [freqTrInv_convC (hfi i) (hfi j), Complex.ofReal_mul, hre, hre]
    rw [e]
    exact transform_of _ (hFi i j)
  · refine ⟨hσFm i j, fun n => ?_⟩
    have hw : Integrable (fun ξ : Space => (1 + ‖ξ‖) ^ n * ‖F i j ξ‖) := by
      obtain ⟨hm, hl⟩ := (memLp_polyWeight_iff n).1 (hFp n i j)
      refine ⟨(Continuous.aestronglyMeasurable (by fun_prop)).mul hm.norm, ?_⟩
      unfold HasFiniteIntegral
      refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun ξ => ?_)) hl
      rw [enorm_mul, enorm_norm, Real.enorm_of_nonneg (by positivity)]
      rfl
    refine hw.mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul (hσFm i j).norm)
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
    have h1 : ‖ξ‖ ^ n ≤ (1 + ‖ξ‖) ^ n := pow_le_pow_left₀ (norm_nonneg _) (by linarith) n
    have h2 : ‖pressureMultiplier i j ξ‖ * ‖F i j ξ‖ ≤ ‖F i j ξ‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (multiplier_norm_le i j ξ)
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  · have hae := PressureSingle.Internal.pressureSymbol_ae_eq (hf 1) hsol
    have hconv : ∀ i j : Fin 3, ∀ᵐ ξ ∂(volume : Measure Space),
        Integrable (fun η => f η i * f (ξ - η) j) := by
      intro i j
      filter_upwards [(hfi i).ae_convolution_exists (L := ContinuousLinearMap.mul ℂ ℂ) (hfi j)]
        with ξ hξ
      simpa [ConvolutionExistsAt] using hξ
    have hsplit : pressureSymbol f =ᵐ[volume]
        fun ξ => ∑ i, ∑ j, pressureMultiplier i j ξ * F i j ξ := by
      filter_upwards [hae, ae_all_iff.2 fun i => ae_all_iff.2 fun j => hconv i j] with ξ h1 h2
      rw [h1]
      unfold pressureBilinSymbol pressurePairTerm freqDot
      have hpt : ∀ η, (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) *
          ((∑ k, ((ξ k : ℝ) : ℂ) * f η k) * (∑ k, ((ξ k : ℝ) : ℂ) * f (ξ - η) k)) =
          ∑ i, ∑ j, -(pressureMultiplier i j ξ * (f η i * f (ξ - η) j)) := by
        intro η
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold pressureMultiplier
        push_cast
        ring
      simp_rw [hpt]
      have hint : ∫ η, ∑ i, ∑ j, -(pressureMultiplier i j ξ * (f η i * f (ξ - η) j)) =
          ∑ i, ∑ j, -(pressureMultiplier i j ξ * F i j ξ) := by
        rw [integral_finsetSum (f := fun i η => ∑ j, -(pressureMultiplier i j ξ * (f η i * f (ξ - η) j)))
          Finset.univ (fun i _ => integrable_finsetSum _ fun j _ =>
            ((h2 i j).const_mul (pressureMultiplier i j ξ)).neg)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum (f := fun j η => -(pressureMultiplier i j ξ * (f η i * f (ξ - η) j)))
          Finset.univ (fun j _ => ((h2 i j).const_mul (pressureMultiplier i j ξ)).neg)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_neg, integral_const_mul]
        rfl
      rw [hint]
      simp only [Finset.sum_neg_distrib, neg_neg]
    have hQ : profilePressure U y = (𝓕⁻ (pressureSymbol f) y).re := by
      unfold profilePressure physScalar
      rw [hfdef, pressure_clean U]
    rw [hQ, Real.fourierInv_congr_ae hsplit y,
      freqTrInv_sum (fun i => integrable_finsetSum _ fun j _ => hσFi i j) y, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [freqTrInv_sum (fun j => hσFi i j) y, Complex.re_sum]

end Breakdown.FracCert.DecayPressureRep
