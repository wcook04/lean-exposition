import Breakdown.CellReduction.AdjointRemainderAzimuthalAlgebra
import Breakdown.CertCell.FormNegativeInverseSquare

open scoped ENNReal ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace AzimuthalParts

namespace Internal

open CellCert.Reduction

variable {N : ℕ}

def groupSet (comp : Fin N → Fin 3) (order : Fin N → ℤ) (c : Fin 3) (m : ℤ) : Finset (Fin N) :=
  (Finset.univ.filter (fun p => comp p = c)).filter (fun p => order p = m)

def orderSet (comp : Fin N → Fin 3) (order : Fin N → ℤ) (c : Fin 3) : Finset ℤ :=
  (Finset.univ.filter (fun p => comp p = c)).image order

def groupField (amp : Fin N → Space → ℂ) (coef : Fin N → ℂ) (comp : Fin N → Fin 3) (order : Fin N → ℤ)
    (c : Fin 3) (m : ℤ) (y : Space) : ℂ :=
  ∑ p ∈ groupSet comp order c m, coef p * amp p y

theorem group_split (amp : Fin N → Space → ℂ) (coef : Fin N → ℂ) (comp : Fin N → Fin 3) (order : Fin N → ℤ)
    (c : Fin 3) (y : Space) :
    ∑ p ∈ Finset.univ.filter (fun p => comp p = c), coef p * amp p y =
      ∑ m ∈ orderSet comp order c, groupField amp coef comp order c m y :=
  (Finset.sum_fiberwise_of_maps_to (fun _ hp => Finset.mem_image_of_mem order hp) _).symm

theorem group_rotation (amp : Fin N → Space → ℂ) (coef : Fin N → ℂ) (comp : Fin N → Fin 3) (order : Fin N → ℤ)
    (hrot : ∀ p α y, amp p (axisRotation α y) = Complex.exp ((order p : ℂ) * (α : ℂ) * Complex.I) * amp p y)
    (c : Fin 3) (m : ℤ) (ρ θ z : ℝ) :
    groupField amp coef comp order c m (ringPoint ρ θ z) =
      Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) * groupField amp coef comp order c m (ringPoint ρ 0 z) := by
  unfold groupField
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hm : order p = m := (Finset.mem_filter.1 hp).2
  rw [← ringPoint_rotation, hrot, hm]
  ring

theorem group_meas (amp : Fin N → Space → ℂ) (coef : Fin N → ℂ) (comp : Fin N → Fin 3) (order : Fin N → ℤ)
    (hampm : ∀ p, AEStronglyMeasurable (amp p) volume) (c : Fin 3) (m : ℤ) :
    AEStronglyMeasurable (groupField amp coef comp order c m) volume := by
  unfold groupField
  exact Finset.aestronglyMeasurable_fun_sum _ fun p _ => (hampm p).const_mul (coef p)

theorem weightedSq_meas {B : Space → ℂ} (hB : AEStronglyMeasurable B volume) :
    AEMeasurable (fun y => ENNReal.ofReal (‖y‖ ^ 2 * ‖B y‖ ^ 2)) volume :=
  ((continuous_norm.pow 2).aestronglyMeasurable.mul (hB.norm.pow 2)).aemeasurable.ennreal_ofReal

theorem group_finite (amp : Fin N → Space → ℂ) (coef : Fin N → ℂ) (comp : Fin N → Fin 3) (order : Fin N → ℤ)
    (hampm : ∀ p, AEStronglyMeasurable (amp p) volume)
    (hfin : ∀ p, ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖amp p y‖ ^ 2) < ⊤) (c : Fin 3) (m : ℤ) :
    ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖groupField amp coef comp order c m y‖ ^ 2) < ⊤ := by
  set s := groupSet comp order c m
  have hpt : ∀ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖groupField amp coef comp order c m y‖ ^ 2) ≤
      ∑ p ∈ s, ENNReal.ofReal ((s.card : ℝ) * ‖coef p‖ ^ 2) * ENNReal.ofReal (‖y‖ ^ 2 * ‖amp p y‖ ^ 2) := by
    intro y
    have eR : ∑ p ∈ s, ENNReal.ofReal ((s.card : ℝ) * ‖coef p‖ ^ 2) * ENNReal.ofReal (‖y‖ ^ 2 * ‖amp p y‖ ^ 2) =
        ENNReal.ofReal (∑ p ∈ s, (s.card : ℝ) * ‖coef p‖ ^ 2 * (‖y‖ ^ 2 * ‖amp p y‖ ^ 2)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
      exact Finset.sum_congr rfl fun p _ => (ENNReal.ofReal_mul (by positivity)).symm
    rw [eR]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ‖groupField amp coef comp order c m y‖ ≤ ∑ p ∈ s, ‖coef p‖ * ‖amp p y‖ := by
      unfold groupField
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun p _ => norm_mul _ _
    have h2 : (∑ p ∈ s, ‖coef p‖ * ‖amp p y‖) ^ 2 ≤ (s.card : ℝ) * ∑ p ∈ s, (‖coef p‖ * ‖amp p y‖) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ‖groupField amp coef comp order c m y‖ ^ 2 ≤ (s.card : ℝ) * ∑ p ∈ s, (‖coef p‖ * ‖amp p y‖) ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
    calc ‖y‖ ^ 2 * ‖groupField amp coef comp order c m y‖ ^ 2
        ≤ ‖y‖ ^ 2 * ((s.card : ℝ) * ∑ p ∈ s, (‖coef p‖ * ‖amp p y‖) ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = ∑ p ∈ s, (s.card : ℝ) * ‖coef p‖ ^ 2 * (‖y‖ ^ 2 * ‖amp p y‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by ring
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_finsetSum' _ fun p _ => (weightedSq_meas (hampm p)).const_mul _]
  refine ENNReal.sum_lt_top.2 fun p _ => ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin p)

theorem ae_ne_zero : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
  rw [ae_iff]
  simp

theorem pair_integrable {u B : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hB : AEStronglyMeasurable B volume)
    (hu2 : ∫⁻ y, ENNReal.ofReal (‖u y‖ ^ 2 / ‖y‖ ^ 2) < ⊤)
    (hB2 : ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖B y‖ ^ 2) < ⊤) :
    Integrable (fun y => starRingEnd ℂ (u y) * B y) volume := by
  refine ⟨(Complex.continuous_conj.comp_aestronglyMeasurable hu).mul hB, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hle : ∀ᵐ y ∂(volume : Measure Space), ENNReal.ofReal ‖starRingEnd ℂ (u y) * B y‖ ≤
      ENNReal.ofReal (‖u y‖ ^ 2 / ‖y‖ ^ 2) + ENNReal.ofReal (‖y‖ ^ 2 * ‖B y‖ ^ 2) := by
    filter_upwards [ae_ne_zero] with y hy
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, Complex.norm_conj]
    have ht : 0 < ‖y‖ := norm_pos_iff.2 hy
    have e : ‖u y‖ ^ 2 / ‖y‖ ^ 2 = (‖u y‖ / ‖y‖) ^ 2 := by rw [div_pow]
    have e2 : ‖u y‖ = ‖u y‖ / ‖y‖ * ‖y‖ := (div_mul_cancel₀ _ ht.ne').symm
    rw [e]
    set a := ‖u y‖ / ‖y‖
    rw [e2]
    nlinarith [sq_nonneg (a - ‖y‖ * ‖B y‖), norm_nonneg (B y), norm_nonneg (u y), ht.le,
      div_nonneg (norm_nonneg (u y)) ht.le]
  refine lt_of_le_of_lt (lintegral_mono_ae hle) ?_
  have hm : AEMeasurable (fun y => ENNReal.ofReal (‖u y‖ ^ 2 / ‖y‖ ^ 2)) volume :=
    ((hu.norm.pow 2).aemeasurable.div (continuous_norm.pow 2).measurable.aemeasurable).ennreal_ofReal
  rw [lintegral_add_left' hm]
  exact ENNReal.add_lt_top.2 ⟨hu2, hB2⟩

theorem sq_sum_le_of_sq_le_mul {ι : Type*} (s : Finset ι) (x a b : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) (h : ∀ i ∈ s, x i ^ 2 ≤ a i * b i) :
    (∑ i ∈ s, x i) ^ 2 ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, b i := by
  have h1 : ∑ i ∈ s, x i ≤ ∑ i ∈ s, Real.sqrt (a i) * Real.sqrt (b i) := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [← Real.sqrt_mul (ha i hi)]
    exact Real.le_sqrt_of_sq_le (h i hi)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (a i)) (fun i => Real.sqrt (b i))
  have e1 : ∑ i ∈ s, Real.sqrt (a i) ^ 2 = ∑ i ∈ s, a i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (ha i hi)
  have e2 : ∑ i ∈ s, Real.sqrt (b i) ^ 2 = ∑ i ∈ s, b i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hb i hi)
  rw [e1, e2] at h2
  have h0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hx
  exact (pow_le_pow_left₀ h0 h1 2).trans h2

end Internal

end AzimuthalParts

end AdjointDefect

end Breakdown
