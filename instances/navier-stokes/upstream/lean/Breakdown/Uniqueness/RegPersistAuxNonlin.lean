import Breakdown.Uniqueness.RegPersistAuxDefs

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem norm_le_sum_comp (x : CSpace) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ i, ‖x i‖ ^ 2) ≤ √((∑ i, ‖x i‖) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _)
    _ = ∑ i, ‖x i‖ := Real.sqrt_sq (Finset.sum_nonneg fun _ _ => norm_nonneg _)

private theorem enorm_le_sum_comp (x : CSpace) : ‖x‖ₑ ≤ ∑ i, ‖x i‖ₑ := by
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_le_sum_comp x)

private theorem norm_sum_coord_mul_le (ξ : Space) (z : CSpace) :
    ‖∑ i, ((ξ i : ℝ) : ℂ) * z i‖ ≤ 3 * (‖ξ‖ * ‖z‖) := by
  calc _ ≤ ∑ i, ‖((ξ i : ℝ) : ℂ) * z i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖ξ‖ * ‖z‖ := by
        gcongr with i
        rw [norm_mul, Complex.norm_real]
        exact mul_le_mul (PiLp.norm_apply_le ξ i) (PiLp.norm_apply_le z i) (norm_nonneg _)
          (norm_nonneg _)
    _ = 3 * (‖ξ‖ * ‖z‖) := by simp

private theorem norm_freqVec_le (ξ : Space) : ‖freqVec ξ‖ ≤ 3 * ‖ξ‖ := by
  calc ‖freqVec ξ‖ ≤ ∑ i, ‖freqVec ξ i‖ := norm_le_sum_comp _
    _ ≤ ∑ _i : Fin 3, ‖ξ‖ := by
        gcongr with i
        have e : freqVec ξ i = ((ξ i : ℝ) : ℂ) := rfl
        rw [e, Complex.norm_real]
        exact PiLp.norm_apply_le ξ i
    _ = 3 * ‖ξ‖ := by simp

private theorem norm_divFreeC_le (ξ : Space) (z : CSpace) : ‖divFreeC ξ z‖ ≤ 10 * ‖z‖ := by
  unfold divFreeC
  have hk : (‖ξ‖ ^ 2)⁻¹ * ‖ξ‖ ^ 2 ≤ 1 := by
    rcases eq_or_ne ‖ξ‖ 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ (by positivity)]
  calc _ ≤ ‖z‖ + ‖((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ((ξ i : ℝ) : ℂ) * z i) • freqVec ξ‖ :=
        norm_sub_le _ _
    _ ≤ ‖z‖ + 9 * ‖z‖ := by
        gcongr
        rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        calc (‖ξ‖ ^ 2)⁻¹ * ‖∑ i, ((ξ i : ℝ) : ℂ) * z i‖ * ‖freqVec ξ‖
            ≤ (‖ξ‖ ^ 2)⁻¹ * (3 * (‖ξ‖ * ‖z‖)) * (3 * ‖ξ‖) := by
              gcongr
              · exact norm_sum_coord_mul_le ξ z
              · exact norm_freqVec_le ξ
          _ = 9 * ‖z‖ * ((‖ξ‖ ^ 2)⁻¹ * ‖ξ‖ ^ 2) := by ring
          _ ≤ 9 * ‖z‖ * 1 := by gcongr
          _ = 9 * ‖z‖ := by ring
    _ = 10 * ‖z‖ := by ring

private theorem enorm_divFreeC_le (ξ : Space) (z : CSpace) : ‖divFreeC ξ z‖ₑ ≤ 10 * ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  calc ENNReal.ofReal ‖divFreeC ξ z‖ ≤ ENNReal.ofReal (10 * ‖z‖) :=
        ENNReal.ofReal_le_ofReal (norm_divFreeC_le ξ z)
    _ = 10 * ENNReal.ofReal ‖z‖ := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        simp

private theorem hsNormSq_mono_nat {k m : ℕ} (h : k ≤ m) (f : Space → CSpace) :
    hsNormSq k f ≤ hsNormSq m f := by
  unfold hsNormSq hsWeight
  refine lintegral_mono fun ξ => ?_
  gcongr
  nlinarith [norm_nonneg ξ]

theorem enorm_nonlinSymbol_le : ∃ C : ℝ, ∀ f : Space → CSpace, AEStronglyMeasurable f volume →
    IsSolenoidalSymbol f → hsNormSq 3 f < ⊤ → ∀ ξ,
      ‖nonlinSymbol f ξ‖ₑ ≤ ENNReal.ofReal (C * ‖ξ‖) * ∫⁻ η, ‖f η‖ₑ * ‖f (ξ - η)‖ₑ := by
  obtain ⟨C0, hC0⟩ := weightedFreqL1_le 0
  obtain ⟨C1, hC1⟩ := weightedFreqL1_le 1
  refine ⟨2 * π * 90, fun f hm hs h3 ξ => ?_⟩
  have hW : freqL1Norm f < ⊤ := by
    have h := hC0 f
    simp only [pow_zero, ENNReal.ofReal_one, one_mul, zero_add] at h
    refine h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      ((hsNormSq_mono_nat (by norm_num) f).trans_lt h3).ne
  have hG : gradFreqL1Norm f < ⊤ := by
    have h := hC1 f
    refine lt_of_le_of_lt ?_ (h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h3.ne)))
    unfold gradFreqL1Norm
    refine lintegral_mono fun η => ?_
    gcongr
    simp
  have h1 : hsNormSq 1 f < ⊤ := (hsNormSq_mono_nat (by norm_num) f).trans_lt h3
  set Q := ∫⁻ η, ‖f η‖ₑ * ‖f (ξ - η)‖ₑ with hQ
  have hconv : ∀ i j, ‖convC (fun η => f η j) (fun η => f η i) ξ‖ₑ ≤ Q := by
    intro i j
    unfold convC
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun η => ?_)
    rw [enorm_mul]
    gcongr
    · exact PiLp.enorm_apply_le _ _
    · exact PiLp.enorm_apply_le _ _
  have hterm : ∀ i j, ‖((ξ j : ℝ) : ℂ) * convC (fun η => f η j) (fun η => f η i) ξ‖ₑ ≤ ‖ξ‖ₑ * Q := by
    intro i j
    rw [enorm_mul]
    gcongr
    · rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
      exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le ξ j)
    · exact hconv i j
  have hc : ‖(2 * (π : ℂ) * Complex.I)‖ₑ = ENNReal.ofReal (2 * π) := by
    rw [← ofReal_norm]
    congr 1
    simp [abs_of_pos Real.pi_pos]
  have hcomp : ∀ i, ‖(2 * (π : ℂ) * Complex.I *
      ∑ j, ((ξ j : ℝ) : ℂ) * convC (fun η => f η j) (fun η => f η i) ξ)‖ₑ ≤
        ENNReal.ofReal (2 * π) * (3 * (‖ξ‖ₑ * Q)) := by
    intro i
    rw [enorm_mul, hc]
    gcongr
    calc _ ≤ ∑ j, ‖((ξ j : ℝ) : ℂ) * convC (fun η => f η j) (fun η => f η i) ξ‖ₑ := enorm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, ‖ξ‖ₑ * Q := Finset.sum_le_sum fun j _ => hterm i j
      _ = 3 * (‖ξ‖ₑ * Q) := by simp
  rw [nonlinSymbol, enorm_neg, advectionSymbol_eq_div hs hm hW hG h1 ξ]
  refine (enorm_divFreeC_le ξ _).trans ?_
  have hsum := enorm_le_sum_comp (WithLp.toLp 2 (fun i => 2 * (π : ℂ) * Complex.I *
      ∑ j, ((ξ j : ℝ) : ℂ) * convC (fun η => f η j) (fun η => f η i) ξ) : CSpace)
  calc 10 * ‖(WithLp.toLp 2 (fun i => 2 * (π : ℂ) * Complex.I *
        ∑ j, ((ξ j : ℝ) : ℂ) * convC (fun η => f η j) (fun η => f η i) ξ) : CSpace)‖ₑ
      ≤ 10 * ∑ _i : Fin 3, ENNReal.ofReal (2 * π) * (3 * (‖ξ‖ₑ * Q)) := by
        gcongr
        exact hsum.trans (Finset.sum_le_sum fun i _ => hcomp i)
    _ = ENNReal.ofReal (2 * π * 90 * ‖ξ‖) * Q := by
        have e1 : ENNReal.ofReal (2 * π * 90 * ‖ξ‖) = ENNReal.ofReal (2 * π) * 90 * ‖ξ‖ₑ := by
          rw [ENNReal.ofReal_mul (p := 2 * π * 90) (by positivity),
            ENNReal.ofReal_mul (p := 2 * π) (by positivity), ofReal_norm]
          simp
        rw [e1]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end Breakdown.SmoothFlow
