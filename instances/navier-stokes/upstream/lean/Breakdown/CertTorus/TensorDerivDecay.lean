import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

namespace TensorDerivDecayInternal

def outerProductLinear : Space →ₗ[ℝ] Space →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ) :=
  LinearMap.mk₂ ℝ (fun a b j k => a j * b k)
    (fun a a' b => by ext j k; simp [add_mul])
    (fun c a b => by ext j k; simp [mul_assoc])
    (fun a b b' => by ext j k; simp [mul_add])
    (fun c a b => by ext j k; simp; ring)

theorem norm_outerProductLinear_le (a b : Space) :
    ‖outerProductLinear a b‖ ≤ 1 * ‖a‖ * ‖b‖ := by
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  show ‖a j * b k‖ ≤ ‖a‖ * ‖b‖
  rw [norm_mul]
  exact mul_le_mul (PiLp.norm_apply_le a j) (PiLp.norm_apply_le b k) (norm_nonneg _)
    (norm_nonneg _)

def outerProduct : Space →L[ℝ] Space →L[ℝ] (Fin 3 → Fin 3 → ℝ) :=
  outerProductLinear.mkContinuous₂ 1 norm_outerProductLinear_le

theorem norm_outerProduct_le : ‖outerProduct‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

theorem pairTensor_eq_outerProduct (W : ℝ → Space → Space) (s : ℝ) :
    pairTensor W W s = fun z => outerProduct (W s z) (W s z) := by
  funext z
  rfl

theorem norm_le_of_weightedBound {E : Type*} [Norm E] {a : ℝ → Space → E} {n : ℕ} {C : ℝ}
    (h : WeightedBound a (n : ℝ) C) (s : ℝ) (y : Space) : ‖a s y‖ ≤ C / (1 + ‖y‖) ^ n := by
  have hp : 0 < (1 + ‖y‖) ^ n := by positivity
  rw [le_div_iff₀ hp, mul_comm, ← Real.rpow_natCast]
  exact h s y

end TensorDerivDecayInternal

open TensorDerivDecayInternal in
theorem tensorDerivDecay_holds : TensorDerivDecay := by
  intro W hW A₀ A₁ A₂ h₀ h₁ h₂
  refine ⟨4 * (max A₀ (max A₁ A₂)) ^ 2, fun s => ?_⟩
  set a := max A₀ (max A₁ A₂) with ha
  have hWs : ContDiff ℝ ∞ (W s) := hW.comp (contDiff_const.prodMk contDiff_id)
  have hWs2 : ContDiff ℝ 2 (W s) := hWs.of_le (WithTop.coe_le_coe.2 le_top)
  refine ⟨?_, fun m hm z => ?_⟩
  · rw [pairTensor_eq_outerProduct]
    exact (outerProduct.contDiff.comp hWs2).clm_apply hWs2
  have hb : ∀ i ≤ 2, ‖iteratedFDeriv ℝ i (W s) z‖ ≤ a / (1 + ‖z‖) ^ (i + 1) := by
    intro i hi
    have hp : 0 < (1 + ‖z‖) ^ (i + 1) := by positivity
    interval_cases i
    · rw [norm_iteratedFDeriv_zero]
      exact (norm_le_of_weightedBound (n := 1) (by simpa using h₀) s z).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) hp.le)
    · rw [norm_iteratedFDeriv_one]
      exact (norm_le_of_weightedBound (n := 2)
          (a := fun s y => fderiv ℝ (W s) y) (by simpa using h₁) s z).trans
        (div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hp.le)
    · exact (norm_le_of_weightedBound (n := 3)
          (a := fun s y => iteratedFDeriv ℝ 2 (W s) y) (by simpa using h₂) s z).trans
        (div_le_div_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hp.le)
  have hterm : ∀ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (W s) z‖ * ‖iteratedFDeriv ℝ (m - i) (W s) z‖ ≤
        (m.choose i : ℝ) * (a ^ 2 / (1 + ‖z‖) ^ (m + 2)) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 := hb i (by omega)
    have e2 := hb (m - i) (by omega)
    have hsplit : a ^ 2 / (1 + ‖z‖) ^ (m + 2) =
        a / (1 + ‖z‖) ^ (i + 1) * (a / (1 + ‖z‖) ^ (m - i + 1)) := by
      rw [div_mul_div_comm, ← pow_add, sq, show i + 1 + (m - i + 1) = m + 2 by omega]
    rw [mul_assoc, hsplit]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul e1 e2 (norm_nonneg _) ((norm_nonneg _).trans e1)) (Nat.cast_nonneg _)
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose] at hsum
  have hbil := outerProduct.norm_iteratedFDeriv_le_of_bilinear hWs2 hWs2 z
    (n := m) (by exact_mod_cast hm)
  have hS : 0 ≤ ∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (W s) z‖ * ‖iteratedFDeriv ℝ (m - i) (W s) z‖ :=
    Finset.sum_nonneg fun i _ => by positivity
  have hq : 0 ≤ a ^ 2 / (1 + ‖z‖) ^ (m + 2) := by positivity
  have h4 : ((2 ^ m : ℕ) : ℝ) ≤ 4 := by
    have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm
    exact_mod_cast this
  rw [pairTensor_eq_outerProduct]
  calc ‖iteratedFDeriv ℝ m (fun y => outerProduct (W s y) (W s y)) z‖
      ≤ ‖outerProduct‖ * ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (W s) z‖ *
            ‖iteratedFDeriv ℝ (m - i) (W s) z‖ := hbil
    _ ≤ 1 * ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (W s) z‖ *
            ‖iteratedFDeriv ℝ (m - i) (W s) z‖ := mul_le_mul_of_nonneg_right norm_outerProduct_le hS
    _ ≤ ((2 ^ m : ℕ) : ℝ) * (a ^ 2 / (1 + ‖z‖) ^ (m + 2)) := by rw [one_mul]; exact hsum
    _ ≤ 4 * (a ^ 2 / (1 + ‖z‖) ^ (m + 2)) := mul_le_mul_of_nonneg_right h4 hq
    _ = 4 * a ^ 2 / (1 + ‖z‖) ^ (2 + m) := by rw [add_comm 2 m, mul_div_assoc]

end Breakdown.FarField
