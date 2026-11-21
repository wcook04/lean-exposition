import Breakdown.Frac.StTorusBasic
import Breakdown.Torus.Basic

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.Periodic

namespace FracKernelInternal

private lemma freq_neg' (k : Lattice) : freq (-k) = -freq k := by
  simp [freq, Finset.sum_neg_distrib]

private lemma divPairing_csmul' (k : Lattice) (z : ℂ) (c : Coef) :
    divPairing k (z • c) = z * divPairing k c := by
  simp only [divPairing, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma divPairing_smul' (k : Lattice) (r : ℝ) (c : Coef) :
    divPairing k (r • c) = (r : ℂ) * divPairing k c := by
  rw [← divPairing_csmul', Complex.coe_smul]

private lemma mem_fieldSpace' {a : Seq} :
    a ∈ fieldSpace ↔ (∀ k i, (a (-k)) i = starRingEnd ℂ ((a k) i)) ∧ ∀ k, divPairing k (a k) = 0 :=
  Iff.rfl

private lemma one_le_norm_freq {k : Lattice} (hk : k ≠ 0) : 1 ≤ ‖freq k‖ := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    exact hk (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  have hz : (1 : ℤ) ≤ k i ^ 2 := by
    rcases lt_trichotomy (k i) 0 with h | h | h
    · nlinarith
    · exact absurd h hi
    · nlinarith
  have h1 : (1 : ℝ) ≤ ((k i : ℤ) : ℝ) ^ 2 := by exact_mod_cast hz
  have h2 : ((k i : ℤ) : ℝ) ^ 2 ≤ ‖freq k‖ ^ 2 := by
    rw [Internal.norm_freq_sq]
    exact Finset.single_le_sum (f := fun j => ((k j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  nlinarith [norm_nonneg (freq k)]

private lemma sq_le_rpow {α : ℝ} (hα : 1 ≤ α) (k : Lattice) :
    4 * π ^ 2 * ‖freq k‖ ^ 2 ≤ (2 * π * ‖freq k‖) ^ (2 * α) := by
  by_cases hk : k = 0
  · subst hk
    have h0 : freq (0 : Lattice) = 0 := by simp [freq]
    rw [h0, norm_zero, mul_zero, Real.zero_rpow (by linarith)]
    simp
  · have hx : 1 ≤ 2 * π * ‖freq k‖ := by
      have := one_le_norm_freq hk
      nlinarith [Real.pi_gt_three]
    have h := Real.rpow_le_rpow_of_exponent_le hx (show (2 : ℝ) ≤ 2 * α by linarith)
    rw [Real.rpow_two] at h
    calc 4 * π ^ 2 * ‖freq k‖ ^ 2 = (2 * π * ‖freq k‖) ^ 2 := by ring
      _ ≤ _ := h

private def ratio (α τ : ℝ) (k : Lattice) : ℝ :=
  Real.exp (-(((2 * π * ‖freq k‖) ^ (2 * α) - 4 * π ^ 2 * ‖freq k‖ ^ 2) * max τ 0))

private lemma abs_ratio_le {α : ℝ} (hα : 1 ≤ α) (τ : ℝ) (k : Lattice) : |ratio α τ k| ≤ 1 := by
  rw [ratio, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
  have h1 := sq_le_rpow hα k
  have h2 := le_max_right τ 0
  exact mul_nonneg (by linarith) h2

private lemma ratio_neg (α τ : ℝ) (k : Lattice) : ratio α τ (-k) = ratio α τ k := by
  rw [ratio, ratio, freq_neg', norm_neg]

private lemma factor_eq (α τ : ℝ) (k : Lattice) :
    fracLatticeFactor α τ k = ratio α τ k * heatFactor τ k := by
  rw [fracLatticeFactor, ratio, heatFactor, ← Real.exp_add]
  congr 1
  ring

private lemma factor_add (α : ℝ) {s τ : ℝ} (hs : 0 ≤ s) (hτ : 0 ≤ τ) (k : Lattice) :
    fracLatticeFactor α s k * fracLatticeFactor α τ k = fracLatticeFactor α (s + τ) k := by
  rw [fracLatticeFactor, fracLatticeFactor, fracLatticeFactor, max_eq_left hs, max_eq_left hτ,
    max_eq_left (add_nonneg hs hτ), ← Real.exp_add]
  congr 1
  ring

private lemma ratio_mem {α : ℝ} (hα : 1 ≤ α) (τ : ℝ) (a : V) :
    mulSeq (ratio α τ) zero_le_one (abs_ratio_le hα τ) (a : Seq) ∈ fieldSpace := by
  obtain ⟨ha, ha'⟩ := mem_fieldSpace'.mp a.2
  refine mem_fieldSpace'.mpr ⟨fun k i => ?_, fun k => ?_⟩
  · show (ratio α τ (-k) • (a : Seq) (-k)) i = starRingEnd ℂ ((ratio α τ k • (a : Seq) k) i)
    rw [ratio_neg, PiLp.smul_apply, PiLp.smul_apply, ha k i]
    simp [Complex.real_smul]
  · show divPairing k (ratio α τ k • (a : Seq) k) = 0
    rw [divPairing_smul', ha' k, mul_zero]

private def mult {α : ℝ} (hα : 1 ≤ α) (τ : ℝ) : V →L[ℝ] V :=
  ((mulSeq (ratio α τ) zero_le_one (abs_ratio_le hα τ)).comp fieldSpace.subtypeL).codRestrict
    fieldSpace (ratio_mem hα τ)

private lemma coeff_mult {α : ℝ} (hα : 1 ≤ α) (τ : ℝ) (x : V) (k : Lattice) :
    coeff (mult hα τ x) k = ratio α τ k • coeff x k := by
  have e : ((mult hα τ x : V) : Seq) k = ratio α τ k • (x : Seq) k := rfl
  unfold coeff
  rw [e, smul_comm]

private lemma coeff_kernel_nonpos {τ : ℝ} (hτ : ¬ 0 < τ) (u v : V) (k : Lattice) :
    coeff (kernel τ u v) k = 0 := by
  unfold coeff
  rw [Internal.kernel_apply]
  unfold kernelSeq
  rw [if_neg hτ, smul_zero]

end FracKernelInternal

open FracKernelInternal

theorem fracTorusKernelExists (α : ℝ) (hα : 1 ≤ α) : FracTorusKernelExists α := by
  intro τ
  refine ⟨(ContinuousLinearMap.compL ℝ V V V (mult hα τ)).comp (kernel τ), fun u v k => ?_⟩
  show coeff (mult hα τ (kernel τ u v)) k = fracTorusKernelCoef α τ u v k
  rw [coeff_mult]
  unfold fracTorusKernelCoef
  split_ifs with hτ
  · rw [coeff_kernel τ hτ, smul_smul, factor_eq]
    congr 1
    ring
  · rw [coeff_kernel_nonpos hτ, smul_zero]

namespace FracKernelInternal

private lemma coeff_fracKernel {α : ℝ} (hα : 1 ≤ α) (τ : ℝ) (u v : V) (k : Lattice) :
    coeff (fracTorusKernel α τ u v) k = fracTorusKernelCoef α τ u v k := by
  have h := fracTorusKernelExists α hα τ
  unfold fracTorusKernel
  rw [dif_pos h]
  exact h.choose_spec u v k

end FracKernelInternal

theorem fracTorusKernelAlgebra (α : ℝ) (hα : 1 ≤ α) (hH : FracTorusHeatAlgebra α) :
    FracTorusKernelAlgebra α := by
  have hHK : ∀ s τ : ℝ, 0 ≤ s → 0 < τ → ∀ u v,
      fracTorusHeat α s (fracTorusKernel α τ u v) = fracTorusKernel α (s + τ) u v := by
    intro s τ hs hτ u v
    refine coeff_injective fun k => ?_
    rw [hH.1, coeff_fracKernel hα, coeff_fracKernel hα]
    unfold fracTorusKernelCoef
    rw [if_pos hτ, if_pos (add_pos_of_nonneg_of_pos hs hτ), smul_smul, ← factor_add α hs hτ.le]
    congr 1
    ring
  refine ⟨fun τ u v k => coeff_fracKernel hα τ u v k, fun τ u v => ?_, fun u v => ?_, hHK⟩
  · refine coeff_injective fun k => ?_
    rw [coeff_fracKernel hα, coeff_fracKernel hα]
    unfold fracTorusKernelCoef
    rw [add_comm (advCoef u v k)]
  · intro τ₀ hτ₀
    have hτ₀' : (0 : ℝ) < τ₀ := hτ₀
    have h0 : (0 : ℝ) < τ₀ / 2 := half_pos hτ₀'
    have hc : Continuous fun τ => fracTorusHeat α (τ - τ₀ / 2) (fracTorusKernel α (τ₀ / 2) u v) :=
      (hH.2.2.2.2.2 _).comp (continuous_id.sub continuous_const)
    have heq : (fun τ => fracTorusHeat α (τ - τ₀ / 2) (fracTorusKernel α (τ₀ / 2) u v)) =ᶠ[𝓝 τ₀]
        fun τ => fracTorusKernel α τ u v := by
      filter_upwards [Ioi_mem_nhds (half_lt_self hτ₀')] with τ hτ
      have hτ' : τ₀ / 2 < τ := hτ
      rw [hHK (τ - τ₀ / 2) (τ₀ / 2) (by linarith) h0 u v, sub_add_cancel]
    exact (hc.continuousAt.congr heq).continuousWithinAt

end Breakdown.Periodic
