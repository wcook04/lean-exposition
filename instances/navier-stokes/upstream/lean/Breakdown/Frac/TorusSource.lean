import Breakdown.Frac.StTorusShell
import Breakdown.Torus.ShellDefs
import Breakdown.Torus.Basic

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.Periodic

namespace FracTorusSource.Internal

theorem one_le_norm_freq {k : Lattice} (hk : k ≠ 0) : 1 ≤ ‖freq k‖ := by
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

theorem sq_le_rpow {α : ℝ} (hα : 1 ≤ α) (k : Lattice) :
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

theorem factor_le_heat {α : ℝ} (hα : 1 ≤ α) (t : ℝ) (k : Lattice) :
    fracLatticeFactor α t k ≤ heatFactor t k := by
  unfold fracLatticeFactor heatFactor
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact mul_le_mul_of_nonneg_right (sq_le_rpow hα k) (le_max_right _ _)

theorem factor_nonneg (α t : ℝ) (k : Lattice) : 0 ≤ fracLatticeFactor α t k := (Real.exp_pos _).le

theorem seq_eq_smul_coeff (u : V) (k : Lattice) : (u : Seq) k = Real.sqrt (weight k) • coeff u k := by
  unfold coeff
  rw [smul_smul, mul_inv_cancel₀ (Internal.sqrt_weight_pos k).ne', one_smul]

theorem norm_force_le {α : ℝ} (hα : 1 ≤ α) (hF : FracTorusForceAlgebra α) (s : ℝ) (F : Space → Space) :
    ‖fracTorusForce α s F‖ ≤ ‖forceV s F‖ := by
  have h : ‖((fracTorusForce α s F : V) : Seq)‖ ≤ ‖((forceV s F : V) : Seq)‖ := by
    refine Internal.norm_le_of_le fun k => ?_
    rw [seq_eq_smul_coeff, hF.1]
    change _ ≤ ‖forceSeq s F k‖
    unfold fracTorusForceCoef forceSeq
    split_ifs with hs
    · rw [smul_smul, norm_smul, norm_smul,
        Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (factor_nonneg α s k)),
        Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Internal.heatFactor_nonneg s k))]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (factor_le_heat hα s k) (Real.sqrt_nonneg _)) (norm_nonneg _)
    · simp
  exact h

theorem force_add_of_coef {α : ℝ} (hF : FracTorusForceAlgebra α) {s : ℝ} {F G H : Space → Space}
    (h : ∀ k, freqTrCoef F k = freqTrCoef G k + freqTrCoef H k) :
    fracTorusForce α s F = fracTorusForce α s G + fracTorusForce α s H := by
  refine coeff_injective fun k => ?_
  rw [ShellDefs.Internal.coeff_add', Pi.add_apply, hF.1, hF.1, hF.1]
  unfold fracTorusForceCoef
  split_ifs
  · rw [h, ShellDefs.Internal.divFree_add', smul_add]
  · simp

theorem force_smul_of_coef {α : ℝ} (hF : FracTorusForceAlgebra α) {s : ℝ} (r : ℝ) {F G : Space → Space}
    (h : ∀ k, freqTrCoef F k = r • freqTrCoef G k) :
    fracTorusForce α s F = r • fracTorusForce α s G := by
  refine coeff_injective fun k => ?_
  rw [ShellDefs.Internal.coeff_smul', Pi.smul_apply, hF.1, hF.1]
  unfold fracTorusForceCoef
  split_ifs
  · rw [h, ShellDefs.Internal.divFree_smul', smul_comm]
  · simp

theorem simScale_pos {α μ : ℝ} (hμ : 0 < μ) : 0 < simScale α μ := Real.rpow_pos_of_pos hμ _

theorem fracSourceFun_bound {α : ℝ} (hα : 1 ≤ α) (hF : FracTorusForceAlgebra α) (μ τ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A, ‖fracSourceFun α μ τ A‖ ≤ C * ‖A‖ := by
  by_cases hμ : 0 < μ
  · have hμ' : 0 < simScale α μ := simScale_pos hμ
    obtain ⟨C, hC, hb⟩ := Breakdown.Periodic.sourceFun_bound (simScale α μ) (μ * τ / simScale α μ)
    refine ⟨C, hC, fun A => ?_⟩
    have ht : simScale α μ * (μ * τ / simScale α μ) = μ * τ := by field_simp
    have e : sourceFun (simScale α μ) (μ * τ / simScale α μ) A =
        forceV (μ * τ) (fun x => (A : Space → Space) (simCoord (simScale α μ) x)) := by
      rw [sourceFun, if_pos hμ', ht]
    have hA := hb A
    rw [e] at hA
    rw [fracSourceFun, if_pos hμ]
    exact (norm_force_le hα hF _ _).trans hA
  · refine ⟨0, le_rfl, fun A => ?_⟩
    rw [fracSourceFun, if_neg hμ, norm_zero, zero_mul]

theorem sourceFun_add {α : ℝ} (hF : FracTorusForceAlgebra α) (μ τ : ℝ) (A B : Freq.L2R) :
    fracSourceFun α μ τ (A + B) = fracSourceFun α μ τ A + fracSourceFun α μ τ B := by
  unfold fracSourceFun
  split_ifs with hμ
  · have hμ' : 0 < simScale α μ := simScale_pos hμ
    exact force_add_of_coef hF fun k =>
      ShellDefs.Internal.freqTrCoef_add_ae (ShellDefs.Internal.integrableOn_sim hμ' A)
        (ShellDefs.Internal.integrableOn_sim hμ' B) (ShellDefs.Internal.sim_add_ae hμ' A B) k
  · simp

theorem sourceFun_smul {α : ℝ} (hF : FracTorusForceAlgebra α) (μ τ r : ℝ) (A : Freq.L2R) :
    fracSourceFun α μ τ (r • A) = r • fracSourceFun α μ τ A := by
  unfold fracSourceFun
  split_ifs with hμ
  · have hμ' : 0 < simScale α μ := simScale_pos hμ
    exact force_smul_of_coef hF r fun k =>
      ShellDefs.Internal.freqTrCoef_smul_ae r (ShellDefs.Internal.sim_smul_ae hμ' r A) k
  · simp

end FracTorusSource.Internal

open FracTorusSource.Internal in
theorem fracSourceOpExists (α : ℝ) (hα : 1 < α) (hF : FracTorusForceAlgebra α) : FracSourceOpExists α := by
  intro μ τ
  refine ⟨LinearMap.mkContinuous
    { toFun := fracSourceFun α μ τ
      map_add' := sourceFun_add hF μ τ
      map_smul' := sourceFun_smul hF μ τ } (fracSourceFun_bound hα.le hF μ τ).choose
    (fun A => (fracSourceFun_bound hα.le hF μ τ).choose_spec.2 A), fun A => rfl⟩

theorem fracSourceOpContinuous (α : ℝ) (hα : 1 < α) (hE : FracSourceOpExists α)
    (hF : FracTorusForceAlgebra α) : FracSourceOpContinuous α := by
  intro μ A hμ
  have e : (fun τ => fracSourceOp α μ τ A) =
      (fun s => fracTorusForce α s (fun x => (A : Space → Space) (simCoord (simScale α μ) x))) ∘
        (fun τ => μ * τ) := by
    funext τ
    have h := hE μ τ
    unfold fracSourceOp
    rw [dif_pos h, h.choose_spec A, fracSourceFun, if_pos hμ, Function.comp_apply]
  rw [e]
  exact (hF.2.2 _).comp (continuous_const.mul continuous_id).continuousOn fun τ hτ => mul_pos hμ hτ

end Breakdown.Periodic
