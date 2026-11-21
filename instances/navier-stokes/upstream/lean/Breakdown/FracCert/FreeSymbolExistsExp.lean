import Breakdown.FracCert.FreeSymbolExistsSmall

open scoped ContDiff ENNReal Nat
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace FreeSymbolExpInternal

open FreeSymbolSmoothInternal

theorem pow_deriv_cont (p : ℝ) (i : ℕ) : ContinuousOn (iteratedFDeriv ℝ i (freqPow p)) {ξ : Space | ξ ≠ 0} := by
  have hopen : IsOpen {ξ : Space | ξ ≠ 0} := isOpen_ne
  have hs : ContDiffOn ℝ ∞ (freqPow p) {ξ : Space | ξ ≠ 0} := fun ξ hξ => (pow_smoothAt p hξ).contDiffWithinAt
  have h := hs.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast le_top) hopen.uniqueDiffOn
  exact h.congr fun ξ hξ => (iteratedFDerivWithin_of_isOpen i hopen hξ).symm

theorem pow_deriv_bound (p : ℝ) (i : ℕ) :
    ∃ K : ℝ, ∀ ξ : Space, ξ ≠ 0 → ‖iteratedFDeriv ℝ i (freqPow p) ξ‖ ≤ K * ‖ξ‖ ^ (p - i) := by
  have hSU : Metric.sphere (0 : Space) 1 ⊆ {ξ : Space | ξ ≠ 0} := fun ξ hξ h0 => by
    rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hξ
    exact zero_ne_one hξ
  obtain ⟨K, hK⟩ := (isCompact_sphere (0 : Space) 1).exists_bound_of_continuousOn ((pow_deriv_cont p i).mono hSU)
  refine ⟨max K 0, fun ξ hξ => ?_⟩
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set l : ℝ := ‖ξ‖ with hl
  set M : Space ≃L[ℝ] Space := (LinearEquiv.smulOfNeZero ℝ Space l⁻¹ (inv_ne_zero hn.ne')).toContinuousLinearEquiv
    with hM
  have hMa : ∀ η, M η = l⁻¹ • η := fun η => rfl
  have hfun : freqPow p = fun η => l ^ p • (freqPow p ∘ M) η := by
    funext η
    simp only [Function.comp_apply, hMa, freqPow, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn, smul_eq_mul]
    rw [← Real.mul_rpow hn.le (by positivity)]
    congr 1
    field_simp
  have hMξ : M ξ ∈ Metric.sphere (0 : Space) 1 := by
    rw [mem_sphere_zero_iff_norm, hMa, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  have hMn : ‖(M : Space →L[ℝ] Space)‖ ≤ l⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hn.le) fun η => ?_
    change ‖M η‖ ≤ _
    rw [hMa, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn]
  have hat : ContDiffAt ℝ i (freqPow p ∘ M) ξ :=
    ((pow_smoothAt p (hSU hMξ)).comp ξ M.contDiff.contDiffAt).of_le (by exact_mod_cast le_top)
  have hcomp : iteratedFDeriv ℝ i (freqPow p ∘ M) ξ =
      (iteratedFDeriv ℝ i (freqPow p) (M ξ)).compContinuousLinearMap fun _ => (M : Space →L[ℝ] Space) := by
    have h := M.iteratedFDerivWithin_comp_right (freqPow p) uniqueDiffOn_univ (Set.mem_univ (M ξ)) i
    simpa [iteratedFDerivWithin_univ] using h
  rw [hfun, iteratedFDeriv_const_smul_apply' hat, hcomp, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hn p)]
  have hb := (iteratedFDeriv ℝ i (freqPow p) (M ξ)).norm_compContinuousLinearMap_le fun _ => (M : Space →L[ℝ] Space)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  have hK' : ‖iteratedFDeriv ℝ i (freqPow p) (M ξ)‖ ≤ max K 0 := le_trans (hK _ hMξ) (le_max_left _ _)
  have hpow : ‖(M : Space →L[ℝ] Space)‖ ^ i ≤ l⁻¹ ^ i := pow_le_pow_left₀ (norm_nonneg _) hMn i
  have hlp : l ^ p * l⁻¹ ^ i = l ^ (p - i) := by
    rw [Real.rpow_sub hn, Real.rpow_natCast, inv_pow, div_eq_mul_inv]
  calc l ^ p * ‖(iteratedFDeriv ℝ i (freqPow p) (M ξ)).compContinuousLinearMap fun _ => (M : Space →L[ℝ] Space)‖
      ≤ l ^ p * (max K 0 * l⁻¹ ^ i) := by
        gcongr
        exact le_trans hb (mul_le_mul hK' hpow (pow_nonneg (norm_nonneg _) _) (le_max_right _ _))
    _ = max K 0 * l ^ (p - i) := by rw [← hlp]; ring

theorem exp_bound : FreeExpBoundStatement := by
  intro α hα1 _ j
  have hα : 0 < α := by linarith
  choose Kf hKf using pow_deriv_bound (2 * α)
  set Km : ℝ := 1 + ∑ i ∈ Finset.range (j + 1), |Kf i| with hKm
  have hKm1 : 1 ≤ Km := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => abs_nonneg _)
  set C0 : ℝ := Real.exp ((2 * π) ^ (2 * α)) with hC0
  refine ⟨(j ! : ℝ) * C0 * Km ^ j, fun ξ hξ hle => ?_⟩
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set U : Set Space := {η : Space | η ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne
  have hk : ContDiffOn ℝ ∞ (freqPow (2 * α)) U := fun η hη => (pow_smoothAt (2 * α) hη).contDiffWithinAt
  have hg : ContDiffOn ℝ ∞ Real.exp Set.univ := Real.contDiff_exp.contDiffOn
  have hkle : freqPow (2 * α) ξ ≤ (2 * π) ^ (2 * α) := by
    unfold freqPow
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    have : 0 < 2 * π := by positivity
    nlinarith
  have hC : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i Real.exp Set.univ (freqPow (2 * α) ξ)‖ ≤ C0 := by
    intro i _
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 hkle
  have hD : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDerivWithin ℝ i (freqPow (2 * α)) U ξ‖ ≤ (Km / ‖ξ‖) ^ i := by
    intro i hi1 hij
    rw [iteratedFDerivWithin_of_isOpen i hUo hξ]
    have h1 := hKf i ξ hξ
    have h2 : ‖ξ‖ ^ (2 * α - i) ≤ ‖ξ‖ ^ (-(i : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hn hle (by linarith)
    have h3 : ‖ξ‖ ^ (-(i : ℝ)) = ‖ξ‖⁻¹ ^ i := by rw [Real.rpow_neg hn.le, Real.rpow_natCast, inv_pow]
    have h4 : Kf i ≤ Km ^ i := by
      have hmem : i ∈ Finset.range (j + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hij)
      have : |Kf i| ≤ ∑ k ∈ Finset.range (j + 1), |Kf k| :=
        Finset.single_le_sum (f := fun k => |Kf k|) (fun k _ => abs_nonneg _) hmem
      have h5 : Km ≤ Km ^ i := le_self_pow₀ hKm1 (by omega)
      linarith [le_abs_self (Kf i)]
    have hp : 0 ≤ ‖ξ‖ ^ (2 * α - i) := (Real.rpow_pos_of_pos hn _).le
    calc ‖iteratedFDeriv ℝ i (freqPow (2 * α)) ξ‖ ≤ Kf i * ‖ξ‖ ^ (2 * α - i) := h1
      _ ≤ Km ^ i * ‖ξ‖ ^ (-(i : ℝ)) := by
        apply mul_le_mul h4 h2 hp (pow_nonneg (by linarith) _)
      _ = (Km / ‖ξ‖) ^ i := by rw [h3, div_eq_mul_inv, mul_pow]
  have key := norm_iteratedFDerivWithin_comp_le hg hk (n := j) (by exact_mod_cast le_top) uniqueDiffOn_univ
    hUo.uniqueDiffOn (Set.mapsTo_univ _ _) (show ξ ∈ U from hξ) hC hD
  rw [iteratedFDerivWithin_of_isOpen j hUo hξ] at key
  have e : (Km / ‖ξ‖) ^ j = Km ^ j * ‖ξ‖ ^ (-(j : ℝ)) := by
    rw [Real.rpow_neg hn.le, Real.rpow_natCast, div_eq_mul_inv, mul_pow, inv_pow]
  calc ‖iteratedFDeriv ℝ j (fun η => Real.exp (freqPow (2 * α) η)) ξ‖ ≤ (j ! : ℝ) * C0 * (Km / ‖ξ‖) ^ j := key
    _ = (j ! : ℝ) * C0 * Km ^ j * ‖ξ‖ ^ (-(j : ℝ)) := by rw [e]; ring

end FreeSymbolExpInternal

theorem freeExpBound : FreeExpBoundStatement := FreeSymbolExpInternal.exp_bound

end SteadyCert

end Breakdown
