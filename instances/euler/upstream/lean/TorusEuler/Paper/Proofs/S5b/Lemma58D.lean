import TorusEuler.Paper.Proofs.S5b.Lemma58C4
import TorusEuler.TruncatedParentResidual

/-!
# Lemma 5.8: arithmetic of the constants and evaluation of sums of profiles

* `profile_sum_eval`: a finite sum of twisted profiles is evaluated pointwise.
* `fieldNorm_nonneg'`: every norm (D.1) is nonnegative.
* `osc_constant_bound`, `mean_constant_bound`: the exponent bookkeeping of (5.48)
  (`sections/08_exact_wave.tex:128-131`): `(𝖣^{C₇}λ^{3/2})^{m+1} 𝖣^{C₆} λ^{-5/4} ≤
  𝖣^{b(m+2)} λ^{3(m+1)/2-5/4}` and `(𝖣^{C₇})^{m+1}𝖣^{C₆} ≤ 𝖣^{b(m+2)}` for `b ≥ C₆, C₇`.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.S5b

open HierarchyTwistedProfile

noncomputable section

/-- A finite sum of twisted profiles is evaluated pointwise. -/
theorem profile_sum_eval {T : ℝ} {k : Vec3} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (s : Finset ι) (f : ι → HierarchyTwistedProfile T k E) (z : HierarchyProfilePoint) :
    (∑ i ∈ s, f i).val.val.val z = ∑ i ∈ s, (f i).val.val.val z := by
  let ev : HierarchyTwistedProfile T k E →ₗ[ℝ] E := (LinearMap.proj z).comp
    (((hierarchySmoothProfileSubmodule T E).subtype.comp
      (hierarchyPeriodicProfileSubmodule T E).subtype).comp
        (hierarchyTwistedProfileSubmodule T k E).subtype)
  exact map_sum ev f s

/-- Every norm (D.1) is nonnegative (a supremum of norms, with `0` among the values). -/
theorem fieldNorm_nonneg' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ h : ℝ)
    (A : Set ℝ) (τ : ℝ → ℝ) (n : ℕ) (f : ℝ → Vec3 × ℝ → E) : 0 ≤ S5.fieldNorm ℓ h A τ n f :=
  Finset.sum_nonneg fun _ _ => Real.sSup_nonneg fun r hr => by
    rcases hr with rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩
    · exact le_rfl
    · exact norm_nonneg _
    · exact hH.elim

/-- `max x 0`. -/
abbrev pos (x : ℝ) : ℝ := max x 0

/-- A real number is at most its positive part. -/
theorem le_pos (x : ℝ) : x ≤ pos x := le_max_left x 0

/-- The positive part is nonnegative. -/
theorem pos_nonneg (x : ℝ) : 0 ≤ pos x := le_max_right x 0

/-- `(𝖣^{C} λ^{3/2})^{j} = 𝖣^{Cj} λ^{3j/2}`. -/
theorem frequency_pow {D lam : ℝ} (hlam : 0 < lam) (C j : ℕ) :
    (D ^ C * lam ^ (3 / 2 : ℝ)) ^ j = D ^ (C * j) * lam ^ ((3 : ℝ) * (j : ℝ) / 2) := by
  rw [mul_pow, ← pow_mul, ← Real.rpow_natCast (lam ^ (3 / 2 : ℝ)), ← Real.rpow_mul hlam.le]
  congr 2
  ring

/-- The exponent bookkeeping of the first bound of (5.48). -/
theorem osc_constant_bound {D lam : ℝ} (hD : 1 ≤ D) (hlam : 1 ≤ lam) {C6 C7 b m : ℕ}
    (h6 : C6 ≤ b) (h7 : C7 ≤ b) {κ κp N γt : ℝ} (hN0 : 0 ≤ N)
    (hN : N ≤ κp * D ^ C6 * lam ^ (-5 / 4 : ℝ)) (hγ0 : 0 ≤ γt) (hγ1 : γt ≤ 1) :
    κ * (D ^ C7 * lam ^ (3 / 2 : ℝ)) ^ (m + 1) * γt * N ≤
      pos κ * pos κp * D ^ (b * (m + 2)) * lam ^ ((3 : ℝ) * ((m : ℝ) + 1) / 2 - 5 / 4) := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hΛ0 : 0 ≤ (D ^ C7 * lam ^ (3 / 2 : ℝ)) ^ (m + 1) := by positivity
  have hlamp : 0 ≤ lam ^ (-5 / 4 : ℝ) := by positivity
  calc κ * (D ^ C7 * lam ^ (3 / 2 : ℝ)) ^ (m + 1) * γt * N
      ≤ pos κ * (D ^ C7 * lam ^ (3 / 2 : ℝ)) ^ (m + 1) * 1 * (pos κp * D ^ C6 * lam ^ (-5 / 4 : ℝ)) := by
        have h1 : κ * (D ^ C7 * lam ^ (3 / 2 : ℝ)) ^ (m + 1) * γt ≤
            pos κ * (D ^ C7 * lam ^ (3 / 2 : ℝ)) ^ (m + 1) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (le_pos κ) hΛ0) hγ1 hγ0
            (mul_nonneg (pos_nonneg κ) hΛ0)
        have h2 : N ≤ pos κp * D ^ C6 * lam ^ (-5 / 4 : ℝ) :=
          hN.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_pos κp)
            (by positivity)) hlamp)
        exact mul_le_mul h1 h2 hN0 (by positivity)
    _ = pos κ * pos κp * (D ^ (C7 * (m + 1)) * D ^ C6) *
          (lam ^ ((3 : ℝ) * ((m + 1 : ℕ) : ℝ) / 2) * lam ^ (-5 / 4 : ℝ)) := by
        rw [frequency_pow hlam0]; ring
    _ ≤ pos κ * pos κp * D ^ (b * (m + 2)) * lam ^ ((3 : ℝ) * ((m : ℝ) + 1) / 2 - 5 / 4) := by
        rw [← Real.rpow_add hlam0, ← pow_add]
        have hexp : C7 * (m + 1) + C6 ≤ b * (m + 2) := by nlinarith
        have hr : (3 : ℝ) * ((m + 1 : ℕ) : ℝ) / 2 + -5 / 4 = (3 : ℝ) * ((m : ℝ) + 1) / 2 - 5 / 4 := by
          push_cast; ring
        rw [hr]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hD hexp) (mul_nonneg (pos_nonneg κ) (pos_nonneg κp))) (by positivity)

/-- The exponent bookkeeping of the second bound of (5.48). -/
theorem mean_constant_bound {D : ℝ} (hD : 1 ≤ D) {C6 C7 b m : ℕ}
    (h6 : C6 ≤ b) (h7 : C7 ≤ b) {κ κp N μ : ℝ} (hμ : 0 ≤ μ) (hN0 : 0 ≤ N)
    (hN : N ≤ κp * D ^ C6 * μ) :
    κ * (D ^ C7) ^ (m + 1) * 1 * N ≤ pos κ * pos κp * D ^ (b * (m + 2)) * μ := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  calc κ * (D ^ C7) ^ (m + 1) * 1 * N ≤ pos κ * (D ^ C7) ^ (m + 1) * 1 * (pos κp * D ^ C6 * μ) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_pos κ)
          (by positivity)) zero_le_one) (hN.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_pos κp) (by positivity)) hμ)) hN0
          (mul_nonneg (mul_nonneg (pos_nonneg κ) (by positivity)) zero_le_one)
    _ = pos κ * pos κp * (D ^ (C7 * (m + 1) + C6)) * μ := by
        rw [show D ^ (C7 * (m + 1) + C6) = (D ^ C7) ^ (m + 1) * D ^ C6 by rw [pow_add, pow_mul]]
        ring
    _ ≤ _ := by
        have hexp : C7 * (m + 1) + C6 ≤ b * (m + 2) := by nlinarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hexp)
          (mul_nonneg (pos_nonneg κ) (pos_nonneg κp))) hμ

end

end TorusEuler.Paper.S5b
