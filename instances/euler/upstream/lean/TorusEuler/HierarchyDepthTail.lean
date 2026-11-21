import TorusEuler.HierarchyDepthAssembly

/-! The loss budget of the exact tail interactions at the retained depth. -/

namespace TorusEuler

section

variable {E Q : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup Q] [Module ℝ Q]

private theorem hierarchy_tail_product_bound {freq L K C x y a b phase : ℝ} {i j : ℕ}
    (hf : 0 < freq) (hL : 1 ≤ L) (hK : 0 ≤ K) (hC : 0 ≤ C) (hy : 0 ≤ y)
    (hx₁ : x ≤ C * L ^ i * freq ^ a) (hy₁ : y ≤ C * L ^ j * freq ^ b) (hij : 1 + i + j ≤ 6) :
    K * L * freq ^ phase * (x * y) ≤ 2 * K * C ^ 2 * (L ^ 6 * freq ^ (phase + a + b)) := by
  have hL₀ := zero_le_one.trans hL
  have hC' : 0 ≤ C * L ^ i * freq ^ a := by positivity
  calc
    _ ≤ K * L * freq ^ phase * ((C * L ^ i * freq ^ a) * (C * L ^ j * freq ^ b)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hx₁ hy₁ hy hC') (by positivity)
    _ = (K * C ^ 2) * (L ^ (1 + i + j) * freq ^ (phase + a + b)) := by
      rw [pow_add L (1 + i) j, pow_add L 1 i, pow_one,
        Real.rpow_add hf (phase + a) b, Real.rpow_add hf phase a]
      ring
    _ ≤ _ := by
      apply mul_le_mul
      · nlinarith [mul_nonneg hK (sq_nonneg C)]
      · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL hij) (by positivity)
      · positivity
      · positivity

private theorem hierarchy_tail_pair_range {P shift : ℕ} {ij : ℕ × ℕ}
    (h : ij ∈ hierarchyTailPairs P shift) :
    shift + 1 ≤ ij.1 ∧ ij.1 ≤ P + 1 ∧ 1 ≤ ij.2 ∧ ij.2 ≤ P + 1 := by
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp (Finset.mem_filter.mp h).1
  exact ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2,
    (Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2⟩

set_option maxHeartbeats 1400000 in
/-- Quantitative assembly of the exact ignored quadratic interactions and
linear relay at the terminal retained level. The operator inequalities have
the same single parent loss at every depth. -/
theorem hierarchy_depth_tail_of_measuredProducts (A : HierarchyOperators E Q)
    (u : HierarchyProfiles E Q) (s : HierarchyMeasuredLevels) (P n : ℕ) (N : Seminorm ℝ E)
    {freq L K C : ℝ} (hf : 1 ≤ freq) (hL : 1 ≤ L) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hsmall : L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (hP : 1 ≤ P)
    (hlevel : ∀ i ∈ Finset.Icc 1 P, HierarchyLevelBound s freq L C (n + 1) i)
    (hcompletion : ∀ i ∈ Finset.Icc 1 P, s.completion n i ≤
      C * L ^ 2 * freq ^ hierarchyCompletionExponent i)
    (hmean : ∀ i ∈ Finset.Icc 2 (P + 1),
      s.mean n i ≤ C * freq ^ hierarchyInductiveMeanExponent i)
    (hYlast : s.Y (n + 1) (P + 1) ≤ s.completion (n + 1) P)
    (hZlast : s.Z (n + 1) (P + 1) ≤ s.completion (n + 1) P)
    (hLinear : N (A.material (u.C P) + A.labelGrad (u.p P)) ≤ K * L * freq ^ (-1 : ℝ) *
      (s.osc (n + 1) P + s.oscSource (n + 1) P))
    (hSlow : ∀ ij ∈ hierarchyTailPairs P 0,
      N (A.labelProduct u ij) ≤ K * L * (s.Z (n + 1) ij.1 * s.Z (n + 1) ij.2))
    (hFastC : ∀ ij ∈ hierarchyTailPairs P 1,
      N (A.completionPhaseProduct u ij) ≤ K * L * freq ^ (3 / 2 : ℝ) *
        (s.completion n (ij.1 - 1) * s.Y (n + 1) ij.2))
    (hFastM : ∀ ij ∈ hierarchyTailPairs P 1,
      N (A.meanPhaseProduct u ij) ≤ K * L * freq ^ (3 / 2 : ℝ) *
        (s.mean n ij.1 * s.Y (n + 1) ij.2)) :
    N (A.remainder u P) ≤ 2 * K * (C + 1) ^ 2 *
      (1 + ((hierarchyTailPairs P 0).card : ℝ) + 2 * ((hierarchyTailPairs P 1).card : ℝ)) *
      freq ^ hierarchyOscExponent (P + 1) := by
  have hf₀ := zero_lt_one.trans_le hf
  have hL₀ := zero_le_one.trans hL
  have hPmem : P ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨hP, le_rfl⟩
  have hLast : s.completion (n + 1) P ≤ C * L ^ 2 * freq ^ hierarchyOscExponent (P + 1) := by
    refine (hlevel P hPmem).completion.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hf ?_) (by positivity))
    have h := hierarchy_completion_previous (p := P + 1) (by omega)
    rw [Nat.add_sub_cancel] at h
    linarith
  have hY {i : ℕ} (hi₁ : 1 ≤ i) (hiP : i ≤ P + 1) :
      s.Y (n + 1) i ≤ C * L ^ 2 * freq ^ hierarchyOscExponent i := by
    by_cases hi : i ≤ P
    · exact (hlevel i (Finset.mem_Icc.mpr ⟨hi₁,hi⟩)).Y
    · have he : i = P + 1 := by omega
      subst i
      exact hYlast.trans hLast
  have hZ {i : ℕ} (hi₁ : 1 ≤ i) (hiP : i ≤ P + 1) :
      s.Z (n + 1) i ≤ C * L ^ 2 * freq ^ hierarchyOscExponent i := by
    by_cases hi : i ≤ P
    · exact (hlevel i (Finset.mem_Icc.mpr ⟨hi₁,hi⟩)).Z
    · have he : i = P + 1 := by omega
      subst i
      exact hZlast.trans hLast
  have hCap : 2 * K * C ^ 2 ≤ 2 * K * (C + 1) ^ 2 := by
    gcongr; linarith
  have hUp {e : ℝ} : 2 * K * C ^ 2 * (L ^ 6 * freq ^ e) ≤
      2 * K * (C + 1) ^ 2 * (L ^ 6 * freq ^ e) :=
    mul_le_mul_of_nonneg_right hCap (by positivity)
  apply hierarchySeminorm_remainder_le A u P N hf (by positivity) (by positivity) hsmall
  · refine hLinear.trans ?_
    have ho := (hlevel P hPmem).osc
    have hs := (hlevel P hPmem).oscSource
    have hsum : s.osc (n + 1) P + s.oscSource (n + 1) P ≤
        2 * (C * L * freq ^ hierarchyOscExponent P) := by
      rw [two_mul]
      refine add_le_add ho (hs.trans ?_)
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC hL) (by positivity)
    calc
      _ ≤ K * L * freq ^ (-1 : ℝ) * (2 * (C * L * freq ^ hierarchyOscExponent P)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * K * C * (L ^ 2 * freq ^ hierarchyCompletionExponent P) := by
        unfold hierarchyCompletionExponent
        rw [sub_eq_add_neg, Real.rpow_add hf₀]
        ring
      _ ≤ _ := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [sq_nonneg C]
        · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (by decide)) (by positivity)
        · positivity
        · positivity
  · intro ij hij
    obtain ⟨hi,hiP,hj,hjP⟩ := hierarchy_tail_pair_range hij
    refine (hSlow ij hij).trans ?_
    have h := hierarchy_tail_product_bound (phase := 0) hf₀ hL hK hC
      (s.nonneg (n + 1) ij.2).2.2.2.2.2.2 (hZ hi hiP) (hZ hj hjP) (by decide)
    rw [Real.rpow_zero, mul_one, zero_add] at h
    exact h.trans hUp
  · intro ij hij
    obtain ⟨hi,hiP,hj,hjP⟩ := hierarchy_tail_pair_range hij
    exact (hFastC ij hij).trans ((hierarchy_tail_product_bound hf₀ hL hK hC
      (s.nonneg (n + 1) ij.2).2.2.2.2.2.1
      (hcompletion _ (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)) (hY hj hjP) (by decide)).trans hUp)
  · intro ij hij
    obtain ⟨hi,hiP,hj,hjP⟩ := hierarchy_tail_pair_range hij
    have hm := hmean ij.1 (Finset.mem_Icc.mpr ⟨hi,hiP⟩)
    have hm' : s.mean n ij.1 ≤ C * L ^ (0 : ℕ) * freq ^ hierarchyInductiveMeanExponent ij.1 := by
      simpa only [pow_zero, mul_one] using hm
    exact (hFastM ij hij).trans ((hierarchy_tail_product_bound hf₀ hL hK hC
      (s.nonneg (n + 1) ij.2).2.2.2.2.2.1 hm' (hY hj hjP) (by decide)).trans hUp)

end

end TorusEuler
