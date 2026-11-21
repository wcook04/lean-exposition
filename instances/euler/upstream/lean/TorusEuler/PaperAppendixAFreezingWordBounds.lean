import TorusEuler.EndpointSpatialDerivativeHierarchy

/-! Quantitative iteration of the triangular spatial derivative estimates of Lemma A.2. -/

namespace TorusEuler

private theorem endpointMixedCorrectionPairs_length_add_one {I : Type*} (word : List I) :
    (endpointMixedCorrectionPairs word).length + 1 = 2 ^ word.length := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    have h := endpointMixedCorrectionPairs_sum_cons (W := ℕ) i word (fun _ => 1)
    simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one] at h
    norm_num at h
    simp only [List.length_cons, pow_succ]
    omega

/-- Uniform coefficient and forcing word bounds propagate through the exact
Leibniz recurrence of the compressed inverse. The result is linear in the
forcing bound, with a constant depending on the cutoff, inverse, projection,
and coefficient bounds. -/
theorem paperA2_wordNorm_le {I : Type*} (N : ℕ) (a p b F : ℝ)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (hb : 0 ≤ b) (hF : 0 ≤ F)
    (coef force solution : List I → ℝ)
    (hCoef : ∀ word, word.length ≤ N → 0 ≤ coef word ∧ coef word ≤ b)
    (hForce : ∀ word, word.length ≤ N → force word ≤ F)
    (hRec : ∀ word, word.length ≤ N → solution word ≤
      a * (force word + p * ((endpointMixedCorrectionPairs word).map
        fun pair => 2 * coef pair.1 * solution pair.2).sum)) :
    ∀ word, word.length ≤ N →
      solution word ≤ (max 1 (a * (1 + p * ((2 : ℝ) ^ N * (2 * b))))) ^ (N + 1) * F := by
  let K := max 1 (a * (1 + p * ((2 : ℝ) ^ N * (2 * b))))
  have hK : 1 ≤ K := le_max_left _ _
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hWord (word : List I) (hLen : word.length ≤ N) :
      solution word ≤ K ^ (word.length + 1) * F := by
    induction hlen : word.length using Nat.strong_induction_on generalizing word with
    | h n ih =>
      have hLower (pair : List I × List I) (hPair : pair ∈ endpointMixedCorrectionPairs word) :
          2 * coef pair.1 * solution pair.2 ≤ 2 * b * (K ^ n * F) := by
        obtain ⟨_, hEq, hLess⟩ := endpointMixedCorrectionPairs_mem hPair
        have hcb := hCoef pair.1 (by omega)
        have hs := ih pair.2.length (by omega) pair.2 (by omega) rfl
        have hpow := pow_le_pow_right₀ hK (show pair.2.length + 1 ≤ n by omega)
        exact (mul_le_mul_of_nonneg_left
          (hs.trans (mul_le_mul_of_nonneg_right hpow hF)) (mul_nonneg (by norm_num) hcb.1)).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcb.2 (by norm_num))
            (by positivity))
      have hCount : ((endpointMixedCorrectionPairs word).length : ℝ) ≤ (2 : ℝ) ^ N := by
        have hcount := endpointMixedCorrectionPairs_length_add_one word
        have hPow : 2 ^ word.length ≤ (2 : ℕ) ^ N := Nat.pow_le_pow_right (by norm_num) hLen
        exact_mod_cast (show (endpointMixedCorrectionPairs word).length ≤ (2 : ℕ) ^ N by omega)
      have hSum : ((endpointMixedCorrectionPairs word).map
          fun pair => 2 * coef pair.1 * solution pair.2).sum ≤ (2 : ℝ) ^ N * (2 * b * (K ^ n * F)) := by
        refine (List.sum_le_sum hLower).trans ?_
        simpa only [List.map_const', List.sum_replicate, nsmul_eq_mul] using
          mul_le_mul_of_nonneg_right hCount (show 0 ≤ 2 * b * (K ^ n * F) by positivity)
      have hBase : F ≤ K ^ n * F := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hK) hF
      calc
        solution word ≤ a * (force word + p * ((endpointMixedCorrectionPairs word).map
          fun pair => 2 * coef pair.1 * solution pair.2).sum) := hRec word hLen
        _ ≤ a * (K ^ n * F + p * ((2 : ℝ) ^ N * (2 * b * (K ^ n * F)))) :=
          mul_le_mul_of_nonneg_left
            (add_le_add ((hForce word hLen).trans hBase) (mul_le_mul_of_nonneg_left hSum hp)) ha
        _ = (a * (1 + p * ((2 : ℝ) ^ N * (2 * b)))) * (K ^ n * F) := by ring
        _ ≤ K * (K ^ n * F) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ = K ^ (n + 1) * F := by rw [pow_succ']; ring
  intro word hLen
  exact (hWord word hLen).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK (Nat.succ_le_succ hLen)) hF)

end TorusEuler
