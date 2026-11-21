import TorusEuler.InductiveStageConstruction

/-! Spatial Bernstein jet bounds for the actual inductive stage. -/

open Set

namespace TorusEuler.InductiveEulerStage

/-- The velocity band and amplitude bound give the spatial derivative scale
of the actual stage, uniformly on the closed slab. -/
theorem exists_velocity_bernstein_bounds :
    ∃ K : ℕ → ℝ, (∀ m, 0 ≤ K m) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation : ℝ}
        (s : InductiveEulerStage P n activation), 1 ≤ P.frequency n →
        ∀ k : ℕ, ∀ t ∈ Icc 0 (P.slab n activation), ∀ x : Vec3,
          ‖iteratedFDeriv ℝ k (s.velocity t) x‖ ≤ K k * (P.frequency n) ^ (5 * k + 1) := by
  obtain ⟨K, hK, hBernstein⟩ := exists_bandBernsteinJetBounds
  refine ⟨K, hK, ?_⟩
  intro P n activation s hfreq k t ht x
  let freq := P.frequency n
  have hpos : 0 < freq := zero_lt_one.trans_le hfreq
  have hband : RealTorusFourierBand (4 * freq ^ 5) (s.torusVelocity t) :=
    fun j hj => s.velocity_band t ht j <|
      (show 2 * freq ^ 5 ≤ 4 * freq ^ 5 from
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hpos.le _)).trans_lt hj
  calc
    ‖iteratedFDeriv ℝ k (s.velocity t) x‖ ≤ K k * freq * (freq ^ 5) ^ k :=
      (hBernstein (s.torusVelocity t) (D := freq ^ 5) (A := freq)
        (pow_pos hpos _) hpos.le (s.velocity_bound t ht) hband).2 k x
    _ = K k * freq ^ (5 * k + 1) := by rw [pow_add, pow_one, pow_mul]; ring

/-- At the coframe scale D = frequency^9, the actual parent velocity satisfies
the uniform derivative hypotheses of the coefficient estimates. -/
theorem exists_velocity_jet_bounds :
    ∃ R : ℕ → ℝ, (∀ m, 0 ≤ R m) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation : ℝ}
        (s : InductiveEulerStage P n activation), 1 ≤ P.frequency n →
        ∀ m k : ℕ, 1 ≤ k → k ≤ m → ∀ t ∈ Icc 0 (P.slab n activation), ∀ x : Vec3,
          ‖iteratedFDeriv ℝ k (s.velocity t) x‖ ≤ R m * ((P.frequency n) ^ 9) ^ k := by
  obtain ⟨K, hK, hBernstein⟩ := exists_velocity_bernstein_bounds
  let R (m : ℕ) := ∑ i ∈ Finset.range (m + 1), K i
  refine ⟨R, fun m => Finset.sum_nonneg fun i _ => hK i, ?_⟩
  intro P n activation s hfreq m k hk hkm t ht x
  have hR : K k ≤ R m :=
    Finset.single_le_sum (fun i _ => hK i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hkm))
  have hExp : 5 * k + 1 ≤ 9 * k := by omega
  calc
    ‖iteratedFDeriv ℝ k (s.velocity t) x‖ ≤ K k * (P.frequency n) ^ (5 * k + 1) :=
      hBernstein s hfreq k t ht x
    _ ≤ R m * (P.frequency n) ^ (9 * k) :=
      mul_le_mul hR (pow_le_pow_right₀ hfreq hExp)
        (pow_nonneg (zero_le_one.trans hfreq) _) (Finset.sum_nonneg fun i _ => hK i)
    _ = R m * ((P.frequency n) ^ 9) ^ k := by rw [pow_mul]

/-- A single frequency threshold puts the first derivative below the parent
coframe scale on the entire actual stage slab. -/
theorem exists_velocity_gradient_bound :
    ∃ N : ℝ, 1 ≤ N ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation : ℝ}
        (s : InductiveEulerStage P n activation), N ≤ P.frequency n →
        ∀ t ∈ Icc 0 (P.slab n activation), ∀ x : Vec3,
          ‖fderiv ℝ (s.velocity t) x‖ ≤ (P.frequency n) ^ 9 := by
  obtain ⟨K, _, hK⟩ := exists_velocity_bernstein_bounds
  refine ⟨max 1 (K 1), le_max_left _ _, ?_⟩
  intro P n activation s hf t ht x
  let freq := P.frequency n
  have hFreq : 1 ≤ freq := (le_max_left (1 : ℝ) (K 1)).trans hf
  have hK₁ : K 1 ≤ freq := (le_max_right (1 : ℝ) (K 1)).trans hf
  have hGrad : ‖fderiv ℝ (s.velocity t) x‖ ≤ K 1 * freq ^ 6 := by
    simpa only [norm_iteratedFDeriv_one, Nat.reduceMul, Nat.reduceAdd] using hK s hFreq 1 t ht x
  calc
    _ ≤ K 1 * freq ^ 6 := hGrad
    _ ≤ freq * freq ^ 6 := mul_le_mul_of_nonneg_right hK₁ (pow_nonneg (zero_le_one.trans hFreq) _)
    _ = freq ^ 7 := by ring
    _ ≤ freq ^ 9 := pow_le_pow_right₀ hFreq (by decide)

end TorusEuler.InductiveEulerStage
