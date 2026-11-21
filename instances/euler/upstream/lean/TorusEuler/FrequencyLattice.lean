import TorusEuler.TorusFourier
import TorusEuler.TransportedPhase
import TorusEuler.FrequencySchedule

/-!
The lattice criterion for the phase in §3, the real activation vector in
§6, and scalar frequency estimates used in §7.
-/

open scoped InnerProductSpace

namespace TorusEuler

theorem spatiallyPeriodic_modOne_linearPhase_iff (k : Vec3) :
    SpatiallyPeriodic (fun a => (⟪k, a⟫_ℝ : UnitAddCircle)) ↔
      ∃ n : Fin 3 → ℤ, k = latticeVector n := by
  constructor
  · intro h
    have hcoord (i : Fin 3) : ∃ z : ℤ, (z : ℝ) = k i := by
      have he : latticeVector (Pi.single i 1) = EuclideanSpace.single i 1 := by
        refine PiLp.ext fun j => ?_
        by_cases hj : j = i <;> simp [latticeVector, hj]
      have hp : ((k i : ℝ) : UnitAddCircle) = 0 := by
        simpa [he, EuclideanSpace.inner_single_right] using h (Pi.single i 1) 0
      simpa [zsmul_one] using (AddCircle.coe_eq_zero_iff 1).mp hp
    choose n hn using hcoord
    exact ⟨n, PiLp.ext fun i => (hn i).symm⟩
  · rintro ⟨n, rfl⟩ m a
    have hlat : ⟪latticeVector n, latticeVector m⟫_ℝ =
        ((∑ i : Fin 3, m i * n i : ℤ) : ℝ) := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, latticeVector, dotProduct]
    simp only [inner_add_right, AddCircle.coe_add, add_eq_left, hlat]
    exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨∑ i, m i * n i, by simp⟩

/-- The real time-zero wave vector prescribed in §6 gives the exact
activation covector under the inverse transpose of the flow derivative. -/
theorem inverseAdjoint_activationWaveVector (F : Vec3 ≃L[ℝ] Vec3) (carrier : ℝ) (E₃ : Vec3) :
    F.symm.toContinuousLinearMap.adjoint (carrier • F.toContinuousLinearMap.adjoint E₃) = carrier • E₃ := by
  have hcomp : F.toContinuousLinearMap.comp F.symm.toContinuousLinearMap = 1 := by
    ext v
    simp
  rw [map_smul, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
    hcomp, ContinuousLinearMap.adjoint_one, one_apply_eq_self]

/-- The §6 choice gives the stated Eulerian gradient at the activation point. -/
theorem hasGradientAt_activationWaveVector
    {A : Velocity} {t : ℝ} {x E₃ : Vec3} {carrier : ℝ} {F : Vec3 ≃L[ℝ] Vec3}
    (hA : HasFDerivAt (A t) F.symm.toContinuousLinearMap x) :
    HasGradientAt (fun y => ⟪carrier • F.toContinuousLinearMap.adjoint E₃, A t y⟫_ℝ)
      (carrier • E₃) x := by
  rw [← inverseAdjoint_activationWaveVector F carrier E₃]
  exact hasGradientAt_transportedPhase hA

/-- Absorption of the fixed-order constant and the parent scale
`D = μ^9` in the frequency gap of (1.14), as used in §7. -/
theorem frequencySchedule_stepConstant_absorption {μ C : ℝ} {b q : ℕ}
    (hμ : 1 ≤ μ) (hC : C ≤ μ) (hb : 1 ≤ b) :
    C * (μ ^ 9) ^ b ≤ μ ^ (10 * b) ∧
      μ ^ (10 * b) ≤ (μ ^ frequencyExponent b q) ^ (1 / 32 : ℝ) := by
  constructor
  · calc
      C * (μ ^ 9) ^ b ≤ μ * (μ ^ 9) ^ b :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ = μ ^ (1 + 9 * b) := by rw [pow_add, pow_one, pow_mul]
      _ ≤ μ ^ (10 * b) := pow_le_pow_right₀ hμ (by omega)
  · rw [← Real.rpow_natCast μ (frequencyExponent b q), ← Real.rpow_mul (by positivity),
      ← Real.rpow_natCast μ (10 * b)]
    apply Real.rpow_le_rpow_of_exponent_le hμ
    push_cast [frequencyExponent]
    have hb' : 0 ≤ (b : ℝ) := by positivity
    have hq' : 0 ≤ (q : ℝ) := by positivity
    nlinarith

private theorem frequencyExponent_at_least_fifteen {b q : ℕ} (hb : 1 ≤ b) :
    15 ≤ frequencyExponent b q := by
  unfold frequencyExponent
  calc
    15 ≤ 320 * 1 * 1 := by decide
    _ ≤ 320 * b * (q + 1) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hb) (Nat.succ_pos _)

/-- The numerical factor absorbed into the current frequency in the
tail estimate of §7. -/
theorem frequencySchedule_nine_mul_le {μ : ℝ} {b q : ℕ} (hμ : 2 ≤ μ) (hb : 1 ≤ b) :
    9 * μ ≤ μ ^ frequencyExponent b q := by
  have hμ₀ : 0 ≤ μ := by linarith
  have hμ₁ : 1 ≤ μ := by linarith
  calc
    9 * μ ≤ μ ^ 4 * μ := mul_le_mul_of_nonneg_right
      ((by norm_num : (9 : ℝ) ≤ 2 ^ 4).trans (pow_le_pow_left₀ (by norm_num) hμ 4)) hμ₀
    _ = μ ^ 5 := (pow_succ μ 4).symm
    _ ≤ μ ^ frequencyExponent b q := pow_le_pow_right₀ hμ₁
      ((by decide : 5 ≤ 15).trans (frequencyExponent_at_least_fifteen hb))

/-- The depth `P = 6 K_{j+1}` converts the expansion error to
`λ_{j+1}^{-4}` under the schedule. -/
theorem frequencySchedule_residual_exponent {freq : ℝ} (hfreq : 0 ≤ freq) (b qNext : ℕ) :
    freq ^ (-2 * ((6 * frequencyExponent b qNext : ℕ) : ℝ) / 3) =
      (freq ^ frequencyExponent b qNext) ^ (-4 : ℝ) := by
  rw [← Real.rpow_natCast freq (frequencyExponent b qNext), ← Real.rpow_mul hfreq]
  congr 1
  push_cast
  ring

/-- The scalar tail estimate with the cutoff exponent five and
`P = 6 K_{j+1}`, as used in §7. -/
theorem frequencySchedule_tail_absorption {μ : ℝ} {b q qNext : ℕ}
    (hμ : 2 ≤ μ) (hb : 1 ≤ b) :
    let freq := μ ^ frequencyExponent b q
    let P := 6 * frequencyExponent b qNext
    9 * μ * freq ^ (5 * (2 - (P : ℝ)) + 4 * ((P : ℝ) + 1)) ≤
      (freq ^ frequencyExponent b qNext) ^ (-5 : ℝ) := by
  dsimp only
  let freq := μ ^ frequencyExponent b q
  let K := frequencyExponent b qNext
  change 9 * μ * freq ^ (5 * (2 - ((6 * K : ℕ) : ℝ)) + 4 * (((6 * K : ℕ) : ℝ) + 1)) ≤
    (freq ^ K) ^ (-5 : ℝ)
  have hfreq : 1 ≤ freq := one_le_pow₀ (by linarith)
  have hfreq_pos : 0 < freq := zero_lt_one.trans_le hfreq
  have hK : (15 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast frequencyExponent_at_least_fifteen (q := qNext) hb
  rw [← Real.rpow_natCast freq K, ← Real.rpow_mul hfreq_pos.le]
  calc
    _ ≤ freq * freq ^ (5 * (2 - ((6 * K : ℕ) : ℝ)) + 4 * (((6 * K : ℕ) : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (frequencySchedule_nine_mul_le hμ hb) (by positivity)
    _ = freq ^ (1 : ℝ) *
        freq ^ (5 * (2 - ((6 * K : ℕ) : ℝ)) + 4 * (((6 * K : ℕ) : ℝ) + 1)) := by
      rw [Real.rpow_one]
    _ = freq ^ (15 - ((6 * K : ℕ) : ℝ)) := by
      rw [← Real.rpow_add hfreq_pos]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hfreq
      push_cast
      linarith

end TorusEuler
