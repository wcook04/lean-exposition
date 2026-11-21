import Breakdown.Spectral.SpectralProjection

noncomputable section

open Metric

namespace Breakdown.Spectral

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

private lemma Internal.norm_eq_of_mem_sphere {z : ℂ} {r : ℝ} (hz : z ∈ sphere (0 : ℂ) r) :
    ‖z‖ = r :=
  mem_sphere_zero_iff_norm.mp hz

private lemma Internal.ne_zero_of_mem_sphere {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : z ∈ sphere (0 : ℂ) r) : z ≠ 0 := by
  intro h
  rw [h, mem_sphere_zero_iff_norm, norm_zero] at hz
  exact hr.ne hz

private lemma Internal.continuousOn_inv_pow {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ContinuousOn (fun z : ℂ => (z ^ n)⁻¹) (sphere 0 r) :=
  (continuousOn_pow n).inv₀ fun _ hz => pow_ne_zero _ (Internal.ne_zero_of_mem_sphere hr hz)

private lemma Internal.exists_bound_resolvent (T : Y →L[ℂ] Y) {r : ℝ}
    (hA : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ sphere (0 : ℂ) r, ‖resolvent T z‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn
    ((continuousOn_resolvent T).mono fun z hz => hA z (Internal.norm_eq_of_mem_sphere hz))
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hC z hz).trans (le_max_left _ _)⟩

private lemma Internal.pow_mul_inv_pow_integral (T : Y →L[ℂ] Y) {r : ℝ} (hr : 0 < r)
    (hA : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) (n : ℕ) :
    T ^ n * (∮ z in C(0, r), (z ^ n)⁻¹ • resolvent T z) =
      (∮ z in C(0, r), resolvent T z) -
        ∑ j ∈ Finset.range n, (if j = 0 then (2 * Real.pi * Complex.I) • T ^ j else 0) := by
  have hint := circleIntegrable_resolvent T hr.le hA (fun z => (z ^ n)⁻¹)
    (Internal.continuousOn_inv_pow hr n)
  have hint1 : CircleIntegrable (resolvent T) 0 r := by
    simpa using circleIntegrable_resolvent T hr.le hA (fun _ => 1) continuousOn_const
  have hterm : ∀ j : ℕ, CircleIntegrable (fun z : ℂ => (z ^ (j + 1))⁻¹ • T ^ j) 0 r := fun j =>
    ContinuousOn.circleIntegrable hr.le ((Internal.continuousOn_inv_pow hr (j + 1)).smul
      continuousOn_const)
  rw [← circleIntegral_mul_left (T ^ n) hint]
  have hcongr : Set.EqOn (fun z : ℂ => T ^ n * ((z ^ n)⁻¹ • resolvent T z))
      (fun z => resolvent T z - ∑ j ∈ Finset.range n, (z ^ (j + 1))⁻¹ • T ^ j) (sphere 0 r) := by
    intro z hz
    have hz0 := Internal.ne_zero_of_mem_sphere hr hz
    simp only
    rw [mul_smul_comm, pow_mul_resolvent T (hA z (Internal.norm_eq_of_mem_sphere hz)) n,
      smul_sub, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hz0), one_smul, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [smul_smul]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, n = j + 1 + k := ⟨n - (j + 1), by
      have := Finset.mem_range.mp hj
      omega⟩
    have hk : j + 1 + k - 1 - j = k := by omega
    rw [hk, pow_add, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hz0), mul_one]
  rw [circleIntegral.integral_congr hr.le hcongr, circleIntegral.integral_sub hint1
    (CircleIntegrable.fun_sum _ fun j _ => hterm j), circleIntegral.integral_fun_sum
    fun j _ => hterm j]
  congr 1
  exact Finset.sum_congr rfl fun j _ => circleIntegral_inv_pow_smul_const _ hr j

theorem pow_mul_specProj (T : Y →L[ℂ] Y) {ρ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ z : ℂ, ‖z‖ = ρ → z ∈ resolventSet ℂ T) (n : ℕ) :
    T ^ n * specProj T ρ = (2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(0, ρ), z ^ n • resolvent T z := by
  have hint1 : CircleIntegrable (resolvent T) 0 ρ := by
    simpa using circleIntegrable_resolvent T hρ.le hA (fun _ => 1) continuousOn_const
  have hintn := circleIntegrable_resolvent T hρ.le hA (fun z => z ^ n) (continuousOn_pow n)
  have hsum : CircleIntegrable (fun z : ℂ => ∑ j ∈ Finset.range n, z ^ (n - 1 - j) • T ^ j) 0 ρ :=
    ContinuousOn.circleIntegrable hρ.le (continuousOn_finsetSum _ fun j _ =>
      (continuousOn_pow _).smul continuousOn_const)
  unfold specProj
  rw [mul_smul_comm, ← circleIntegral_mul_left (T ^ n) hint1]
  congr 1
  have hcongr : Set.EqOn (fun z : ℂ => T ^ n * resolvent T z)
      (fun z => z ^ n • resolvent T z - ∑ j ∈ Finset.range n, z ^ (n - 1 - j) • T ^ j)
      (sphere 0 ρ) := fun z hz =>
    pow_mul_resolvent T (hA z (Internal.norm_eq_of_mem_sphere hz)) n
  rw [circleIntegral.integral_congr hρ.le hcongr, circleIntegral.integral_sub hintn hsum,
    circleIntegral.integral_fun_sum (f := fun j (z : ℂ) => z ^ (n - 1 - j) • T ^ j) fun j _ =>
      ContinuousOn.circleIntegrable hρ.le ((continuousOn_pow _).smul continuousOn_const)]
  rw [Finset.sum_eq_zero fun j _ => circleIntegral_pow_smul_const (T ^ j) (n - 1 - j), sub_zero]

theorem pow_mul_backProj (T : Y →L[ℂ] Y) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hA : ∀ z : ℂ, ‖z‖ = ρ → z ∈ resolventSet ℂ T) (hR : ‖T‖ < R) (n : ℕ) :
    T ^ n * backProj T ρ R n = 1 - specProj T ρ := by
  have hAR : ∀ z : ℂ, ‖z‖ = R → z ∈ resolventSet ℂ T := fun z hz =>
    mem_resolventSet_of_norm_le_lt (le_refl ‖T‖) (hz ▸ hR)
  have e : specProj T R - specProj T ρ = 1 - specProj T ρ := by rw [specProj_large T hR]
  rw [← e]
  unfold backProj
  rw [mul_smul_comm, mul_sub, Internal.pow_mul_inv_pow_integral T (hρ.trans hρR) hAR n,
    Internal.pow_mul_inv_pow_integral T hρ hA n, sub_sub_sub_cancel_right, smul_sub]
  rfl

theorem norm_pow_mul_specProj_le (T : Y →L[ℂ] Y) {ρ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ z : ℂ, ‖z‖ = ρ → z ∈ resolventSet ℂ T) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, ‖T ^ n * specProj T ρ‖ ≤ K * ρ ^ n := by
  obtain ⟨M, hM0, hM⟩ := Internal.exists_bound_resolvent T hA
  refine ⟨ρ * (M + 1), by positivity, fun n => ?_⟩
  rw [pow_mul_specProj T hρ hA n]
  have hb : ∀ z ∈ sphere (0 : ℂ) ρ, ‖z ^ n • resolvent T z‖ ≤ ρ ^ n * M := by
    intro z hz
    rw [norm_smul, norm_pow, Internal.norm_eq_of_mem_sphere hz]
    exact mul_le_mul_of_nonneg_left (hM z hz) (pow_nonneg hρ.le n)
  calc ‖(2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(0, ρ), z ^ n • resolvent T z‖
      ≤ ρ * (ρ ^ n * M) := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ.le hb
    _ ≤ ρ * (ρ ^ n * (M + 1)) := by
        have := pow_pos hρ n
        gcongr
        linarith
    _ = ρ * (M + 1) * ρ ^ n := by ring

private lemma Internal.norm_inv_pow_integral_le (T : Y →L[ℂ] Y) {r : ℝ} (hr : 0 < r) {M : ℝ}
    (hM : ∀ z ∈ sphere (0 : ℂ) r, ‖resolvent T z‖ ≤ M) (n : ℕ) :
    ‖(2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(0, r), (z ^ n)⁻¹ • resolvent T z‖ ≤
      r * (r⁻¹ ^ n * M) := by
  refine circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le fun z hz => ?_
  rw [norm_smul, norm_inv, norm_pow, Internal.norm_eq_of_mem_sphere hz, ← inv_pow]
  exact mul_le_mul_of_nonneg_left (hM z hz) (by positivity)

theorem norm_backProj_le (T : Y →L[ℂ] Y) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hA : ∀ z : ℂ, ‖z‖ = ρ → z ∈ resolventSet ℂ T) (hR : ‖T‖ < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, ‖backProj T ρ R n‖ ≤ K * ρ⁻¹ ^ n := by
  have hR0 : 0 < R := hρ.trans hρR
  have hAR : ∀ z : ℂ, ‖z‖ = R → z ∈ resolventSet ℂ T := fun z hz =>
    mem_resolventSet_of_norm_le_lt (le_refl ‖T‖) (hz ▸ hR)
  obtain ⟨M, hM0, hM⟩ := Internal.exists_bound_resolvent T hA
  obtain ⟨N, hN0, hN⟩ := Internal.exists_bound_resolvent T hAR
  refine ⟨R * (N + 1) + ρ * (M + 1), by positivity, fun n => ?_⟩
  have h1 : R⁻¹ ^ n ≤ ρ⁻¹ ^ n :=
    pow_le_pow_left₀ (inv_nonneg.mpr hR0.le) (inv_anti₀ hρ hρR.le) n
  have h2 : 0 ≤ ρ⁻¹ ^ n := by positivity
  have eR : R * (R⁻¹ ^ n * N) ≤ R * (N + 1) * ρ⁻¹ ^ n := by
    calc R * (R⁻¹ ^ n * N) ≤ R * (ρ⁻¹ ^ n * (N + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 (by linarith) hN0 h2) hR0.le
      _ = R * (N + 1) * ρ⁻¹ ^ n := by ring
  have eρ : ρ * (ρ⁻¹ ^ n * M) ≤ ρ * (M + 1) * ρ⁻¹ ^ n := by
    calc ρ * (ρ⁻¹ ^ n * M) ≤ ρ * (ρ⁻¹ ^ n * (M + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) h2) hρ.le
      _ = ρ * (M + 1) * ρ⁻¹ ^ n := by ring
  unfold backProj
  rw [smul_sub]
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ R * (R⁻¹ ^ n * N) + ρ * (ρ⁻¹ ^ n * M) :=
        add_le_add (Internal.norm_inv_pow_integral_le T hR0 hN n)
          (Internal.norm_inv_pow_integral_le T hρ hM n)
    _ ≤ (R * (N + 1) + ρ * (M + 1)) * ρ⁻¹ ^ n := by linarith

end Breakdown.Spectral
