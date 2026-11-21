import Mathlib

noncomputable section

namespace Breakdown.Spectral

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

theorem hasEigenvalue_of_mem_spectrum (T₀ C : Y →L[ℂ] Y) {b : ℝ} (hT₀ : ‖T₀‖ ≤ b)
    (hC : IsCompactOperator C) {z : ℂ} (hz : z ∈ spectrum ℂ (T₀ + C)) (hbz : b < ‖z‖) :
    Module.End.HasEigenvalue ((T₀ + C : Y →L[ℂ] Y) : Module.End ℂ Y) z := by
  have hR : z ∈ resolventSet ℂ T₀ := by
    apply spectrum.mem_resolventSet_of_norm_lt_mul
    calc ‖T₀‖ * ‖(1 : Y →L[ℂ] Y)‖ ≤ ‖T₀‖ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ = ‖T₀‖ := mul_one _
      _ < ‖z‖ := lt_of_le_of_lt hT₀ hbz
  obtain ⟨u, hu⟩ := spectrum.mem_resolventSet_iff.mp hR
  set K : Y →L[ℂ] Y := (↑u⁻¹ : Y →L[ℂ] Y) * C with hK
  have hKc : IsCompactOperator K := hC.clm_comp (↑u⁻¹ : Y →L[ℂ] Y)
  have hfac : algebraMap ℂ (Y →L[ℂ] Y) z - (T₀ + C) = (u : Y →L[ℂ] Y) * (1 - K) := by
    rw [hK, mul_sub, mul_one, ← mul_assoc, Units.mul_inv, one_mul, hu]
    abel
  rcases hKc.hasEigenvalue_or_mem_resolventSet (one_ne_zero : (1 : ℂ) ≠ 0) with h | h
  · obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    have hKx : K x = x := by
      have := Module.End.mem_eigenspace_iff.mp hx.1
      simpa using this
    have hCx : C x = (u : Y →L[ℂ] Y) x := by
      have h1 : (u : Y →L[ℂ] Y) (K x) = C x := by
        show ((u : Y →L[ℂ] Y) * ((↑u⁻¹ : Y →L[ℂ] Y) * C)) x = C x
        rw [← mul_assoc, Units.mul_inv, one_mul]
      rw [← h1, hKx]
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := x)
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hx.2⟩
    have hux : (u : Y →L[ℂ] Y) x = z • x - T₀ x := by
      rw [hu]
      simp [Algebra.algebraMap_eq_smul_one]
    show T₀ x + C x = z • x
    rw [hCx, hux]
    abel
  · exfalso
    apply spectrum.mem_iff.mp hz
    rw [hfac]
    have h1 : IsUnit (1 - K) := by
      have := spectrum.mem_resolventSet_iff.mp h
      simpa using this
    exact u.isUnit.mul h1

theorem isCompactOperator_pow_sub_pow (T₀ C : Y →L[ℂ] Y) (hC : IsCompactOperator C) (N : ℕ) :
    IsCompactOperator ⇑((T₀ + C) ^ N - T₀ ^ N) := by
  induction N with
  | zero => simpa using (isCompactOperator_zero : IsCompactOperator (0 : Y → Y))
  | succ n ih =>
    have heq : (T₀ + C) ^ (n + 1) - T₀ ^ (n + 1)
        = (T₀ + C) * ((T₀ + C) ^ n - T₀ ^ n) + C * T₀ ^ n := by
      rw [pow_succ', pow_succ']
      noncomm_ring
    rw [heq]
    exact (ih.clm_comp (T₀ + C)).add (hC.comp_clm (T₀ ^ n))

theorem hasEigenvalue_pow {S : Y →L[ℂ] Y} {μ : ℂ}
    (h : Module.End.HasEigenvalue (S : Module.End ℂ Y) μ) (N : ℕ) :
    Module.End.HasEigenvalue ((S ^ N : Y →L[ℂ] Y) : Module.End ℂ Y) (μ ^ N) := by
  have hc : ((S ^ N : Y →L[ℂ] Y) : Module.End ℂ Y) = (S : Module.End ℂ Y) ^ N := by
    induction N with
    | zero => ext x; simp
    | succ n ih =>
      rw [pow_succ, pow_succ, ← ih]
      ext x
      simp
  rw [hc]
  exact h.pow N

end Breakdown.Spectral
