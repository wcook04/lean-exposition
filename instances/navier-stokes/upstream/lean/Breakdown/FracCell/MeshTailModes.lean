import Breakdown.FracCell.MeshTailSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace MeshTail

theorem modeSquareSum_le {m : ℕ} (hm : 1 ≤ m) (S : Finset ℤ) (h : ℝ → ℂ)
    (hL2 : MemLp h 2 (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) :
    ∑ n ∈ S, ‖(1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * h θ‖ ^ 2
      ≤ (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖h θ‖ ^ 2 := by
  have hab : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsum := hasSum_sq_fourierCoeffOn hab hL2
  have key : ∀ n : ℤ, (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * h θ = fourierCoeffOn hab h (n * m) := by
    intro n
    rw [fourierCoeffOn_eq_integral _ _ hab, Complex.real_smul]
    congr 1
    · push_cast; ring
    · refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [smul_eq_mul]
      rw [fourier_coe_apply]
      congr 2
      unfold azimuth
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      push_cast
      field_simp
      ring
  have hinj : Set.InjOn (fun n : ℤ => n * (m : ℤ)) S := by
    intro a _ b _ hab'
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    exact mul_right_cancel₀ hm' hab'
  calc ∑ n ∈ S, ‖(1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * h θ‖ ^ 2
        = ∑ k ∈ S.image (fun n : ℤ => n * (m : ℤ)), ‖fourierCoeffOn hab h k‖ ^ 2 := by
          rw [Finset.sum_image hinj]
          exact Finset.sum_congr rfl fun n _ => by rw [key]
    _ ≤ (2 * Real.pi - 0)⁻¹ • ∫ x in (0 : ℝ)..(2 * Real.pi), ‖h x‖ ^ 2 :=
          sum_le_hasSum _ (fun _ _ => by positivity) hsum
    _ = (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖h θ‖ ^ 2 := by
          rw [smul_eq_mul, sub_zero, one_div]

theorem tailFinite_of (hA : CoefModeStatement) (hT : AngleTailStatement) : TailFiniteStatement := by
  intro K B hK hB m hm D I O _ _ T hreg hb w F
  refine le_trans ?_ (hT K B hK hB m hm D T hreg hb w F)
  refine Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left ?_ (hb.outWeight_nonneg o)
  have hab : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmem : ∀ jl : ℕ × ℕ, MemLp (fun θ => B.coef K (fun p => T.angleField m B w o p θ) jl.1 jl.2) 2
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := fun jl => (hA K B hK m T hreg w o 0 jl.1 jl.2).2
  have hint : ∀ jl : ℕ × ℕ, IntervalIntegrable
      (fun θ => ‖B.coef K (fun p => T.angleField m B w o p θ) jl.1 jl.2‖ ^ 2) volume 0 (2 * Real.pi) := by
    intro jl
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    exact (memLp_two_iff_integrable_sq_norm (hmem jl).1).1 (hmem jl)
  rw [Finset.sum_comm, intervalIntegral.integral_finsetSum (fun jl _ => by
    by_cases hf : D < max jl.1 jl.2
    · simpa only [hf, if_true] using hint jl
    · simp only [hf, if_false]; exact intervalIntegrable_const), Finset.mul_sum]
  refine Finset.sum_le_sum fun jl _ => ?_
  by_cases hf : D < max jl.1 jl.2
  · simp only [hf, if_true]
    refine le_of_eq_of_le ?_ (modeSquareSum_le hm (T.outModes o) _ (hmem jl))
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [(hA K B hK m T hreg w o n jl.1 jl.2).1]
  · simp only [hf, if_false, Finset.sum_const_zero, intervalIntegral.integral_zero, mul_zero, le_refl]

end MeshTail

end CellAnalysis

end CellCert

end Breakdown
