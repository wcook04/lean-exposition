import Breakdown.CellReduction.AdjointRemainderAzimuthalParts

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace AzimuthalParts

namespace Internal

namespace TimeSum

theorem sq_norm_eq_mul_conj (z : ℂ) : (((‖z‖ ^ 2 : ℝ)) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem integral_phase (n : ℤ) :
    ∫ σ in (0 : ℝ)..1, Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (σ : ℂ) * Complex.I) =
      if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn
    simp
  · have hc : (2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I) ≠ 0 := by
      have h1 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
      have h2 : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 hn
      simp [h1, h2, Complex.I_ne_zero]
    have hrw : ∀ σ : ℝ, Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (σ : ℂ) * Complex.I) =
        Complex.exp ((2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I) * (σ : ℂ)) := by
      intro σ
      ring_nf
    simp_rw [hrw]
    rw [integral_exp_mul_complex hc]
    have he : Complex.exp ((2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I n]
      congr 1
      push_cast
      ring
    rw [he]
    simp

theorem phase_mul_conj (m n : ℤ) (σ : ℝ) (c d : ℂ) :
    Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * (σ : ℂ) * Complex.I) * c *
        (starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (σ : ℂ) * Complex.I) * d) =
      c * (starRingEnd ℂ) d *
        Complex.exp (2 * (Real.pi : ℂ) * (((m - n : ℤ)) : ℂ) * (σ : ℂ) * Complex.I) := by
  rw [map_mul, ← Complex.exp_conj]
  have hconj : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * (n : ℂ) * (σ : ℂ) * Complex.I) =
      -(2 * (Real.pi : ℂ) * (n : ℂ) * (σ : ℂ) * Complex.I) := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [hconj]
  have hsplit : Complex.exp (2 * (Real.pi : ℂ) * (((m - n : ℤ)) : ℂ) * (σ : ℂ) * Complex.I) =
      Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * (σ : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (σ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit]
  ring

theorem modeSum_integral {N : ℕ} (f : Fin N → ℤ) (S : Finset (Fin N)) (hf : Set.InjOn f S)
    (c : Fin N → ℂ) :
    ∫ σ in (0 : ℝ)..1,
        (((‖∑ p ∈ S, Complex.exp (2 * (Real.pi : ℂ) * (f p : ℂ) * (σ : ℂ) * Complex.I) * c p‖ ^ 2 : ℝ)) : ℂ) =
      (((∑ p ∈ S, ‖c p‖ ^ 2 : ℝ)) : ℂ) := by
  have hexp : ∀ σ : ℝ,
      (((‖∑ p ∈ S, Complex.exp (2 * (Real.pi : ℂ) * (f p : ℂ) * (σ : ℂ) * Complex.I) * c p‖ ^ 2 : ℝ)) : ℂ) =
        ∑ p ∈ S, ∑ q ∈ S, c p * (starRingEnd ℂ) (c q) *
          Complex.exp (2 * (Real.pi : ℂ) * (((f p - f q : ℤ)) : ℂ) * (σ : ℂ) * Complex.I) := by
    intro σ
    rw [sq_norm_eq_mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    exact phase_mul_conj (f p) (f q) σ (c p) (c q)
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum]
  · have hin : ∀ p ∈ S, (∫ σ in (0 : ℝ)..1, ∑ q ∈ S, c p * (starRingEnd ℂ) (c q) *
          Complex.exp (2 * (Real.pi : ℂ) * (((f p - f q : ℤ)) : ℂ) * (σ : ℂ) * Complex.I)) =
        (((‖c p‖ ^ 2 : ℝ)) : ℂ) := by
      intro p hp
      rw [intervalIntegral.integral_finsetSum]
      · simp_rw [intervalIntegral.integral_const_mul, integral_phase]
        have hiff : ∀ q ∈ S, (f p - f q = 0 ↔ p = q) := by
          intro q hq
          rw [sub_eq_zero]
          exact ⟨fun h => hf hp hq h, fun h => h ▸ rfl⟩
        rw [Finset.sum_congr rfl (fun q hq => by rw [if_congr (hiff q hq) rfl rfl])]
        simp only [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq S p, if_pos hp, sq_norm_eq_mul_conj]
      · intro q _
        exact (by fun_prop : Continuous fun σ : ℝ => c p * (starRingEnd ℂ) (c q) *
          Complex.exp (2 * (Real.pi : ℂ) * (((f p - f q : ℤ)) : ℂ) * (σ : ℂ) * Complex.I)).intervalIntegrable _ _
    rw [Finset.sum_congr rfl hin]
    push_cast
    rfl
  · intro p _
    exact (by fun_prop : Continuous fun σ : ℝ => ∑ q ∈ S, c p * (starRingEnd ℂ) (c q) *
      Complex.exp (2 * (Real.pi : ℂ) * (((f p - f q : ℤ)) : ℂ) * (σ : ℂ) * Complex.I)).intervalIntegrable _ _

theorem modeSum_lintegral {N : ℕ} (f : Fin N → ℤ) (S : Finset (Fin N)) (hf : Set.InjOn f S)
    (c : Fin N → ℂ) (w : ℝ) (hw : 0 ≤ w) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (w *
        ‖∑ p ∈ S, Complex.exp (2 * (Real.pi : ℂ) * (f p : ℂ) * (σ : ℂ) * Complex.I) * c p‖ ^ 2) =
      ENNReal.ofReal (w * ∑ p ∈ S, ‖c p‖ ^ 2) := by
  have hcont : Continuous fun σ : ℝ => w *
      ‖∑ p ∈ S, Complex.exp (2 * (Real.pi : ℂ) * (f p : ℂ) * (σ : ℂ) * Complex.I) * c p‖ ^ 2 := by
    fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)
    (Filter.Eventually.of_forall (fun σ => by positivity))]
  congr 1
  rw [integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  congr 1
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  exact modeSum_integral f S hf c

end TimeSum

end Internal

theorem timeModeSum : TimeModeSumHolds := by
  intro N a f S hf ha
  set b : Fin N → Space → ℂ := fun p => (ha p).mk (a p)
  have hb : ∀ p, Measurable (b p) := fun p => (ha p).stronglyMeasurable_mk.measurable
  have hab : ∀ᵐ y ∂(volume : Measure Space), ∀ p, a p y = b p y :=
    ae_all_iff.2 (fun p => (ha p).ae_eq_mk)
  have hleft : ∀ σ : ℝ, (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 *
      ‖∑ p ∈ S, Complex.exp (2 * (Real.pi : ℂ) * (f p : ℂ) * (σ : ℂ) * Complex.I) * a p y‖ ^ 2)) =
      ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 *
      ‖∑ p ∈ S, Complex.exp (2 * (Real.pi : ℂ) * (f p : ℂ) * (σ : ℂ) * Complex.I) * b p y‖ ^ 2) := by
    intro σ
    apply lintegral_congr_ae
    filter_upwards [hab] with y hy
    simp only [hy]
  have hright : ∀ p, (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖a p y‖ ^ 2)) =
      ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖b p y‖ ^ 2) := by
    intro p
    apply lintegral_congr_ae
    filter_upwards [hab] with y hy
    simp only [hy]
  simp_rw [hleft, hright]
  have hjoint : Measurable (Function.uncurry fun (σ : ℝ) (y : Space) => ENNReal.ofReal (‖y‖ ^ 2 *
      ‖∑ p ∈ S, Complex.exp (2 * (Real.pi : ℂ) * (f p : ℂ) * (σ : ℂ) * Complex.I) * b p y‖ ^ 2)) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul
    · exact (continuous_norm.comp continuous_snd).measurable.pow_const 2
    · apply Measurable.pow_const
      apply Measurable.norm
      apply Finset.measurable_sum
      intro p _
      apply Measurable.mul
      · exact (by fun_prop : Continuous fun z : ℝ × Space =>
          Complex.exp (2 * (Real.pi : ℂ) * (f p : ℂ) * (z.1 : ℂ) * Complex.I)).measurable
      · exact (hb p).comp measurable_snd
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  have hpt : ∀ y : Space, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (‖y‖ ^ 2 *
      ‖∑ p ∈ S, Complex.exp (2 * (Real.pi : ℂ) * (f p : ℂ) * (σ : ℂ) * Complex.I) * b p y‖ ^ 2)) =
      ∑ p ∈ S, ENNReal.ofReal (‖y‖ ^ 2 * ‖b p y‖ ^ 2) := by
    intro y
    rw [Internal.TimeSum.modeSum_lintegral f S hf (fun p => b p y) (‖y‖ ^ 2) (by positivity),
      Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
  simp_rw [hpt]
  rw [lintegral_finsetSum]
  intro p _
  apply ENNReal.measurable_ofReal.comp
  exact ((continuous_norm.measurable.pow_const 2).mul ((hb p).norm.pow_const 2))

end AzimuthalParts

end AdjointDefect

end Breakdown
