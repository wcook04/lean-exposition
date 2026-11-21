import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.UniformApproximation

open Filter MeasureTheory Set
open scoped Topology

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem tendsto_intervalIntegral_of_uniform
    {T t : ℝ} (ht : t ∈ Icc 0 T) {F : ℕ → ℝ → E} {f : ℝ → E}
    (hF : TendstoUniformlyOn F f atTop (Icc 0 T))
    (hFc : ∀ j, ContinuousOn (F j) (Icc 0 T)) (hfc : ContinuousOn f (Icc 0 T)) :
    Tendsto (fun j => ∫ s in (0 : ℝ)..t, F j s) atTop (𝓝 (∫ s in (0 : ℝ)..t, f s)) := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hInt (j : ℕ) : IntervalIntegrable (F j) volume 0 t :=
    ((hFc j).mono hsub).intervalIntegrable_of_Icc ht.1
  have hfInt : IntervalIntegrable f volume 0 t :=
    (hfc.mono hsub).intervalIntegrable_of_Icc ht.1
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ht' : 0 < t + 1 := add_pos_of_nonneg_of_pos ht.1 zero_lt_one
  have hratio : 0 < ε / (t + 1) := div_pos hε ht'
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hF _ hratio] with j hj
  rw [dist_eq_norm, ← intervalIntegral.integral_sub (hInt j) hfInt]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (f := fun s => F j s - f s) (C := ε / (t + 1)) (fun s hs => by
      rw [uIoc_of_le ht.1] at hs
      rw [← dist_eq_norm, dist_comm]
      exact (hj s ⟨hs.1.le, hs.2.trans ht.2⟩).le)
  calc
    ‖∫ s in (0 : ℝ)..t, F j s - f s‖ ≤ (ε / (t + 1)) * t := by
      simpa only [sub_zero, abs_of_nonneg ht.1] using hbound
    _ < (ε / (t + 1)) * (t + 1) := mul_lt_mul_of_pos_left
      (lt_add_of_pos_right t zero_lt_one) hratio
    _ = ε := div_mul_cancel₀ _ ht'.ne'

variable [CompleteSpace E]

/-- The time-integral limit passage for the uniformly vanishing residual in
Proposition 8.1. The derivative is taken within the closed interval, including
at both endpoints. -/
theorem integratedLimit_of_uniformConvergence
    {T : ℝ} (hT : 0 ≤ T) {U D R : ℕ → ℝ → E} {u d : ℝ → E}
    (hU : TendstoUniformlyOn U u atTop (Icc 0 T))
    (hD : TendstoUniformlyOn D d atTop (Icc 0 T))
    (hR : TendstoUniformlyOn R (fun _ => 0) atTop (Icc 0 T))
    (hDc : ∀ j, ContinuousOn (D j) (Icc 0 T))
    (hRc : ∀ j, ContinuousOn (R j) (Icc 0 T))
    (hEq : ∀ j t, t ∈ Icc 0 T →
      U j t = U j 0 - (∫ s in (0 : ℝ)..t, D j s) + ∫ s in (0 : ℝ)..t, R j s) :
    (∀ t ∈ Icc 0 T, u t = u 0 - ∫ s in (0 : ℝ)..t, d s) ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt u (-d t) (Icc 0 T) t := by
  have hdc : ContinuousOn d (Icc 0 T) := hD.continuousOn (Frequently.of_forall hDc)
  have hlimit (t : ℝ) (ht : t ∈ Icc 0 T) : u t = u 0 - ∫ s in (0 : ℝ)..t, d s := by
    have hinit := hU.tendsto_at (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)
    have hDInt := tendsto_intervalIntegral_of_uniform ht hD hDc hdc
    have hRInt := tendsto_intervalIntegral_of_uniform ht hR hRc continuousOn_const
    have hRhs := (hinit.sub hDInt).add hRInt
    simpa only [intervalIntegral.integral_zero, add_zero] using
      tendsto_nhds_unique_of_eventuallyEq (hU.tendsto_at ht) hRhs
        (Eventually.of_forall fun j => hEq j t ht)
  refine ⟨hlimit, fun t ht => ?_⟩
  have : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  have hInt : IntervalIntegrable d volume 0 t :=
    (hdc.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hder : HasDerivWithinAt (fun v => ∫ s in (0 : ℝ)..v, d s) (d t) (Icc 0 T) t :=
    intervalIntegral.integral_hasDerivWithinAt_right hInt
      (hdc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hdc t ht)
  exact (hder.const_sub (u 0)).congr_of_mem hlimit ht

end TorusEuler
