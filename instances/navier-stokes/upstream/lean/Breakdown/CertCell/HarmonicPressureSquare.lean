import Breakdown.CertCell.BridgeTraceStatements

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

namespace Internal

open CellCalculus

theorem sq_lintegral_unit_le {f : ℝ → ℝ≥0∞}
    (hf : AEMeasurable f (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    (∫⁻ τ in Set.Icc (0 : ℝ) 1, f τ) ^ 2 ≤ ∫⁻ τ in Set.Icc (0 : ℝ) 1, f τ ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Icc (0 : ℝ) 1))
    Real.HolderConjugate.two_two hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have hone : (∫⁻ _ in Set.Icc (0 : ℝ) 1, (1 : ℝ≥0∞) ^ (2 : ℝ)) = 1 := by
    simp [Real.volume_Icc]
  rw [hone, ENNReal.one_rpow, mul_one] at h
  simp only [Pi.mul_apply, mul_one] at h
  have hsq : (fun a => f a ^ (2 : ℝ)) = fun a => f a ^ 2 := by
    funext a
    exact ENNReal.rpow_two (f a)
  rw [hsq] at h
  calc (∫⁻ τ in Set.Icc (0 : ℝ) 1, f τ) ^ 2
      ≤ ((∫⁻ a in Set.Icc (0 : ℝ) 1, f a ^ 2) ^ (1 / (2 : ℝ))) ^ 2 := pow_le_pow_left₀ zero_le h 2
    _ = ∫⁻ a in Set.Icc (0 : ℝ) 1, f a ^ 2 := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

theorem coefficient_sq_le (c : ℝ → ℝ) (hc : ∀ τ, |c τ| ≤ 1) (g : ℝ → Space)
    (hg : AEStronglyMeasurable g (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ENNReal.ofReal (‖∫ τ in Set.Icc (0 : ℝ) 1, c τ • g τ‖ ^ 2)
      ≤ ∫⁻ τ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (‖g τ‖ ^ 2) := by
  have hpt : ∀ x : Space, ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2 := by
    intro x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hpt]
  simp only [hpt]
  have h1 : ‖∫ τ in Set.Icc (0 : ℝ) 1, c τ • g τ‖ₑ ≤ ∫⁻ τ in Set.Icc (0 : ℝ) 1, ‖g τ‖ₑ := by
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun τ => ?_)
    rw [enorm_smul]
    have : ‖c τ‖ₑ ≤ 1 := by
      rw [← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_one.mpr (hc τ)
    calc ‖c τ‖ₑ * ‖g τ‖ₑ ≤ 1 * ‖g τ‖ₑ := by gcongr
      _ = ‖g τ‖ₑ := one_mul _
  exact (pow_le_pow_left₀ zero_le h1 2).trans (sq_lintegral_unit_le hg.enorm)

theorem pressure_swap_measurable {Pg : ℝ → Space → Space} (hp : IsPeriodicPressure Pg) :
    AEStronglyMeasurable (fun z : Space × ℝ => Pg z.2 z.1) ((volume : Measure Space).prod volume) :=
  AEStronglyMeasurable.prod_swap (f := fun z : ℝ × Space => Pg z.1 z.2) hp.measurable

theorem pressure_swap_measurable_restrict {Pg : ℝ → Space → Space} (hp : IsPeriodicPressure Pg)
    (s : Set Space) (t : Set ℝ) :
    AEStronglyMeasurable (fun z : Space × ℝ => Pg z.2 z.1) ((volume.restrict s).prod (volume.restrict t)) := by
  rw [Measure.prod_restrict]
  exact (pressure_swap_measurable hp).restrict

theorem cos_coefficient_measurable {Pg : ℝ → Space → Space} (hp : IsPeriodicPressure Pg) (ν : ℤ) :
    AEStronglyMeasurable (harmonicCos ν Pg) volume := by
  have h := pressure_swap_measurable_restrict hp Set.univ (Set.Icc (0 : ℝ) 1)
  rw [Measure.restrict_univ] at h
  have hc : AEStronglyMeasurable (fun z : Space × ℝ => Real.cos (2 * Real.pi * ν * z.2))
      ((volume : Measure Space).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    (by fun_prop : Continuous fun z : Space × ℝ => Real.cos (2 * Real.pi * ν * z.2)).aestronglyMeasurable
  exact (hc.smul h).integral_prod_right'

theorem sin_coefficient_measurable {Pg : ℝ → Space → Space} (hp : IsPeriodicPressure Pg) (ν : ℤ) :
    AEStronglyMeasurable (harmonicSin ν Pg) volume := by
  have h := pressure_swap_measurable_restrict hp Set.univ (Set.Icc (0 : ℝ) 1)
  rw [Measure.restrict_univ] at h
  have hc : AEStronglyMeasurable (fun z : Space × ℝ => Real.sin (2 * Real.pi * ν * z.2))
      ((volume : Measure Space).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    (by fun_prop : Continuous fun z : Space × ℝ => Real.sin (2 * Real.pi * ν * z.2)).aestronglyMeasurable
  exact (hc.smul h).integral_prod_right'.neg

theorem ball_square_finite {Pg : ℝ → Space → Space} (hp : IsPeriodicPressure Pg) (c : ℝ → ℝ)
    (hc : ∀ τ, |c τ| ≤ 1) (Q : Space → Space)
    (hQ : ∀ y, ‖Q y‖ = ‖∫ τ in Set.Icc (0 : ℝ) 1, c τ • Pg τ y‖) (R : ℝ) :
    ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖Q y‖ ^ 2) < ⊤ := by
  have hm := pressure_swap_measurable_restrict hp (Metric.closedBall (0 : Space) R) (Set.Icc (0 : ℝ) 1)
  have hsec := hm.prodMk_left
  have hle : ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖Q y‖ ^ 2)
      ≤ ∫⁻ y in Metric.closedBall (0 : Space) R, ∫⁻ τ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (‖Pg τ y‖ ^ 2) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hsec] with y hy
    rw [hQ y]
    exact coefficient_sq_le c hc (fun τ => Pg τ y) hy
  have hmeas : AEMeasurable (Function.uncurry fun (y : Space) (τ : ℝ) => ENNReal.ofReal (‖Pg τ y‖ ^ 2))
      ((volume.restrict (Metric.closedBall (0 : Space) R)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    (hm.norm.aemeasurable.pow_const 2).ennreal_ofReal
  rw [lintegral_lintegral_swap hmeas] at hle
  exact hle.trans_lt (hp.local_square R)

end Internal

open CellCalculus Internal

theorem harmonicPressureSquare : HarmonicPressureSquareHolds := by
  intro Pg hp ν
  refine ⟨⟨cos_coefficient_measurable hp ν, fun R => ?_⟩, ⟨sin_coefficient_measurable hp ν, fun R => ?_⟩⟩
  · refine ball_square_finite hp (fun τ => Real.cos (2 * Real.pi * ν * τ)) (fun τ => Real.abs_cos_le_one _)
      (harmonicCos ν Pg) (fun y => rfl) R
  · refine ball_square_finite hp (fun τ => Real.sin (2 * Real.pi * ν * τ)) (fun τ => Real.abs_sin_le_one _)
      (harmonicSin ν Pg) (fun y => by simp only [harmonicSin, norm_neg]) R

end SideTrace

end CertCell

end Breakdown
