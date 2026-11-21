import Breakdown.Frac.StTorusShell
import Breakdown.Torus.HeatComparisonTorusSide

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracTorusShellSeries.Internal

open TorusShellSeries.Internal

theorem simScale_pos {α μ : ℝ} (hμ : 0 < μ) : 0 < simScale α μ := Real.rpow_pos_of_pos hμ _

theorem sqrt_simScale_rpow {α μ : ℝ} (hα : 0 < α) (hμ : 0 < μ) :
    Real.sqrt (simScale α μ) ^ (2 * α) = μ := by
  have e : 1 / α * (1 / 2) * (2 * α) = 1 := by field_simp
  rw [Real.sqrt_eq_rpow, simScale, ← Real.rpow_mul hμ.le, ← Real.rpow_mul hμ.le, e, Real.rpow_one]

theorem simScale_quarter {α μ : ℝ} (hα : 0 < α) (hμ : 0 < μ) :
    simScale α μ ^ (1 / 4 : ℝ) * μ ^ (-(1 / (4 * α))) = 1 := by
  rw [simScale, ← Real.rpow_mul hμ.le, ← Real.rpow_add hμ]
  have e : 1 / α * (1 / 4) + -(1 / (4 * α)) = 0 := by field_simp; ring
  rw [e, Real.rpow_zero]

theorem fracFactor_eq {α μ : ℝ} (hα : 0 < α) (hμ : 0 < μ) (t : ℝ) (k : Lattice) :
    fracLatticeFactor α (μ * t) k = Freq.fracHeatFactor α t (Real.sqrt (simScale α μ) • freq k) := by
  have e : max (μ * t) 0 = μ * max t 0 := by rw [mul_max_of_nonneg _ _ hμ.le, mul_zero]
  have hs := Real.sqrt_nonneg (simScale α μ)
  have e2 : 2 * π * ‖Real.sqrt (simScale α μ) • freq k‖ = Real.sqrt (simScale α μ) * (2 * π * ‖freq k‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
    ring
  rw [fracLatticeFactor, Freq.fracHeatFactor, e2,
    Real.mul_rpow hs (by positivity), sqrt_simScale_rpow hα hμ, e]
  congr 1
  ring

theorem fracLatticeFactor_nonneg (α t : ℝ) (k : Lattice) : 0 ≤ fracLatticeFactor α t k :=
  (Real.exp_pos _).le

theorem one_le_norm_freq {k : Lattice} (hk : k ≠ 0) : 1 ≤ ‖freq k‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hk
  have hi' : k i ≠ 0 := by simpa using hi
  have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast Int.one_le_abs hi'
  have h2 : (1 : ℝ) ≤ (k i : ℝ) ^ 2 := by nlinarith [sq_abs (k i : ℝ), abs_nonneg (k i : ℝ)]
  have hs : (k i : ℝ) ^ 2 ≤ ‖freq k‖ ^ 2 := by
    rw [FreqTrSeries.Internal.norm_freq_sq]
    exact Finset.single_le_sum (f := fun j => (k j : ℝ) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  by_contra h
  have h' := not_le.1 h
  nlinarith [norm_nonneg (freq k)]

theorem fracLatticeFactor_le_heat {α : ℝ} (hα : 1 ≤ α) (t : ℝ) (k : Lattice) :
    fracLatticeFactor α t k ≤ heatFactor t k := by
  unfold fracLatticeFactor heatFactor
  apply Real.exp_le_exp.2
  have hm := le_max_right t 0
  have key : (2 * π * ‖freq k‖) ^ 2 ≤ (2 * π * ‖freq k‖) ^ (2 * α) := by
    by_cases hk : k = 0
    · have h0 : freq (0 : Lattice) = 0 := freq_eq_zero.2 rfl
      subst hk
      rw [h0, norm_zero, mul_zero, Real.zero_rpow (by linarith : (2 * α) ≠ 0)]
      simp
    · have h1 := one_le_norm_freq hk
      have h2 : (1 : ℝ) ≤ 2 * π * ‖freq k‖ := by nlinarith [Real.pi_gt_three]
      have := Real.rpow_le_rpow_of_exponent_le h2 (by linarith : (2 : ℝ) ≤ 2 * α)
      rwa [Real.rpow_two] at this
  have e : 4 * π ^ 2 * ‖freq k‖ ^ 2 * max t 0 = (2 * π * ‖freq k‖) ^ 2 * max t 0 := by ring
  rw [e]
  exact neg_le_neg (mul_le_mul_of_nonneg_right key hm)

theorem coeff_fracSourceOp {α μ τ : ℝ} (hF : FracTorusForceAlgebra α) (hE : FracSourceOpExists α)
    (hμ : 0 < μ) (hτ : 0 < τ) (A : Freq.L2R) (k : Lattice) :
    coeff (fracSourceOp α μ τ A) k = fracLatticeFactor α (μ * τ) k •
      divFree k (freqTrCoef (fun x => (A : Space → Space) (simCoord (simScale α μ) x)) k) := by
  have e : fracSourceOp α μ τ A =
      fracTorusForce α (μ * τ) (fun x => (A : Space → Space) (simCoord (simScale α μ) x)) := by
    rw [fracSourceOp, dif_pos (hE μ τ), (hE μ τ).choose_spec A, fracSourceFun, if_pos hμ]
  rw [e, hF.1, fracTorusForceCoef, if_pos (mul_pos hμ hτ)]

theorem source_value {α : ℝ} (hα : 0 < α) (hC : SourceCoefFormula) (hF : FracTorusForceAlgebra α)
    (hE : FracSourceOpExists α) {b' μ τ : ℝ} (hμ : 0 < μ) (hτ : 0 < τ)
    (hb' : Real.sqrt (simScale α μ) * b' ≤ 1 / 4) (A : Freq.L2R)
    (hA : ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) (y : Space) (k : Lattice) :
    character (-k) (center + Real.sqrt (simScale α μ) • y) •
        ((simScale α μ ^ (1 / 4 : ℝ)) • coeff ((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ A) k) =
      (Real.sqrt (simScale α μ) ^ 3) •
        fracValueDensity α τ (⇑A) y (Real.sqrt (simScale α μ) • freq k) := by
  have hμ' := simScale_pos (α := α) hμ
  rw [coeff_smul, coeff_fracSourceOp hF hE hμ hτ, hC b' (simScale α μ) hμ' hb' A hA k,
    fracFactor_eq hα hμ, divFree_eq (Real.sqrt_pos.2 hμ'), fracValueDensity,
    ← Complex.coe_smul (simScale α μ ^ (3 / 2 : ℝ)), divFreeVec_csmul, divFreeVec_csmul]
  have e1 := character_shift k (Real.sqrt (simScale α μ)) y
  have e2 : ((simScale α μ ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((μ ^ (-(1 / (4 * α))) : ℝ) : ℂ) = 1 := by
    exact_mod_cast simScale_quarter hα hμ
  have e3 : ((simScale α μ ^ (3 / 2 : ℝ) : ℝ) : ℂ) = ((Real.sqrt (simScale α μ) ^ 3 : ℝ) : ℂ) := by
    rw [rpow_three_halves hμ']
  simp only [← Complex.coe_smul, smul_smul]
  congr 1
  linear_combination
    (((Freq.fracHeatFactor α τ (Real.sqrt (simScale α μ) • freq k) : ℝ) : ℂ) *
      ((simScale α μ ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
      ((simScale α μ ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((μ ^ (-(1 / (4 * α))) : ℝ) : ℂ)) * e1 +
    (((Freq.fracHeatFactor α τ (Real.sqrt (simScale α μ) • freq k) : ℝ) : ℂ) *
      ((simScale α μ ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
      expChar y (Real.sqrt (simScale α μ) • freq k)) * e2 +
    (((Freq.fracHeatFactor α τ (Real.sqrt (simScale α μ) • freq k) : ℝ) : ℂ) *
      expChar y (Real.sqrt (simScale α μ) • freq k)) * e3

theorem norm_coeff_source_le {α μ τ : ℝ} (hα : 1 ≤ α) (hF : FracTorusForceAlgebra α)
    (hE : FracSourceOpExists α) (hμ : 0 < μ) (hτ : 0 < τ) (A : Freq.L2R) (k : Lattice) :
    ‖coeff ((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ A) k‖ ≤
      (μ ^ (-(1 / (4 * α))) *
        (2 * ∫ x in cell, ‖complexify ((A : Space → Space) (simCoord (simScale α μ) x))‖)) *
        heatFactor (μ * τ) k := by
  rw [coeff_smul, coeff_fracSourceOp hF hE hμ hτ, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hμ _),
    abs_of_nonneg (fracLatticeFactor_nonneg _ _ _)]
  have h1 := (Breakdown.Periodic.Internal.norm_divFree_le k
    (freqTrCoef (fun x => (A : Space → Space) (simCoord (simScale α μ) x)) k)).trans
    (mul_le_mul_of_nonneg_left (FreqTrSeries.Internal.norm_freqTrCoef_le k) zero_le_two)
  have h2 := fracLatticeFactor_le_heat hα (μ * τ) k
  have h3 := Real.rpow_pos_of_pos hμ (-(1 / (4 * α)))
  have h4 := mul_le_mul h2 h1 (norm_nonneg _) (Breakdown.Periodic.Internal.heatFactor_nonneg (μ * τ) k)
  calc μ ^ (-(1 / (4 * α))) * (fracLatticeFactor α (μ * τ) k *
        ‖divFree k (freqTrCoef (fun x => (A : Space → Space) (simCoord (simScale α μ) x)) k)‖) ≤
      μ ^ (-(1 / (4 * α))) * (heatFactor (μ * τ) k *
        (2 * ∫ x in cell, ‖complexify ((A : Space → Space) (simCoord (simScale α μ) x))‖)) :=
        mul_le_mul_of_nonneg_left h4 h3.le
    _ = _ := by ring

theorem free_value {α : ℝ} (hα : 0 < α) (hH : FracTorusHeatAlgebra α) (hT : TransplantCoefFormula)
    (hD : CoefDeriv) (hTS : TransplantSmooth)
    {φ : Space → Space} (hφ : IsTestField φ) {b' μ τ : ℝ} (hμ : 0 < μ) (hsh : IsShellScale (simScale α μ) b')
    (hsupp : tsupport φ ⊆ Metric.closedBall 0 b') (y : Space) (k : Lattice) :
    character (-k) (center + Real.sqrt (simScale α μ) • y) •
        ((simScale α μ ^ (1 / 4 : ℝ)) • coeff ((simScale α μ ^ (1 / 4 : ℝ)) •
          fracTorusHeat α (μ * τ) (toV (transplantField (simScale α μ) φ))) k) =
      (Real.sqrt (simScale α μ) ^ 3) • fracFreeDensity α τ φ y (Real.sqrt (simScale α μ) • freq k) := by
  obtain ⟨hs1, hs2, hs3, -⟩ := hTS φ (simScale α μ) b' hφ.1 hφ.2.2 hsh hsupp
  have hμ' := hsh.1
  have hb4 : Real.sqrt (simScale α μ) * b' ≤ 1 / 4 := by linarith [hsh.2.2.2]
  rw [coeff_smul, hH.1, FreqTrSeries.Internal.coeff_toV hD hs1 hs2 hs3,
    hT φ hφ b' (simScale α μ) hμ' hb4 hsupp k, fracFactor_eq hα hμ, fracFreeDensity]
  have e1 := character_shift k (Real.sqrt (simScale α μ)) y
  have e2 : ((simScale α μ ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((simScale α μ ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
      ((simScale α μ : ℝ) : ℂ) = ((Real.sqrt (simScale α μ) ^ 3 : ℝ) : ℂ) := by
    rw [← rpow_free hμ']
    push_cast
    ring
  simp only [← Complex.coe_smul, smul_smul]
  congr 1
  linear_combination
    (((Freq.fracHeatFactor α τ (Real.sqrt (simScale α μ) • freq k) : ℝ) : ℂ) *
      ((simScale α μ ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
      ((simScale α μ ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((simScale α μ : ℝ) : ℂ)) * e1 +
    (((Freq.fracHeatFactor α τ (Real.sqrt (simScale α μ) • freq k) : ℝ) : ℂ) *
      expChar y (Real.sqrt (simScale α μ) • freq k)) * e2

end FracTorusShellSeries.Internal

open TorusShellSeries.Internal FracTorusShellSeries.Internal

theorem fracTorusSourceSeries_of (α : ℝ) (hα : 1 < α) (hP : TorusSeriesPointwise)
    (hC : SourceCoefFormula) (hF : FracTorusForceAlgebra α) (hE : FracSourceOpExists α) :
    FracTorusSourceSeries α := by
  intro b b' μ τ hμ _ hsh hb' hτ A hA
  obtain ⟨hμ', -, -, hhb⟩ := hsh
  have hα0 : 0 < α := by linarith
  have hh : 0 < Real.sqrt (simScale α μ) := Real.sqrt_pos.2 hμ'
  have hval := source_value hα0 hC hF hE hμ hτ hb' A hA
  have hM : 0 ≤ μ ^ (-(1 / (4 * α))) *
      (2 * ∫ x in cell, ‖complexify ((A : Space → Space) (simCoord (simScale α μ) x))‖) :=
    mul_nonneg (Real.rpow_nonneg hμ.le _) (mul_nonneg zero_le_two (integral_nonneg fun _ => norm_nonneg _))
  have hb := norm_coeff_source_le hα.le hF hE hμ hτ A
  have hsum : Summable fun k => ‖coeff ((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ A) k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb ((summable_heat (mul_pos hμ hτ)).mul_left _)
  refine ⟨series_pullback 6 _ (hP _ hsum).2 hh hhb _ hval, fun j => ?_⟩
  refine series_pullback 2 _ (hP _ (summable_grad_of_bound hM (mul_pos hμ hτ) hb j)).1 hh hhb
    (fracGradDensity α j τ A) fun y k => ?_
  rw [rpow_grad hμ']
  exact grad_identity j hval y k

theorem fracTorusFreeSeries_of (α : ℝ) (hα : 1 < α) (hP : TorusSeriesPointwise)
    (hT : TransplantCoefFormula) (hD : CoefDeriv) (hTS : TransplantSmooth) (hS : StepIntegral)
    (hH : FracTorusHeatAlgebra α) (hFD : FracFreeDensityBounds α) : FracTorusFreeSeries α := by
  intro φ hφ b b' μ τ hμ _ hsh hsh' hτ hsupp
  have hα0 : 0 < α := by linarith
  have hμ' := hsh.1
  have hh : 0 < Real.sqrt (simScale α μ) := Real.sqrt_pos.2 hμ'
  have hs : 0 < simScale α μ ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hμ' _
  have hs' : 0 < simScale α μ ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hμ' _
  have hval := free_value hα0 hH hT hD hTS hφ (τ := τ) hμ hsh' hsupp
  obtain ⟨K, hK⟩ := hFD φ hφ 0 (1 / (τ + 1)) (by positivity)
  have hτI : τ ∈ Icc 0 (1 / (τ + 1))⁻¹ := ⟨hτ, by rw [one_div, inv_inv]; linarith⟩
  have hy0 : ‖(0 : Space)‖ ≤ 0 := by simp
  have hsq := (hS _ hh).2.2
  have hsum := summable_of_density hh hs hval (fun ξ => (hK 0 hy0 τ hτI ξ).1) hsq
  refine ⟨series_pullback 6 _ (hP _ hsum).2 hh hsh.2.2.2 _ hval, fun j => ?_⟩
  have hgrad : ∀ y k, character (-k) (center + Real.sqrt (simScale α μ) • y) •
      ((simScale α μ ^ (3 / 4 : ℝ)) • gradCoef j ((simScale α μ ^ (1 / 4 : ℝ)) •
        fracTorusHeat α (μ * τ) (toV (transplantField (simScale α μ) φ))) k) =
      (Real.sqrt (simScale α μ) ^ 3) •
        fracFreeGradDensity α j τ φ y (Real.sqrt (simScale α μ) • freq k) := fun y k => by
    rw [rpow_grad hμ']
    exact grad_identity j hval y k
  have hgsum := summable_of_density hh hs' hgrad (fun ξ => (hK 0 hy0 τ hτI ξ).2 j) hsq
  exact series_pullback 2 _ (hP _ hgsum).1 hh hsh.2.2.2 (fracFreeGradDensity α j τ φ) hgrad

end Breakdown.Periodic
