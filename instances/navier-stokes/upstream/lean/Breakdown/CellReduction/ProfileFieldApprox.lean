import Breakdown.CellReduction.ReductionStatements
import Breakdown.CellReduction.SliceSupNormMollify
import Breakdown.FracCell.ReductionAdjointMollifySecondApprox
import Breakdown.CellReduction.AdjointTestDensityCutoff

open scoped ContDiff ENNReal NNReal Convolution
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal.ProfileFieldApprox

open CertCell.TailBand.SquareInternal (roundBump roundBump_nonneg roundBump_le_one scaledBump
  scaledBump_contDiff scaledBump_hasCompactSupport scaledBump_eq_one continuous_matSq')
open AdjointDefect.Internal.TestDensity (round_bounds cut_spaceDeriv cut_spaceDeriv2
  cut_spaceDeriv_near cut_spaceDeriv_far)
open Breakdown.CertReduction.Internal.WeakFieldMollify (integrable_of_lintegral_lt kernel_pow_integral
  fderiv_kernel_apply second_diag_eq)
open CellCert.Reduction.MollifySecondApproxInternal (kernelBump conv_sq_tendsto diff_sq_integrable)

def tailSet (R : ℝ) : Set Space := {y | R ≤ ‖y‖}

def ringSet (R : ℝ) : Set Space := {y | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}

def smoothed (w : Space → Space) (n : ℕ) : Space → Space :=
  (kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w

theorem tailSet_measurable (R : ℝ) : MeasurableSet (tailSet R) :=
  measurableSet_le measurable_const continuous_norm.measurable

theorem ind_nonneg (S : Set Space) (y : Space) : 0 ≤ S.indicator (fun _ => (1 : ℝ)) y :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) y

theorem ind_le_one (S : Set Space) (y : Space) : S.indicator (fun _ => (1 : ℝ)) y ≤ 1 := by
  by_cases h : y ∈ S
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]; exact zero_le_one

theorem sq_le_split {t s : ℝ} (hs : 0 < s) : t ^ 2 ≤ s + t ^ 6 / s ^ 2 := by
  by_cases h : t ^ 2 ≤ s
  · have : 0 ≤ t ^ 6 / s ^ 2 := by positivity
    linarith
  · replace h := not_le.1 h
    have h1 : s ^ 2 ≤ (t ^ 2) ^ 2 := pow_le_pow_left₀ hs.le h.le 2
    have h2 : t ^ 2 * s ^ 2 ≤ t ^ 6 := by
      have e : t ^ 6 = t ^ 2 * (t ^ 2) ^ 2 := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : t ^ 2 ≤ t ^ 6 / s ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      exact h2
    linarith

theorem add_sq_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem add_three_sq_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

theorem norm_add_sq_le (x y : Space) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2).trans (add_sq_le_two _ _)

theorem norm_unit (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem matSq_nonneg_map (X : Space →L[ℝ] Space) : 0 ≤ matSq X :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem matSq_add_le (X Y : Space →L[ℝ] Space) : matSq (X + Y) ≤ 2 * matSq X + 2 * matSq Y := by
  simp only [matSq, ContinuousLinearMap.add_apply, Fin.sum_univ_three]
  linarith [norm_add_sq_le (X (unitVector 0)) (Y (unitVector 0)),
    norm_add_sq_le (X (unitVector 1)) (Y (unitVector 1)),
    norm_add_sq_le (X (unitVector 2)) (Y (unitVector 2))]

theorem apply_unit_sq_le (L : Space →L[ℝ] ℝ) (i : Fin 3) : (L (unitVector i)) ^ 2 ≤ ‖L‖ ^ 2 := by
  have h := L.le_opNorm (unitVector i)
  rw [norm_unit, mul_one, Real.norm_eq_abs] at h
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

theorem apply_unit_two_le (B : Space →L[ℝ] Space →L[ℝ] ℝ) (i : Fin 3) :
    |B (unitVector i) (unitVector i)| ≤ ‖B‖ := by
  have h := B.le_opNorm₂ (unitVector i) (unitVector i)
  rw [norm_unit, mul_one, mul_one, Real.norm_eq_abs] at h
  exact h

theorem cut_first_le {R c : ℝ} (hR : 0 < R)
    (hc : ∀ x, ‖fderiv ℝ roundBump x‖ ≤ c ∧ ‖fderiv ℝ (fderiv ℝ roundBump) x‖ ≤ c) (y : Space) :
    ‖fderiv ℝ (scaledBump R) y‖ ≤ R⁻¹ * c := by
  rw [cut_spaceDeriv]
  dsimp only
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
  exact mul_le_mul_of_nonneg_left (hc _).1 (inv_nonneg.2 hR.le)

theorem cut_second_le {R c : ℝ} (hR : 1 ≤ R)
    (hc : ∀ x, ‖fderiv ℝ roundBump x‖ ≤ c ∧ ‖fderiv ℝ (fderiv ℝ roundBump) x‖ ≤ c) (y : Space) :
    ‖fderiv ℝ (fderiv ℝ (scaledBump R)) y‖ ≤ R⁻¹ * c := by
  have hR0 : 0 < R := by linarith
  have h1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0).1
  rw [cut_spaceDeriv2, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc R⁻¹ * R⁻¹ * ‖fderiv ℝ (fderiv ℝ roundBump) (R⁻¹ • y)‖ ≤ R⁻¹ * R⁻¹ * c :=
        mul_le_mul_of_nonneg_left (hc _).2 (by positivity)
    _ ≤ R⁻¹ * 1 * c := by gcongr
    _ = R⁻¹ * c := by ring

theorem cut_first_zero {R : ℝ} (hR : 0 < R) {y : Space} (hy : y ∉ ringSet R) :
    fderiv ℝ (scaledBump R) y = 0 := by
  simp only [ringSet, Set.mem_setOf_eq, not_and_or, not_le] at hy
  rcases hy with h | h
  · exact cut_spaceDeriv_near hR h
  · exact cut_spaceDeriv_far hR h

theorem cut_second_zero {R : ℝ} (hR : 0 < R) {y : Space} (hy : y ∉ ringSet R) :
    fderiv ℝ (fderiv ℝ (scaledBump R)) y = 0 := by
  simp only [ringSet, Set.mem_setOf_eq, not_and_or, not_le] at hy
  rcases hy with h | h
  · have e : fderiv ℝ (scaledBump R) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds h] with z hz
      exact cut_spaceDeriv_near hR hz
    rw [e.fderiv_eq]
    exact fderiv_const_apply 0
  · have e : fderiv ℝ (scaledBump R) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds h] with z hz
      exact cut_spaceDeriv_far hR hz
    rw [e.fderiv_eq]
    exact fderiv_const_apply 0

theorem cut_sub_one_sq {R : ℝ} (hR : 0 < R) (y : Space) :
    (scaledBump R y - 1) ^ 2 ≤ (tailSet R).indicator (fun _ => (1 : ℝ)) y := by
  by_cases h : ‖y‖ ≤ R
  · rw [scaledBump_eq_one hR h, sub_self, zero_pow two_ne_zero]
    exact ind_nonneg _ y
  · replace h := not_le.1 h
    rw [Set.indicator_of_mem (show y ∈ tailSet R from h.le)]
    have h0 : 0 ≤ scaledBump R y := roundBump_nonneg _
    have h1 : scaledBump R y ≤ 1 := roundBump_le_one _
    nlinarith

theorem cut_first_sq {R c : ℝ} (hR : 0 < R)
    (hc : ∀ x, ‖fderiv ℝ roundBump x‖ ≤ c ∧ ‖fderiv ℝ (fderiv ℝ roundBump) x‖ ≤ c) (y : Space) :
    ‖fderiv ℝ (scaledBump R) y‖ ^ 2 ≤ (R⁻¹ * c) ^ 2 * (ringSet R).indicator (fun _ => (1 : ℝ)) y := by
  by_cases h : y ∈ ringSet R
  · rw [Set.indicator_of_mem h, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) (cut_first_le hR hc y) 2
  · rw [cut_first_zero hR h, Set.indicator_of_notMem h]
    simp

theorem cut_second_sq {R c : ℝ} (hR : 1 ≤ R)
    (hc : ∀ x, ‖fderiv ℝ roundBump x‖ ≤ c ∧ ‖fderiv ℝ (fderiv ℝ roundBump) x‖ ≤ c) (y : Space) :
    ‖fderiv ℝ (fderiv ℝ (scaledBump R)) y‖ ^ 2 ≤
      (R⁻¹ * c) ^ 2 * (ringSet R).indicator (fun _ => (1 : ℝ)) y := by
  have hR0 : 0 < R := by linarith
  by_cases h : y ∈ ringSet R
  · rw [Set.indicator_of_mem h, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) (cut_second_le hR hc y) 2
  · rw [cut_second_zero hR0 h, Set.indicator_of_notMem h]
    simp

theorem first_col (χ : Space → ℝ) (v : Space → Space) (hχ : ContDiff ℝ ∞ χ) (hv : ContDiff ℝ ∞ v)
    (y e : Space) :
    fderiv ℝ (fun z => χ z • v z) y e = χ y • fderiv ℝ v y e + fderiv ℝ χ y e • v y := by
  have h := (hχ.differentiable (by simp) y).hasFDerivAt.smul (hv.differentiable (by simp) y).hasFDerivAt
  rw [show fderiv ℝ (fun z => χ z • v z) y = _ from h.fderiv]
  simp

theorem first_col_sub (χ : Space → ℝ) (v : Space → Space) (hχ : ContDiff ℝ ∞ χ)
    (hv : ContDiff ℝ ∞ v) (y e : Space) :
    (fderiv ℝ (fun z => χ z • v z) y - fderiv ℝ v y) e =
      (χ y - 1) • fderiv ℝ v y e + fderiv ℝ χ y e • v y := by
  rw [ContinuousLinearMap.sub_apply, first_col χ v hχ hv]
  module

theorem dir_second_eq (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (y e : Space) :
    fderiv ℝ (fun z => fderiv ℝ χ z e) y e = fderiv ℝ (fderiv ℝ χ) y e e := by
  have hd : DifferentiableAt ℝ (fderiv ℝ χ) y :=
    ((contDiff_infty_iff_fderiv.1 hχ).2.differentiable (by simp)) y
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem second_col (χ : Space → ℝ) (v : Space → Space) (hχ : ContDiff ℝ ∞ χ) (hv : ContDiff ℝ ∞ v)
    (y e : Space) :
    fderiv ℝ (fun z => fderiv ℝ (fun z => χ z • v z) z e) y e =
      χ y • fderiv ℝ (fun z => fderiv ℝ v z e) y e + (2 * fderiv ℝ χ y e) • fderiv ℝ v y e +
        fderiv ℝ (fderiv ℝ χ) y e e • v y := by
  have e1 : (fun z => fderiv ℝ (fun z => χ z • v z) z e) =
      fun z => χ z • fderiv ℝ v z e + fderiv ℝ χ z e • v z :=
    funext fun z => first_col χ v hχ hv z e
  have hv1 : ContDiff ℝ ∞ (fun z => fderiv ℝ v z e) :=
    (contDiff_infty_iff_fderiv.1 hv).2.clm_apply contDiff_const
  have hχ1 : ContDiff ℝ ∞ (fun z => fderiv ℝ χ z e) :=
    (contDiff_infty_iff_fderiv.1 hχ).2.clm_apply contDiff_const
  have h := ((hχ.differentiable (by simp) y).hasFDerivAt.smul
    (hv1.differentiable (by simp) y).hasFDerivAt).add
    ((hχ1.differentiable (by simp) y).hasFDerivAt.smul (hv.differentiable (by simp) y).hasFDerivAt)
  rw [e1, show fderiv ℝ (fun z => χ z • fderiv ℝ v z e + fderiv ℝ χ z e • v z) y = _ from h.fderiv,
    ← dir_second_eq χ hχ y e]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  module

theorem trace_continuous {u : Space → Space} (hu : ContDiff ℝ ∞ u) : Continuous (sumSecondPartialsAt u) := by
  have e : sumSecondPartialsAt u = fun y => ∑ i : Fin 3, fderiv ℝ (fun z => fderiv ℝ u z (unitVector i)) y (unitVector i) :=
    funext fun y => by simp only [sumSecondPartialsAt, second_diag_eq u hu]
  rw [e]
  refine continuous_finsetSum _ fun i _ => ?_
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ u z (unitVector i)) :=
    (contDiff_infty_iff_fderiv.1 hu).2.clm_apply contDiff_const
  exact (h1.continuous_fderiv (by simp)).clm_apply continuous_const

theorem trace_product_sub (χ : Space → ℝ) (v : Space → Space) (hχ : ContDiff ℝ ∞ χ)
    (hv : ContDiff ℝ ∞ v) (y : Space) :
    sumSecondPartialsAt (fun z => χ z • v z) y - sumSecondPartialsAt v y =
      (χ y - 1) • sumSecondPartialsAt v y +
        ∑ i : Fin 3, (2 * fderiv ℝ χ y (unitVector i)) • fderiv ℝ v y (unitVector i) +
        (∑ i : Fin 3, fderiv ℝ (fderiv ℝ χ) y (unitVector i) (unitVector i)) • v y := by
  have hu : ContDiff ℝ ∞ (fun z => χ z • v z) := hχ.smul hv
  simp only [sumSecondPartialsAt, second_diag_eq _ hu, second_diag_eq _ hv, second_col χ v hχ hv,
    Fin.sum_univ_three]
  module


theorem grad_err_le {R c : ℝ} (hR : 1 ≤ R)
    (hc : ∀ x, ‖fderiv ℝ roundBump x‖ ≤ c ∧ ‖fderiv ℝ (fderiv ℝ roundBump) x‖ ≤ c)
    {v : Space → Space} (hv : ContDiff ℝ ∞ v) (y : Space) :
    matSq (fderiv ℝ (fun z => scaledBump R z • v z) y - fderiv ℝ v y) ≤
      2 * ((tailSet R).indicator (fun _ => (1 : ℝ)) y * matSq (fderiv ℝ v y)) +
        6 * c ^ 2 * (R⁻¹ ^ 2 * ((ringSet R).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 2)) := by
  have hR0 : 0 < R := by linarith
  have ho := cut_sub_one_sq hR0 y
  have hg := cut_first_sq hR0 hc y
  have hcol : ∀ i : Fin 3,
      ‖(fderiv ℝ (fun z => scaledBump R z • v z) y - fderiv ℝ v y) (unitVector i)‖ ^ 2 ≤
        2 * ((tailSet R).indicator (fun _ => (1 : ℝ)) y * ‖fderiv ℝ v y (unitVector i)‖ ^ 2) +
          2 * ((R⁻¹ * c) ^ 2 * (ringSet R).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 2) := by
    intro i
    rw [first_col_sub _ _ (scaledBump_contDiff R) hv]
    refine (norm_add_sq_le _ _).trans ?_
    rw [norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    have d1 := (apply_unit_sq_le (fderiv ℝ (scaledBump R) y) i).trans hg
    have m1 := mul_le_mul_of_nonneg_right ho (sq_nonneg ‖fderiv ℝ v y (unitVector i)‖)
    have m2 := mul_le_mul_of_nonneg_right d1 (sq_nonneg ‖v y‖)
    linarith
  simp only [matSq, Fin.sum_univ_three]
  linarith [hcol 0, hcol 1, hcol 2]

theorem trace_err_le {R c : ℝ} (hR : 1 ≤ R)
    (hc : ∀ x, ‖fderiv ℝ roundBump x‖ ≤ c ∧ ‖fderiv ℝ (fderiv ℝ roundBump) x‖ ≤ c)
    {v : Space → Space} (hv : ContDiff ℝ ∞ v) (y : Space) :
    ‖sumSecondPartialsAt (fun z => scaledBump R z • v z) y - sumSecondPartialsAt v y‖ ^ 2 ≤
      3 * ((tailSet R).indicator (fun _ => (1 : ℝ)) y * ‖sumSecondPartialsAt v y‖ ^ 2) +
        36 * c ^ 2 * (R⁻¹ ^ 2 * matSq (fderiv ℝ v y)) +
        27 * c ^ 2 * (R⁻¹ ^ 2 * ((ringSet R).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 2)) := by
  have hR0 : 0 < R := by linarith
  have ho := cut_sub_one_sq hR0 y
  have hg := cut_first_sq hR0 hc y
  have hs := cut_second_sq hR hc y
  have ha1 := ind_le_one (ringSet R) y
  have ha0 := ind_nonneg (ringSet R) y
  set g := ‖fderiv ℝ (scaledBump R) y‖ with hg_def
  set s := ‖fderiv ℝ (fderiv ℝ (scaledBump R)) y‖ with hs_def
  set P := ∑ i : Fin 3, ‖fderiv ℝ v y (unitVector i)‖ with hP
  rw [trace_product_sub _ _ (scaledBump_contDiff R) hv]
  have n1 : ‖(scaledBump R y - 1) • sumSecondPartialsAt v y‖ = |scaledBump R y - 1| * ‖sumSecondPartialsAt v y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have n2 : ‖∑ i : Fin 3, (2 * fderiv ℝ (scaledBump R) y (unitVector i)) • fderiv ℝ v y (unitVector i)‖ ≤
      2 * g * P := by
    refine (norm_sum_le _ _).trans ?_
    rw [hP, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
    have h1 : |fderiv ℝ (scaledBump R) y (unitVector i)| ≤ g := by
      have h := (fderiv ℝ (scaledBump R) y).le_opNorm (unitVector i)
      rwa [norm_unit, mul_one, Real.norm_eq_abs] at h
    have := mul_le_mul_of_nonneg_right h1 (norm_nonneg (fderiv ℝ v y (unitVector i)))
    linarith
  have n3 : ‖(∑ i : Fin 3, fderiv ℝ (fderiv ℝ (scaledBump R)) y (unitVector i) (unitVector i)) • v y‖ ≤
      3 * s * ‖v y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h := fun i => apply_unit_two_le (fderiv ℝ (fderiv ℝ (scaledBump R)) y) i
    simp only [Fin.sum_univ_three]
    linarith [h 0, h 1, h 2]
  have hP2 : P ^ 2 ≤ 3 * matSq (fderiv ℝ v y) := by
    simp only [hP, matSq, Fin.sum_univ_three]
    nlinarith [sq_nonneg (‖fderiv ℝ v y (unitVector 0)‖ - ‖fderiv ℝ v y (unitVector 1)‖),
      sq_nonneg (‖fderiv ℝ v y (unitVector 1)‖ - ‖fderiv ℝ v y (unitVector 2)‖),
      sq_nonneg (‖fderiv ℝ v y (unitVector 0)‖ - ‖fderiv ℝ v y (unitVector 2)‖)]
  have hsum : ‖(scaledBump R y - 1) • sumSecondPartialsAt v y +
      ∑ i : Fin 3, (2 * fderiv ℝ (scaledBump R) y (unitVector i)) • fderiv ℝ v y (unitVector i) +
      (∑ i : Fin 3, fderiv ℝ (fderiv ℝ (scaledBump R)) y (unitVector i) (unitVector i)) • v y‖ ≤
      ‖(scaledBump R y - 1) • sumSecondPartialsAt v y‖ +
      ‖∑ i : Fin 3, (2 * fderiv ℝ (scaledBump R) y (unitVector i)) • fderiv ℝ v y (unitVector i)‖ +
      ‖(∑ i : Fin 3, fderiv ℝ (fderiv ℝ (scaledBump R)) y (unitVector i) (unitVector i)) • v y‖ :=
    norm_add₃_le
  rw [n1] at hsum
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hg0 : 0 ≤ g := norm_nonneg _
  have hs0 : 0 ≤ s := norm_nonneg _
  have htot : ‖(scaledBump R y - 1) • sumSecondPartialsAt v y +
      ∑ i : Fin 3, (2 * fderiv ℝ (scaledBump R) y (unitVector i)) • fderiv ℝ v y (unitVector i) +
      (∑ i : Fin 3, fderiv ℝ (fderiv ℝ (scaledBump R)) y (unitVector i) (unitVector i)) • v y‖ ≤
      |scaledBump R y - 1| * ‖sumSecondPartialsAt v y‖ + 2 * g * P + 3 * s * ‖v y‖ := by linarith
  have hsq := (pow_le_pow_left₀ (norm_nonneg _) htot 2).trans
    (add_three_sq_le (|scaledBump R y - 1| * ‖sumSecondPartialsAt v y‖) (2 * g * P) (3 * s * ‖v y‖))
  have A : (|scaledBump R y - 1| * ‖sumSecondPartialsAt v y‖) ^ 2 ≤
      (tailSet R).indicator (fun _ => (1 : ℝ)) y * ‖sumSecondPartialsAt v y‖ ^ 2 := by
    rw [mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_right ho (sq_nonneg _)
  have hgK : g ^ 2 ≤ (R⁻¹ * c) ^ 2 := by
    have := mul_le_mul_of_nonneg_left ha1 (sq_nonneg (R⁻¹ * c))
    linarith
  have B : (2 * g * P) ^ 2 ≤ 12 * ((R⁻¹ * c) ^ 2 * matSq (fderiv ℝ v y)) := by
    have e : (2 * g * P) ^ 2 = 4 * (g ^ 2 * P ^ 2) := by ring
    rw [e]
    have h1 := mul_le_mul hgK hP2 (sq_nonneg P) (sq_nonneg _)
    linarith
  have C : (3 * s * ‖v y‖) ^ 2 ≤
      9 * ((R⁻¹ * c) ^ 2 * (ringSet R).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 2) := by
    have e : (3 * s * ‖v y‖) ^ 2 = 9 * (s ^ 2 * ‖v y‖ ^ 2) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖v y‖)
    linarith
  have e2 : (R⁻¹ * c) ^ 2 = c ^ 2 * R⁻¹ ^ 2 := by ring
  rw [e2] at B C
  nlinarith [hsq, A, B, C]

theorem ofReal_ind_mul_le (S : Set Space) (F : Space → ℝ) (hF : ∀ y, 0 ≤ F y) (y : Space) :
    ENNReal.ofReal (S.indicator (fun _ => (1 : ℝ)) y * F y) ≤ ENNReal.ofReal (F y) := by
  refine ENNReal.ofReal_le_ofReal ?_
  have := mul_le_mul_of_nonneg_right (ind_le_one S y) (hF y)
  linarith

theorem tail_tendsto {F : Space → ℝ} (hF : Continuous F) (hF0 : ∀ y, 0 ≤ F y) (hi : Integrable F) :
    Tendsto (fun k : ℕ => ∫⁻ y, ENNReal.ofReal
      ((tailSet ((k : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y * F y)) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence' (fun y => ENNReal.ofReal (F y))
    (F := fun k : ℕ => fun y => ENNReal.ofReal
      ((tailSet ((k : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y * F y)) (f := fun _ => 0)
    (fun k => (((measurable_const.indicator (tailSet_measurable _)).mul
      hF.measurable).ennreal_ofReal).aemeasurable)
    (fun k => ae_of_all _ fun y => ofReal_ind_mul_le _ F hF0 y) hi.lintegral_lt_top.ne
    (ae_of_all _ fun y => by
      obtain ⟨N, hN⟩ := exists_nat_gt ‖y‖
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with k hk
      have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
      have hy : y ∉ tailSet ((k : ℝ) + 1) := by
        simp only [tailSet, Set.mem_setOf_eq, not_le]
        linarith
      rw [Set.indicator_of_notMem hy, zero_mul, ENNReal.ofReal_zero])
  simpa using h

theorem ring_bound (v : Space → Space) {R η : ℝ} (hR : 1 ≤ R) (hη : 0 < η) :
    ∫⁻ y, ENNReal.ofReal (R⁻¹ ^ 2 * ((ringSet R).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 2)) ≤
      ENNReal.ofReal (8 * η) * volume (Metric.ball (0 : Space) 1) +
        ENNReal.ofReal (η⁻¹ ^ 2) *
          ∫⁻ y, ENNReal.ofReal ((tailSet R).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 6) := by
  have hR0 : 0 < R := by linarith
  calc ∫⁻ y, ENNReal.ofReal (R⁻¹ ^ 2 * ((ringSet R).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 2))
      ≤ ∫⁻ y, ((Metric.closedBall (0 : Space) (2 * R)).indicator
          (fun _ => ENNReal.ofReal (η * R⁻¹ ^ 3)) y +
          ENNReal.ofReal (η⁻¹ ^ 2) *
            ENNReal.ofReal ((tailSet R).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 6)) := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ ringSet R
        · have hyb : y ∈ Metric.closedBall (0 : Space) (2 * R) := by
            rw [mem_closedBall_zero_iff]
            exact hy.2
          have hyt : y ∈ tailSet R := hy.1
          rw [Set.indicator_of_mem hy, Set.indicator_of_mem hyb, Set.indicator_of_mem hyt, one_mul,
            one_mul, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have key := sq_le_split (t := ‖v y‖) (show 0 < η * R⁻¹ by positivity)
          calc R⁻¹ ^ 2 * ‖v y‖ ^ 2 ≤ R⁻¹ ^ 2 * (η * R⁻¹ + ‖v y‖ ^ 6 / (η * R⁻¹) ^ 2) :=
                mul_le_mul_of_nonneg_left key (by positivity)
            _ = η * R⁻¹ ^ 3 + η⁻¹ ^ 2 * ‖v y‖ ^ 6 := by
                field_simp
        · rw [Set.indicator_of_notMem hy, zero_mul, mul_zero, ENNReal.ofReal_zero]
          exact zero_le
    _ = ENNReal.ofReal (η * R⁻¹ ^ 3) * volume (Metric.closedBall (0 : Space) (2 * R)) +
        ENNReal.ofReal (η⁻¹ ^ 2) *
          ∫⁻ y, ENNReal.ofReal ((tailSet R).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 6) := by
        rw [lintegral_add_left' (aemeasurable_const.indicator Metric.isClosed_closedBall.measurableSet),
          lintegral_indicator_const Metric.isClosed_closedBall.measurableSet,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (8 * η) * volume (Metric.ball (0 : Space) 1) +
        ENNReal.ofReal (η⁻¹ ^ 2) *
          ∫⁻ y, ENNReal.ofReal ((tailSet R).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 6) := by
        rw [Measure.addHaar_closedBall volume 0 (by positivity : (0 : ℝ) ≤ 2 * R),
          finrank_euclideanSpace_fin, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 3
        field_simp
        ring

theorem ring_tendsto {v : Space → Space} (hv : Continuous v) (h6 : Integrable (fun y => ‖v y‖ ^ 6)) :
    Tendsto (fun k : ℕ => ∫⁻ y, ENNReal.ofReal ((((k : ℝ) + 1)⁻¹) ^ 2 *
      ((ringSet ((k : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 2))) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  have hV : volume (Metric.ball (0 : Space) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hlim : Tendsto (fun η : ℝ => ENNReal.ofReal (8 * η) * volume (Metric.ball (0 : Space) 1))
      (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (fun η : ℝ => ENNReal.ofReal (8 * η)) (𝓝 0) (𝓝 0) := by
      have h0 : Tendsto (fun η : ℝ => 8 * η) (𝓝 0) (𝓝 (8 * 0)) := tendsto_const_nhds.mul tendsto_id
      simpa using ENNReal.tendsto_ofReal h0
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hV)
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨η, hηb, hη0⟩ := (((hlim.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hε2)).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  have hη : 0 < η := hη0
  have ht := tail_tendsto (F := fun y => ‖v y‖ ^ 6) (hv.norm.pow 6) (fun y => by positivity) h6
  have ht2 : Tendsto (fun k : ℕ => ENNReal.ofReal (η⁻¹ ^ 2) * ∫⁻ y, ENNReal.ofReal
      ((tailSet ((k : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 6)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.ofReal_ne_top)
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.1 ht2 (ε / 2) hε2
  refine ⟨N, fun k hk => ?_⟩
  have hR : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  calc _ ≤ _ := ring_bound v hR hη
    _ ≤ ε / 2 + ε / 2 := add_le_add hηb.le (hN k hk)
    _ = ε := ENNReal.add_halves ε

theorem inv_sq_tendsto :
    Tendsto (fun k : ℕ => ENNReal.ofReal ((((k : ℝ) + 1)⁻¹) ^ 2)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h : Tendsto (fun k : ℕ => (((k : ℝ) + 1)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa [one_div] using h0.pow 2
  have h2 := ENNReal.tendsto_ofReal h
  rwa [ENNReal.ofReal_zero] at h2

theorem cutoff_limits {v : Space → Space} (hv : ContDiff ℝ ∞ v) (h6 : Integrable (fun y => ‖v y‖ ^ 6))
    (h2 : Integrable (fun y => matSq (fderiv ℝ v y)))
    (hl : Integrable (fun y => ‖sumSecondPartialsAt v y‖ ^ 2)) :
    Tendsto (fun k : ℕ => ∫⁻ y, ENNReal.ofReal (matSq
      (fderiv ℝ (fun z => scaledBump ((k : ℝ) + 1) z • v z) y - fderiv ℝ v y))) atTop (𝓝 0) ∧
    Tendsto (fun k : ℕ => ∫⁻ y, ENNReal.ofReal (‖sumSecondPartialsAt
      (fun z => scaledBump ((k : ℝ) + 1) z • v z) y - sumSecondPartialsAt v y‖ ^ 2)) atTop (𝓝 0) := by
  obtain ⟨c, -, hc⟩ := round_bounds
  have hvc : Continuous v := hv.continuous
  have hdc : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by simp)
  have hFc : Continuous (fun y => matSq (fderiv ℝ v y)) := continuous_matSq'.comp hdc
  have hLc : Continuous (fun y => ‖sumSecondPartialsAt v y‖ ^ 2) := (trace_continuous hv).norm.pow 2
  have T1 := tail_tendsto hFc (fun y => matSq_nonneg_map _) h2
  have T2 := tail_tendsto hLc (fun y => by positivity) hl
  have Rg := ring_tendsto hvc h6
  have hI2 : ∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ v y)) ≠ ⊤ := h2.lintegral_lt_top.ne
  have hR : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have mT : ∀ (R : ℝ) (F : Space → ℝ), Continuous F →
      Measurable (fun y => ENNReal.ofReal ((tailSet R).indicator (fun _ => (1 : ℝ)) y * F y)) :=
    fun R F hF => ((measurable_const.indicator (tailSet_measurable R)).mul hF.measurable).ennreal_ofReal
  constructor
  · have bound : ∀ k : ℕ, ∫⁻ y, ENNReal.ofReal (matSq
        (fderiv ℝ (fun z => scaledBump ((k : ℝ) + 1) z • v z) y - fderiv ℝ v y)) ≤
        ENNReal.ofReal 2 * (∫⁻ y, ENNReal.ofReal
          ((tailSet ((k : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y * matSq (fderiv ℝ v y))) +
        ENNReal.ofReal (6 * c ^ 2) * (∫⁻ y, ENNReal.ofReal ((((k : ℝ) + 1)⁻¹) ^ 2 *
          ((ringSet ((k : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 2))) := by
      intro k
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_add_left' ((mT _ _ hFc).const_mul _).aemeasurable]
      refine lintegral_mono fun y => ?_
      dsimp only
      have h := grad_err_le (hR k) hc hv y
      have a0 := ind_nonneg (tailSet ((k : ℝ) + 1)) y
      have a1 := ind_nonneg (ringSet ((k : ℝ) + 1)) y
      have f0 := matSq_nonneg_map (fderiv ℝ v y)
      rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      linarith
    have hsum : Tendsto (fun k : ℕ =>
        ENNReal.ofReal 2 * (∫⁻ y, ENNReal.ofReal
          ((tailSet ((k : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y * matSq (fderiv ℝ v y))) +
        ENNReal.ofReal (6 * c ^ 2) * (∫⁻ y, ENNReal.ofReal ((((k : ℝ) + 1)⁻¹) ^ 2 *
          ((ringSet ((k : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 2)))) atTop (𝓝 0) := by
      have h := (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal 2) T1 (Or.inr ENNReal.ofReal_ne_top)).add
        (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (6 * c ^ 2)) Rg (Or.inr ENNReal.ofReal_ne_top))
      simp only [mul_zero, add_zero] at h
      exact h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le) bound
  · have bound : ∀ k : ℕ, ∫⁻ y, ENNReal.ofReal (‖sumSecondPartialsAt
        (fun z => scaledBump ((k : ℝ) + 1) z • v z) y - sumSecondPartialsAt v y‖ ^ 2) ≤
        ENNReal.ofReal 3 * (∫⁻ y, ENNReal.ofReal
          ((tailSet ((k : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y * ‖sumSecondPartialsAt v y‖ ^ 2)) +
        ENNReal.ofReal (36 * c ^ 2) * (ENNReal.ofReal ((((k : ℝ) + 1)⁻¹) ^ 2) *
          ∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ v y))) +
        ENNReal.ofReal (27 * c ^ 2) * (∫⁻ y, ENNReal.ofReal ((((k : ℝ) + 1)⁻¹) ^ 2 *
          ((ringSet ((k : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 2))) := by
      intro k
      refine (lintegral_mono (g := fun y =>
        ENNReal.ofReal 3 * ENNReal.ofReal
          ((tailSet ((k : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y * ‖sumSecondPartialsAt v y‖ ^ 2) +
        ENNReal.ofReal (36 * c ^ 2) * (ENNReal.ofReal ((((k : ℝ) + 1)⁻¹) ^ 2) *
          ENNReal.ofReal (matSq (fderiv ℝ v y))) +
        ENNReal.ofReal (27 * c ^ 2) * ENNReal.ofReal ((((k : ℝ) + 1)⁻¹) ^ 2 *
          ((ringSet ((k : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y * ‖v y‖ ^ 2))) ?_).trans (le_of_eq ?_)
      swap
      · have mA : AEMeasurable (fun y => ENNReal.ofReal 3 * ENNReal.ofReal
            ((tailSet ((k : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y * ‖sumSecondPartialsAt v y‖ ^ 2)) volume :=
          ((mT _ _ hLc).const_mul _).aemeasurable
        have mAB : AEMeasurable (fun y => ENNReal.ofReal 3 * ENNReal.ofReal
            ((tailSet ((k : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y * ‖sumSecondPartialsAt v y‖ ^ 2) +
            ENNReal.ofReal (36 * c ^ 2) * (ENNReal.ofReal ((((k : ℝ) + 1)⁻¹) ^ 2) *
              ENNReal.ofReal (matSq (fderiv ℝ v y)))) volume :=
          (((mT _ _ hLc).const_mul _).add ((hFc.measurable.ennreal_ofReal.const_mul _).const_mul _)).aemeasurable
        rw [lintegral_add_left' mAB, lintegral_add_left' mA,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      intro y
      dsimp only
      have h := trace_err_le (hR k) hc hv y
      have a0 := ind_nonneg (tailSet ((k : ℝ) + 1)) y
      have a1 := ind_nonneg (ringSet ((k : ℝ) + 1)) y
      have f0 := matSq_nonneg_map (fderiv ℝ v y)
      rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      linarith
    have hmid : Tendsto (fun k : ℕ => ENNReal.ofReal (36 * c ^ 2) *
        (ENNReal.ofReal ((((k : ℝ) + 1)⁻¹) ^ 2) * ∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ v y))))
        atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (36 * c ^ 2))
        (ENNReal.Tendsto.mul_const inv_sq_tendsto (Or.inr hI2)) (Or.inr ENNReal.ofReal_ne_top)
      simp only [zero_mul, mul_zero] at h
      exact h
    have hsum := ((ENNReal.Tendsto.const_mul (a := ENNReal.ofReal 3) T2 (Or.inr ENNReal.ofReal_ne_top)).add
      hmid).add (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (27 * c ^ 2)) Rg (Or.inr ENNReal.ofReal_ne_top))
    simp only [mul_zero, add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le) bound

theorem diag_locallyIntegrable {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : ∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    (i : Fin 3) : LocallyIntegrable (fun y => H y (unitVector i) (unitVector i)) volume := fun x => by
  have h := (ContinuousLinearMap.apply ℝ Space (unitVector i)).integrableAtFilter_comp ((hH i).2.1 x)
  simpa [Function.comp_def] using h

theorem smoothed_trace {w : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hw : IsWeakGradient w G)
    (hH : ∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    (n : ℕ) :
    sumSecondPartialsAt (smoothed w n) =
      (kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => secondDerivTrace (H z) := by
  funext y
  have hs : ContDiff ℝ ∞ (smoothed w n) :=
    (kernelBump n).hasCompactSupport_normed.contDiff_convolution_left _ (kernelBump n).contDiff_normed hw.1
  have hcol : ∀ i : Fin 3, (fun z => fderiv ℝ (smoothed w n) z (unitVector i)) =
      (kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => G z (unitVector i) :=
    fun i => funext fun z => fderiv_kernel_apply _ w G hw z i
  have hdiag : ∀ i : Fin 3, iteratedFDeriv ℝ 2 (smoothed w n) y ![unitVector i, unitVector i] =
      ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun z => H z (unitVector i) (unitVector i)) y := by
    intro i
    rw [second_diag_eq _ hs, hcol i, fderiv_kernel_apply _ _ _ (hH i) y i]
    simp only [ContinuousLinearMap.flip_apply]
  have hex : ∀ i : Fin 3, Integrable (fun t => (ContinuousLinearMap.lsmul ℝ ℝ)
      ((kernelBump n).normed volume t) (H (y - t) (unitVector i) (unitVector i))) := fun i =>
    (((kernelBump n).hasCompactSupport_normed (μ := volume)).convolutionExists_left (μ := volume)
      (ContinuousLinearMap.lsmul ℝ ℝ) ((kernelBump n).continuous_normed (μ := volume))
      (diag_locallyIntegrable hH i) y).integrable
  simp only [sumSecondPartialsAt, hdiag, convolution_def]
  rw [← integral_finsetSum _ fun i _ => hex i]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp [secondDerivTrace]

theorem mollify_limits {w : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hw : IsWeakGradient w G)
    (hH : ∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    (h6 : (∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6)) < ⊤) (hG : (∫⁻ y, ENNReal.ofReal (matSq (G y))) < ⊤)
    (hT : (∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H y)‖ ^ 2)) < ⊤) :
    (∀ n, ContDiff ℝ ∞ (smoothed w n)) ∧ (∀ n, Integrable (fun y => ‖smoothed w n y‖ ^ 6)) ∧
    (∀ n, Integrable (fun y => matSq (fderiv ℝ (smoothed w n) y))) ∧
    (∀ n, Integrable (fun y => ‖sumSecondPartialsAt (smoothed w n) y‖ ^ 2)) ∧
    Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ (smoothed w n) y - G y))) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫⁻ y, ENNReal.ofReal
      (‖sumSecondPartialsAt (smoothed w n) y - secondDerivTrace (H y)‖ ^ 2)) atTop (𝓝 0) := by
  have hwl : LocallyIntegrable w volume := hw.1
  have hGl : ∀ i : Fin 3, LocallyIntegrable (fun y => G y (unitVector i)) volume := fun i => (hH i).1
  have hTl : LocallyIntegrable (fun y => secondDerivTrace (H y)) volume := by
    have e : (fun y => secondDerivTrace (H y)) = fun y => ∑ i ∈ Finset.univ, H y (unitVector i) (unitVector i) :=
      rfl
    rw [e]
    exact locallyIntegrable_finsetSum Finset.univ fun i _ => diag_locallyIntegrable hH i
  have hw6 : Integrable (fun y => ‖w y‖ ^ 6) :=
    integrable_of_lintegral_lt (hwl.aestronglyMeasurable.norm.pow 6) (fun y => by positivity) h6
  have hG2 : ∀ i : Fin 3, Integrable (fun y => ‖G y (unitVector i)‖ ^ 2) := by
    intro i
    refine integrable_of_lintegral_lt ((hGl i).aestronglyMeasurable.norm.pow 2) (fun y => by positivity)
      (lt_of_le_of_lt (lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_) hG)
    exact Finset.single_le_sum (f := fun j => ‖G y (unitVector j)‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  have hT2 : Integrable (fun y => ‖secondDerivTrace (H y)‖ ^ 2) :=
    integrable_of_lintegral_lt (hTl.aestronglyMeasurable.norm.pow 2) (fun y => by positivity) hT
  have hs : ∀ n, ContDiff ℝ ∞ (smoothed w n) := fun n =>
    (kernelBump n).hasCompactSupport_normed.contDiff_convolution_left _ (kernelBump n).contDiff_normed hwl
  have hcol : ∀ n y (i : Fin 3), fderiv ℝ (smoothed w n) y (unitVector i) =
      ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun z => G z (unitVector i)) y := fun n y i => fderiv_kernel_apply _ w G hw y i
  have hdI : ∀ n (i : Fin 3), Integrable (fun y => ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      fun z => G z (unitVector i)) y - G y (unitVector i)‖ ^ 2) := fun n i =>
    diff_sq_integrable _ _ (hGl i).aestronglyMeasurable (hG2 i)
  refine ⟨hs, fun n => (kernel_pow_integral _ w 6 (by norm_num) hwl hw6).1, fun n => ?_, fun n => ?_, ?_, ?_⟩
  · have e : (fun y => matSq (fderiv ℝ (smoothed w n) y)) = fun y => ∑ i : Fin 3,
        ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun z => G z (unitVector i)) y‖ ^ 2 := by
      funext y
      simp only [matSq, hcol]
    rw [e]
    exact integrable_finsetSum _ fun i _ => (kernel_pow_integral _ _ 2 (by norm_num) (hGl i) (hG2 i)).1
  · rw [smoothed_trace hw hH n]
    exact (kernel_pow_integral _ _ 2 (by norm_num) hTl hT2).1
  · have e : (fun n => ∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ (smoothed w n) y - G y))) = fun n =>
        ENNReal.ofReal (∑ i : Fin 3, ∫ y, ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun z => G z (unitVector i)) y - G y (unitVector i)‖ ^ 2) := by
      funext n
      have e1 : (fun y => matSq (fderiv ℝ (smoothed w n) y - G y)) = fun y => ∑ i : Fin 3,
          ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            fun z => G z (unitVector i)) y - G y (unitVector i)‖ ^ 2 := by
        funext y
        simp only [matSq, ContinuousLinearMap.sub_apply, hcol]
      rw [← integral_finsetSum _ fun i _ => hdI n i,
        ofReal_integral_eq_lintegral_ofReal (integrable_finsetSum _ fun i _ => hdI n i)
          (ae_of_all _ fun y => Finset.sum_nonneg fun i _ => by positivity)]
      exact lintegral_congr fun y => congrArg ENNReal.ofReal (congrFun e1 y)
    rw [e]
    have h := ENNReal.tendsto_ofReal (tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ =>
      conv_sq_tendsto _ (hGl i).aestronglyMeasurable (hG2 i))
    simpa using h
  · have e : (fun n => ∫⁻ y, ENNReal.ofReal (‖sumSecondPartialsAt (smoothed w n) y - secondDerivTrace (H y)‖ ^ 2)) =
        fun n => ENNReal.ofReal (∫ y, ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun z => secondDerivTrace (H z)) y - secondDerivTrace (H y)‖ ^ 2) := by
      funext n
      rw [smoothed_trace hw hH n, ofReal_integral_eq_lintegral_ofReal
        (diff_sq_integrable _ _ hTl.aestronglyMeasurable hT2) (ae_of_all _ fun y => by positivity)]
    rw [e]
    have h := ENNReal.tendsto_ofReal (conv_sq_tendsto _ hTl.aestronglyMeasurable hT2)
    simpa using h

theorem approx_step {Γ : Set Symmetry} {w : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsProfileField Γ w G H) (r : ℝ) (hr : 0 < r) :
    ∃ u : Space → Space, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
      (∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ u y - G y))) ≤ ENNReal.ofReal r ∧
      (∫⁻ y, ENNReal.ofReal (‖sumSecondPartialsAt u y - secondDerivTrace (H y)‖ ^ 2)) ≤ ENNReal.ofReal r := by
  obtain ⟨hs, h6s, h2s, hls, M1, M2⟩ := mollify_limits h.weak_gradient h.weak_secondDeriv h.sixth_power
    h.gradient_finite h.sumSecondPartials_finite
  have hq : 0 < ENNReal.ofReal (r / 4) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨N1, hN1⟩ := ENNReal.tendsto_atTop_zero.1 M1 _ hq
  obtain ⟨N2, hN2⟩ := ENNReal.tendsto_atTop_zero.1 M2 _ hq
  set n := max N1 N2 with hn
  obtain ⟨C1, C2⟩ := cutoff_limits (hs n) (h6s n) (h2s n) (hls n)
  obtain ⟨K1, hK1⟩ := ENNReal.tendsto_atTop_zero.1 C1 _ hq
  obtain ⟨K2, hK2⟩ := ENNReal.tendsto_atTop_zero.1 C2 _ hq
  set k := max K1 K2 with hk
  set v := smoothed w n with hv
  set u : Space → Space := fun z => scaledBump ((k : ℝ) + 1) z • v z with hu_def
  have hu : ContDiff ℝ ∞ u := (scaledBump_contDiff _).smul (hs n)
  have hfin : ENNReal.ofReal 2 * ENNReal.ofReal (r / 4) + ENNReal.ofReal 2 * ENNReal.ofReal (r / 4) =
      ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  refine ⟨u, hu, (scaledBump_hasCompactSupport (by positivity)).smul_right, ?_, ?_⟩
  · have mA : AEMeasurable (fun y => ENNReal.ofReal 2 * ENNReal.ofReal
        (matSq (fderiv ℝ u y - fderiv ℝ v y))) volume :=
      (((continuous_matSq'.comp ((hu.continuous_fderiv (by simp)).sub
        ((hs n).continuous_fderiv (by simp)))).measurable.ennreal_ofReal).const_mul _).aemeasurable
    calc (∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ u y - G y)))
        ≤ ∫⁻ y, (ENNReal.ofReal 2 * ENNReal.ofReal (matSq (fderiv ℝ u y - fderiv ℝ v y)) +
            ENNReal.ofReal 2 * ENNReal.ofReal (matSq (fderiv ℝ v y - G y))) := by
          refine lintegral_mono fun y => ?_
          have h1 := matSq_add_le (fderiv ℝ u y - fderiv ℝ v y) (fderiv ℝ v y - G y)
          rw [sub_add_sub_cancel] at h1
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by have := matSq_nonneg_map (fderiv ℝ u y - fderiv ℝ v y); positivity)
              (by have := matSq_nonneg_map (fderiv ℝ v y - G y); positivity)]
          exact ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal 2 * (∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ u y - fderiv ℝ v y))) +
            ENNReal.ofReal 2 * ∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ v y - G y)) := by
          rw [lintegral_add_left' mA, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (r / 4) + ENNReal.ofReal 2 * ENNReal.ofReal (r / 4) := by
          gcongr
          · exact hK1 k (le_max_left _ _)
          · exact hN1 n (le_max_left _ _)
      _ = ENNReal.ofReal r := hfin
  · have mA : AEMeasurable (fun y => ENNReal.ofReal 2 * ENNReal.ofReal
        (‖sumSecondPartialsAt u y - sumSecondPartialsAt v y‖ ^ 2)) volume :=
      (((((trace_continuous hu).sub (trace_continuous (hs n))).norm.pow 2).measurable.ennreal_ofReal).const_mul
        _).aemeasurable
    calc (∫⁻ y, ENNReal.ofReal (‖sumSecondPartialsAt u y - secondDerivTrace (H y)‖ ^ 2))
        ≤ ∫⁻ y, (ENNReal.ofReal 2 * ENNReal.ofReal (‖sumSecondPartialsAt u y - sumSecondPartialsAt v y‖ ^ 2) +
            ENNReal.ofReal 2 * ENNReal.ofReal (‖sumSecondPartialsAt v y - secondDerivTrace (H y)‖ ^ 2)) := by
          refine lintegral_mono fun y => ?_
          have h1 := norm_add_sq_le (sumSecondPartialsAt u y - sumSecondPartialsAt v y) (sumSecondPartialsAt v y - secondDerivTrace (H y))
          rw [sub_add_sub_cancel] at h1
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal 2 * (∫⁻ y, ENNReal.ofReal (‖sumSecondPartialsAt u y - sumSecondPartialsAt v y‖ ^ 2)) +
            ENNReal.ofReal 2 * ∫⁻ y, ENNReal.ofReal (‖sumSecondPartialsAt v y - secondDerivTrace (H y)‖ ^ 2) := by
          rw [lintegral_add_left' mA, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (r / 4) + ENNReal.ofReal 2 * ENNReal.ofReal (r / 4) := by
          gcongr
          · exact hK2 k (le_max_right _ _)
          · exact hN2 n (le_max_right _ _)
      _ = ENNReal.ofReal r := hfin

end Internal.ProfileFieldApprox

open Internal.ProfileFieldApprox in
theorem profileFieldApprox {Γ : Set Symmetry} {w : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsProfileField Γ w G H) :
    ∃ u : ℕ → Space → Space, (∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n)) ∧
      Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ (u n) y - G y))) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (‖sumSecondPartialsAt (u n) y - secondDerivTrace (H y)‖ ^ 2))
        atTop (𝓝 0) := by
  choose u hu using fun k : ℕ => approx_step h (1 / ((k : ℝ) + 1)) (by positivity)
  have hb : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    have h0 := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rwa [ENNReal.ofReal_zero] at h0
  refine ⟨u, fun n => ⟨(hu n).1, (hu n).2.1⟩, ?_, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => zero_le)
      fun k => (hu k).2.2.1
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => zero_le)
      fun k => (hu k).2.2.2

end CertReduction

end Breakdown
