import Breakdown.Cert.CoerciveSmoothEnergyIdentityDefs

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEnergyIdentityInternal

open EnergyIdentityInternal

namespace Time

theorem period_ftc (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hp : g 1 = g 0) :
    ∫ σ in Set.Icc (0 : ℝ) 1, deriv g σ * g σ = 0 := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hder : ∀ σ ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => g s * g s / 2) (deriv g σ * g σ) σ := by
    intro σ _
    have h := ((hd σ).hasDerivAt.mul (hd σ).hasDerivAt).div_const 2
    have e : deriv g σ * g σ = (deriv g σ * g σ + g σ * deriv g σ) / 2 := by ring
    rw [e]
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (((hg.continuous_deriv (by norm_num)).mul hg.continuous).intervalIntegrable _ _)]
  simp [hp]

theorem sq_integrable (f : ℝ → Space → (Space →L[ℝ] Space))
    (hc : Continuous (fun z : ℝ × Space => f z.1 z.2))
    (hf : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖f σ y‖ ^ 2)) < ⊤) :
    Integrable (fun z : ℝ × Space => ‖f z.1 z.2‖ ^ 2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  have hm : Continuous (fun z : ℝ × Space => ‖f z.1 z.2‖ ^ 2) := hc.norm.pow 2
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun z => by positivity))]
  rw [lintegral_prod _ hm.measurable.ennreal_ofReal.aemeasurable]
  exact hf

theorem time_field_smooth (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (z.1, z.2) (1, 0)) :=
  (hv.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem time_field_eq (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (σ : ℝ) :
    (fun x => deriv (fun s => v s x) σ) =
      fun x => fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (σ, x) (1, 0) := by
  funext x
  exact time_deriv_eq v (hv.smooth.differentiable (by simp)) σ x

theorem time_grad_continuous (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (fun x => deriv (fun s => v s x) z.1) z.2) := by
  have e : (fun z : ℝ × Space => fderiv ℝ (fun x => deriv (fun s => v s x) z.1) z.2) =
      fun z : ℝ × Space => fderiv ℝ
        ((fun s x => fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (s, x) (1, 0)) z.1) z.2 := by
    funext z
    rw [time_field_eq P v hv z.1]
  rw [e]
  exact (joint_partial (fun s x => fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (s, x) (1, 0))
    (time_field_smooth P v hv) (m := ∞) (n := ∞) (by simp) (by simp)).continuous

theorem space_grad_continuous (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
  (joint_partial v hv.smooth (m := ∞) (n := ∞) (by simp) (by simp)).continuous

theorem pair_bound (A B : Space →L[ℝ] Space) :
    |∑ j : Fin 3, inner ℝ (A (unitVector j)) (B (unitVector j))| ≤ 3 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
  have hj : ∀ j : Fin 3, ‖unitVector j‖ = 1 := fun j => by simp [unitVector]
  calc |∑ j : Fin 3, inner ℝ (A (unitVector j)) (B (unitVector j))|
      ≤ ∑ j : Fin 3, |inner ℝ (A (unitVector j)) (B (unitVector j))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, ‖A‖ * ‖B‖ := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have h1 := A.le_opNorm (unitVector j)
        have h2 := B.le_opNorm (unitVector j)
        rw [hj, mul_one] at h1 h2
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _))
    _ = 3 * (‖A‖ * ‖B‖) := by simp
    _ ≤ 3 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
        have ha := norm_nonneg A
        have hb := norm_nonneg B
        nlinarith [sq_nonneg (‖A‖ - ‖B‖)]

theorem joint_integrable (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    Integrable (fun z : ℝ × Space => timePair v z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  have cA := time_grad_continuous P v hv
  have cB := space_grad_continuous P v hv
  have iA : Integrable (fun z : ℝ × Space => ‖fderiv ℝ (fun x => deriv (fun s => v s x) z.1) z.2‖ ^ 2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    refine sq_integrable (fun σ y => fderiv ℝ (fun x => deriv (fun s => v s x) σ) y) cA ?_
    have h := hv.time_derivatives_finite 1 le_rfl
    simp only [periodLIntegral, norm_iteratedFDeriv_one] at h
    exact h
  have iB : Integrable (fun z : ℝ × Space => ‖fderiv ℝ (v z.1) z.2‖ ^ 2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    refine sq_integrable (fun σ y => fderiv ℝ (v σ) y) cB ?_
    have h := hv.derivatives_finite 1 le_rfl
    simp only [periodLIntegral, norm_iteratedFDeriv_one] at h
    exact h
  have hm : Continuous (fun z : ℝ × Space => timePair v z.1 z.2) := by
    unfold timePair
    exact continuous_finsetSum _ (fun j _ =>
      (cA.clm_apply continuous_const).inner (cB.clm_apply continuous_const))
  refine ((iA.add iB).const_mul 3).mono' hm.aestronglyMeasurable (ae_of_all _ (fun z => ?_))
  rw [Real.norm_eq_abs]
  exact pair_bound _ _

theorem slice_time_zero (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (y : Space) :
    ∫ σ in Set.Icc (0 : ℝ) 1, timePair v σ y = 0 := by
  have hd : Differentiable ℝ (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.differentiable (by simp)
  have hVi : ∀ i : Fin 3, ContDiff ℝ ∞ (fun z : ℝ × Space => v z.1 z.2 i) := fun i => by
    have h := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hv.smooth
    exact h
  have hg : ∀ i j : Fin 3, ContDiff ℝ 1 (fun s => fderiv ℝ (fun x => v s x i) y (unitVector j)) := by
    intro i j
    have h := ((joint_partial (fun s x => v s x i) (hVi i) (m := ∞) (n := ∞) (by simp) (by simp)).comp
      (contDiff_id.prodMk (contDiff_const (c := y)))).clm_apply (contDiff_const (c := unitVector j))
    exact h.of_le (by simp)
  have hτ : ∀ σ, Differentiable ℝ (fun x => deriv (fun s => v s x) σ) := by
    intro σ
    rw [time_field_eq P v hv σ]
    exact ((time_field_smooth P v hv).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hdv : ∀ σ, Differentiable ℝ (v σ) := fun σ =>
    (hv.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have dcomp : ∀ σ x (i : Fin 3), deriv (fun s => v s x) σ i = deriv (fun s => v s x i) σ := by
    intro σ x i
    have h := time_hasDeriv v hd σ x
    have h' := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt σ h
    simp only [Function.comp_def] at h'
    rw [h.deriv]
    exact h'.deriv.symm
  have hpt : ∀ σ, timePair v σ y = ∑ j : Fin 3, ∑ i : Fin 3,
      deriv (fun s => fderiv ℝ (fun x => v s x i) y (unitVector j)) σ *
        fderiv ℝ (fun x => v σ x i) y (unitVector j) := by
    intro σ
    unfold timePair
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [inner_coord]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    · rw [← fderiv_component _ (hτ σ y) i]
      rw [show (fun x => deriv (fun s => v s x) σ i) = fun x => deriv (fun s => v s x i) σ from
        funext fun x => dcomp σ x i]
      exact mixed_partial (fun s x => v s x i) (hVi i) σ y j
    · exact (fderiv_component (v σ) (hdv σ y) i (unitVector j)).symm
  have hI : ∀ i j : Fin 3, IntegrableOn (fun σ => deriv (fun s => fderiv ℝ (fun x => v s x i) y
      (unitVector j)) σ * fderiv ℝ (fun x => v σ x i) y (unitVector j)) (Set.Icc (0 : ℝ) 1) := by
    intro i j
    exact (((hg i j).continuous_deriv (by norm_num)).mul (hg i j).continuous).integrableOn_Icc
  have hp : ∀ i j : Fin 3, fderiv ℝ (fun x => v 1 x i) y (unitVector j) =
      fderiv ℝ (fun x => v 0 x i) y (unitVector j) := by
    intro i j
    have e : (fun x => v 1 x i) = fun x => v 0 x i := funext fun x => by
      have := hv.periodic 0 x
      rw [zero_add] at this
      rw [this]
    rw [e]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hI i j))]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [integral_finsetSum _ (fun i _ => hI i j)]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  exact period_ftc (fun s => fderiv ℝ (fun x => v s x i) y (unitVector j)) (hg i j) (hp i j)

end Time

theorem time_term_zero (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, timePair v σ y = 0 := by
  rw [integral_integral_swap (f := fun σ y => timePair v σ y) (Time.joint_integrable P v hv)]
  simp [Time.slice_time_zero P v hv]

theorem time_integrable (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    IntegrableOn (fun σ => ∫ y, timePair v σ y) (Set.Icc (0 : ℝ) 1) :=
  (Time.joint_integrable P v hv).integral_prod_left

end SmoothEnergyIdentityInternal

end Coercive

end Breakdown
