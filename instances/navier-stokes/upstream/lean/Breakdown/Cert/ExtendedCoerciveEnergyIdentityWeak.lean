import Breakdown.Cert.CoerciveSmoothEnergyIdentityCutoff
import Breakdown.Cert.ExtendedCoerciveStatement

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace EnergyIdentityWeakInternal

open Coercive Coercive.EnergyIdentityInternal Coercive.SmoothEnergyIdentityInternal

def WeakPartial (f F : Space → ℝ) (j : Fin 3) : Prop :=
  LocallyIntegrable f ∧ LocallyIntegrable F ∧
    ∀ φ, IsTestFunction φ → ∫ y, φ y * F y = -∫ y, fderiv ℝ φ y (unitVector j) * f y

private theorem unit_norm_one (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

private theorem locint_comp {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : Space → E} (hf : LocallyIntegrable f)
    (L : E →L[ℝ] G) : LocallyIntegrable (fun y => L (f y)) :=
  locallyIntegrable_iff.2 fun _ hk => L.integrable_comp (hf.integrableOn_isCompact hk)

private theorem test_mul_int {F : Space → ℝ} (hF : LocallyIntegrable F) {φ : Space → ℝ}
    (hφ : IsTestFunction φ) : Integrable (fun y => φ y * F y) := by
  simpa [smul_eq_mul] using hF.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2

private theorem test_deriv_cont {φ : Space → ℝ} (hφ : IsTestFunction φ) (j : Fin 3) :
    Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
  (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem test_deriv_supp {φ : Space → ℝ} (hφ : IsTestFunction φ) (j : Fin 3) :
    HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
  hφ.2.fderiv_apply (𝕜 := ℝ) _

private theorem test_deriv_mul_int {f : Space → ℝ} (hf : LocallyIntegrable f) {φ : Space → ℝ}
    (hφ : IsTestFunction φ) (j : Fin 3) : Integrable (fun y => fderiv ℝ φ y (unitVector j) * f y) := by
  simpa [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport (test_deriv_cont hφ j)
    (test_deriv_supp hφ j)

theorem weakPartial_of_contDiff (f : Space → ℝ) (hf : ContDiff ℝ 1 f) (j : Fin 3) :
    WeakPartial f (fun y => fderiv ℝ f y (unitVector j)) j := by
  refine ⟨hf.continuous.locallyIntegrable,
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).locallyIntegrable, fun φ hφ => ?_⟩
  exact ibp φ f j (hφ.1.of_le (by simp)) hf hφ.2

theorem WeakPartial.add {f g F G : Space → ℝ} {j : Fin 3} (hf : WeakPartial f F j) (hg : WeakPartial g G j) :
    WeakPartial (fun y => f y + g y) (fun y => F y + G y) j := by
  refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, fun φ hφ => ?_⟩
  have e1 : (fun y => φ y * (F y + G y)) = fun y => φ y * F y + φ y * G y := by
    funext y; ring
  have e2 : (fun y => fderiv ℝ φ y (unitVector j) * (f y + g y)) =
      fun y => fderiv ℝ φ y (unitVector j) * f y + fderiv ℝ φ y (unitVector j) * g y := by
    funext y; ring
  rw [e1, e2, integral_add (test_mul_int hf.2.1 hφ) (test_mul_int hg.2.1 hφ),
    integral_add (test_deriv_mul_int hf.1 hφ j) (test_deriv_mul_int hg.1 hφ j), hf.2.2 φ hφ, hg.2.2 φ hφ]
  ring

theorem WeakPartial.const_mul {f F : Space → ℝ} {j : Fin 3} (hf : WeakPartial f F j) (c : ℝ) :
    WeakPartial (fun y => c * f y) (fun y => c * F y) j := by
  refine ⟨hf.1.smul c, hf.2.1.smul c, fun φ hφ => ?_⟩
  have e1 : (fun y => φ y * (c * F y)) = fun y => c * (φ y * F y) := by
    funext y; ring
  have e2 : (fun y => fderiv ℝ φ y (unitVector j) * (c * f y)) =
      fun y => c * (fderiv ℝ φ y (unitVector j) * f y) := by
    funext y; ring
  rw [e1, e2, integral_const_mul, integral_const_mul, hf.2.2 φ hφ]
  ring

theorem WeakPartial.sum {ι : Type*} (s : Finset ι) {f F : ι → Space → ℝ} {j : Fin 3}
    (h : ∀ t ∈ s, WeakPartial (f t) (F t) j) :
    WeakPartial (fun y => ∑ t ∈ s, f t y) (fun y => ∑ t ∈ s, F t y) j := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨locallyIntegrable_const 0, locallyIntegrable_const 0, fun φ _ => by simp⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih (fun t ht => h t (Finset.mem_insert_of_mem ht)))

theorem WeakPartial.mul_smooth {f F ψ : Space → ℝ} {j : Fin 3} (hF : WeakPartial f F j) (hf : Continuous f)
    (hψ : ContDiff ℝ ∞ ψ) :
    WeakPartial (fun y => f y * ψ y) (fun y => F y * ψ y + f y * fderiv ℝ ψ y (unitVector j)) j := by
  have cψ : Continuous ψ := hψ.continuous
  have cdψ : Continuous (fun y => fderiv ℝ ψ y (unitVector j)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have lFψ : LocallyIntegrable (fun y => F y * ψ y) :=
    locallyIntegrable_iff.2 fun _ hk => (hF.2.1.integrableOn_isCompact hk).mul_continuousOn cψ.continuousOn hk
  refine ⟨(hf.mul cψ).locallyIntegrable, lFψ.add (hf.mul cdψ).locallyIntegrable, fun φ hφ => ?_⟩
  have hT : IsTestFunction (fun y => φ y * ψ y) := ⟨hφ.1.mul hψ, hφ.2.mul_right⟩
  have key := hF.2.2 _ hT
  have hd : ∀ y, fderiv ℝ (fun y => φ y * ψ y) y (unitVector j) =
      fderiv ℝ φ y (unitVector j) * ψ y + φ y * fderiv ℝ ψ y (unitVector j) := by
    intro y
    rw [fderiv_fun_mul ((hφ.1.differentiable (by simp)) y) ((hψ.differentiable (by simp)) y)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  simp only [hd, add_mul] at key
  have i1 : Integrable (fun y => φ y * ψ y * F y) := test_mul_int hF.2.1 hT
  have i2 : Integrable (fun y => φ y * fderiv ℝ ψ y (unitVector j) * f y) :=
    ((hφ.1.continuous.mul cdψ).mul hf).integrable_of_hasCompactSupport (hφ.2.mul_right.mul_right)
  have i3 : Integrable (fun y => fderiv ℝ φ y (unitVector j) * ψ y * f y) :=
    (((test_deriv_cont hφ j).mul cψ).mul hf).integrable_of_hasCompactSupport
      ((test_deriv_supp hφ j).mul_right.mul_right)
  rw [integral_add i3 i2] at key
  have e1 : (fun y => φ y * (F y * ψ y + f y * fderiv ℝ ψ y (unitVector j))) =
      fun y => φ y * ψ y * F y + φ y * fderiv ℝ ψ y (unitVector j) * f y := by
    funext y; ring
  have e3 : (fun y => fderiv ℝ φ y (unitVector j) * (f y * ψ y)) =
      fun y => fderiv ℝ φ y (unitVector j) * ψ y * f y := by
    funext y; ring
  rw [e1, e3, integral_add i1 i2, key]
  ring

theorem weakPartial_secondDeriv {W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (a : Fin 3)
    (hW : IsWeakGradient (fun y => fderiv ℝ W₀ y (unitVector a)) (fun y => (H y).flip (unitVector a)))
    (b m : Fin 3) :
    WeakPartial (fun y => fderiv ℝ W₀ y (unitVector a) b) (fun y => H y (unitVector m) (unitVector a) b) m := by
  obtain ⟨hf, hg, hid⟩ := hW
  have lf := locint_comp hf (EuclideanSpace.proj b : Space →L[ℝ] ℝ)
  have lgv := locint_comp hg (ContinuousLinearMap.apply ℝ Space (unitVector m))
  have lg := locint_comp lgv (EuclideanSpace.proj b : Space →L[ℝ] ℝ)
  simp only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.flip_apply] at lgv lg
  refine ⟨by simpa using lf, by simpa using lg, fun φ hφ => ?_⟩
  have i1 : Integrable (fun y => φ y • H y (unitVector m) (unitVector a)) :=
    lgv.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  have i2 : Integrable (fun y => fderiv ℝ φ y (unitVector m) • fderiv ℝ W₀ y (unitVector a)) :=
    hf.integrable_smul_left_of_hasCompactSupport (test_deriv_cont hφ m) (test_deriv_supp hφ m)
  have hv := hid φ hφ m
  simp only [ContinuousLinearMap.flip_apply] at hv
  have c1 := (EuclideanSpace.proj b : Space →L[ℝ] ℝ).integral_comp_comm i1
  have c2 := (EuclideanSpace.proj b : Space →L[ℝ] ℝ).integral_comp_comm i2
  rw [hv, map_neg, ← c2] at c1
  simpa [smul_eq_mul] using c1

theorem weak_ibp {f F ψ : Space → ℝ} {j : Fin 3} (hF : WeakPartial f F j) (hψ : ContDiff ℝ ∞ ψ)
    (h1 : Integrable (fun y => f y * fderiv ℝ ψ y (unitVector j)))
    (h2 : Integrable (fun y => F y * ψ y))
    (h3 : Integrable (fun y => |f y| * |ψ y| / (1 + ‖y‖))) :
    ∫ y, f y * fderiv ℝ ψ y (unitVector j) = -∫ y, F y * ψ y := by
  obtain ⟨C, hC0, hC⟩ := bump_deriv_bound
  have cψ : Continuous ψ := hψ.continuous
  have cdψ : Continuous (fun y => fderiv ℝ ψ y (unitVector j)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have mf : AEStronglyMeasurable f := hF.1.aestronglyMeasurable
  have mF : AEStronglyMeasurable F := hF.2.1.aestronglyMeasurable
  have hT : ∀ n, IsTestFunction (fun y => cutoff (radiusSeq n) y * ψ y) := fun n =>
    ⟨(cutoff_contDiff _).mul hψ, (cutoff_support (radiusSeq_pos n)).mul_right⟩
  have hd : ∀ n y, fderiv ℝ (fun y => cutoff (radiusSeq n) y * ψ y) y (unitVector j) =
      fderiv ℝ (cutoff (radiusSeq n)) y (unitVector j) * ψ y
        + cutoff (radiusSeq n) y * fderiv ℝ ψ y (unitVector j) := by
    intro n y
    rw [fderiv_fun_mul (((cutoff_contDiff _).differentiable (by simp)) y) ((hψ.differentiable (by simp)) y)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have step : ∀ n, ∫ y, cutoff (radiusSeq n) y * ψ y * F y =
      -∫ y, (fderiv ℝ (cutoff (radiusSeq n)) y (unitVector j) * ψ y
        + cutoff (radiusSeq n) y * fderiv ℝ ψ y (unitVector j)) * f y := by
    intro n
    have key := hF.2.2 _ (hT n)
    simp only [hd] at key
    exact key
  have lim1 : Tendsto (fun n => ∫ y, cutoff (radiusSeq n) y * ψ y * F y) atTop (𝓝 (∫ y, F y * ψ y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖F y * ψ y‖) (fun n => ?_) h2.norm
      (fun n => ?_) ?_
    · exact (((cutoff_contDiff _).continuous.mul cψ).aestronglyMeasurable).mul mF
    · refine Eventually.of_forall (fun y => ?_)
      have e : cutoff (radiusSeq n) y * ψ y * F y = cutoff (radiusSeq n) y * (F y * ψ y) := by ring
      rw [e, norm_mul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)
    · refine Eventually.of_forall (fun y => ?_)
      apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_eventually_one y] with n hn
      rw [hn]
      ring
  have lim2 : Tendsto (fun n => ∫ y, (fderiv ℝ (cutoff (radiusSeq n)) y (unitVector j) * ψ y
        + cutoff (radiusSeq n) y * fderiv ℝ ψ y (unitVector j)) * f y) atTop
      (𝓝 (∫ y, f y * fderiv ℝ ψ y (unitVector j))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => C * (|f y| * |ψ y| / (1 + ‖y‖)) + ‖f y * fderiv ℝ ψ y (unitVector j)‖)
      (fun n => ?_) ((h3.const_mul C).add h1.norm) (fun n => ?_) ?_
    · refine (Continuous.aestronglyMeasurable ?_).mul mf
      exact ((((cutoff_contDiff _).continuous_fderiv (by simp)).clm_apply continuous_const).mul cψ).add
        ((cutoff_contDiff _).continuous.mul cdψ)
    · refine Eventually.of_forall (fun y => ?_)
      have hb := cutoff_fderiv_bound hC (radiusSeq_one_le n) y (unitVector j)
      rw [unit_norm_one, mul_one] at hb
      have e : (fderiv ℝ (cutoff (radiusSeq n)) y (unitVector j) * ψ y
          + cutoff (radiusSeq n) y * fderiv ℝ ψ y (unitVector j)) * f y =
          fderiv ℝ (cutoff (radiusSeq n)) y (unitVector j) * (ψ y * f y)
            + cutoff (radiusSeq n) y * (f y * fderiv ℝ ψ y (unitVector j)) := by ring
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        calc |fderiv ℝ (cutoff (radiusSeq n)) y (unitVector j)| * (|ψ y| * |f y|)
            ≤ C / (1 + ‖y‖) * (|ψ y| * |f y|) := mul_le_mul_of_nonneg_right hb (by positivity)
          _ = C * (|f y| * |ψ y| / (1 + ‖y‖)) := by ring
      · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)
    · refine Eventually.of_forall (fun y => ?_)
      apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_eventually_one y, cutoff_fderiv_eventually_zero y] with n hn hn'
      rw [hn, hn']
      simp [mul_comm]
  have lim3 : Tendsto (fun n => ∫ y, cutoff (radiusSeq n) y * ψ y * F y) atTop
      (𝓝 (-∫ y, f y * fderiv ℝ ψ y (unitVector j))) := by
    simp_rw [step]
    exact lim2.neg
  have := tendsto_nhds_unique lim1 lim3
  linarith

end EnergyIdentityWeakInternal

end CoerciveWeak

end Breakdown
