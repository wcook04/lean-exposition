import Breakdown.Cert.ExtendedCoercivePairingSplitIncrement
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.WeakAeDiff

variable {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}

theorem decay_nonneg (hW : IsWeakSecondDerivState W HW D) : 0 ≤ D := by
  have h := (hW.decay 0 0).1
  simp only [norm_zero, add_zero, div_one] at h
  exact (norm_nonneg _).trans h

theorem fderiv_increment (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) :
    LipschitzWith (Real.toNNReal D) (fderiv ℝ (W σ)) := by
  have hD := decay_nonneg hW
  have hs : ContDiff ℝ 1 (W σ) := hW.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hfc : Continuous (fderiv ℝ (W σ)) := hs.continuous_fderiv one_ne_zero
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hD]
  refine WeakIncrement.increment_of_weakSecondDeriv (f := fderiv ℝ (W σ)) (H := HW σ) hfc (hW.secondDeriv_weak σ)
    b a D (fun ε hε => ⟨1, one_pos, fun z _ w _ => ?_⟩)
  calc ‖HW σ w‖ ≤ D / (1 + ‖w‖) ^ 3 := (hW.decay σ w).2.2
    _ ≤ D := div_le_self hD (one_le_pow₀ (by linarith [norm_nonneg w]))
    _ ≤ D + ε := by linarith

def entry (i j k : Fin 3) : (Space →L[ℝ] Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp
    ((ContinuousLinearMap.apply ℝ Space (unitVector j)).comp
      (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector i)))

def column (j k : Fin 3) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.apply ℝ Space (unitVector j))

theorem locallyIntegrable_clm_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : Space → E} (hg : LocallyIntegrable g) (L : E →L[ℝ] F) :
    LocallyIntegrable (fun y => L (g y)) := fun x => by
  obtain ⟨U, hU, hi⟩ := hg x
  exact ⟨U, hU, L.integrable_comp hi⟩

theorem entry_ae_eq (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) (i j k : Fin 3) :
    ∀ᵐ y, lineDeriv ℝ (fun x => column j k (fderiv ℝ (W σ) x)) y (unitVector i)
      = entry i j k (HW σ y) := by
  have hL := fderiv_increment hW σ
  have hφ : LipschitzWith (‖column j k‖₊ * Real.toNNReal D) (fun x => column j k (fderiv ℝ (W σ) x)) :=
    (column j k).lipschitz.comp hL
  have hloc : LocallyIntegrable (fun y => entry i j k (HW σ y)) := by
    have h := locallyIntegrable_clm_comp (hW.secondDeriv_weak σ j).2.1
      ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.apply ℝ Space (unitVector i)))
    simpa [entry] using h
  refine ae_eq_of_integral_contDiff_smul_eq (hφ.locallyIntegrable_lineDeriv _) hloc fun g hg hgs => ?_
  obtain ⟨Cg, hgL⟩ := hg.lipschitzWith_of_hasCompactSupport hgs (by simp)
  have hs : ContDiff ℝ 1 (W σ) := hW.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hfc : Continuous (fderiv ℝ (W σ)) := hs.continuous_fderiv one_ne_zero
  have int1 : Integrable (fun y => g y • (HW σ y).flip (unitVector j) (unitVector i)) :=
    (locallyIntegrable_clm_comp (hW.secondDeriv_weak σ j).2.1
      (ContinuousLinearMap.apply ℝ Space (unitVector i))).integrable_smul_left_of_hasCompactSupport
      hg.continuous hgs
  have hgc : HasCompactSupport (fun y => fderiv ℝ g y (unitVector i)) := by
    refine (hgs.fderiv (𝕜 := ℝ)).mono ?_
    intro t ht
    rw [Function.mem_support] at ht ⊢
    intro h0
    apply ht
    rw [h0]
    simp
  have int2 : Integrable (fun y => fderiv ℝ g y (unitVector i) • fderiv ℝ (W σ) y (unitVector j)) :=
    (hfc.clm_apply continuous_const).locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      ((hg.continuous_fderiv (by simp)).clm_apply continuous_const) hgc
  have ibp := hφ.integral_lineDeriv_mul_eq (μ := volume) hgL hgs (unitVector i)
  have e1 : ∀ x, lineDeriv ℝ g x (-unitVector i) = -(fderiv ℝ g x (unitVector i)) := fun x => by
    rw [(hg.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    simp
  have w := (hW.secondDeriv_weak σ j).2.2 g ⟨hg, hgs⟩ i
  have wk := congrArg (EuclideanSpace.proj k : Space →L[ℝ] ℝ) w
  rw [← ContinuousLinearMap.integral_comp_comm _ int1, map_neg,
    ← ContinuousLinearMap.integral_comp_comm _ int2] at wk
  simp only [map_smul, smul_eq_mul, ContinuousLinearMap.flip_apply] at wk
  calc ∫ x, g x • lineDeriv ℝ (fun x => column j k (fderiv ℝ (W σ) x)) x (unitVector i)
      = ∫ x, lineDeriv ℝ (fun x => column j k (fderiv ℝ (W σ) x)) x (unitVector i) * g x := by
        congr 1; funext x; rw [smul_eq_mul, mul_comm]
    _ = ∫ x, lineDeriv ℝ g x (-unitVector i) * column j k (fderiv ℝ (W σ) x) := ibp
    _ = -∫ x, fderiv ℝ g x (unitVector i) * column j k (fderiv ℝ (W σ) x) := by
        simp only [e1, neg_mul, integral_neg]
    _ = ∫ x, g x • entry i j k (HW σ x) := by
        simp only [column, entry, ContinuousLinearMap.coe_comp, Function.comp_apply,
          ContinuousLinearMap.apply_apply, smul_eq_mul]
        rw [wk]

theorem entry_ext {A B : Space →L[ℝ] Space →L[ℝ] Space} (h : ∀ i j k, entry i j k A = entry i j k B) :
    A = B := by
  have e : ∀ (C : Space →L[ℝ] Space →L[ℝ] Space) (a b : Space),
      C a b = ∑ i : Fin 3, ∑ j : Fin 3, (a i * b j) • C (unitVector i) (unitVector j) := by
    intro C a b
    conv_lhs => rw [WeakIncrement.eq_sum_basis a, WeakIncrement.eq_sum_basis b]
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  have hij : ∀ i j, A (unitVector i) (unitVector j) = B (unitVector i) (unitVector j) := by
    intro i j
    ext k
    have := h i j k
    simpa [entry] using this
  exact ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => by
    rw [e A, e B]
    simp only [hij]

theorem ae_hasFDerivAt (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) :
    ∀ᵐ y, HasFDerivAt (fderiv ℝ (W σ)) (HW σ y) y := by
  have hdiff := (fderiv_increment hW σ).ae_differentiableAt (μ := volume)
  have hall : ∀ᵐ y, ∀ i j k : Fin 3, lineDeriv ℝ (fun x => column j k (fderiv ℝ (W σ) x)) y (unitVector i)
      = entry i j k (HW σ y) := by
    simp only [ae_all_iff]
    exact fun i j k => entry_ae_eq hW σ i j k
  filter_upwards [hdiff, hall] with y hy hc
  have key : fderiv ℝ (fderiv ℝ (W σ)) y = HW σ y := by
    refine entry_ext fun i j k => ?_
    rw [← hc i j k]
    have hd : HasFDerivAt (fun x => column j k (fderiv ℝ (W σ) x))
        ((column j k).comp (fderiv ℝ (fderiv ℝ (W σ)) y)) y :=
      (column j k).hasFDerivAt.comp y hy.hasFDerivAt
    rw [(hd.hasLineDerivAt (unitVector i)).lineDeriv]
    simp [entry, column]
  rw [← key]
  exact hy.hasFDerivAt

end Internal.WeakAeDiff

end CoerciveWeak

end Breakdown
