import Breakdown.Uniqueness.FundSolDefs

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FundSol.Internal

def dirDeriv (v : Space) (f : Space → ℝ) (x : Space) : ℝ := fderiv ℝ f x v

theorem contDiff_fderiv_of_smooth {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fderiv ℝ f) :=
  (contDiff_infty_iff_fderiv.1 hf).2

theorem contDiff_dirDeriv {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (v : Space) :
    ContDiff ℝ ∞ (dirDeriv v f) :=
  (contDiff_fderiv_of_smooth hf).clm_apply contDiff_const

theorem differentiable_of_contDiff_infty {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ f :=
  hf.differentiable (by simp)

theorem norm_iteratedFDeriv_dirDeriv_le {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (v : Space)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (dirDeriv v f) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  have h := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ f) (c := v) (x := x) (n := n)
    (contDiff_fderiv_of_smooth hf).contDiffAt (by exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h

theorem norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem norm_iteratedFDeriv_dirDeriv_unit_le {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (dirDeriv (unitVector i) f) x‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  simpa [norm_unitVector] using norm_iteratedFDeriv_dirDeriv_le hf (unitVector i) n x

theorem abs_dirDeriv_le {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (a : Fin 3) (x : Space) :
    |dirDeriv (unitVector a) f x| ≤ ‖iteratedFDeriv ℝ 1 f x‖ := by
  have h := norm_iteratedFDeriv_dirDeriv_unit_le hf a 0 x
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h

theorem abs_dirDeriv_two_le {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (a b : Fin 3) (x : Space) :
    |dirDeriv (unitVector a) (dirDeriv (unitVector b) f) x| ≤ ‖iteratedFDeriv ℝ 2 f x‖ :=
  (abs_dirDeriv_le (contDiff_dirDeriv hf _) a x).trans
    (norm_iteratedFDeriv_dirDeriv_unit_le hf b 1 x)

theorem abs_dirDeriv_three_le {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (a b c : Fin 3) (x : Space) :
    |dirDeriv (unitVector a) (dirDeriv (unitVector b) (dirDeriv (unitVector c) f)) x| ≤
      ‖iteratedFDeriv ℝ 3 f x‖ :=
  ((abs_dirDeriv_two_le (contDiff_dirDeriv hf _) a b x).trans
    (norm_iteratedFDeriv_dirDeriv_unit_le hf c 2 x))

theorem dirDeriv_dirDeriv_apply {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (u v x : Space) :
    dirDeriv u (dirDeriv v f) x = fderiv ℝ (fderiv ℝ f) x u v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (contDiff_fderiv_of_smooth hf).differentiable (by simp) x
  show fderiv ℝ (fun y => fderiv ℝ f y v) x u = _
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem dirDeriv_comm {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (u v : Space) :
    dirDeriv u (dirDeriv v f) = dirDeriv v (dirDeriv u f) := by
  funext x
  rw [dirDeriv_dirDeriv_apply hf, dirDeriv_dirDeriv_apply hf]
  exact hf.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out) u v

theorem secondPartial_eq_dirDeriv {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin 3)
    (x : Space) :
    secondPartial f i j x = dirDeriv (unitVector i) (dirDeriv (unitVector j) f) x := by
  rw [dirDeriv_dirDeriv_apply hf, secondPartial, iteratedFDeriv_two_apply]
  simp

theorem integral_mul_dirDeriv {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (v : Space) (h1 : Integrable (fun x => dirDeriv v f x * g x))
    (h2 : Integrable (fun x => f x * dirDeriv v g x)) (h3 : Integrable (fun x => f x * g x)) :
    ∫ x, f x * dirDeriv v g x = - ∫ x, dirDeriv v f x * g x :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => differentiable_of_contDiff_infty hf x) (fun x _ => differentiable_of_contDiff_infty hg x)

theorem inv_one_add_norm_pow_le (x : Space) {m : ℕ} (hm : 4 ≤ m) :
    (1 + ‖x‖)⁻¹ ^ m ≤ (1 + ‖x‖) ^ (-(4 : ℝ)) := by
  have h0 : 0 < 1 + ‖x‖ := by positivity
  have h1 : (1 + ‖x‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg x])
  rw [Real.rpow_neg h0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← inv_pow]
  exact pow_le_pow_of_le_one (by positivity) h1 hm

theorem integrable_of_abs_le_decay {F : Space → ℝ} (hF : Continuous F) {C : ℝ} {m : ℕ}
    (hm : 4 ≤ m) (hb : ∀ x, |F x| ≤ C * (1 + ‖x‖)⁻¹ ^ m) : Integrable F := by
  have hC : 0 ≤ C := by simpa using (abs_nonneg _).trans (hb 0)
  have hi : Integrable (fun x : Space => (1 + ‖x‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  refine (hi.const_mul C).mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact (hb x).trans (mul_le_mul_of_nonneg_left (inv_one_add_norm_pow_le x hm) hC)

theorem integrable_mul_of_decay {F G : Space → ℝ} (hF : Continuous F) (hG : Continuous G)
    {C D : ℝ} {p q : ℕ} (hpq : 4 ≤ p + q) (hFb : ∀ x, |F x| ≤ C * (1 + ‖x‖)⁻¹ ^ p)
    (hGb : ∀ x, |G x| ≤ D * (1 + ‖x‖)⁻¹ ^ q) : Integrable (fun x => F x * G x) := by
  have hC : 0 ≤ C := by simpa using (abs_nonneg _).trans (hFb 0)
  refine integrable_of_abs_le_decay (hF.mul hG) (C := C * D) hpq fun x => ?_
  rw [abs_mul, pow_add]
  calc |F x| * |G x| ≤ (C * (1 + ‖x‖)⁻¹ ^ p) * (D * (1 + ‖x‖)⁻¹ ^ q) :=
        mul_le_mul (hFb x) (hGb x) (abs_nonneg _) (by positivity)
    _ = C * D * ((1 + ‖x‖)⁻¹ ^ p * (1 + ‖x‖)⁻¹ ^ q) := by ring

end Breakdown.FundSol.Internal
