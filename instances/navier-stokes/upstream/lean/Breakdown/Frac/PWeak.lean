import Breakdown.Frac.StProfile
import Breakdown.Frac.OpExports
import Breakdown.Frac.RExports
import Breakdown.Frac.PFlow
import Breakdown.Frac.PSlice

open MeasureTheory Set Real Filter
open scoped ContDiff Topology

noncomputable section

namespace Breakdown

namespace FracInternal

namespace WeakProfile

theorem norm_iteratedFDeriv_scaled (f : Space → Space) (hf : ContDiff ℝ ∞ f) (c l : ℝ) (j : ℕ)
    (y : Space) : ‖iteratedFDeriv ℝ j (fun x => c • f (l • x)) y‖ =
      |c| * |l| ^ j * ‖iteratedFDeriv ℝ j f (l • y)‖ := by
  have hj : ContDiff ℝ j f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hc : ContDiff ℝ j (fun x => f (l • x)) := hj.comp (contDiff_const_smul l)
  rw [iteratedFDeriv_const_smul_apply' hc.contDiffAt,
    congrFun (iteratedFDeriv_comp_const_smul l hj) y, norm_smul, norm_smul, norm_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc]

theorem scale_bounded {α μ : ℝ} {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ j ≤ 3, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ C) :
    ∀ j ≤ 3, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ j (scaleField α μ f) y‖ ≤ C := by
  intro j hj
  obtain ⟨C, hC⟩ := hb j hj
  refine ⟨|μ ^ (1 - 1 / (2 * α))| * |μ ^ (1 / (2 * α))| ^ j * C, fun y => ?_⟩
  have e : scaleField α μ f = fun x => μ ^ (1 - 1 / (2 * α)) • f (μ ^ (1 / (2 * α)) • x) := rfl
  rw [e, norm_iteratedFDeriv_scaled f hf]
  exact mul_le_mul_of_nonneg_left (hC _) (by positivity)

theorem decay_bdd {f : Space → Space} (hf : IsDecayField f) :
    ∃ B : ℝ, (∀ y, ‖f y‖ ≤ B) ∧ ∀ y, ‖fderiv ℝ f y‖ ≤ B := by
  obtain ⟨-, -, C, hC⟩ := hf
  refine ⟨|C|, fun y => ?_, fun y => ?_⟩
  · have h1 : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    calc ‖f y‖ ≤ C / (1 + ‖y‖) := (hC y).1
      _ ≤ |C| / (1 + ‖y‖) := div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| := div_le_self (abs_nonneg C) h1
  · have h1 : (1 : ℝ) ≤ (1 + ‖y‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg y])
    calc ‖fderiv ℝ f y‖ ≤ C / (1 + ‖y‖) ^ 2 := (hC y).2
      _ ≤ |C| / (1 + ‖y‖) ^ 2 := div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| := div_le_self (abs_nonneg C) h1

theorem adv_bdd {f : Space → Space} {B : ℝ} (h1 : ∀ y, ‖f y‖ ≤ B) (h2 : ∀ y, ‖fderiv ℝ f y‖ ≤ B) :
    ∀ y, ‖advectionAt f y‖ ≤ B * B := by
  intro y
  have hB : 0 ≤ B := (norm_nonneg _).trans (h1 0)
  unfold advectionAt
  exact ((fderiv ℝ f y).le_opNorm (f y)).trans (mul_le_mul (h2 y) (h1 y) (norm_nonneg _) hB)

theorem continuous_advection {v : Space → Space} (hv : ContDiff ℝ ∞ v) :
    Continuous (advectionAt v) := by
  unfold advectionAt
  exact (hv.continuous_fderiv (by simp)).clm_apply hv.continuous

theorem integrable_inner_bdd {f : Space → Space} (hf : Continuous f) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B)
    (ψ : SchwartzMap Space Space) : Integrable (fun x => inner ℝ (f x) (ψ x)) := by
  refine (ψ.integrable.norm.const_mul B).mono' (hf.inner ψ.continuous).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  calc ‖inner ℝ (f x) (ψ x)‖ ≤ ‖f x‖ * ‖ψ x‖ := norm_inner_le_norm _ _
    _ ≤ B * ‖ψ x‖ := mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

theorem weighted_norm_le_abs {α K d : ℝ} (hα : 1 < α) {x u : Space}
    (h : ‖u‖ ≤ K * |d| * (1 + ‖x‖) ^ (-(4 * α - 1))) : ‖u‖ ≤ |K| * |d| := by
  have ht : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hr := Real.rpow_le_one_of_one_le_of_nonpos ht (z := -(4 * α - 1)) (by linarith)
  have hr0 := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + ‖x‖) (-(4 * α - 1))
  calc ‖u‖ ≤ K * |d| * (1 + ‖x‖) ^ (-(4 * α - 1)) := h
    _ ≤ |K| * |d| * (1 + ‖x‖) ^ (-(4 * α - 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg d)) hr0
    _ ≤ |K| * |d| * 1 := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = |K| * |d| := mul_one _

theorem sq_le_of_le {e : ℝ} (x : Space) (c : ℝ) {u : Space} (h : ‖u‖ ≤ c * (1 + ‖x‖) ^ (-e)) :
    ‖u‖ ^ 2 ≤ c ^ 2 * (1 + ‖x‖) ^ (-(2 * e)) := by
  have hx : 0 < 1 + ‖x‖ := by positivity
  have e1 : (1 + ‖x‖) ^ (-(2 * e)) = ((1 + ‖x‖) ^ (-e)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  calc ‖u‖ ^ 2 ≤ (c * (1 + ‖x‖) ^ (-e)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by rw [e1, mul_pow]

theorem integrable_weight {α : ℝ} (hα : 1 < α) :
    Integrable (fun x : Space => (1 + ‖x‖) ^ (-(2 * (4 * α - 1)))) := by
  apply integrable_one_add_norm
  rw [finrank_euclideanSpace, Fintype.card_fin]
  push_cast
  linarith

theorem smooth_dir_scalar {h : Space → ℝ} (hh : ContDiff ℝ ∞ h) (v : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ h y v) :=
  (hh.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const

theorem coord_smooth {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y => φ y i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hφ

theorem coord_dir {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) (x v : Space) :
    fderiv ℝ (fun y => φ y i) x v = fderiv ℝ φ x v i := by
  have hd : DifferentiableAt ℝ φ x := hφ.differentiable (by simp) x
  have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  have e : (fun y => φ y i) = (EuclideanSpace.proj (𝕜 := ℝ) i) ∘ φ := by
    funext y
    simp
  rw [e, h]
  simp

theorem gradient_inner (g : Space → ℝ) (x w : Space) :
    inner ℝ (gradientAt g x) w = ∑ i : Fin 3, fderiv ℝ g x (unitVector i) * w i := by
  unfold gradientAt
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, unitVector, EuclideanSpace.inner_single_left]
  simp

theorem coord_le (w : Space) (i : Fin 3) : |w i| ≤ ‖w‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le w i

theorem unit_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem gradient_pairing_zero {p : Space → ℝ} (hp : ContDiff ℝ ∞ p) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y, |p x - p y| ≤ L * ‖x - y‖) (ψ : SchwartzMap Space Space)
    (hdiv : ∀ y, divergenceAt ψ y = 0) :
    Integrable (fun x => inner ℝ (gradientAt p x) (ψ x)) ∧
      ∫ x, inner ℝ (gradientAt p x) (ψ x) = 0 := by
  have hψs : ContDiff ℝ ∞ (ψ : Space → Space) := ψ.smooth ⊤
  have hslope : LipschitzWith (Real.toNNReal L) p := LipschitzWith.of_dist_le' fun x y => by
    rw [Real.dist_eq, dist_eq_norm]
    exact hL x y
  have hD : ∀ x, ‖fderiv ℝ p x‖ ≤ L := fun x => by
    have h0 := norm_fderiv_le_of_lipschitz ℝ hslope (x₀ := x)
    rwa [Real.coe_toNNReal', max_eq_left hL0] at h0
  have hG : ∀ x, |p x| ≤ |p 0| + L * ‖x‖ := fun x => by
    have h0 := hL x 0
    rw [sub_zero] at h0
    have h5 := abs_sub_abs_le_abs_sub (p x) (p 0)
    linarith
  have I0 : Integrable (fun x => ‖ψ x‖) := ψ.integrable.norm
  have I1 : Integrable (fun x => ‖x‖ * ‖ψ x‖) := by
    simpa using ψ.integrable_pow_mul volume 1
  have J0 : Integrable (fun x => ‖fderiv ℝ ψ x‖) := by
    simpa [norm_iteratedFDeriv_one] using ψ.integrable_pow_mul_iteratedFDeriv volume 0 1
  have J1 : Integrable (fun x => ‖x‖ * ‖fderiv ℝ ψ x‖) := by
    simpa [norm_iteratedFDeriv_one] using ψ.integrable_pow_mul_iteratedFDeriv volume 1 1
  have hpd : ∀ x (i : Fin 3), |fderiv ℝ p x (unitVector i)| ≤ L := fun x i => by
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ p x (unitVector i)‖ ≤ ‖fderiv ℝ p x‖ * ‖unitVector i‖ := (fderiv ℝ p x).le_opNorm _
      _ ≤ L := by rw [unit_norm, mul_one]; exact hD x
  have hdir : ∀ x (i : Fin 3), |fderiv ℝ (fun y => ψ y i) x (unitVector i)| ≤ ‖fderiv ℝ ψ x‖ :=
    fun x i => by
      rw [coord_dir hψs]
      calc |fderiv ℝ ψ x (unitVector i) i| ≤ ‖fderiv ℝ ψ x (unitVector i)‖ := coord_le _ i
        _ ≤ ‖fderiv ℝ ψ x‖ * ‖unitVector i‖ := (fderiv ℝ ψ x).le_opNorm _
        _ = ‖fderiv ℝ ψ x‖ := by rw [unit_norm, mul_one]
  have Ia : ∀ i : Fin 3, Integrable (fun x => fderiv ℝ p x (unitVector i) * ψ x i) := fun i => by
    refine (I0.const_mul L).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact (((smooth_dir_scalar hp _).continuous).mul
        (coord_smooth hψs i).continuous).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hpd x i) (coord_le _ i) (abs_nonneg _) hL0
  have Ib : ∀ i : Fin 3, Integrable (fun x => p x * fderiv ℝ (fun y => ψ y i) x (unitVector i)) :=
    fun i => by
      refine ((J0.const_mul |p 0|).add (J1.const_mul L)).mono' ?_ (Eventually.of_forall fun x => ?_)
      · exact (hp.continuous.mul
          (smooth_dir_scalar (coord_smooth hψs i) _).continuous).aestronglyMeasurable
      · show _ ≤ |p 0| * ‖fderiv ℝ ψ x‖ + L * (‖x‖ * ‖fderiv ℝ ψ x‖)
        rw [Real.norm_eq_abs, abs_mul]
        calc |p x| * |fderiv ℝ (fun y => ψ y i) x (unitVector i)|
            ≤ (|p 0| + L * ‖x‖) * ‖fderiv ℝ ψ x‖ :=
              mul_le_mul (hG x) (hdir x i) (abs_nonneg _) (by positivity)
          _ = _ := by ring
  have Ic : ∀ i : Fin 3, Integrable (fun x => p x * ψ x i) := fun i => by
    refine ((I0.const_mul |p 0|).add (I1.const_mul L)).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact (hp.continuous.mul (coord_smooth hψs i).continuous).aestronglyMeasurable
    · show _ ≤ |p 0| * ‖ψ x‖ + L * (‖x‖ * ‖ψ x‖)
      rw [Real.norm_eq_abs, abs_mul]
      calc |p x| * |ψ x i| ≤ (|p 0| + L * ‖x‖) * ‖ψ x‖ :=
            mul_le_mul (hG x) (coord_le _ i) (abs_nonneg _) (by positivity)
        _ = _ := by ring
  have hterm : ∀ i : Fin 3, ∫ x, fderiv ℝ p x (unitVector i) * ψ x i =
      -∫ x, p x * fderiv ℝ (fun y => ψ y i) x (unitVector i) := fun i => by
    rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (Ia i) (Ib i) (Ic i)
      (fun x _ => (hp.differentiable (by simp)) x)
      (fun x _ => ((coord_smooth hψs i).differentiable (by simp)) x), neg_neg]
  have hfun : (fun x => inner ℝ (gradientAt p x) (ψ x)) =
      fun x => ∑ i : Fin 3, fderiv ℝ p x (unitVector i) * ψ x i := by
    funext x
    exact gradient_inner p x (ψ x)
  rw [hfun]
  refine ⟨integrable_finsetSum _ (fun i _ => Ia i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => Ia i), Finset.sum_congr rfl (fun i _ => hterm i),
    Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => Ib i)]
  have hz : (fun x => ∑ i : Fin 3, p x * fderiv ℝ (fun y => ψ y i) x (unitVector i)) =
      fun _ => 0 := by
    funext x
    rw [← Finset.mul_sum]
    simp_rw [coord_dir hψs]
    have h0 := hdiv x
    unfold divergenceAt at h0
    rw [h0, mul_zero]
  rw [hz, integral_zero, neg_zero]

theorem comp_increment {P : Space → ℝ} {M : ℝ} (hP : ∀ u w, |P u - P w| ≤ M * ‖u - w‖)
    (k l : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) :
    ∀ x y, |k * P (R (l • x)) - k * P (R (l • y))| ≤ (|k| * M * |l|) * ‖x - y‖ := by
  intro x y
  rw [← mul_sub, abs_mul]
  have h3 := hP (R (l • x)) (R (l • y))
  rw [← map_sub, LinearIsometryEquiv.norm_map, ← smul_sub, norm_smul, Real.norm_eq_abs] at h3
  calc |k| * |P (R (l • x)) - P (R (l • y))| ≤ |k| * (M * (|l| * ‖x - y‖)) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ = (|k| * M * |l|) * ‖x - y‖ := by ring

theorem pressure_increment {α a : ℝ} (hα : 1 < α) {U : Space → Space} {P : Space → ℝ}
    (h : IsRotatingProfile α a 1 U P) (s₀ t : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y,
      |selfSimilarPressure α a P s₀ t x - selfSimilarPressure α a P s₀ t y| ≤ L * ‖x - y‖ := by
  obtain ⟨C, hC⟩ := h.decay 0
  have hPd : Differentiable ℝ P := h.smooth_pressure.differentiable (by simp)
  have hb : ∀ y, ‖fderiv ℝ P y‖₊ ≤ Real.toNNReal (max C 0) := by
    intro y
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal', max_eq_left (le_max_right C 0),
      ← norm_iteratedFDeriv_one]
    have h2 : ‖iteratedFDeriv ℝ 1 P y‖ ≤ C * (1 + ‖y‖) ^ (-(4 * α - 1 + ((0 : ℕ) : ℝ))) :=
      (hC y).2.1
    have ht : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    have hr := Real.rpow_le_one_of_one_le_of_nonpos ht (z := -(4 * α - 1 + ((0 : ℕ) : ℝ)))
      (by push_cast; linarith)
    have hr0 := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + ‖y‖)
      (-(4 * α - 1 + ((0 : ℕ) : ℝ)))
    calc ‖iteratedFDeriv ℝ 1 P y‖ ≤ C * (1 + ‖y‖) ^ (-(4 * α - 1 + ((0 : ℕ) : ℝ))) := h2
      _ ≤ max C 0 * (1 + ‖y‖) ^ (-(4 * α - 1 + ((0 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hr0
      _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hr (le_max_right _ _)
      _ = max C 0 := mul_one _
  have hslope := lipschitzWith_of_nnnorm_fderiv_le hPd hb
  have hP : ∀ u w, |P u - P w| ≤ max C 0 * ‖u - w‖ := fun u w => by
    have h0 := hslope.dist_le_mul u w
    rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal', max_eq_left (le_max_right C 0)] at h0
  refine ⟨|((1 - t)⁻¹) ^ (2 - 1 / α)| * max C 0 * |((1 - t)⁻¹) ^ (1 / (2 * α))|,
    mul_nonneg (mul_nonneg (abs_nonneg _) (le_max_right _ _)) (abs_nonneg _), ?_⟩
  exact comp_increment hP _ _ _

theorem pressure_smooth {α a : ℝ} {U : Space → Space} {P : Space → ℝ}
    (h : IsRotatingProfile α a 1 U P) (s₀ t : ℝ) :
    ContDiff ℝ ∞ (selfSimilarPressure α a P s₀ t) := by
  unfold selfSimilarPressure
  exact contDiff_const.mul
    (h.smooth_pressure.comp ((axialRotation _).contDiff.comp (contDiff_const_smul _)))

end WeakProfile

end FracInternal

open FracInternal.WeakProfile in
theorem selfSimilarWeak_of (h1 : SelfSimilarMomentum) (h2 : SelfSimilarTimeBound)
    (h3 : RotatingSliceDecay) (h4 : ∀ α : ℝ, 1 < α → α < 3 / 2 → Freq.NiceFieldProps α) :
    SelfSimilarWeak := by
  intro α hα hα' a U P hprof s₀ T hT0 hT1
  have hα32 : α < 3 / 2 := by linarith
  have hsl : ∀ σ, IsDecayField (rotatingSlice a U σ) := fun σ => (h3 α hα hα' a U P hprof σ).1
  have hdec : ∀ t, t < 1 → IsDecayField (selfSimilarField α a U s₀ t) := fun t ht =>
    Freq.decayFieldScale α (by linarith) ((1 - t)⁻¹)
      (rotatingSlice a U (s₀ - Real.log (1 - t))) (inv_pos.mpr (by linarith)) (hsl _)
  have hcont : ∀ t, Continuous (selfSimilarField α a U s₀ t) := fun t => by
    unfold selfSimilarField scaleField
    exact (((hsl _).1.continuous).comp (continuous_id.const_smul (((1 - t)⁻¹) ^ (1 / (2 * α))))).const_smul (((1 - t)⁻¹) ^ (1 - 1 / (2 * α)))
  have pair_int : ∀ (ψ : SchwartzMap Space Space) τ, τ < 1 →
      Integrable (fun x => inner ℝ (selfSimilarField α a U s₀ τ x) (ψ x)) := by
    intro ψ τ hτ
    obtain ⟨B, hB1, -⟩ := decay_bdd (hdec τ hτ)
    exact integrable_inner_bdd (hcont τ) hB1 ψ
  obtain ⟨K, hK⟩ := h2 α hα hα' a U P hprof s₀ T hT1
  have hKa : ∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T, ∀ x,
      ‖selfSimilarField α a U s₀ t x - selfSimilarField α a U s₀ t' x‖ ≤ |K| * |t - t'| :=
    fun t ht t' ht' x => weighted_norm_le_abs hα (hK t ht t' ht' x)
  have hint : ∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T,
      Integrable (fun x => ‖selfSimilarField α a U s₀ t x - selfSimilarField α a U s₀ t' x‖ ^ 2) := by
    intro t ht t' ht'
    refine ((integrable_weight hα).const_mul ((K * |t - t'|) ^ 2)).mono' ?_
      (Eventually.of_forall fun x => ?_)
    · exact (((hcont t).sub (hcont t')).norm.pow 2).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      exact sq_le_of_le x _ (hK t ht t' ht' x)
  refine ⟨fun t ht => hdec t (by linarith [ht.2]), ?_, hint, ?_, ?_, ?_⟩
  · have hEq : EqOn (fun t => Freq.embedX (selfSimilarField α a U s₀ t))
        (fun t => Freq.fracDilX α ((1 - t)⁻¹)
          (Freq.embedX (rotatingSlice a U (s₀ - Real.log (1 - t))))) (Icc 0 T) := by
      intro t ht
      have hμ : 0 < (1 - t)⁻¹ := inv_pos.mpr (by linarith [ht.2])
      exact (Freq.fracEmbedDilate α (by linarith) (Freq.fracDilationAlgebra_holds α hα)
        (Freq.decayFieldScale α (by linarith)) ((1 - t)⁻¹) _ hμ (hsl _)).symm
    obtain ⟨F, -, -, hD⟩ := (Freq.fracFramework_holds α hα).1
    have hj := scaledDilateJointContinuous Freq.X (dilExponent α) F
    rw [hD] at hj
    have hne : ∀ t ∈ Icc (0 : ℝ) T, 1 - t ≠ 0 := fun t ht => by linarith [ht.2]
    have hsc := rotatingSliceContinuous_holds α hα hα' a U P hprof
    have hg : ContinuousOn (fun t : ℝ => ((1 - t)⁻¹,
        Freq.embedX (rotatingSlice a U (s₀ - Real.log (1 - t))))) (Icc 0 T) := by
      refine ContinuousOn.prodMk ((continuousOn_const.sub continuousOn_id).inv₀ hne) ?_
      exact hsc.comp_continuousOn (continuousOn_const.sub
        ((continuousOn_const.sub continuousOn_id).log hne))
    have hmaps : MapsTo (fun t : ℝ => ((1 - t)⁻¹,
        Freq.embedX (rotatingSlice a U (s₀ - Real.log (1 - t))))) (Icc 0 T) (Ioi 0 ×ˢ univ) :=
      fun t ht => ⟨show (0 : ℝ) < (1 - t)⁻¹ from inv_pos.mpr (by linarith [ht.2]), mem_univ _⟩
    exact (hj.comp hg hmaps).congr hEq
  · intro t₀ ht₀
    have hg : Tendsto (fun t => (K * |t - t₀|) ^ 2 * ∫ x : Space, (1 + ‖x‖) ^ (-(2 * (4 * α - 1))))
        (𝓝[Icc 0 T] t₀) (𝓝 0) := by
      have hc : Continuous (fun t : ℝ =>
          (K * |t - t₀|) ^ 2 * ∫ x : Space, (1 + ‖x‖) ^ (-(2 * (4 * α - 1)))) := by
        fun_prop
      have h0 := hc.tendsto t₀
      simp only [sub_self, abs_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
    · exact Eventually.of_forall (fun t => integral_nonneg (fun x => by positivity))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [← integral_const_mul]
      exact integral_mono (hint t ht t₀ ht₀) ((integrable_weight hα).const_mul _)
        (fun x => sq_le_of_le x _ (hK t ht t₀ ht₀ x))
  · intro φ hφ t ht
    obtain ⟨⟨ψ, rfl⟩, hφd, -⟩ := h4 α hα hα32 φ hφ
    have ht1 : t < 1 := by linarith [ht.2]
    have hsd := hdec t ht1
    obtain ⟨B, hB1, hB2⟩ := decay_bdd hsd
    have hvs : ContDiff ℝ ∞ (selfSimilarField α a U s₀ t) := hsd.1
    have hv3 : ∀ j ≤ 3, ∃ C : ℝ, ∀ y,
        ‖iteratedFDeriv ℝ j (selfSimilarField α a U s₀ t) y‖ ≤ C :=
      scale_bounded (hsl _).1 (h3 α hα hα' a U P hprof _).2
    obtain ⟨iA, -, hsym⟩ := symmetryRapid α hα hα32 _ hvs hv3 ψ
    have iB : Integrable (fun x => inner ℝ (advectionAt (selfSimilarField α a U s₀ t) x) (ψ x)) :=
      integrable_inner_bdd (continuous_advection hvs) (adv_bdd hB1 hB2) ψ
    obtain ⟨Lp, hLp0, hLp⟩ := pressure_increment hα hprof s₀ t
    obtain ⟨iC, hzero⟩ := gradient_pairing_zero (pressure_smooth hprof s₀ t) hLp0 hLp ψ hφd.2.1
    have hs : Ioo 0 T ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
    have hslope : ∀ᵐ x ∂(volume : Measure Space), LipschitzOnWith (Real.nnabs (|K| * ‖ψ x‖))
        (fun τ => inner ℝ (selfSimilarField α a U s₀ τ x) (ψ x)) (Ioo 0 T) := by
      refine Eventually.of_forall fun x => LipschitzOnWith.of_dist_le_mul fun τ hτ τ' hτ' => ?_
      rw [Real.coe_nnabs, abs_of_nonneg (by positivity), Real.dist_eq, Real.dist_eq,
        ← inner_sub_left]
      calc |inner ℝ (selfSimilarField α a U s₀ τ x - selfSimilarField α a U s₀ τ' x) (ψ x)|
          ≤ ‖selfSimilarField α a U s₀ τ x - selfSimilarField α a U s₀ τ' x‖ * ‖ψ x‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ (|K| * |τ - τ'|) * ‖ψ x‖ :=
            mul_le_mul_of_nonneg_right (hKa τ (Ioo_subset_Icc_self hτ) τ'
              (Ioo_subset_Icc_self hτ') x) (norm_nonneg _)
        _ = |K| * ‖ψ x‖ * |τ - τ'| := by ring
    have hdiff : ∀ᵐ x ∂(volume : Measure Space),
        HasDerivAt (fun τ => inner ℝ (selfSimilarField α a U s₀ τ x) (ψ x))
          (-inner ℝ (fractionalPowerAt α (selfSimilarField α a U s₀ t) x) (ψ x)
            - inner ℝ (advectionAt (selfSimilarField α a U s₀ t) x) (ψ x)
            - inner ℝ (gradientAt (selfSimilarPressure α a P s₀ t) x) (ψ x)) t := by
      refine Eventually.of_forall fun x => ?_
      have hh := (h1 α hα hα' a U P hprof s₀ t ht1 x).inner ℝ (hasDerivAt_const t (ψ x))
      rw [inner_zero_right, zero_add, inner_sub_left, inner_sub_left, inner_neg_left] at hh
      exact hh
    have hmeas : AEStronglyMeasurable (fun x =>
        -inner ℝ (fractionalPowerAt α (selfSimilarField α a U s₀ t) x) (ψ x)
          - inner ℝ (advectionAt (selfSimilarField α a U s₀ t) x) (ψ x)
          - inner ℝ (gradientAt (selfSimilarPressure α a P s₀ t) x) (ψ x)) volume :=
      ((iA.neg.sub iB).sub iC).aestronglyMeasurable
    have hmain := hasDerivAt_integral_of_dominated_loc_of_lip hs
      (Eventually.of_forall fun τ => ((hcont τ).inner ψ.continuous).aestronglyMeasurable)
      (pair_int ψ t ht1) hmeas hslope (ψ.integrable.norm.const_mul |K|) hdiff
    have hd := hmain.2
    refine hd.congr_deriv ?_
    have e1 := integral_sub (iA.neg.sub iB) iC
    have e2 := integral_sub iA.neg iB
    have e3 := integral_neg (μ := volume)
      (fun x => inner ℝ (fractionalPowerAt α (selfSimilarField α a U s₀ t) x) (ψ x))
    simp only [Pi.sub_apply, Pi.neg_apply] at e1 e2
    rw [e1, e2, e3, hzero, hsym]
    unfold fieldPairing advectionPairing
    ring
  · intro φ hφ
    obtain ⟨⟨ψ, rfl⟩, -⟩ := h4 α hα hα32 φ hφ
    have hL : LipschitzOnWith (Real.toNNReal (|K| * ∫ x, ‖ψ x‖))
        (fun τ => fieldPairing (selfSimilarField α a U s₀ τ) ψ) (Icc 0 T) := by
      refine LipschitzOnWith.of_dist_le' fun τ hτ τ' hτ' => ?_
      unfold fieldPairing
      rw [Real.dist_eq, Real.dist_eq,
        ← integral_sub (pair_int ψ τ (by linarith [hτ.2])) (pair_int ψ τ' (by linarith [hτ'.2]))]
      simp only [← inner_sub_left]
      rw [← Real.norm_eq_abs]
      calc ‖∫ x, inner ℝ (selfSimilarField α a U s₀ τ x - selfSimilarField α a U s₀ τ' x) (ψ x)‖
          ≤ ∫ x, |K| * |τ - τ'| * ‖ψ x‖ := by
            refine norm_integral_le_of_norm_le (ψ.integrable.norm.const_mul _)
              (Eventually.of_forall fun x => ?_)
            calc ‖inner ℝ (selfSimilarField α a U s₀ τ x - selfSimilarField α a U s₀ τ' x) (ψ x)‖
                ≤ ‖selfSimilarField α a U s₀ τ x - selfSimilarField α a U s₀ τ' x‖ * ‖ψ x‖ :=
                  norm_inner_le_norm _ _
              _ ≤ |K| * |τ - τ'| * ‖ψ x‖ :=
                  mul_le_mul_of_nonneg_right (hKa τ hτ τ' hτ' x) (norm_nonneg _)
        _ = |K| * (∫ x, ‖ψ x‖) * |τ - τ'| := by rw [integral_const_mul]; ring
    exact hL.continuousOn

end Breakdown
