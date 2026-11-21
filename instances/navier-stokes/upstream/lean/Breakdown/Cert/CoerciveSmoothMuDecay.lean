import Breakdown.Cert.CoerciveSmoothMuSum

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.MuSmooth

namespace Decay

theorem coord_abs_le (x : Space) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have h := Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  simpa [Real.norm_eq_abs, sq_abs] using h

theorem rot_norm (φ : ℝ) (y : Space) : ‖axialRot φ y‖ = ‖y‖ := by
  obtain ⟨R, hR⟩ := axialRotationHolds_proof.1 φ
  rw [← hR, R.norm_map]

theorem modeAverage_norm_le {β : Type*} (ι : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ) (b : β) {M : ℝ}
    (hM : ∀ τ φ, |f τ φ b| ≤ M) : ‖modeAverage ι f b‖ ≤ M := by
  unfold modeAverage
  have hpi : 0 < 2 * Real.pi := by positivity
  have hin : ∀ τ : ℝ, ‖∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f τ φ b : ℝ) : ℂ)‖
      ≤ M * (2 * Real.pi) := by
    intro τ
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 2 * Real.pi)
      (C := M) (f := fun φ => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
        * ((f τ φ b : ℝ) : ℂ)) (fun φ _ => by
          rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
          simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_self, neg_zero, Real.exp_zero, one_mul]
          exact hM τ φ)
    rwa [sub_zero, abs_of_pos hpi] at h
  have hout := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := M * (2 * Real.pi)) (fun τ _ => hin τ)
  rw [sub_zero, abs_one, mul_one] at hout
  rw [norm_mul]
  have hc : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc]
  calc 1 / (2 * Real.pi) * ‖_‖ ≤ 1 / (2 * Real.pi) * (M * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hout (by positivity)
    _ = M := by field_simp

theorem cnormSq_modeVel_le (X : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) {M : ℝ}
    (hM : ∀ τ φ, ‖X (σ + τ) (axialRot φ y)‖ ≤ M) : cnormSq (modeVel ι X σ y) ≤ 3 * M ^ 2 := by
  have h : ∀ i, ‖modeVel ι X σ y i‖ ≤ M := fun i => by
    unfold modeVel
    refine modeAverage_norm_le ι _ i fun τ φ => ?_
    exact (coord_abs_le _ i).trans (by rw [rot_norm]; exact hM τ φ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (h 0)
  unfold cnormSq
  calc ∑ i, ‖modeVel ι X σ y i‖ ^ 2 ≤ ∑ _i : Fin 3, M ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
    _ = 3 * M ^ 2 := by simp

theorem cnormSq_modeGrad_le (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) {M : ℝ}
    (hM : ∀ τ φ, ‖G (σ + τ) (axialRot φ y)‖ ≤ M) : cnormSq (modeGrad ι G σ y) ≤ 9 * M ^ 2 := by
  have h : ∀ ij, ‖modeGrad ι G σ y ij‖ ≤ M := fun ij => by
    unfold modeGrad
    refine modeAverage_norm_le ι _ ij fun τ φ => ?_
    refine (coord_abs_le _ ij.1).trans ?_
    rw [rot_norm]
    refine ((G (σ + τ) (axialRot φ y)).le_opNorm _).trans ?_
    have hu : ‖axialRot φ (unitVector ij.2)‖ = 1 := by
      rw [rot_norm]; unfold unitVector; simp
    rw [hu, mul_one]
    exact hM τ φ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (h (0, 0))
  unfold cnormSq
  calc ∑ ij, ‖modeGrad ι G σ y ij‖ ^ 2 ≤ ∑ _ij : Fin 3 × Fin 3, M ^ 2 :=
        Finset.sum_le_sum fun ij _ => pow_le_pow_left₀ (norm_nonneg _) (h ij) 2
    _ = 9 * M ^ 2 := by simp

theorem unit_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by
  unfold unitVector
  simp

theorem rot_sub (φ : ℝ) (a c : Space) : axialRot φ a - axialRot φ c = axialRot φ (a - c) := by
  ext i
  fin_cases i <;> simp [axialRot, unitVector] <;> ring

theorem modeAverage_sub {β : Type*} (ι : ℤ × ℤ) (f g : ℝ → ℝ → β → ℝ) (b : β)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2 b)) (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2 b)) :
    modeAverage ι f b - modeAverage ι g b = modeAverage ι (fun τ φ b => f τ φ b - g τ φ b) b := by
  unfold modeAverage
  have hE : Continuous (fun p : ℝ × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * p.1 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))) := by fun_prop
  have hF : Continuous (Function.uncurry (fun τ φ : ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f τ φ b : ℝ) : ℂ))) :=
    hE.mul (Complex.continuous_ofReal.comp hf)
  have hG : Continuous (Function.uncurry (fun τ φ : ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((g τ φ b : ℝ) : ℂ))) :=
    hE.mul (Complex.continuous_ofReal.comp hg)
  have hin : ∀ τ : ℝ, (∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f τ φ b - g τ φ b : ℝ) : ℂ)) =
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f τ φ b : ℝ) : ℂ))
      - ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((g τ φ b : ℝ) : ℂ) := by
    intro τ
    rw [← intervalIntegral.integral_sub]
    · congr 1
      funext φ
      push_cast
      ring
    · exact (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    · exact (hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  simp_rw [hin]
  rw [intervalIntegral.integral_sub, mul_sub]
  · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF _ _).intervalIntegrable _ _
  · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG _ _).intervalIntegrable _ _

theorem meanField_norm_le (W : ℝ → Space → Space) {D : ℝ} (hD : ∀ σ y, ‖W σ y‖ ≤ D / (1 + ‖y‖)) (y : Space) :
    ‖meanField W y‖ ≤ 3 * (D / (1 + ‖y‖)) := by
  have h : ∀ i, ‖modeVel (0, 0) W 0 y i‖ ≤ D / (1 + ‖y‖) := fun i => by
    unfold modeVel
    refine modeAverage_norm_le _ _ i fun τ φ => ?_
    refine (coord_abs_le _ i).trans ?_
    rw [rot_norm]
    have := hD (0 + τ) (axialRot φ y)
    rwa [rot_norm] at this
  unfold meanField
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin 3, ‖(modeVel (0, 0) W 0 y i).re • unitVector i‖ ≤ ∑ _i : Fin 3, D / (1 + ‖y‖) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, unit_norm, mul_one, Real.norm_eq_abs]
        exact (Complex.abs_re_le_norm _).trans (h i)
    _ = 3 * (D / (1 + ‖y‖)) := by simp

theorem slice_differentiable {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (σ : ℝ) : Differentiable ℝ (W σ) :=
  (hW.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)

theorem flow_sub_le {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) {D : ℝ}
    (hD1 : ∀ σ z, ‖fderiv ℝ (W σ) z‖ ≤ D / (1 + ‖z‖) ^ 2) (hD0 : 0 ≤ D) (σ : ℝ) (y x : Space)
    (hx : ‖x - y‖ < (1 + ‖y‖) / 2) :
    ‖W σ x - W σ y‖ ≤ 4 * D / (1 + ‖y‖) ^ 2 * ‖x - y‖ := by
  have hu : 0 < 1 + ‖y‖ := by positivity
  refine Convex.norm_image_sub_le_of_norm_fderiv_le (s := Metric.ball y ((1 + ‖y‖) / 2))
    (fun z _ => (slice_differentiable hW σ) z) (fun z hz => ?_) (convex_ball _ _)
    (Metric.mem_ball_self (by positivity)) (by rw [Metric.mem_ball, dist_eq_norm]; exact hx)
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hz2 : (1 + ‖y‖) / 2 ≤ 1 + ‖z‖ := by
    have := norm_sub_norm_le y z
    rw [norm_sub_rev] at this
    linarith [norm_sub_rev z y]
  refine (hD1 σ z).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : ((1 + ‖y‖) / 2) ^ 2 ≤ (1 + ‖z‖) ^ 2 := pow_le_pow_left₀ (by positivity) hz2 2
  nlinarith


theorem rot_continuous {X : Type*} [TopologicalSpace X] {a : X → ℝ} {u : X → Space}
    (ha : Continuous a) (hu : Continuous u) : Continuous fun q => axialRot (a q) (u q) := by
  unfold axialRot
  fun_prop

theorem integrand_continuous {X : ℝ → Space → Space} (h : Continuous (fun z : ℝ × Space => X z.1 z.2))
    (σ : ℝ) (y : Space) (i : Fin 3) :
    Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (X (σ + p.1) (axialRot p.2 y)) i) := by
  have h1 : Continuous (fun p : ℝ × ℝ => X (σ + p.1) (axialRot p.2 y)) :=
    h.comp ((continuous_const.add continuous_fst).prodMk (rot_continuous continuous_snd continuous_const))
  exact (PiLp.continuous_apply 2 _ i).comp (rot_continuous continuous_snd.neg h1)

theorem meanField_fderiv_le {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) {D : ℝ}
    (hD1 : ∀ σ z, ‖fderiv ℝ (W σ) z‖ ≤ D / (1 + ‖z‖) ^ 2) (hD0 : 0 ≤ D) (y : Space) :
    ‖fderiv ℝ (meanField W) y‖ ≤ 12 * D / (1 + ‖y‖) ^ 2 := by
  have hu : 0 < 1 + ‖y‖ := by positivity
  have hWc : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  refine norm_fderiv_le_of_lip' ℝ (by positivity) ?_
  have hball : Metric.ball y ((1 + ‖y‖) / 2) ∈ nhds y := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hball] with x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hcomp : ∀ (i : Fin 3), ‖modeVel (0, 0) W 0 x i - modeVel (0, 0) W 0 y i‖
      ≤ 4 * D / (1 + ‖y‖) ^ 2 * ‖x - y‖ := fun i => by
    unfold modeVel
    rw [modeAverage_sub _ _ _ i (integrand_continuous hWc 0 x i)
      (integrand_continuous hWc 0 y i)]
    refine modeAverage_norm_le _ _ i fun τ φ => ?_
    rw [← PiLp.sub_apply, rot_sub]
    refine (coord_abs_le _ i).trans ?_
    rw [rot_norm]
    have hrx : ‖axialRot φ x - axialRot φ y‖ = ‖x - y‖ := by rw [rot_sub, rot_norm]
    have h := flow_sub_le hW hD1 hD0 (0 + τ) (axialRot φ y) (axialRot φ x) (by rw [hrx, rot_norm]; exact hx)
    rwa [hrx, rot_norm] at h
  unfold meanField
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin 3, ‖(modeVel (0, 0) W 0 x i).re • unitVector i - (modeVel (0, 0) W 0 y i).re • unitVector i‖
      ≤ ∑ _i : Fin 3, 4 * D / (1 + ‖y‖) ^ 2 * ‖x - y‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sub_smul, norm_smul, unit_norm, mul_one, Real.norm_eq_abs, ← Complex.sub_re]
        exact (Complex.abs_re_le_norm _).trans (hcomp i)
    _ = 12 * D / (1 + ‖y‖) ^ 2 * ‖x - y‖ := by simp; ring

theorem ind_le_one (p : Prop) : ModeWeights.ind p ≤ 1 := by
  unfold ModeWeights.ind
  split_ifs <;> norm_num

theorem prod_le_energy {X u g a A : ℝ} (hu : 0 < u) (hX : 0 ≤ X) (hXu : X * u ≤ A) (hg : 0 ≤ g) (ha : 0 ≤ a) :
    X * g * a ≤ A * (g ^ 2 + a ^ 2 / u ^ 2) := by
  have hA : 0 ≤ A := le_trans (mul_nonneg hX hu.le) hXu
  set r := a / u with hr
  have hr0 : 0 ≤ r := div_nonneg ha hu.le
  have ha' : a = r * u := by rw [hr]; field_simp
  have hr2 : a ^ 2 / u ^ 2 = r ^ 2 := by rw [hr, div_pow]
  rw [hr2, ha']
  have h1 : X * g * (r * u) = (X * u) * (g * r) := by ring
  rw [h1]
  have h2 : (X * u) * (g * r) ≤ A * (g * r) := mul_le_mul_of_nonneg_right hXu (mul_nonneg hg hr0)
  have h3 : g * r ≤ g ^ 2 + r ^ 2 := by nlinarith [sq_nonneg (g - r)]
  nlinarith [mul_le_mul_of_nonneg_left h3 hA]

theorem sq_le_energy {X u a A : ℝ} (hu : 0 < u) (hXu : X * u ^ 2 ≤ A) :
    X * a ^ 2 ≤ A * (a ^ 2 / u ^ 2) := by
  have hu2 : 0 < u ^ 2 := by positivity
  rw [mul_div_assoc', le_div_iff₀ hu2]
  nlinarith [mul_le_mul_of_nonneg_right hXu (sq_nonneg a)]

theorem sum_sq_le_card {κ : Type*} (s : Finset κ) (f : κ → ℝ) :
    (∑ α ∈ s, f α) ^ 2 ≤ (s.card : ℝ) * ∑ α ∈ s, f α ^ 2 := by
  have := sq_sum_le_card_mul_sum_sq (s := s) (f := f)
  simpa using this

theorem press_mean_le {f a u E e emin D : ℝ} (hu1 : 1 ≤ u) (hemin : 0 < emin) (he : emin ≤ e)
    (hf0 : 0 ≤ f) (hfd : f ≤ 12 * D / u ^ 2) (hEa : a ^ 2 / u ^ 2 ≤ E) :
    f ^ 2 * a ^ 2 / e ≤ 144 * D ^ 2 / emin * E := by
  have hu0 : 0 < u := by linarith
  have hu' : u ≠ 0 := hu0.ne'
  have hu2 : 0 < u ^ 2 := by positivity
  have h0 : f * u ^ 2 ≤ 12 * D := by rwa [le_div_iff₀ hu2] at hfd
  have h1 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
  have h2 : (f * u ^ 2) ^ 2 ≤ (12 * D) ^ 2 := pow_le_pow_left₀ (by positivity) h0 2
  have hf2 : f ^ 2 * u ^ 2 ≤ 144 * D ^ 2 := by
    nlinarith only [h2, mul_le_mul_of_nonneg_left h1 (sq_nonneg f)]
  have hq : f ^ 2 * a ^ 2 / e ≤ f ^ 2 * a ^ 2 / emin := div_le_div_of_nonneg_left (by positivity) hemin he
  have e1 : f ^ 2 * a ^ 2 = (f ^ 2 * u ^ 2) * (a ^ 2 / u ^ 2) := by
    field_simp
  have h3 : (f ^ 2 * u ^ 2) * (a ^ 2 / u ^ 2) ≤ 144 * D ^ 2 * E :=
    mul_le_mul hf2 hEa (by positivity) (by positivity)
  calc f ^ 2 * a ^ 2 / e ≤ f ^ 2 * a ^ 2 / emin := hq
    _ ≤ 144 * D ^ 2 * E / emin := by rw [e1]; exact div_le_div_of_nonneg_right h3 hemin.le
    _ = 144 * D ^ 2 / emin * E := by ring

theorem press_wave_le {κ : Type*} (s : Finset κ) (G V M : κ → ℝ) {u e emin D : ℝ} (hu1 : 1 ≤ u)
    (hemin : 0 < emin) (he : emin ≤ e) (hG0 : ∀ α, 0 ≤ G α) (hG : ∀ α, G α ≤ 3 * D / u ^ 2)
    (hM : ∀ α, V α ^ 2 / u ^ 2 ≤ M α) :
    (∑ α ∈ s, G α * V α) ^ 2 / e ≤ 9 * D ^ 2 * (s.card : ℝ) / emin * ∑ α ∈ s, M α := by
  have hu0 : 0 < u := by linarith
  have hu' : u ≠ 0 := hu0.ne'
  have hu2 : 0 < u ^ 2 := by positivity
  have h1 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
  have hterm : ∀ α, (G α * V α) ^ 2 ≤ 9 * D ^ 2 * M α := fun α => by
    have h0 : G α * u ^ 2 ≤ 3 * D := by
      have := hG α
      rwa [le_div_iff₀ hu2] at this
    have h2 : (G α * u ^ 2) ^ 2 ≤ (3 * D) ^ 2 := pow_le_pow_left₀ (mul_nonneg (hG0 α) hu2.le) h0 2
    have hq2 : G α ^ 2 * u ^ 2 ≤ 9 * D ^ 2 := by
      nlinarith only [h2, mul_le_mul_of_nonneg_left h1 (sq_nonneg (G α))]
    have e1 : (G α * V α) ^ 2 = (G α ^ 2 * u ^ 2) * (V α ^ 2 / u ^ 2) := by
      field_simp
    rw [e1]
    exact mul_le_mul hq2 (hM α) (by positivity) (by positivity)
  have hcs := sum_sq_le_card s (fun α => G α * V α)
  have hs2 : ∑ α ∈ s, (G α * V α) ^ 2 ≤ 9 * D ^ 2 * ∑ α ∈ s, M α := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun α _ => hterm α
  have hN0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  calc (∑ α ∈ s, G α * V α) ^ 2 / e ≤ (∑ α ∈ s, G α * V α) ^ 2 / emin :=
        div_le_div_of_nonneg_left (sq_nonneg _) hemin he
    _ ≤ ((s.card : ℝ) * (9 * D ^ 2 * ∑ α ∈ s, M α)) / emin :=
        div_le_div_of_nonneg_right (hcs.trans (mul_le_mul_of_nonneg_left hs2 hN0)) hemin.le
    _ = 9 * D ^ 2 * (s.card : ℝ) / emin * ∑ α ∈ s, M α := by ring

theorem press_weight_le {e eM mu u a B1 E : ℝ} (he : 0 < e) (heM : e ≤ eM) (hmu0 : 0 ≤ mu)
    (hmu : mu * u ^ 2 ≤ 4 * B1) (hu1 : 1 ≤ u) (hEa : a ^ 2 / u ^ 2 ≤ E) :
    (1 / 2) * e * mu ^ 2 * a ^ 2 ≤ 8 * eM * B1 ^ 2 * E := by
  have hu0 : 0 < u := by linarith
  have hu' : u ≠ 0 := hu0.ne'
  have heM0 : 0 ≤ eM := he.le.trans heM
  have h1 : (mu * u ^ 2) ^ 2 ≤ (4 * B1) ^ 2 := pow_le_pow_left₀ (by positivity) hmu 2
  have h2 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
  have hm2 : mu ^ 2 * u ^ 2 ≤ 16 * B1 ^ 2 := by
    nlinarith only [h1, mul_le_mul_of_nonneg_left h2 (sq_nonneg mu)]
  have e1 : (1 / 2) * e * mu ^ 2 * a ^ 2 = (1 / 2) * e * (mu ^ 2 * u ^ 2) * (a ^ 2 / u ^ 2) := by
    field_simp
  have hc0 : 0 ≤ (1 / 2) * eM * (16 * B1 ^ 2) := mul_nonneg (mul_nonneg (by norm_num) heM0) (by positivity)
  have h3 : (1 / 2) * e * (mu ^ 2 * u ^ 2) ≤ (1 / 2) * eM * (16 * B1 ^ 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left heM (by norm_num)) hm2 (by positivity)
      (mul_nonneg (by norm_num) heM0)
  rw [e1]
  calc (1 / 2) * e * (mu ^ 2 * u ^ 2) * (a ^ 2 / u ^ 2) ≤ (1 / 2) * eM * (16 * B1 ^ 2) * (a ^ 2 / u ^ 2) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ ≤ (1 / 2) * eM * (16 * B1 ^ 2) * E := mul_le_mul_of_nonneg_left hEa hc0
    _ = 8 * eM * B1 ^ 2 * E := by ring

end Decay

open Decay

def modeEnergy (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  cnormSq (modeGrad ι (gradField v) σ y) + cnormSq (modeVel ι (weighted v) σ y)

theorem rest_pointwise {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    ∃ K, 0 ≤ K ∧ ∀ ι σ y, transportLoss m W v ι σ y + pressureLoss m W v ι σ y
      ≤ K * (modeEnergy v ι σ y + ∑ α ∈ m.waves, modeEnergy v (ι - α) σ y) := by
  obtain ⟨D, hD⟩ := hWdecay
  have hWn : ∀ σ y, ‖W σ y‖ ≤ D / (1 + ‖y‖) := fun σ y => by
    have h := hD σ y 0 (by norm_num)
    rwa [norm_iteratedFDeriv_zero, zero_add, pow_one] at h
  have hD1 : ∀ σ y, ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) ^ 2 := fun σ y => by
    have h := hD σ y 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at h
  have hD0 : 0 ≤ D := by
    have h := hWn 0 0
    rw [norm_zero, add_zero, div_one] at h
    exact (norm_nonneg _).trans h
  obtain ⟨B1, hB1⟩ := hm.muW_decay
  obtain ⟨Br, hBr⟩ := hm.rate_bounded
  have := hm.finite_classes
  have : Nonempty C := ⟨m.classOf 0⟩
  choose Kc hKc using hm.muW_increment
  obtain ⟨c1, hc1⟩ := Finite.exists_max (fun c => (Kc c : ℝ))
  obtain ⟨c2, hc2⟩ := Finite.exists_max m.eta
  have hB10 : 0 ≤ B1 := (abs_nonneg _).trans (hB1 (m.classOf 0) 0).1
  have hBr0 : 0 ≤ Br := (abs_nonneg _).trans (hBr (m.classOf 0) 0)
  have hKL0 : 0 ≤ (Kc c1 : ℝ) := NNReal.coe_nonneg _
  have hemin := hm.etaMin_pos
  have hηM0 : 0 ≤ m.eta c2 := (hm.eta_pos c2).le
  set N : ℝ := (m.waves.card : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set Cr : ℝ := 3 * D + 1 + 2 * Br with hCr
  set A1 : ℝ := 4 * B1 * Cr + (Kc c1 : ℝ) + B1 with hA1
  set A2 : ℝ := 4 * B1 * Br with hA2
  set A3 : ℝ := 8 * B1 * D with hA3
  set A4 : ℝ := 144 * D ^ 2 / m.etaMin with hA4
  set A5 : ℝ := 9 * D ^ 2 * N / m.etaMin with hA5
  set A6 : ℝ := 8 * m.eta c2 * B1 ^ 2 with hA6
  have hA10 : 0 ≤ A1 := by positivity
  have hA20 : 0 ≤ A2 := by positivity
  have hA30 : 0 ≤ A3 := by positivity
  have hA40 : 0 ≤ A4 := by positivity
  have hA50 : 0 ≤ A5 := by positivity
  have hA60 : 0 ≤ A6 := by positivity
  refine ⟨A1 + A2 + A3 * (N + 1) + A4 + A5 + A6, by positivity, fun ι σ y => ?_⟩
  set u : ℝ := 1 + ‖y‖ with hu
  have hu0 : 0 < u := by positivity
  have hu1 : 1 ≤ u := by simp [hu]
  set c := m.classOf ι with hc
  have hmu0 : 0 ≤ m.mu ι y := abs_nonneg _
  have hmu : m.mu ι y * u ^ 2 ≤ 4 * B1 := by
    obtain ⟨h1, h2, -⟩ := hB1 c y
    have ht : 2 * ‖y‖ ≤ 1 + ‖y‖ ^ 2 := by nlinarith only [sq_nonneg (‖y‖ - 1)]
    have e : m.mu ι y * u ^ 2 = m.mu ι y + m.mu ι y * (2 * ‖y‖) + ‖y‖ ^ 2 * m.mu ι y := by rw [hu]; ring
    have h3 : m.mu ι y * (2 * ‖y‖) ≤ m.mu ι y * (1 + ‖y‖ ^ 2) := mul_le_mul_of_nonneg_left ht hmu0
    have e2 : |m.muW c y| * u ^ 2 = |m.muW c y| + |m.muW c y| * (2 * ‖y‖) + ‖y‖ ^ 2 * |m.muW c y| := e
    have h32 : |m.muW c y| * (2 * ‖y‖) ≤ |m.muW c y| * (1 + ‖y‖ ^ 2) := h3
    show |m.muW c y| * u ^ 2 ≤ 4 * B1
    nlinarith only [e2, h32, h1, h2]
  have hmug0 : 0 ≤ m.muGrad ι y := norm_nonneg _
  have hmug : m.muGrad ι y * u ≤ (Kc c1 : ℝ) + B1 := by
    obtain ⟨-, -, h3⟩ := hB1 c y
    have hk : m.muGrad ι y ≤ Kc c1 := (norm_fderiv_le_of_lipschitz ℝ (hKc c)).trans (hc1 c)
    have h3' : ‖y‖ * m.muGrad ι y ≤ B1 := h3
    rw [hu]
    nlinarith only [h3', hk]
  have hmf : ‖meanField W y‖ ≤ 3 * D := by
    refine (meanField_norm_le W hWn y).trans ?_
    have : D / u ≤ D := div_le_self hD0 hu1
    linarith
  have hrv : ‖relativeVelocity W (m.rate c) y‖ ≤ Cr * u := by
    unfold relativeVelocity
    have hr := hBr c y
    have h1 : ‖-(y 1) • unitVector 0 + y 0 • unitVector 1‖ ≤ 2 * ‖y‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, unit_norm, unit_norm, mul_one, mul_one, norm_neg, Real.norm_eq_abs,
        Real.norm_eq_abs]
      linarith [coord_abs_le y 0, coord_abs_le y 1]
    have h2 : ‖m.rate c y • (-(y 1) • unitVector 0 + y 0 • unitVector 1)‖ ≤ Br * (2 * ‖y‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hr h1 (norm_nonneg _) hBr0
    have h3 : ‖(1 / 2 : ℝ) • y‖ = (1 / 2) * ‖y‖ := by rw [norm_smul]; norm_num
    have h4 := norm_sub_le (meanField W y + (1 / 2 : ℝ) • y) (m.rate c y • (-(y 1) • unitVector 0 + y 0 • unitVector 1))
    have h5 := norm_add_le (meanField W y) ((1 / 2 : ℝ) • y)
    have hy : ‖y‖ ≤ u := by rw [hu]; linarith
    rw [hCr]
    nlinarith only [h4, h5, h3, h2, hmf, hy, hu1, mul_le_mul_of_nonneg_left hu1 hD0, mul_le_mul_of_nonneg_left hy hBr0, norm_nonneg y]
  have hvW : ∀ α, velAmp W α σ y ≤ 2 * D / u := fun α => by
    have h := cnormSq_modeVel_le W α σ y (M := D / u) (fun τ φ => by
      have := hWn (σ + τ) (axialRot φ y); rwa [rot_norm] at this)
    unfold velAmp
    rw [Real.sqrt_le_left (by positivity)]
    refine h.trans ?_
    rw [div_pow, div_pow]
    have hu2 : 0 < u ^ 2 := by positivity
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hu2]
    nlinarith only [sq_nonneg D]
  have hgW : ∀ α, gradAmp (gradField W) α σ y ≤ 3 * D / u ^ 2 := fun α => by
    have h := cnormSq_modeGrad_le (gradField W) α σ y (M := D / u ^ 2) (fun τ φ => by
      have := hD1 (σ + τ) (axialRot φ y); rwa [rot_norm] at this)
    unfold gradAmp
    rw [Real.sqrt_le_left (by positivity)]
    refine h.trans (le_of_eq ?_)
    ring
  have hmfd := meanField_fderiv_le hW hD1 hD0 y
  have hEq : ∀ κ, modeEnergy v κ σ y = gradAmp (gradField v) κ σ y ^ 2 + velAmp v κ σ y ^ 2 / u ^ 2 := fun κ => by
    unfold modeEnergy gradAmp velAmp
    rw [cnormSq_weighted, Real.sq_sqrt (cnorm_nonneg _), Real.sq_sqrt (cnorm_nonneg _)]
  have hE0 : ∀ κ, 0 ≤ modeEnergy v κ σ y := fun κ => add_nonneg (cnorm_nonneg _) (cnorm_nonneg _)
  have hEι := hEq ι
  set E := modeEnergy v ι σ y with hEdef
  set S := ∑ α ∈ m.waves, modeEnergy v (ι - α) σ y with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun α _ => hE0 _
  set a := velAmp v ι σ y with ha
  set g := gradAmp (gradField v) ι σ y with hg
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hg0 : 0 ≤ g := Real.sqrt_nonneg _
  have hEa : a ^ 2 / u ^ 2 ≤ E := by rw [hEι]; exact le_add_of_nonneg_left (sq_nonneg g)
  have hEag : g ^ 2 + a ^ 2 / u ^ 2 = E := hEι.symm
  have hmu4 : m.mu ι y ≤ 4 * B1 := le_trans (le_mul_of_one_le_right hmu0 (one_le_pow₀ hu1)) hmu
  have t1 : (m.mu ι y * ‖relativeVelocity W (m.rate c) y‖ + m.muGrad ι y) * g * a ≤ A1 * E := by
    rw [← hEag]
    refine prod_le_energy hu0 (by positivity) ?_ hg0 ha0
    have hCr0 : 0 ≤ Cr := by positivity
    have h1 : m.mu ι y * ‖relativeVelocity W (m.rate c) y‖ * u ≤ Cr * (4 * B1) := by
      have := mul_le_mul_of_nonneg_left hrv hmu0
      nlinarith only [mul_le_mul_of_nonneg_right this hu0.le, mul_le_mul_of_nonneg_left hmu hCr0]
    rw [hA1]
    nlinarith only [h1, hmug]
  have t2 : m.mu ι y * |m.rate c y| * a ^ 2 ≤ A2 * E := by
    refine le_trans (sq_le_energy hu0 ?_) (mul_le_mul_of_nonneg_left hEa hA20)
    have := hBr c y
    have h2 : m.mu ι y * |m.rate c y| * u ^ 2 = |m.rate c y| * (m.mu ι y * u ^ 2) := by ring
    rw [h2, hA2]
    nlinarith only [mul_le_mul_of_nonneg_right this (mul_nonneg hmu0 (sq_nonneg u)), mul_le_mul_of_nonneg_left hmu hBr0]
  have t3 : m.mu ι y * a * ∑ α ∈ m.waves, velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y
      ≤ A3 * (N + 1) * (E + S) := by
    have hterm : ∀ α ∈ m.waves, m.mu ι y * velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y * a
        ≤ A3 * (modeEnergy v (ι - α) σ y + E) := fun α _ => by
      have hv0 : 0 ≤ velAmp W α σ y := Real.sqrt_nonneg _
      have h := prod_le_energy (X := m.mu ι y * velAmp W α σ y) (A := A3) hu0 (mul_nonneg hmu0 hv0) ?_
        (Real.sqrt_nonneg (cnormSq (modeGrad (ι - α) (gradField v) σ y))) ha0
      · refine h.trans (mul_le_mul_of_nonneg_left ?_ hA30)
        rw [hEq (ι - α)]
        exact add_le_add (le_add_of_nonneg_right (by positivity)) hEa
      · have h1 : velAmp W α σ y * u ≤ 2 * D := by
          have := mul_le_mul_of_nonneg_right (hvW α) hu0.le
          rwa [div_mul_cancel₀ _ hu0.ne'] at this
        have h2 : m.mu ι y * velAmp W α σ y * u = m.mu ι y * (velAmp W α σ y * u) := by ring
        rw [h2, hA3]
        nlinarith only [mul_le_mul_of_nonneg_left h1 hmu0, mul_le_mul_of_nonneg_right hmu4 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD0)]
    have hsum : m.mu ι y * a * ∑ α ∈ m.waves, velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y
        = ∑ α ∈ m.waves, m.mu ι y * velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y * a := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by ring
    rw [hsum]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← hN, ← hSdef]
    nlinarith only [mul_nonneg hA30 hS0, mul_nonneg hA30 (mul_nonneg hN0 hS0), mul_nonneg hA30 (hE0 ι)]
  have hη := hm.eta_pos c
  have hηmin := hm.etaMin_le c
  have hηmax := hc2 c
  have p1 : ‖fderiv ℝ (meanField W) y‖ ^ 2 * a ^ 2 / m.eta c ≤ A4 * E :=
    press_mean_le hu1 hemin hηmin (norm_nonneg _) hmfd hEa
  have p2 : (∑ α ∈ m.waves, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / m.eta c ≤ A5 * S :=
    press_wave_le m.waves (fun α => gradAmp (gradField W) α σ y) (fun α => velAmp v (ι - α) σ y)
      (fun α => modeEnergy v (ι - α) σ y) hu1 hemin hηmin (fun α => Real.sqrt_nonneg _) hgW
      (fun α => by rw [hEq (ι - α)]; exact le_add_of_nonneg_left (sq_nonneg _))
  have p3 : (1 / 2) * m.eta c * m.mu ι y ^ 2 * a ^ 2 ≤ A6 * E :=
    press_weight_le hη hηmax hmu0 hmu hu1 hEa
  have hP : pressureLoss m W v ι σ y ≤ A4 * E + A5 * S + A6 * E := by
    show ModeWeights.ind (∃ x, m.muW c x ≠ 0)
      * ((‖fderiv ℝ (meanField W) y‖ ^ 2 * a ^ 2
        + (∑ α ∈ m.waves, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2) / m.eta c
      + (1 / 2) * m.eta c * m.mu ι y ^ 2 * a ^ 2) ≤ A4 * E + A5 * S + A6 * E
    have hY : 0 ≤ (‖fderiv ℝ (meanField W) y‖ ^ 2 * a ^ 2
        + (∑ α ∈ m.waves, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2) / m.eta c
        + (1 / 2) * m.eta c * m.mu ι y ^ 2 * a ^ 2 :=
      add_nonneg (div_nonneg (add_nonneg (by positivity) (sq_nonneg _)) hη.le)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hη.le) (sq_nonneg _)) (sq_nonneg _))
    refine (mul_le_of_le_one_left hY (ind_le_one _)).trans ?_
    rw [add_div]
    linarith only [p1, p2, p3]
  have hT : transportLoss m W v ι σ y ≤ A1 * E + A2 * E + A3 * (N + 1) * (E + S) := by
    show (m.mu ι y * ‖relativeVelocity W (m.rate c) y‖ + m.muGrad ι y) * g * a
      + m.mu ι y * |m.rate c y| * a ^ 2
      + m.mu ι y * a * ∑ α ∈ m.waves, velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y ≤ _
    linarith only [t1, t2, t3]
  have hE0' := hE0 ι
  nlinarith only [hT, hP, mul_nonneg hA10 hS0, mul_nonneg hA20 hS0, mul_nonneg hA40 hS0, mul_nonneg hA60 hS0,
    mul_nonneg hA50 hE0']

end Internal.MuSmooth

end Coercive

end Breakdown
