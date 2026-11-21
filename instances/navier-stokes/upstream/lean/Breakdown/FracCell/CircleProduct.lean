import Breakdown.FracCell.SharpCircleBound

open MeasureTheory ComplexConjugate Real

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.CircleProduct

variable {T : ℝ} [hT : Fact (0 < T)]

theorem inner_eq (f g : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) :
    inner ℂ f g = ∫ t, conj (f t) * g t ∂AddCircle.haarAddCircle := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [RCLike.inner_apply]
  try ring

theorem coeff_eq (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) (i : ℤ) :
    inner ℂ (fourierBasis i) f = fourierCoeff f i := by
  rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr]

theorem mul_memLp (F : AddCircle T → ℂ) (hF : AEStronglyMeasurable F AddCircle.haarAddCircle)
    (C : ℝ) (hC : ∀ t, ‖F t‖ ≤ C) (Y : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) :
    MemLp (fun t => F t * Y t) 2 AddCircle.haarAddCircle :=
  (Lp.memLp Y).of_le_mul (hF.mul (Lp.memLp Y).1) (ae_of_all _ fun t => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _))

theorem coeff_mul_hasSum (F : AddCircle T → ℂ) (hF : AEStronglyMeasurable F AddCircle.haarAddCircle)
    (C : ℝ) (hC : ∀ t, ‖F t‖ ≤ C) (Y : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) (j : ℤ) :
    HasSum (fun i : ℤ => fourierCoeff F (j - i) * fourierCoeff Y i)
      (fourierCoeff (fun t => F t * Y t) j) := by
  have hV : MemLp (fun t => conj (F t) * fourier j t) 2 (AddCircle.haarAddCircle (T := T)) := by
    refine MemLp.of_bound (hF.star.mul (fourier j).continuous.aestronglyMeasurable) C
      (ae_of_all _ fun t => ?_)
    rw [norm_mul, RCLike.norm_conj]
    have h1 : ‖fourier j t‖ = 1 := by
      rw [fourier_apply]; exact Circle.norm_coe _
    rw [h1, mul_one]
    exact hC t
  have H := fourierBasis.hasSum_inner_mul_inner hV.toLp Y
  have e1 : ∀ i : ℤ, inner ℂ hV.toLp (fourierBasis i) = fourierCoeff F (j - i) := by
    intro i
    rw [← inner_conj_symm, coeff_eq, fourierCoeff_congr_ae hV.coeFn_toLp, fourierCoeff, fourierCoeff,
      ← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [smul_eq_mul]
    rw [show -(j - i) = i + -j by ring, fourier_add, fourier_neg, fourier_neg]
    simp only [map_mul, RCLike.conj_conj]
    ring
  have e2 : inner ℂ hV.toLp Y = fourierCoeff (fun t => F t * Y t) j := by
    rw [inner_eq, fourierCoeff]
    refine integral_congr_ae ?_
    filter_upwards [hV.coeFn_toLp] with t ht
    rw [ht, smul_eq_mul, fourier_neg]
    simp only [map_mul, RCLike.conj_conj]
    ring
  simp only [e1, coeff_eq, e2] at H
  exact H

theorem pair_hasSum (X : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) (Z : AddCircle T → ℂ)
    (hZ : MemLp Z 2 AddCircle.haarAddCircle) :
    HasSum (fun j : ℤ => conj (fourierCoeff X j) * fourierCoeff Z j)
      (∫ t, conj (X t) * Z t ∂AddCircle.haarAddCircle) := by
  have H := fourierBasis.hasSum_inner_mul_inner X hZ.toLp
  have e1 : ∀ j : ℤ, inner ℂ X (fourierBasis j) = conj (fourierCoeff X j) := by
    intro j; rw [← inner_conj_symm, coeff_eq]
  have e2 : ∀ j : ℤ, inner ℂ (fourierBasis j) hZ.toLp = fourierCoeff Z j := by
    intro j; rw [coeff_eq, fourierCoeff_congr_ae hZ.coeFn_toLp]
  have e3 : inner ℂ X hZ.toLp = ∫ t, conj (X t) * Z t ∂AddCircle.haarAddCircle := by
    rw [inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [hZ.coeFn_toLp] with t ht
    rw [ht]
  simp only [e1, e2, e3] at H
  exact H

def spread (m : ℕ) (x : ℤ → ℂ) (j : ℤ) : ℂ := if (m : ℤ) ∣ j then x (j / m) else 0

theorem mul_injective {m : ℕ} (hm : 1 ≤ m) : Function.Injective (fun n : ℤ => n * (m : ℤ)) := by
  intro a b h
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  exact mul_right_cancel₀ hm0 h

theorem spread_mul {m : ℕ} (hm : 1 ≤ m) (x : ℤ → ℂ) (n : ℤ) : spread m x (n * m) = x n := by
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp [spread, Int.mul_ediv_cancel _ hm0]

theorem spread_off (m : ℕ) (x : ℤ → ℂ) (j : ℤ) (hj : j ∉ Set.range (fun n : ℤ => n * (m : ℤ))) :
    spread m x j = 0 := by
  unfold spread
  split_ifs with h
  · obtain ⟨n, hn⟩ := h
    exact absurd ⟨n, by rw [hn]; ring⟩ hj
  · rfl

theorem spread_sq_summable {m : ℕ} (hm : 1 ≤ m) (x : ℤ → ℂ) (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    Summable (fun j => ‖spread m x j‖ ^ 2) := by
  refine ((mul_injective hm).summable_iff (fun j hj => ?_)).1 ?_
  · simp [spread_off m x j hj]
  · refine hx.congr (fun n => ?_)
    simp only [Function.comp_apply, spread_mul hm]

theorem spread_memℓp {m : ℕ} (hm : 1 ≤ m) (x : ℤ → ℂ) (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    Memℓp (spread m x) 2 := by
  refine (memℓp_gen_iff (by norm_num)).2 ?_
  refine (spread_sq_summable hm x hx).congr (fun j => ?_)
  simp only [ENNReal.toReal_ofNat]
  exact (Real.rpow_natCast _ 2).symm

def lift {m : ℕ} (hm : 1 ≤ m) (x : ℤ → ℂ) (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := T)) :=
  fourierBasis.repr.symm ⟨spread m x, spread_memℓp hm x hx⟩

theorem lift_coeff {m : ℕ} (hm : 1 ≤ m) (x : ℤ → ℂ) (hx : Summable (fun n => ‖x n‖ ^ 2)) (j : ℤ) :
    fourierCoeff (lift (T := T) hm x hx) j = spread m x j := by
  rw [← fourierBasis_repr, lift, LinearIsometryEquiv.apply_symm_apply]

theorem lift_coeff_mul {m : ℕ} (hm : 1 ≤ m) (x : ℤ → ℂ) (hx : Summable (fun n => ‖x n‖ ^ 2)) (n : ℤ) :
    fourierCoeff (lift (T := T) hm x hx) (n * m) = x n := by
  rw [lift_coeff, spread_mul hm]

theorem lift_sq {m : ℕ} (hm : 1 ≤ m) (x : ℤ → ℂ) (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    ∫ t, ‖lift (T := T) hm x hx t‖ ^ 2 ∂AddCircle.haarAddCircle = ∑' n, ‖x n‖ ^ 2 := by
  rw [← tsum_sq_fourierCoeff]
  simp only [lift_coeff]
  rw [← (mul_injective hm).tsum_eq (fun j hj => ?_)]
  · simp only [spread_mul hm]
  · simp only [Function.mem_support] at hj
    by_contra h
    exact hj (by rw [spread_off m x j h, norm_zero]; norm_num)

theorem inner_hasSum {m : ℕ} (hm : 1 ≤ m) (F : AddCircle T → ℂ) (hF : AEStronglyMeasurable F AddCircle.haarAddCircle)
    (C : ℝ) (hC : ∀ t, ‖F t‖ ≤ C) (y : ℤ → ℂ) (hy : Summable (fun n => ‖y n‖ ^ 2)) (n : ℤ) :
    HasSum (fun n' : ℤ => fourierCoeff F ((n - n') * m) * y n')
      (fourierCoeff (fun t => F t * lift (T := T) hm y hy t) (n * m)) := by
  have H := coeff_mul_hasSum F hF C hC (lift hm y hy) (n * m)
  rw [← (mul_injective hm).hasSum_iff (fun j hj => by simp [lift_coeff, spread_off m y j hj])] at H
  convert H using 1
  funext n'
  simp only [Function.comp_apply, lift_coeff_mul]
  congr 2
  ring

theorem outer_hasSum {m : ℕ} (hm : 1 ≤ m) (x : ℤ → ℂ) (hx : Summable (fun n => ‖x n‖ ^ 2))
    (Z : AddCircle T → ℂ) (hZ : MemLp Z 2 AddCircle.haarAddCircle) :
    HasSum (fun n : ℤ => conj (x n) * fourierCoeff Z (n * m))
      (∫ t, conj (lift (T := T) hm x hx t) * Z t ∂AddCircle.haarAddCircle) := by
  have H := pair_hasSum (lift hm x hx) Z hZ
  rw [← (mul_injective hm).hasSum_iff (fun j hj => by simp [lift_coeff, spread_off m x j hj])] at H
  convert H using 1
  funext n
  simp only [Function.comp_apply, lift_coeff_mul]

theorem quad_re_le (F : Fin 3 → Fin 3 → ℂ) (hreal : ∀ a b, (F a b).im = 0) (lam : ℝ)
    (hle : ∀ u : Fin 3 → ℝ, ∑ a, ∑ b, u a * (F a b).re * u b ≤ lam * ∑ a, u a ^ 2) (w : Fin 3 → ℂ) :
    (∑ a, ∑ b, conj (w a) * (F a b * w b)).re ≤ lam * ∑ a, ‖w a‖ ^ 2 := by
  have h1 := hle (fun a => (w a).re)
  have h2 := hle (fun a => (w a).im)
  have e : (∑ a, ∑ b, conj (w a) * (F a b * w b)).re
      = (∑ a, ∑ b, (w a).re * (F a b).re * (w b).re) + ∑ a, ∑ b, (w a).im * (F a b).re * (w b).im := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, hreal]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have e2 : ∑ a, ‖w a‖ ^ 2 = ∑ a, (w a).re ^ 2 + ∑ a, (w a).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [e, e2]
  linarith

def bandPairing {m : ℕ} (F : Fin 3 → Fin 3 → AddCircle T → ℂ) (ω : ℤ → Fin 3 → ℂ) (n n' : ℤ) : ℂ :=
  ∑ a, conj (ω n a) * ∑ b, fourierCoeff (F a b) ((n - n') * m) * ω n' b

theorem bandPairing_bound {m : ℕ} (hm : 1 ≤ m) (F : Fin 3 → Fin 3 → AddCircle T → ℂ)
    (hFm : ∀ a b, AEStronglyMeasurable (F a b) AddCircle.haarAddCircle) (C : ℝ) (hC : ∀ a b t, ‖F a b t‖ ≤ C)
    (hreal : ∀ a b t, (F a b t).im = 0) (lam : ℝ)
    (hle : ∀ t (u : Fin 3 → ℝ), ∑ a, ∑ b, u a * (F a b t).re * u b ≤ lam * ∑ a, u a ^ 2)
    (ω : ℤ → Fin 3 → ℂ) (hω : ∀ a, Summable (fun n => ‖ω n a‖ ^ 2)) :
    (∀ n, Summable (fun n' => bandPairing (m := m) F ω n n')) ∧ Summable (fun n => ∑' n', bandPairing (m := m) F ω n n') ∧
      (∑' n, ∑' n', bandPairing (m := m) F ω n n').re ≤ lam * ∑' n, ∑ a, ‖ω n a‖ ^ 2 := by
  set X : Fin 3 → Lp ℂ 2 (AddCircle.haarAddCircle (T := T)) := fun a => lift hm (fun n => ω n a) (hω a) with hX
  have hZ : ∀ a b, MemLp (fun t => F a b t * X b t) 2 AddCircle.haarAddCircle :=
    fun a b => mul_memLp (F a b) (hFm a b) C (hC a b) (X b)
  have hin : ∀ n, HasSum (fun n' => bandPairing (m := m) F ω n n')
      (∑ a, conj (ω n a) * ∑ b, fourierCoeff (fun t => F a b t * X b t) (n * m)) := by
    intro n
    refine hasSum_sum fun a _ => ?_
    refine HasSum.mul_left _ ?_
    exact hasSum_sum fun b _ => inner_hasSum hm (F a b) (hFm a b) C (hC a b) (fun n => ω n b) (hω b) n
  have hout : HasSum (fun n => ∑ a, conj (ω n a) * ∑ b, fourierCoeff (fun t => F a b t * X b t) (n * m))
      (∑ a, ∑ b, ∫ t, conj (X a t) * (F a b t * X b t) ∂AddCircle.haarAddCircle) := by
    refine hasSum_sum fun a _ => ?_
    simp_rw [Finset.mul_sum]
    exact hasSum_sum fun b _ => outer_hasSum hm (fun n => ω n a) (hω a) _ (hZ a b)
  have htsum : ∀ n, ∑' n', bandPairing (m := m) F ω n n'
      = ∑ a, conj (ω n a) * ∑ b, fourierCoeff (fun t => F a b t * X b t) (n * m) := fun n => (hin n).tsum_eq
  refine ⟨fun n => (hin n).summable, ?_, ?_⟩
  · simp_rw [htsum]; exact hout.summable
  · simp_rw [htsum]
    rw [hout.tsum_eq]
    have hint : ∀ a b, Integrable (fun t => conj (X a t) * (F a b t * X b t)) AddCircle.haarAddCircle := by
      intro a b
      refine (MeasureTheory.L2.integrable_inner (X a) (hZ a b).toLp).congr ?_
      filter_upwards [(hZ a b).coeFn_toLp] with t ht
      rw [ht, RCLike.inner_apply]
      try ring
    have hsq : ∀ a, Integrable (fun t => ‖X a t‖ ^ 2) AddCircle.haarAddCircle :=
      fun a => (memLp_two_iff_integrable_sq_norm (Lp.memLp (X a)).1).1 (Lp.memLp (X a))
    have e1 : (∑ a, ∑ b, ∫ t, conj (X a t) * (F a b t * X b t) ∂AddCircle.haarAddCircle)
        = ∫ t, ∑ a, ∑ b, conj (X a t) * (F a b t * X b t) ∂AddCircle.haarAddCircle := by
      rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ fun b _ => hint a b]
    have hint2 : Integrable (fun t => ∑ a, ∑ b, conj (X a t) * (F a b t * X b t)) AddCircle.haarAddCircle :=
      integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b
    have hre := integral_re hint2
    simp only [RCLike.re_to_complex] at hre
    rw [e1, ← hre]
    have e2 : lam * ∑' n, ∑ a, ‖ω n a‖ ^ 2 = ∫ t, lam * ∑ a, ‖X a t‖ ^ 2 ∂AddCircle.haarAddCircle := by
      rw [integral_const_mul, integral_finsetSum _ fun a _ => hsq a, Summable.tsum_finsetSum fun a _ => hω a]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hX, lift_sq]
    rw [e2]
    refine integral_mono hint2.re ((integrable_finsetSum _ fun a _ => hsq a).const_mul lam) fun t => ?_
    exact quad_re_le (fun a b => F a b t) (fun a b => hreal a b t) lam (hle t) (fun a => X a t)

theorem frame_inner_eq (θ : ℝ) (a b : Fin 3) :
    inner ℝ (frameUnit θ a) (frameUnit θ b) = if a = b then 1 else 0 := by
  have h := Real.cos_sq_add_sin_sq θ
  fin_cases a <;> fin_cases b <;>
    simp [frameUnit, radialUnit, angularUnit, axialUnit, PiLp.inner_apply, Fin.sum_univ_three,
      -inner_self_eq_norm_sq_to_K] <;> first | ring1 | nlinarith [h]

theorem frame_quad (θ : ℝ) (M : Space →L[ℝ] Space) (u : Fin 3 → ℝ) :
    ∑ a, ∑ b, u a * frameMat θ M a b * u b
      = inner ℝ (M (∑ b, u b • frameUnit θ b)) (∑ a, u a • frameUnit θ a) := by
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  simp only [Fin.sum_univ_three, frameMat, frameUnit, RCLike.conj_to_real]
  ring

theorem frame_sq (θ : ℝ) (u : Fin 3 → ℝ) : ‖∑ a, u a • frameUnit θ a‖ ^ 2 = ∑ a, u a ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, frame_inner_eq, RCLike.conj_to_real]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Finset.mem_univ, sq]

theorem pi_len : (0 : ℝ) < π - -π := by linarith [Real.pi_pos]

theorem pi_fact : Fact ((0 : ℝ) < π - -π) := ⟨pi_len⟩

attribute [local instance] pi_fact

theorem mode_coeff (m : ℕ) (β : ℤ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) :
    modeMat m β G p.1 p.2 a b = fourierCoeff (AddCircle.liftIoc (π - -π) (-π)
      (fun θ => (frameMat θ (G (cylPoint p.1 θ p.2)) a b : ℂ))) (β * m) := by
  have hab : -π < π := by linarith [Real.pi_pos]
  have hT2 : π - -π = 2 * π := by ring
  have e0 : fourierCoeff (T := π - -π) (AddCircle.liftIoc (π - -π) (-π)
      (fun θ => (frameMat θ (G (cylPoint p.1 θ p.2)) a b : ℂ))) (β * m)
      = fourierCoeffOn hab (fun θ => (frameMat θ (G (cylPoint p.1 θ p.2)) a b : ℂ)) (β * m) := rfl
  rw [e0, fourierCoeffOn_eq_integral _ _ hab]
  set g : ℝ → ℂ := fun θ => fourier (-(β * (m : ℤ))) (θ : AddCircle (π - -π)) •
    (frameMat θ (G (cylPoint p.1 θ p.2)) a b : ℂ) with hg
  have hper : Function.Periodic g (π - -π) := by
    intro θ
    simp only [hg, AddCircle.coe_add_period]
    congr 2
    rw [hT2]
    simp only [frameMat, cylPoint, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hshift := hper.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + (π - -π) = π by ring, hT2] at hshift
  unfold modeMat
  rw [← hshift, Complex.real_smul]
  congr 1
  · push_cast; ring
  · refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hg, smul_eq_mul]
    rw [fourier_coe_apply]
    congr 2
    simp only [azimuth]
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
    ring

end Breakdown.CellCert.CellAnalysis.CircleProduct
