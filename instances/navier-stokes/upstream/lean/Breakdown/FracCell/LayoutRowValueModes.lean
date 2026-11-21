import Breakdown.FracCell.LayoutRowValueParts
import Breakdown.FracCell.CellDensityModesSolid

open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

namespace LayoutRowModes

open CellCert CellCert.CellFormula CellCert.CellAnalysis CellCert.CellAnalysis.CellScalars SteadyCert
  CellCert.Assembly

theorem pairing_mode_reduction {K : CellBox} (hK : IsCellBox K)
    {row F : Space → Space} (hsupp : ∀ y ∉ K.solid, row y = 0)
    (hFi : Integrable (fun y => inner ℝ (F y) (row y)))
    (hm : ∀ᵐ y ∂volume, y ∈ K.solid → inner ℝ (F (mirror y)) (row (mirror y)) = inner ℝ (F y) (row y))
    (X : ℝ × ℝ → ℝ)
    (hcirc : ∀ᵐ p ∂(volume.restrict K.rect),
      ∫ θ in (0 : ℝ)..(2 * Real.pi), inner ℝ (F (cylPoint p.1 θ p.2)) (row (cylPoint p.1 θ p.2)) =
        2 * Real.pi * X p) :
    l2Pair F row = 4 * Real.pi * ∫ p in K.rect, p.1 * X p := by
  have h1 : l2Pair F row = ∫ y in K.solid, inner ℝ (F y) (row y) := by
    unfold l2Pair
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    rw [hsupp y hy, inner_zero_right]
  rw [h1, CellDensityModesSolid.solid_formula K hK _ hFi.integrableOn hm]
  have h2 : (∫ p in K.rect, p.1 * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      inner ℝ (F (cylPoint p.1 θ p.2)) (row (cylPoint p.1 θ p.2))) =
      ∫ p in K.rect, (2 * Real.pi) * (p.1 * X p) := by
    refine setIntegral_congr_ae (CellDensityModesSolid.rect_meas K) ?_
    filter_upwards [(ae_restrict_iff' (CellDensityModesSolid.rect_meas K)).1 hcirc] with p hp hpK
    rw [hp hpK]; ring
  rw [h2, integral_const_mul]
  ring


private theorem frame_inner (θ : ℝ) (u w : Space) :
    inner ℝ u w = ∑ a : Fin 3, frameVec θ u a * frameVec θ w a := by
  simp only [frameVec, Fin.sum_univ_three, radialUnit, angularUnit, axialUnit, inner_add_right,
    EuclideanSpace.inner_single_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, conj_trivial, one_mul]
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_three, conj_trivial, RCLike.inner_apply]
  linear_combination (-(u 0 * w 0 + u 1 * w 1)) * (Real.sin_sq_add_cos_sq θ)


private theorem mode_conj (f t : ℝ → ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), (f θ : ℂ) * Complex.exp ((t θ : ℝ) * Complex.I) =
      (starRingEnd ℂ) (∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(t θ : ℝ) * Complex.I) * (f θ : ℂ)) := by
  have h : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [intervalIntegral.integral_of_le h, intervalIntegral.integral_of_le h, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I]
  ring_nf

private theorem sum_ii {ι : Type} (s : Finset ι) {g : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (g i) volume a b) :
    IntervalIntegrable (fun θ => ∑ i ∈ s, g i θ) volume a b := by
  have := IntervalIntegrable.sum s h
  rwa [Finset.sum_fn] at this

private theorem re_term (f : ℝ → ℝ) (w : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) (hw : Continuous w) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ * (w θ).re = (∫ θ in (0 : ℝ)..(2 * Real.pi), (f θ : ℂ) * w θ).re := by
  have hc : IntervalIntegrable (fun θ => (f θ : ℂ) * w θ) volume 0 (2 * Real.pi) :=
    (show IntervalIntegrable (fun θ => (f θ : ℂ)) volume 0 (2 * Real.pi) from
      ⟨hf.1.ofReal, hf.2.ofReal⟩).mul_continuousOn hw.continuousOn
  have := Complex.reCLM.intervalIntegral_comp_comm hc
  rw [Complex.reCLM_apply] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [Complex.reCLM_apply, Complex.re_ofReal_mul]

theorem circle_pairing (m : ℕ) (s : Finset ℤ) (F row : Space → Space) (r z : ℝ) (W : ℤ → Fin 3 → ℂ)
    (hexp : ∀ θ a, frameVec θ (row (cylPoint r θ z)) a =
      (∑ n ∈ s, W n a * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re)
    (hint : ∀ a, IntervalIntegrable (fun θ => frameVec θ (F (cylPoint r θ z)) a) volume 0 (2 * Real.pi)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), inner ℝ (F (cylPoint r θ z)) (row (cylPoint r θ z)) =
      2 * Real.pi * (∑ n ∈ s, pairC (modeVec m n F r z) (W n)).re := by
  have he : ∀ (a : Fin 3) (n : ℤ), Continuous (fun θ : ℝ => W n a * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)) :=
    fun a n => by fun_prop
  have hterm : ∀ (a : Fin 3) (n : ℤ), IntervalIntegrable (fun θ => frameVec θ (F (cylPoint r θ z)) a *
      (W n a * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re) volume 0 (2 * Real.pi) := fun a n =>
    (hint a).mul_continuousOn (Complex.continuous_re.comp (he a n)).continuousOn
  have hpt : ∀ θ, inner ℝ (F (cylPoint r θ z)) (row (cylPoint r θ z)) =
      ∑ a : Fin 3, ∑ n ∈ s, frameVec θ (F (cylPoint r θ z)) a *
        (W n a * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re := by
    intro θ
    rw [frame_inner θ]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hexp θ a, Complex.re_sum, Finset.mul_sum]
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum fun a _ => sum_ii s fun n _ => hterm a n]
  simp_rw [intervalIntegral.integral_finsetSum fun n _ => hterm _ n]
  have hk : ∀ (a : Fin 3) (n : ℤ), ∫ θ in (0 : ℝ)..(2 * Real.pi), frameVec θ (F (cylPoint r θ z)) a *
      (W n a * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re =
      (W n a * (2 * Real.pi * (starRingEnd ℂ) (modeVec m n F r z a))).re := by
    intro a n
    rw [re_term _ _ (hint a) (he a n)]
    congr 1
    have h1 : (fun θ : ℝ => (frameVec θ (F (cylPoint r θ z)) a : ℂ) *
        (W n a * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I))) =
        fun θ => W n a * ((frameVec θ (F (cylPoint r θ z)) a : ℂ) *
          Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)) := by
      funext θ; ring
    rw [h1, intervalIntegral.integral_const_mul,
      mode_conj (fun θ => frameVec θ (F (cylPoint r θ z)) a) (fun θ => azimuth m n * θ)]
    unfold modeVec
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      exact_mod_cast this.ne'
    simp only [map_div₀, map_one, map_mul, map_ofNat, Complex.conj_ofReal]
    field_simp
    simp only [mul_comm Complex.I]
  simp_rw [hk]
  rw [Finset.sum_comm]
  unfold pairC
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat]
  ring


theorem pairing_modes {K : CellBox} (hK : IsCellBox K) {row F : Space → Space} (hsupp : ∀ y ∉ K.solid, row y = 0)
    (hFi : Integrable (fun y => inner ℝ (F y) (row y)))
    (hm : ∀ᵐ y ∂volume, y ∈ K.solid → inner ℝ (F (mirror y)) (row (mirror y)) = inner ℝ (F y) (row y))
    (m : ℕ) (s : Finset ℤ) (W : ℝ × ℝ → ℤ → Fin 3 → ℂ)
    (hexp : ∀ p ∈ K.rect, ∀ θ a, frameVec θ (row (cylPoint p.1 θ p.2)) a =
      (∑ n ∈ s, W p n a * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re)
    (hint : ∀ᵐ p ∂(volume.restrict K.rect), ∀ a,
      IntervalIntegrable (fun θ => frameVec θ (F (cylPoint p.1 θ p.2)) a) volume 0 (2 * Real.pi)) :
    l2Pair F row = 4 * Real.pi *
      ∫ p in K.rect, p.1 * (∑ n ∈ s, pairC (modeVec m n F p.1 p.2) (W p n)).re := by
  refine pairing_mode_reduction hK hsupp hFi hm _ ?_
  filter_upwards [hint, ae_restrict_mem (CellDensityModesSolid.rect_meas K)] with p hp hpK
  exact circle_pairing m s F row p.1 p.2 (W p) (hexp p hpK) hp

theorem mirror_inner (u w : Space) : inner ℝ (mirror u) (mirror w) = inner ℝ u w := by
  simp only [mirror, inner_add_left, inner_add_right, EuclideanSpace.inner_single_right, PiLp.single_apply]
  simp
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]

theorem class_pairing_mirror {m : ℕ} {F row : Space → Space} (hF : IsClassField m F) (hrow : IsClassField m row) :
    ∀ᵐ y ∂volume, inner ℝ (F (mirror y)) (row (mirror y)) = inner ℝ (F y) (row y) := by
  filter_upwards [hF.2, hrow.2] with y h1 h2
  rw [h1, h2, mirror_inner]


end LayoutRowModes

end FracInternal

end Breakdown
