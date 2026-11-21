import Breakdown.FracCell.DensitySliceParts
import Breakdown.FracCell.LowEntry

open MeasureTheory Real ComplexConjugate

noncomputable section

namespace Breakdown.FracInternal.DensitySlice

open CellCert CellAnalysis SteadyCert Assembly

theorem pair_modeCoeffOn {a b : ℝ} {f g : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a b))) (hg : MemLp g 2 (volume.restrict (Set.Ioc a b))) :
    HasSum (fun i => conj (fourierCoeffOn hab g i) * fourierCoeffOn hab f i)
      ((b - a)⁻¹ • ∫ x in a..b, conj (g x) * f x) := by
  obtain ⟨T, rfl⟩ : ∃ T, b = a + T := ⟨b - a, by ring⟩
  have hT : 0 < T := by linarith
  have := Fact.mk hT
  have h1 := hf.memLp_liftIoc.haarAddCircle
  have h2 := hg.memLp_liftIoc.haarAddCircle
  have H := fourierBasis.hasSum_inner_mul_inner h2.toLp h1.toLp
  have e1 : (fun i => conj (fourierCoeffOn hab g i) * fourierCoeffOn hab f i) = fun i =>
      inner ℂ h2.toLp (fourierBasis i) * inner ℂ (fourierBasis i) h1.toLp := by
    funext i
    rw [← inner_conj_symm h2.toLp, ← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply,
      fourierBasis_repr, fourierBasis_repr, fourierCoeff_congr_ae h1.coeFn_toLp,
      fourierCoeff_congr_ae h2.coeFn_toLp, fourierCoeff_liftIoc_eq, fourierCoeff_liftIoc_eq]
  have e2 : ((a + T - a)⁻¹ • ∫ x in a..a + T, conj (g x) * f x) = inner ℂ h2.toLp h1.toLp := by
    rw [add_sub_cancel_left, MeasureTheory.L2.inner_def, ← AddCircle.integral_liftIoc_eq_intervalIntegral,
      ← AddCircle.integral_haarAddCircle]
    apply integral_congr_ae
    filter_upwards [h1.coeFn_toLp, h2.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2]
    simp [AddCircle.liftIoc, mul_comm]
  rw [e1, e2]
  exact H

def circleCoeff (t : ℝ) (h : ℝ → ℂ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), Complex.exp (-(t * θ : ℝ) * Complex.I) * h θ

theorem circle_len_pos : (0 : ℝ) < 2 * π := by positivity

theorem circleCoeff_eq (k : ℤ) (h : ℝ → ℂ) :
    circleCoeff k h = fourierCoeffOn circle_len_pos h k := by
  rw [fourierCoeffOn_eq_integral _ _ circle_len_pos, circleCoeff, Complex.real_smul]
  congr 1
  · push_cast; ring
  · refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [smul_eq_mul]
    rw [fourier_coe_apply]
    congr 2
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
    ring

theorem circleCoeff_shift {m : ℕ} (hm : 0 < m) (h : ℝ → ℂ) (hper : ∀ θ, h (θ + 2 * π) = h θ)
    (hturn : ∀ᵐ θ ∂volume, h (θ + 2 * π / m) = h θ) (k : ℤ) (hk : ¬ (m : ℤ) ∣ k) :
    circleCoeff k h = 0 := by
  set F : ℝ → ℂ := fun θ => Complex.exp (-(k * θ : ℝ) * Complex.I) * h θ with hF
  have hFper : Function.Periodic F (2 * π) := by
    intro θ
    simp only [hF, hper]
    congr 1
    rw [show (k : ℝ) * (θ + 2 * π) = k * θ + (k : ℝ) * (2 * π) by ring]
    push_cast
    rw [show -(((k : ℂ) * θ + k * (2 * π))) * Complex.I = -((k : ℂ) * θ) * Complex.I + ((-k : ℤ) : ℂ) * (2 * π * Complex.I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  set c : ℂ := Complex.exp (-((k : ℝ) * (2 * π / m) : ℝ) * Complex.I) with hc
  have hshift : (∫ θ in (0 : ℝ)..(2 * π), F θ) = c * ∫ θ in (0 : ℝ)..(2 * π), F θ := by
    have e1 : (∫ θ in (0 : ℝ)..(2 * π), F θ) = ∫ θ in (0 : ℝ)..(2 * π), F (θ + 2 * π / m) := by
      rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (2 * π) (2 * π / m)]
      exact ((hFper.intervalIntegral_add_eq (2 * π / m) 0).trans (by rw [zero_add])).symm
    have hexp : ∀ θ : ℝ, Complex.exp (-((k : ℝ) * (θ + 2 * π / m) : ℝ) * Complex.I) =
        c * Complex.exp (-((k : ℝ) * θ : ℝ) * Complex.I) := by
      intro θ
      rw [hc, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← intervalIntegral.integral_const_mul]
    refine e1.trans (intervalIntegral.integral_congr_ae (hturn.mono fun θ hθ _ => ?_))
    show Complex.exp (-((k : ℝ) * (θ + 2 * π / m) : ℝ) * Complex.I) * h (θ + 2 * π / m) =
      c * (Complex.exp (-((k : ℝ) * θ : ℝ) * Complex.I) * h θ)
    rw [hθ, hexp θ, mul_assoc]
  have hc1 : c ≠ 1 := by
    intro h1
    rw [hc, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    apply hk
    refine ⟨-n, ?_⟩
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    push_cast at hn
    have : (k : ℂ) = ((m : ℤ) * (-n) : ℤ) := by
      push_cast
      field_simp at hn
      linear_combination -hn
    exact_mod_cast this
  have h0 : (∫ θ in (0 : ℝ)..(2 * π), F θ) = 0 := by
    have : (1 - c) * (∫ θ in (0 : ℝ)..(2 * π), F θ) = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h).symm hc1
    · exact h
  rw [circleCoeff]
  have : (∫ θ in (0 : ℝ)..(2 * π), Complex.exp (-((k : ℝ) * θ : ℝ) * Complex.I) * h θ) = ∫ θ in (0 : ℝ)..(2 * π), F θ := rfl
  rw [this, h0, mul_zero]

theorem circle_modes {m : ℕ} (hm : 0 < m) {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (hg : MemLp g 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hper : ∀ θ, f (θ + 2 * π) = f θ) (hturn : ∀ᵐ θ ∂volume, f (θ + 2 * π / m) = f θ) :
    HasSum (fun n : ℤ => circleCoeff (azimuth m n) f * conj (circleCoeff (azimuth m n) g))
      ((2 * π)⁻¹ • ∫ θ in (0 : ℝ)..(2 * π), f θ * conj (g θ)) := by
  have H := pair_modeCoeffOn circle_len_pos hf hg
  rw [sub_zero] at H
  have hinj : Function.Injective (fun n : ℤ => n * (m : ℤ)) := by
    intro a b hab
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    exact mul_right_cancel₀ hm' hab
  have hvan : ∀ x ∉ Set.range (fun n : ℤ => n * (m : ℤ)),
      conj (fourierCoeffOn circle_len_pos g x) * fourierCoeffOn circle_len_pos f x = 0 := by
    intro x hx
    have hd : ¬ (m : ℤ) ∣ x := by
      rintro ⟨q, rfl⟩
      exact hx ⟨q, mul_comm _ _⟩
    rw [← circleCoeff_eq x f, circleCoeff_shift hm f hper hturn x hd, mul_zero]
  have H2 := (hinj.hasSum_iff hvan).2 H
  have e : ∀ n : ℤ, azimuth m n = ((n * (m : ℤ) : ℤ) : ℝ) := fun n => by
    unfold azimuth; push_cast; ring
  have e2 : (∫ θ in (0 : ℝ)..(2 * π), f θ * conj (g θ)) = ∫ θ in (0 : ℝ)..(2 * π), conj (g θ) * f θ :=
    intervalIntegral.integral_congr fun θ _ => mul_comm _ _
  rw [e2]
  convert H2 using 1
  funext n
  simp only [Function.comp_apply, e, circleCoeff_eq]
  ring

theorem coord_sum (u : Space) : u = ∑ j : Fin 3, u j • unitVector j := by
  ext i
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem inner_expand (M : Space →L[ℝ] Space) (u w : Space) :
    inner ℝ (M u) w = ∑ i : Fin 3, ∑ j : Fin 3, w i * u j * entry M i j := by
  conv_lhs => rw [coord_sum u]
  simp only [map_sum, map_smul, sum_inner, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, entry, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem frame_entryInner (θ : ℝ) (M K : Space →L[ℝ] Space) :
    entryInner M K = ∑ a : Fin 3, ∑ b : Fin 3, frameMat θ M a b * frameMat θ K a b := by
  have hK : ∀ i l : Fin 3, K (unitVector i) l = entry K l i := fun _ _ => rfl
  simp only [entryInner, frameMat, inner_expand, hK]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, radialUnit, angularUnit, axialUnit, unitVector, PiLp.add_apply,
    PiLp.single_apply]
  simp
  linear_combination (-(entry M 0 0 * entry K 0 0 + entry M 0 1 * entry K 0 1 + entry M 0 2 * entry K 0 2
      + entry M 1 0 * entry K 1 0 + entry M 1 1 * entry K 1 1 + entry M 1 2 * entry K 1 2
      + entry M 0 0 * entry K 0 0 + entry M 1 0 * entry K 1 0 + entry M 2 0 * entry K 2 0
      + entry M 0 1 * entry K 0 1 + entry M 1 1 * entry K 1 1 + entry M 2 1 * entry K 2 1
      + (Real.sin θ ^ 2 + Real.cos θ ^ 2 - 1) * (entry M 0 0 * entry K 0 0 + entry M 0 1 * entry K 0 1
        + entry M 1 0 * entry K 1 0 + entry M 1 1 * entry K 1 1))) * Real.sin_sq_add_cos_sq θ

theorem cyl_per (r θ z : ℝ) : cylPoint r (θ + 2 * π) z = cylPoint r θ z := by
  simp only [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem frameMat_add (θ : ℝ) (M : Space →L[ℝ] Space) (a b : Fin 3) :
    frameMat (θ + 2 * π) M a b = frameMat θ M a b := by
  simp only [frameMat, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem entry_modes {m : ℕ} (hm : 0 < m) {g h : ℝ → ℝ}
    (hg : IsCircleSliceRegular m g) (hh : MemLp h 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hper : ∀ θ, g (θ + 2 * π) = g θ) :
    HasSum (fun n : ℤ => circleCoeff (azimuth m n) (fun θ => (g θ : ℂ)) *
        conj (circleCoeff (azimuth m n) (fun θ => (h θ : ℂ))))
      (((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), g θ * h θ : ℝ) : ℂ) := by
  have H := circle_modes hm (f := fun θ => (g θ : ℂ)) (g := fun θ => (h θ : ℂ)) hg.1.ofReal hh.ofReal
    (fun θ => by simp only [hper]) (hg.2.mono fun θ hθ => by simp only [hθ])
  convert H using 1
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, intervalIntegral.integral_ofReal]
  rw [Complex.real_smul]
  push_cast
  ring

theorem product_integrable {g h : ℝ → ℝ} (hg : MemLp g 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hh : MemLp h 2 (volume.restrict (Set.Ioc 0 (2 * π)))) :
    IntervalIntegrable (fun θ => g θ * h θ) volume 0 (2 * π) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le circle_len_pos.le]
  exact hg.integrable_mul hh

theorem slice_pair {m : ℕ} (hm : 0 < m) (G A : Space → (Space →L[ℝ] Space)) (r z : ℝ)
    (hG : ∀ a b, IsCircleSliceRegular m (fun θ => frameMat θ (G (cylPoint r θ z)) a b))
    (hA : ∀ a b, MemLp (fun θ => frameMat θ (A (cylPoint r θ z)) a b) 2 (volume.restrict (Set.Ioc 0 (2 * π)))) :
    HasSum (fun n : ℤ => entryPairing (fun a b => modeMat m n G r z a b) (fun a b => modeMat m n A r z a b))
      (((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), entryInner (G (cylPoint r θ z)) (A (cylPoint r θ z)) : ℝ) : ℂ) := by
  have hper : ∀ a b θ, frameMat (θ + 2 * π) (G (cylPoint r (θ + 2 * π) z)) a b = frameMat θ (G (cylPoint r θ z)) a b :=
    fun a b θ => by rw [cyl_per, frameMat_add]
  have H : ∀ a b, HasSum (fun n : ℤ => modeMat m n G r z a b * conj (modeMat m n A r z a b))
      (((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), frameMat θ (G (cylPoint r θ z)) a b * frameMat θ (A (cylPoint r θ z)) a b : ℝ) : ℂ) :=
    fun a b => entry_modes hm (hG a b) (hA a b) (hper a b)
  have H2 := hasSum_sum (s := Finset.univ) fun a _ => hasSum_sum (s := Finset.univ) fun b _ => H a b
  convert H2 using 1
  · funext n
    rfl
  have hint : ∀ a b, IntervalIntegrable (fun θ => frameMat θ (G (cylPoint r θ z)) a b *
      frameMat θ (A (cylPoint r θ z)) a b) volume 0 (2 * π) := fun a b => product_integrable (hG a b).1 (hA a b)
  have e : (∫ θ in (0 : ℝ)..(2 * π), entryInner (G (cylPoint r θ z)) (A (cylPoint r θ z))) =
      ∑ a : Fin 3, ∑ b : Fin 3, ∫ θ in (0 : ℝ)..(2 * π), frameMat θ (G (cylPoint r θ z)) a b *
        frameMat θ (A (cylPoint r θ z)) a b := by
    rw [intervalIntegral.integral_congr (fun θ _ => frame_entryInner θ (G (cylPoint r θ z)) (A (cylPoint r θ z))),
      intervalIntegral.integral_finsetSum fun a _ => ?_]
    · refine Finset.sum_congr rfl fun a _ => ?_
      exact intervalIntegral.integral_finsetSum fun b _ => hint a b
    · have := IntervalIntegrable.sum (Finset.univ) fun b _ => hint a b
      simpa [Finset.sum_fn] using this
  rw [e]
  push_cast
  simp only [Finset.mul_sum]

theorem inner_expand3 (H : Space →L[ℝ] Space →L[ℝ] Space) (u v w : Space) :
    inner ℝ (H u v) w = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      w i * v j * u k * H (unitVector k) (unitVector j) i := by
  conv_lhs => rw [coord_sum u, coord_sum v]
  simp only [Fin.sum_univ_three, map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.smul_apply, smul_eq_mul, PiLp.add_apply]
  ring

theorem curlOf_apply (G : Space →L[ℝ] Space) (i : Fin 3) :
    curlOf G i = ∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * entry G l j := by
  fin_cases i <;> simp [curlOf, unitVector, Fin.sum_univ_three]

theorem frame_curl (θ : ℝ) (G : Space →L[ℝ] Space) :
    ‖curlOf G‖ ^ 2 = ∑ i : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * frameMat θ G l j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, curlOf_apply, frameMat, inner_expand]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, radialUnit, angularUnit, axialUnit, PiLp.add_apply, PiLp.single_apply]
  simp [permSign]
  linear_combination (-(entry G 0 1)^2 + 2*(entry G 0 1)*(entry G 1 0) - (entry G 0 2)^2 + 2*(entry G 0 2)*(entry G 2 0) - (entry G 1 0)^2 - (entry G 1 2)^2 + 2*(entry G 1 2)*(entry G 2 1) - (entry G 2 0)^2 - (entry G 2 1)^2 + Real.cos θ^2*(-(entry G 0 1)^2 + 2*(entry G 0 1)*(entry G 1 0) - (entry G 1 0)^2) + Real.sin θ^2*(-(entry G 0 1)^2 + 2*(entry G 0 1)*(entry G 1 0) - (entry G 1 0)^2)) * Real.sin_sq_add_cos_sq θ

private theorem frame_coordSq (θ : ℝ) (w : Space) :
    ∑ a : Fin 3, inner ℝ w (frameUnit θ a) ^ 2 = ‖w‖ ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, frameUnit, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, radialUnit, angularUnit, axialUnit, inner_add_right,
    EuclideanSpace.inner_single_right, Real.norm_eq_abs, sq_abs, conj_trivial]
  linear_combination (w 0 ^ 2 + w 1 ^ 2) * h

private theorem frame_normSq (θ : ℝ) (T : Space →L[ℝ] Space) :
    ∑ b : Fin 3, ‖T (frameUnit θ b)‖ ^ 2 = ∑ j : Fin 3, ‖T (unitVector j)‖ ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  have er : radialUnit θ = Real.cos θ • unitVector 0 + Real.sin θ • unitVector 1 := by
    ext i
    fin_cases i <;> simp [radialUnit, unitVector]
  have ea : angularUnit θ = (-Real.sin θ) • unitVector 0 + Real.cos θ • unitVector 1 := by
    ext i
    fin_cases i <;> simp [angularUnit, unitVector]
  have ez : axialUnit = unitVector 2 := by
    ext i
    fin_cases i <;> simp [axialUnit, unitVector]
  simp only [Fin.sum_univ_three, frameUnit, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, er, ea, ez, map_add, map_smul, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs, sq_abs, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  linear_combination (T (unitVector 0) 0 ^ 2 + T (unitVector 0) 1 ^ 2 + T (unitVector 0) 2 ^ 2 +
    T (unitVector 1) 0 ^ 2 + T (unitVector 1) 1 ^ 2 + T (unitVector 1) 2 ^ 2) * h

theorem frame_second (θ : ℝ) (H : Space →L[ℝ] Space →L[ℝ] Space) :
    CellCert.fullSecondSq H = ∑ a : Fin 3, ∑ b : Fin 3, ∑ d : Fin 3, frameThird θ H a b d ^ 2 := by
  have h1 : ∀ b d : Fin 3, ∑ a : Fin 3, frameThird θ H a b d ^ 2 = ‖H (frameUnit θ d) (frameUnit θ b)‖ ^ 2 :=
    fun b d => by simp only [frameThird]; exact frame_coordSq θ _
  have h2 : ∀ d : Fin 3, ∑ b : Fin 3, ‖H (frameUnit θ d) (frameUnit θ b)‖ ^ 2 =
      ∑ j : Fin 3, ‖H (frameUnit θ d) (unitVector j)‖ ^ 2 :=
    fun d => frame_normSq θ (H (frameUnit θ d))
  have h3 : ∀ j : Fin 3, ∑ d : Fin 3, ‖H (frameUnit θ d) (unitVector j)‖ ^ 2 =
      ∑ k : Fin 3, ‖H (unitVector k) (unitVector j)‖ ^ 2 :=
    fun j => by simpa only [ContinuousLinearMap.flip_apply] using frame_normSq θ (H.flip (unitVector j))
  calc CellCert.fullSecondSq H = ∑ j : Fin 3, ∑ k : Fin 3, ‖H (unitVector k) (unitVector j)‖ ^ 2 := by
        unfold CellCert.fullSecondSq
        exact Finset.sum_comm
    _ = ∑ j : Fin 3, ∑ d : Fin 3, ‖H (frameUnit θ d) (unitVector j)‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => (h3 j).symm
    _ = ∑ d : Fin 3, ∑ j : Fin 3, ‖H (frameUnit θ d) (unitVector j)‖ ^ 2 := Finset.sum_comm
    _ = ∑ d : Fin 3, ∑ b : Fin 3, ‖H (frameUnit θ d) (frameUnit θ b)‖ ^ 2 :=
        Finset.sum_congr rfl fun d _ => (h2 d).symm
    _ = ∑ d : Fin 3, ∑ b : Fin 3, ∑ a : Fin 3, frameThird θ H a b d ^ 2 :=
        Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => (h1 b d).symm
    _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ d : Fin 3, frameThird θ H a b d ^ 2 := by
        simp only [Fin.sum_univ_three]
        ring

theorem frame_curlGrad (θ : ℝ) (H : Space →L[ℝ] Space →L[ℝ] Space) :
    CellCert.curlGradSq H = ∑ i : Fin 3, ∑ d : Fin 3,
      (∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * frameThird θ H l j d) ^ 2 := by
  simp only [CellCert.curlGradSq, frameThird, frameUnit, inner_expand3]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, radialUnit, angularUnit, axialUnit, PiLp.add_apply, PiLp.single_apply]
  simp [permSign]
  linear_combination (-(H (unitVector 0) (unitVector 1) 0)^2 + 2*(H (unitVector 0) (unitVector 1) 0)*(H (unitVector 0) (unitVector 0) 1) - (H (unitVector 1) (unitVector 1) 0)^2 + 2*(H (unitVector 1) (unitVector 1) 0)*(H (unitVector 1) (unitVector 0) 1) - (H (unitVector 2) (unitVector 1) 0)^2 + 2*(H (unitVector 2) (unitVector 1) 0)*(H (unitVector 2) (unitVector 0) 1) - (H (unitVector 0) (unitVector 2) 0)^2 + 2*(H (unitVector 0) (unitVector 2) 0)*(H (unitVector 0) (unitVector 0) 2) - (H (unitVector 1) (unitVector 2) 0)^2 + 2*(H (unitVector 1) (unitVector 2) 0)*(H (unitVector 1) (unitVector 0) 2) - (H (unitVector 2) (unitVector 2) 0)^2 + 2*(H (unitVector 2) (unitVector 2) 0)*(H (unitVector 2) (unitVector 0) 2) - (H (unitVector 0) (unitVector 0) 1)^2 - (H (unitVector 1) (unitVector 0) 1)^2 - (H (unitVector 2) (unitVector 0) 1)^2 - (H (unitVector 0) (unitVector 2) 1)^2 + 2*(H (unitVector 0) (unitVector 2) 1)*(H (unitVector 0) (unitVector 1) 2) - (H (unitVector 1) (unitVector 2) 1)^2 + 2*(H (unitVector 1) (unitVector 2) 1)*(H (unitVector 1) (unitVector 1) 2) - (H (unitVector 2) (unitVector 2) 1)^2 + 2*(H (unitVector 2) (unitVector 2) 1)*(H (unitVector 2) (unitVector 1) 2) - (H (unitVector 0) (unitVector 0) 2)^2 - (H (unitVector 1) (unitVector 0) 2)^2 - (H (unitVector 2) (unitVector 0) 2)^2 - (H (unitVector 0) (unitVector 1) 2)^2 - (H (unitVector 1) (unitVector 1) 2)^2 - (H (unitVector 2) (unitVector 1) 2)^2 + Real.cos θ^4*(-(H (unitVector 0) (unitVector 1) 0)^2 + 2*(H (unitVector 0) (unitVector 1) 0)*(H (unitVector 0) (unitVector 0) 1) - (H (unitVector 1) (unitVector 1) 0)^2 + 2*(H (unitVector 1) (unitVector 1) 0)*(H (unitVector 1) (unitVector 0) 1) - (H (unitVector 0) (unitVector 0) 1)^2 - (H (unitVector 1) (unitVector 0) 1)^2) + Real.cos θ^2*Real.sin θ^2*(-2*(H (unitVector 0) (unitVector 1) 0)^2 + 4*(H (unitVector 0) (unitVector 1) 0)*(H (unitVector 0) (unitVector 0) 1) - 2*(H (unitVector 1) (unitVector 1) 0)^2 + 4*(H (unitVector 1) (unitVector 1) 0)*(H (unitVector 1) (unitVector 0) 1) - 2*(H (unitVector 0) (unitVector 0) 1)^2 - 2*(H (unitVector 1) (unitVector 0) 1)^2) + Real.cos θ^2*(-(H (unitVector 0) (unitVector 1) 0)^2 + 2*(H (unitVector 0) (unitVector 1) 0)*(H (unitVector 0) (unitVector 0) 1) - (H (unitVector 1) (unitVector 1) 0)^2 + 2*(H (unitVector 1) (unitVector 1) 0)*(H (unitVector 1) (unitVector 0) 1) - (H (unitVector 2) (unitVector 1) 0)^2 + 2*(H (unitVector 2) (unitVector 1) 0)*(H (unitVector 2) (unitVector 0) 1) - (H (unitVector 0) (unitVector 2) 0)^2 + 2*(H (unitVector 0) (unitVector 2) 0)*(H (unitVector 0) (unitVector 0) 2) - (H (unitVector 1) (unitVector 2) 0)^2 + 2*(H (unitVector 1) (unitVector 2) 0)*(H (unitVector 1) (unitVector 0) 2) - (H (unitVector 0) (unitVector 0) 1)^2 - (H (unitVector 1) (unitVector 0) 1)^2 - (H (unitVector 2) (unitVector 0) 1)^2 - (H (unitVector 0) (unitVector 2) 1)^2 + 2*(H (unitVector 0) (unitVector 2) 1)*(H (unitVector 0) (unitVector 1) 2) - (H (unitVector 1) (unitVector 2) 1)^2 + 2*(H (unitVector 1) (unitVector 2) 1)*(H (unitVector 1) (unitVector 1) 2) - (H (unitVector 0) (unitVector 0) 2)^2 - (H (unitVector 1) (unitVector 0) 2)^2 - (H (unitVector 0) (unitVector 1) 2)^2 - (H (unitVector 1) (unitVector 1) 2)^2) + Real.sin θ^4*(-(H (unitVector 0) (unitVector 1) 0)^2 + 2*(H (unitVector 0) (unitVector 1) 0)*(H (unitVector 0) (unitVector 0) 1) - (H (unitVector 1) (unitVector 1) 0)^2 + 2*(H (unitVector 1) (unitVector 1) 0)*(H (unitVector 1) (unitVector 0) 1) - (H (unitVector 0) (unitVector 0) 1)^2 - (H (unitVector 1) (unitVector 0) 1)^2) + Real.sin θ^2*(-(H (unitVector 0) (unitVector 1) 0)^2 + 2*(H (unitVector 0) (unitVector 1) 0)*(H (unitVector 0) (unitVector 0) 1) - (H (unitVector 1) (unitVector 1) 0)^2 + 2*(H (unitVector 1) (unitVector 1) 0)*(H (unitVector 1) (unitVector 0) 1) - (H (unitVector 2) (unitVector 1) 0)^2 + 2*(H (unitVector 2) (unitVector 1) 0)*(H (unitVector 2) (unitVector 0) 1) - (H (unitVector 0) (unitVector 2) 0)^2 + 2*(H (unitVector 0) (unitVector 2) 0)*(H (unitVector 0) (unitVector 0) 2) - (H (unitVector 1) (unitVector 2) 0)^2 + 2*(H (unitVector 1) (unitVector 2) 0)*(H (unitVector 1) (unitVector 0) 2) - (H (unitVector 0) (unitVector 0) 1)^2 - (H (unitVector 1) (unitVector 0) 1)^2 - (H (unitVector 2) (unitVector 0) 1)^2 - (H (unitVector 0) (unitVector 2) 1)^2 + 2*(H (unitVector 0) (unitVector 2) 1)*(H (unitVector 0) (unitVector 1) 2) - (H (unitVector 1) (unitVector 2) 1)^2 + 2*(H (unitVector 1) (unitVector 2) 1)*(H (unitVector 1) (unitVector 1) 2) - (H (unitVector 0) (unitVector 0) 2)^2 - (H (unitVector 1) (unitVector 0) 2)^2 - (H (unitVector 0) (unitVector 1) 2)^2 - (H (unitVector 1) (unitVector 1) 2)^2)) * Real.sin_sq_add_cos_sq θ

theorem entrySq_frame (θ : ℝ) (M : Space →L[ℝ] Space) :
    entrySq M = ∑ a : Fin 3, ∑ b : Fin 3, frameMat θ M a b ^ 2 := by
  have h := frame_entryInner θ M M
  simp only [entryInner, real_inner_self_eq_norm_sq] at h
  simp only [entrySq]
  rw [h]
  simp only [sq]

theorem frameThird_add (θ : ℝ) (H : Space →L[ℝ] Space →L[ℝ] Space) (a b d : Fin 3) :
    frameThird (θ + 2 * π) H a b d = frameThird θ H a b d := by
  simp only [frameThird, frameUnit, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem regular_integrable {m : ℕ} {f : ℝ → ℝ} (hf : IsCircleSliceRegular m f) :
    IntervalIntegrable f volume 0 (2 * π) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le circle_len_pos.le]
  exact hf.1.integrable one_le_two

theorem regular_const {m : ℕ} (w : ℝ) {f : ℝ → ℝ} (hf : IsCircleSliceRegular m f) :
    IsCircleSliceRegular m (fun θ => w * f θ) :=
  ⟨hf.1.const_mul w, hf.2.mono fun θ hθ => by simp only [hθ]⟩

theorem regular_sum {m : ℕ} {ι : Type} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, IsCircleSliceRegular m (f i)) :
    IsCircleSliceRegular m (fun θ => ∑ i ∈ s, f i θ) := by
  refine ⟨memLp_finsetSum s fun i hi => (hf i hi).1, ?_⟩
  have h := (Filter.eventually_all_finset s).2 fun i hi => (hf i hi).2
  exact h.mono fun θ hθ => Finset.sum_congr rfl hθ

theorem circleCoeff_const (t w : ℝ) (f : ℝ → ℝ) :
    circleCoeff t (fun θ => ((w * f θ : ℝ) : ℂ)) = (w : ℂ) * circleCoeff t (fun θ => (f θ : ℂ)) := by
  unfold circleCoeff
  have e : ∀ θ : ℝ, Complex.exp (-(t * θ : ℝ) * Complex.I) * ((w * f θ : ℝ) : ℂ) =
      (w : ℂ) * (Complex.exp (-(t * θ : ℝ) * Complex.I) * (f θ : ℂ)) := fun θ => by push_cast; ring
  simp only [e, intervalIntegral.integral_const_mul]
  ring

theorem circleCoeff_sum (t : ℝ) {ι : Type} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume 0 (2 * π)) :
    circleCoeff t (fun θ => ((∑ i ∈ s, f i θ : ℝ) : ℂ)) = ∑ i ∈ s, circleCoeff t (fun θ => (f i θ : ℂ)) := by
  unfold circleCoeff
  have e : ∀ θ : ℝ, Complex.exp (-(t * θ : ℝ) * Complex.I) * ((∑ i ∈ s, f i θ : ℝ) : ℂ) =
      ∑ i ∈ s, Complex.exp (-(t * θ : ℝ) * Complex.I) * (f i θ : ℂ) := fun θ => by
    push_cast; rw [Finset.mul_sum]
  have hi : ∀ i ∈ s, IntervalIntegrable (fun θ => Complex.exp (-(t * θ : ℝ) * Complex.I) * (f i θ : ℂ))
      volume 0 (2 * π) := by
    intro i hi
    have h1 : IntervalIntegrable (fun θ => (f i θ : ℂ)) volume 0 (2 * π) := ⟨(hf i hi).1.ofReal, (hf i hi).2.ofReal⟩
    exact h1.continuousOn_mul (by fun_prop : Continuous fun θ : ℝ => Complex.exp (-(t * θ : ℝ) * Complex.I)).continuousOn
  simp only [e]
  rw [intervalIntegral.integral_finsetSum hi, Finset.mul_sum]

def ModeSum (f : ℤ → ℝ) (F : ℝ → ℝ) : Prop :=
  IntervalIntegrable F volume 0 (2 * π) ∧ HasSum f ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), F θ)

theorem modeSum_sum {ι : Type} (s : Finset ι) {f : ι → ℤ → ℝ} {F : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, ModeSum (f i) (F i)) : ModeSum (fun n => ∑ i ∈ s, f i n) (fun θ => ∑ i ∈ s, F i θ) := by
  refine ⟨?_, ?_⟩
  · have := IntervalIntegrable.sum s fun i hi => (h i hi).1
    simpa [Finset.sum_fn] using this
  · rw [intervalIntegral.integral_finsetSum fun i hi => (h i hi).1, Finset.mul_sum]
    exact hasSum_sum fun i hi => (h i hi).2

theorem modeSum_const (w : ℝ) {f : ℤ → ℝ} {F : ℝ → ℝ} (h : ModeSum f F) :
    ModeSum (fun n => w * f n) (fun θ => w * F θ) := by
  refine ⟨h.1.const_mul w, ?_⟩
  rw [intervalIntegral.integral_const_mul, mul_left_comm]
  exact h.2.mul_left w

theorem modeSum_add {f g : ℤ → ℝ} {F K : ℝ → ℝ} (h₁ : ModeSum f F) (h₂ : ModeSum g K) :
    ModeSum (fun n => f n + g n) (fun θ => F θ + K θ) := by
  refine ⟨h₁.1.add h₂.1, ?_⟩
  rw [intervalIntegral.integral_add h₁.1 h₂.1, mul_add]
  exact h₁.2.add h₂.2

theorem modeSum_congr {f f' : ℤ → ℝ} {F F' : ℝ → ℝ} (h : ModeSum f F) (hf : ∀ n, f n = f' n)
    (hF : ∀ θ, F θ = F' θ) : ModeSum f' F' := by
  have e1 : f = f' := funext hf
  have e2 : F = F' := funext hF
  rw [← e1, ← e2]
  exact h

theorem modeSum_sq {m : ℕ} (hm : 0 < m) {g : ℝ → ℝ} (hg : IsCircleSliceRegular m g)
    (hper : ∀ θ, g (θ + 2 * π) = g θ) :
    ModeSum (fun n => ‖circleCoeff (azimuth m n) (fun θ => (g θ : ℂ))‖ ^ 2) (fun θ => g θ ^ 2) := by
  refine ⟨?_, ?_⟩
  · simpa only [sq] using product_integrable hg.1 hg.1
  · have H := Complex.reCLM.hasSum (entry_modes hm hg hg.1 hper)
    simp only [Complex.reCLM_apply, Complex.ofReal_re, Complex.mul_conj, Complex.normSq_eq_norm_sq] at H
    simpa only [sq] using H

theorem quadratic_slice : CircleSliceQuadraticStatement := by
  intro α k N c hm x p hd
  have hm0 : 0 < c.order := by omega
  obtain ⟨-, hG, hH, -, -, -, hwt⟩ := hd
  have pG : ∀ a b θ, frameMat (θ + 2 * π) (x.2.1 (cylPoint p.1 (θ + 2 * π) p.2)) a b =
      frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) a b := fun a b θ => by rw [cyl_per, frameMat_add]
  have pH : ∀ a b d θ, frameThird (θ + 2 * π) (x.2.2.1 (cylPoint p.1 (θ + 2 * π) p.2)) a b d =
      frameThird θ (x.2.2.1 (cylPoint p.1 θ p.2)) a b d := fun a b d θ => by rw [cyl_per, frameThird_add]
  have rG : ∀ i, IsCircleSliceRegular c.order (fun θ => ∑ j : Fin 3, ∑ l : Fin 3,
      permSign i j l * frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) l j) := fun i =>
    regular_sum _ fun j _ => regular_sum _ fun l _ => regular_const _ (hG l j)
  have rH : ∀ i d, IsCircleSliceRegular c.order (fun θ => ∑ j : Fin 3, ∑ l : Fin 3,
      permSign i j l * frameThird θ (x.2.2.1 (cylPoint p.1 θ p.2)) l j d) := fun i d =>
    regular_sum _ fun j _ => regular_sum _ fun l _ => regular_const _ (hH l j d)
  have qG : ∀ i θ, (fun θ => ∑ j : Fin 3, ∑ l : Fin 3,
      permSign i j l * frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) l j) (θ + 2 * π) =
      (fun θ => ∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) l j) θ :=
    fun i θ => by simp only [pG]
  have qH : ∀ i d θ, (fun θ => ∑ j : Fin 3, ∑ l : Fin 3,
      permSign i j l * frameThird θ (x.2.2.1 (cylPoint p.1 θ p.2)) l j d) (θ + 2 * π) =
      (fun θ => ∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * frameThird θ (x.2.2.1 (cylPoint p.1 θ p.2)) l j d) θ :=
    fun i d θ => by simp only [pH]
  have cG : ∀ (n : ℤ) i, curlComp (fun a b => gradMode c.order n x.2.1 a b p) i =
      circleCoeff (azimuth c.order n) (fun θ => ((∑ j : Fin 3, ∑ l : Fin 3,
        permSign i j l * frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) l j : ℝ) : ℂ)) := by
    intro n i
    rw [circleCoeff_sum _ _ _ fun j _ => regular_integrable (regular_sum _ fun l _ => regular_const _ (hG l j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [circleCoeff_sum _ _ _ fun l _ => regular_integrable (regular_const _ (hG l j))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [circleCoeff_const]
    rfl
  have cH : ∀ (n : ℤ) i d, curlComp (fun a b => modeThird c.order n x.2.2.1 a b d p) i =
      circleCoeff (azimuth c.order n) (fun θ => ((∑ j : Fin 3, ∑ l : Fin 3,
        permSign i j l * frameThird θ (x.2.2.1 (cylPoint p.1 θ p.2)) l j d : ℝ) : ℂ)) := by
    intro n i d
    rw [circleCoeff_sum _ _ _ fun j _ => regular_integrable (regular_sum _ fun l _ => regular_const _ (hH l j d))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [circleCoeff_sum _ _ _ fun l _ => regular_integrable (regular_const _ (hH l j d))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [circleCoeff_const]
    rfl
  have M1 : ModeSum (fun n => secondModeSq c.order n x.2.2.1 p)
      (fun θ => CellCert.fullSecondSq (x.2.2.1 (cylPoint p.1 θ p.2))) :=
    modeSum_congr (modeSum_sum Finset.univ fun a _ => modeSum_sum Finset.univ fun b _ =>
      modeSum_sum Finset.univ fun d _ => modeSum_sq hm0 (hH a b d) (pH a b d)) (fun n => rfl)
      (fun θ => (frame_second θ _).symm)
  have M2 : ModeSum (fun n => curlGradModeSq c.order n x.2.2.1 p)
      (fun θ => CellCert.curlGradSq (x.2.2.1 (cylPoint p.1 θ p.2))) :=
    modeSum_congr (modeSum_sum Finset.univ fun i _ => modeSum_sum Finset.univ fun d _ =>
      modeSum_sq hm0 (rH i d) (qH i d)) (fun n => by simp only [curlGradModeSq, cH])
      (fun θ => (frame_curlGrad θ _).symm)
  have M3 : ModeSum (fun n => curlSq (fun a b => gradMode c.order n x.2.1 a b p))
      (fun θ => ‖curlOf (x.2.1 (cylPoint p.1 θ p.2))‖ ^ 2) :=
    modeSum_congr (modeSum_sum Finset.univ fun i _ => modeSum_sq hm0 (rG i) (qG i))
      (fun n => by simp only [curlSq, cG]) (fun θ => (frame_curl θ _).symm)
  have M4 : ModeSum (fun n => sumSq (fun a b => gradMode c.order n x.2.1 a b p))
      (fun θ => entrySq (x.2.1 (cylPoint p.1 θ p.2))) :=
    modeSum_congr (modeSum_sum Finset.univ fun a _ => modeSum_sum Finset.univ fun b _ =>
      modeSum_sq hm0 (hG a b) (pG a b)) (fun n => rfl) (fun θ => (entrySq_frame θ _).symm)
  have M := modeSum_add (modeSum_add (modeSum_const (c.innerWeight - c.coercivity) M1)
    (modeSum_const (c.splitVisc - c.innerWeight) M2))
    (modeSum_add (modeSum_const (1 - 3 / (4 * α) - c.curlWeight) M3)
      (modeSum_const (c.curlWeight - c.coercivity * CellScalars.sampleWeight c p) M4))
  have M' : ModeSum (fun n => modeLocalDensity c α x n p) (fun θ => quadraticDensity c α x (cylPoint p.1 θ p.2)) :=
    modeSum_congr M (fun n => rfl) (fun θ => by simp only [quadraticDensity, hwt θ])
  exact ⟨M'.1, M'.2⟩

theorem circle_conv {m : ℕ} (hm : 0 < m) {f w : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (hw : MemLp w 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hper : ∀ θ, f (θ + 2 * π) = f θ) (hturn : ∀ᵐ θ ∂volume, f (θ + 2 * π / m) = f θ) (n : ℤ) :
    HasSum (fun n' : ℤ => circleCoeff (azimuth m n') f * circleCoeff (azimuth m (n - n')) w)
      (circleCoeff (azimuth m n) (fun θ => w θ * f θ)) := by
  set h : ℝ → ℂ := fun θ => conj (w θ) * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I) with hh
  have hmeas : AEStronglyMeasurable h (volume.restrict (Set.Ioc 0 (2 * π))) :=
    (Complex.continuous_conj.comp_aestronglyMeasurable hw.1).mul (by fun_prop : Continuous fun θ : ℝ =>
      Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).aestronglyMeasurable
  have hL : MemLp h 2 (volume.restrict (Set.Ioc 0 (2 * π))) := by
    refine hw.of_le hmeas (Filter.Eventually.of_forall fun θ => ?_)
    simp only [hh, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_conj, le_refl]
  have H := circle_modes hm hf hL hper hturn
  have e1 : ∀ n' : ℤ, conj (circleCoeff (azimuth m n') h) = circleCoeff (azimuth m (n - n')) w := by
    intro n'
    have hp : (0 : ℝ) ≤ 2 * π := circle_len_pos.le
    unfold circleCoeff
    rw [map_mul, intervalIntegral.integral_of_le hp, intervalIntegral.integral_of_le hp, ← integral_conj]
    congr 1
    · rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [hh, map_mul, Complex.conj_conj, ← Complex.exp_conj, map_neg, Complex.conj_ofReal, Complex.conj_I]
      rw [mul_comm (w θ), ← mul_assoc, ← Complex.exp_add]
      congr 2
      unfold azimuth
      push_cast
      ring
  have e2 : ((2 * π)⁻¹ • ∫ θ in (0 : ℝ)..(2 * π), f θ * conj (h θ)) =
      circleCoeff (azimuth m n) (fun θ => w θ * f θ) := by
    unfold circleCoeff
    rw [Complex.real_smul]
    congr 1
    · push_cast; ring
    · refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [hh, map_mul, Complex.conj_conj, ← Complex.exp_conj, Complex.conj_ofReal]
      rw [Complex.conj_I, show ((azimuth m n * θ : ℝ) : ℂ) * -Complex.I = -((azimuth m n * θ : ℝ) : ℂ) * Complex.I by ring]
      ring
  rw [← e2]
  convert H using 1
  funext n'
  rw [e1]

theorem clm_coord (M : Space →L[ℝ] Space) (u : Space) (i : Fin 3) :
    M u i = ∑ j : Fin 3, entry M i j * u j := by
  conv_lhs => rw [coord_sum u]
  simp only [Fin.sum_univ_three, map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, entry]
  ring

theorem frame_jForm (θ : ℝ) (S Gm Dv : Space →L[ℝ] Space) (v : Space) :
    jForm S Gm Dv v =
      -(∑ a : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, permSign a j l * frameMat θ Dv l j) *
          ∑ b : Fin 3, frameMat θ S a b * (∑ j : Fin 3, ∑ l : Fin 3, permSign b j l * frameMat θ Dv l j))
        + ∑ i : Fin 3, ∑ l : Fin 3,
          (-(∑ j : Fin 3, permSign i l j * ∑ b : Fin 3, frameMat θ Gm j b * frameVec θ v b)
            + (1 / 2 : ℝ) * ∑ q : Fin 3, (∑ j : Fin 3, permSign i q j * frameVec θ v j) * frameMat θ Gm l q)
            * frameMat θ Dv i l := by
  simp only [jForm, curlOf_apply, clm_coord, frameMat, frameVec,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, radialUnit, angularUnit, axialUnit, PiLp.add_apply, PiLp.single_apply]
  simp [permSign]
  linear_combination (-(entry Dv 0 0)*(entry Gm 0 1)*(v 2)/2 + (entry Dv 0 0)*(entry Gm 0 2)*(v 1)/2 + (entry Dv 0 1)^2*(entry S 2 2) - (entry Dv 0 1)*(entry Dv 0 2)*(entry S 1 2) - (entry Dv 0 1)*(entry Dv 0 2)*(entry S 2 1) - 2*(entry Dv 0 1)*(entry Dv 1 0)*(entry S 2 2) + (entry Dv 0 1)*(entry Dv 1 2)*(entry S 0 2) + (entry Dv 0 1)*(entry Dv 1 2)*(entry S 2 0) + (entry Dv 0 1)*(entry Dv 2 0)*(entry S 1 2) + (entry Dv 0 1)*(entry Dv 2 0)*(entry S 2 1) - (entry Dv 0 1)*(entry Dv 2 1)*(entry S 0 2) - (entry Dv 0 1)*(entry Dv 2 1)*(entry S 2 0) - (entry Dv 0 1)*(entry Gm 1 1)*(v 2)/2 + (entry Dv 0 1)*(entry Gm 1 2)*(v 1)/2 + (entry Dv 0 1)*(entry Gm 2 0)*(v 0) + (entry Dv 0 1)*(entry Gm 2 1)*(v 1) + (entry Dv 0 1)*(entry Gm 2 2)*(v 2) + (entry Dv 0 2)^2*(entry S 1 1) + (entry Dv 0 2)*(entry Dv 1 0)*(entry S 1 2) + (entry Dv 0 2)*(entry Dv 1 0)*(entry S 2 1) - (entry Dv 0 2)*(entry Dv 1 2)*(entry S 0 1) - (entry Dv 0 2)*(entry Dv 1 2)*(entry S 1 0) - 2*(entry Dv 0 2)*(entry Dv 2 0)*(entry S 1 1) + (entry Dv 0 2)*(entry Dv 2 1)*(entry S 0 1) + (entry Dv 0 2)*(entry Dv 2 1)*(entry S 1 0) - (entry Dv 0 2)*(entry Gm 1 0)*(v 0) - (entry Dv 0 2)*(entry Gm 1 1)*(v 1) - (entry Dv 0 2)*(entry Gm 1 2)*(v 2) - (entry Dv 0 2)*(entry Gm 2 1)*(v 2)/2 + (entry Dv 0 2)*(entry Gm 2 2)*(v 1)/2 + (entry Dv 1 0)^2*(entry S 2 2) - (entry Dv 1 0)*(entry Dv 1 2)*(entry S 0 2) - (entry Dv 1 0)*(entry Dv 1 2)*(entry S 2 0) - (entry Dv 1 0)*(entry Dv 2 0)*(entry S 1 2) - (entry Dv 1 0)*(entry Dv 2 0)*(entry S 2 1) + (entry Dv 1 0)*(entry Dv 2 1)*(entry S 0 2) + (entry Dv 1 0)*(entry Dv 2 1)*(entry S 2 0) + (entry Dv 1 0)*(entry Gm 0 0)*(v 2)/2 - (entry Dv 1 0)*(entry Gm 0 2)*(v 0)/2 - (entry Dv 1 0)*(entry Gm 2 0)*(v 0) - (entry Dv 1 0)*(entry Gm 2 1)*(v 1) - (entry Dv 1 0)*(entry Gm 2 2)*(v 2) + (entry Dv 1 1)*(entry Gm 1 0)*(v 2)/2 - (entry Dv 1 1)*(entry Gm 1 2)*(v 0)/2 + (entry Dv 1 2)^2*(entry S 0 0) + (entry Dv 1 2)*(entry Dv 2 0)*(entry S 0 1) + (entry Dv 1 2)*(entry Dv 2 0)*(entry S 1 0) - 2*(entry Dv 1 2)*(entry Dv 2 1)*(entry S 0 0) + (entry Dv 1 2)*(entry Gm 0 0)*(v 0) + (entry Dv 1 2)*(entry Gm 0 1)*(v 1) + (entry Dv 1 2)*(entry Gm 0 2)*(v 2) + (entry Dv 1 2)*(entry Gm 2 0)*(v 2)/2 - (entry Dv 1 2)*(entry Gm 2 2)*(v 0)/2 + (entry Dv 2 0)^2*(entry S 1 1) - (entry Dv 2 0)*(entry Dv 2 1)*(entry S 0 1) - (entry Dv 2 0)*(entry Dv 2 1)*(entry S 1 0) - (entry Dv 2 0)*(entry Gm 0 0)*(v 1)/2 + (entry Dv 2 0)*(entry Gm 0 1)*(v 0)/2 + (entry Dv 2 0)*(entry Gm 1 0)*(v 0) + (entry Dv 2 0)*(entry Gm 1 1)*(v 1) + (entry Dv 2 0)*(entry Gm 1 2)*(v 2) + (entry Dv 2 1)^2*(entry S 0 0) - (entry Dv 2 1)*(entry Gm 0 0)*(v 0) - (entry Dv 2 1)*(entry Gm 0 1)*(v 1) - (entry Dv 2 1)*(entry Gm 0 2)*(v 2) - (entry Dv 2 1)*(entry Gm 1 0)*(v 1)/2 + (entry Dv 2 1)*(entry Gm 1 1)*(v 0)/2 - (entry Dv 2 2)*(entry Gm 2 0)*(v 1)/2 + (entry Dv 2 2)*(entry Gm 2 1)*(v 0)/2 + Real.cos θ^2*(-(entry Dv 0 0)*(entry Gm 0 1)*(v 2)/2 + (entry Dv 0 0)*(entry Gm 0 2)*(v 1)/2 + (entry Dv 0 1)^2*(entry S 2 2) - (entry Dv 0 1)*(entry Dv 0 2)*(entry S 1 2) - (entry Dv 0 1)*(entry Dv 0 2)*(entry S 2 1) - 2*(entry Dv 0 1)*(entry Dv 1 0)*(entry S 2 2) + (entry Dv 0 1)*(entry Dv 1 2)*(entry S 0 2) + (entry Dv 0 1)*(entry Dv 1 2)*(entry S 2 0) + (entry Dv 0 1)*(entry Dv 2 0)*(entry S 1 2) + (entry Dv 0 1)*(entry Dv 2 0)*(entry S 2 1) - (entry Dv 0 1)*(entry Dv 2 1)*(entry S 0 2) - (entry Dv 0 1)*(entry Dv 2 1)*(entry S 2 0) - (entry Dv 0 1)*(entry Gm 1 1)*(v 2)/2 + (entry Dv 0 1)*(entry Gm 1 2)*(v 1)/2 + (entry Dv 0 1)*(entry Gm 2 0)*(v 0) + (entry Dv 0 1)*(entry Gm 2 1)*(v 1) + (entry Dv 0 2)^2*(entry S 1 1) + (entry Dv 0 2)*(entry Dv 1 0)*(entry S 1 2) + (entry Dv 0 2)*(entry Dv 1 0)*(entry S 2 1) - (entry Dv 0 2)*(entry Dv 1 2)*(entry S 0 1) - (entry Dv 0 2)*(entry Dv 1 2)*(entry S 1 0) - 2*(entry Dv 0 2)*(entry Dv 2 0)*(entry S 1 1) + (entry Dv 0 2)*(entry Dv 2 1)*(entry S 0 1) + (entry Dv 0 2)*(entry Dv 2 1)*(entry S 1 0) - (entry Dv 0 2)*(entry Gm 1 0)*(v 0) - (entry Dv 0 2)*(entry Gm 1 1)*(v 1) + (entry Dv 1 0)^2*(entry S 2 2) - (entry Dv 1 0)*(entry Dv 1 2)*(entry S 0 2) - (entry Dv 1 0)*(entry Dv 1 2)*(entry S 2 0) - (entry Dv 1 0)*(entry Dv 2 0)*(entry S 1 2) - (entry Dv 1 0)*(entry Dv 2 0)*(entry S 2 1) + (entry Dv 1 0)*(entry Dv 2 1)*(entry S 0 2) + (entry Dv 1 0)*(entry Dv 2 1)*(entry S 2 0) + (entry Dv 1 0)*(entry Gm 0 0)*(v 2)/2 - (entry Dv 1 0)*(entry Gm 0 2)*(v 0)/2 - (entry Dv 1 0)*(entry Gm 2 0)*(v 0) - (entry Dv 1 0)*(entry Gm 2 1)*(v 1) + (entry Dv 1 1)*(entry Gm 1 0)*(v 2)/2 - (entry Dv 1 1)*(entry Gm 1 2)*(v 0)/2 + (entry Dv 1 2)^2*(entry S 0 0) + (entry Dv 1 2)*(entry Dv 2 0)*(entry S 0 1) + (entry Dv 1 2)*(entry Dv 2 0)*(entry S 1 0) - 2*(entry Dv 1 2)*(entry Dv 2 1)*(entry S 0 0) + (entry Dv 1 2)*(entry Gm 0 0)*(v 0) + (entry Dv 1 2)*(entry Gm 0 1)*(v 1) + (entry Dv 2 0)^2*(entry S 1 1) - (entry Dv 2 0)*(entry Dv 2 1)*(entry S 0 1) - (entry Dv 2 0)*(entry Dv 2 1)*(entry S 1 0) - (entry Dv 2 0)*(entry Gm 0 0)*(v 1)/2 + (entry Dv 2 0)*(entry Gm 0 1)*(v 0)/2 + (entry Dv 2 0)*(entry Gm 1 0)*(v 0) + (entry Dv 2 0)*(entry Gm 1 1)*(v 1) + (entry Dv 2 1)^2*(entry S 0 0) - (entry Dv 2 1)*(entry Gm 0 0)*(v 0) - (entry Dv 2 1)*(entry Gm 0 1)*(v 1) - (entry Dv 2 1)*(entry Gm 1 0)*(v 1)/2 + (entry Dv 2 1)*(entry Gm 1 1)*(v 0)/2) + Real.sin θ^2*(-(entry Dv 0 0)*(entry Gm 0 1)*(v 2)/2 + (entry Dv 0 0)*(entry Gm 0 2)*(v 1)/2 + (entry Dv 0 1)^2*(entry S 2 2) - (entry Dv 0 1)*(entry Dv 0 2)*(entry S 1 2) - (entry Dv 0 1)*(entry Dv 0 2)*(entry S 2 1) - 2*(entry Dv 0 1)*(entry Dv 1 0)*(entry S 2 2) + (entry Dv 0 1)*(entry Dv 1 2)*(entry S 0 2) + (entry Dv 0 1)*(entry Dv 1 2)*(entry S 2 0) + (entry Dv 0 1)*(entry Dv 2 0)*(entry S 1 2) + (entry Dv 0 1)*(entry Dv 2 0)*(entry S 2 1) - (entry Dv 0 1)*(entry Dv 2 1)*(entry S 0 2) - (entry Dv 0 1)*(entry Dv 2 1)*(entry S 2 0) - (entry Dv 0 1)*(entry Gm 1 1)*(v 2)/2 + (entry Dv 0 1)*(entry Gm 1 2)*(v 1)/2 + (entry Dv 0 1)*(entry Gm 2 0)*(v 0) + (entry Dv 0 1)*(entry Gm 2 1)*(v 1) + (entry Dv 0 2)^2*(entry S 1 1) + (entry Dv 0 2)*(entry Dv 1 0)*(entry S 1 2) + (entry Dv 0 2)*(entry Dv 1 0)*(entry S 2 1) - (entry Dv 0 2)*(entry Dv 1 2)*(entry S 0 1) - (entry Dv 0 2)*(entry Dv 1 2)*(entry S 1 0) - 2*(entry Dv 0 2)*(entry Dv 2 0)*(entry S 1 1) + (entry Dv 0 2)*(entry Dv 2 1)*(entry S 0 1) + (entry Dv 0 2)*(entry Dv 2 1)*(entry S 1 0) - (entry Dv 0 2)*(entry Gm 1 0)*(v 0) - (entry Dv 0 2)*(entry Gm 1 1)*(v 1) + (entry Dv 1 0)^2*(entry S 2 2) - (entry Dv 1 0)*(entry Dv 1 2)*(entry S 0 2) - (entry Dv 1 0)*(entry Dv 1 2)*(entry S 2 0) - (entry Dv 1 0)*(entry Dv 2 0)*(entry S 1 2) - (entry Dv 1 0)*(entry Dv 2 0)*(entry S 2 1) + (entry Dv 1 0)*(entry Dv 2 1)*(entry S 0 2) + (entry Dv 1 0)*(entry Dv 2 1)*(entry S 2 0) + (entry Dv 1 0)*(entry Gm 0 0)*(v 2)/2 - (entry Dv 1 0)*(entry Gm 0 2)*(v 0)/2 - (entry Dv 1 0)*(entry Gm 2 0)*(v 0) - (entry Dv 1 0)*(entry Gm 2 1)*(v 1) + (entry Dv 1 1)*(entry Gm 1 0)*(v 2)/2 - (entry Dv 1 1)*(entry Gm 1 2)*(v 0)/2 + (entry Dv 1 2)^2*(entry S 0 0) + (entry Dv 1 2)*(entry Dv 2 0)*(entry S 0 1) + (entry Dv 1 2)*(entry Dv 2 0)*(entry S 1 0) - 2*(entry Dv 1 2)*(entry Dv 2 1)*(entry S 0 0) + (entry Dv 1 2)*(entry Gm 0 0)*(v 0) + (entry Dv 1 2)*(entry Gm 0 1)*(v 1) + (entry Dv 2 0)^2*(entry S 1 1) - (entry Dv 2 0)*(entry Dv 2 1)*(entry S 0 1) - (entry Dv 2 0)*(entry Dv 2 1)*(entry S 1 0) - (entry Dv 2 0)*(entry Gm 0 0)*(v 1)/2 + (entry Dv 2 0)*(entry Gm 0 1)*(v 0)/2 + (entry Dv 2 0)*(entry Gm 1 0)*(v 0) + (entry Dv 2 0)*(entry Gm 1 1)*(v 1) + (entry Dv 2 1)^2*(entry S 0 0) - (entry Dv 2 1)*(entry Gm 0 0)*(v 0) - (entry Dv 2 1)*(entry Gm 0 1)*(v 1) - (entry Dv 2 1)*(entry Gm 1 0)*(v 1)/2 + (entry Dv 2 1)*(entry Gm 1 1)*(v 0)/2)) * Real.sin_sq_add_cos_sq θ

theorem turn_cyl (m : ℕ) (r θ z : ℝ) : turnStep m (cylPoint r θ z) = cylPoint r (θ + 2 * π / m) z := by
  ext i
  fin_cases i <;> simp [turnStep, cylPoint, Real.cos_add, Real.sin_add] <;> ring

theorem turn_frame (m : ℕ) (θ : ℝ) (a : Fin 3) : turnStep m (frameUnit θ a) = frameUnit (θ + 2 * π / m) a := by
  ext i
  fin_cases a <;> fin_cases i <;>
    simp [turnStep, frameUnit, radialUnit, angularUnit, axialUnit, Real.cos_add, Real.sin_add] <;> ring

theorem turn_inner (m : ℕ) (u w : Space) : inner ℝ (turnStep m u) (turnStep m w) = inner ℝ u w := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three, turnStep, PiLp.add_apply,
    PiLp.single_apply]
  simp
  linear_combination (u 0 * w 0 + u 1 * w 1) * Real.sin_sq_add_cos_sq (2 * π / m)

theorem frameMat_turn (m : ℕ) (θ : ℝ) {M M' : Space →L[ℝ] Space} (h : ∀ u, M' (turnStep m u) = turnStep m (M u))
    (a b : Fin 3) : frameMat (θ + 2 * π / m) M' a b = frameMat θ M a b := by
  have e : ∀ d, (![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) d = frameUnit θ d := fun _ => rfl
  have e' : ∀ d, (![radialUnit (θ + 2 * π / m), angularUnit (θ + 2 * π / m), axialUnit] : Fin 3 → Space) d =
      frameUnit (θ + 2 * π / m) d := fun _ => rfl
  simp only [frameMat, e, e', ← turn_frame, h, turn_inner]

theorem frameVec_unit (θ : ℝ) (u : Space) (a : Fin 3) : frameVec θ u a = inner ℝ u (frameUnit θ a) := by
  fin_cases a <;> rfl

theorem frameVec_turn (m : ℕ) (θ : ℝ) {u u' : Space} (h : u' = turnStep m u) (a : Fin 3) :
    frameVec (θ + 2 * π / m) u' a = frameVec θ u a := by
  rw [frameVec_unit, frameVec_unit, h, ← turn_frame, turn_inner]

theorem frameThird_turn (m : ℕ) (θ : ℝ) {L L' : Space →L[ℝ] Space →L[ℝ] Space}
    (h : ∀ u w, L' (turnStep m u) (turnStep m w) = turnStep m (L u w)) (a b d : Fin 3) :
    frameThird (θ + 2 * π / m) L' a b d = frameThird θ L a b d := by
  simp only [frameThird, ← turn_frame, h, turn_inner]

theorem ae_fst_ne : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have h : volume ({(0 : ℝ)} ×ˢ (Set.univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with p hp
  intro h0
  exact hp ⟨h0, Set.mem_univ _⟩

theorem slice_ae {P : Space → Prop} (hP : ∀ᵐ y ∂volume, P y) {K : CellBox} (hK : IsCellBox K) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∀ᵐ θ ∂(volume.restrict (Set.Ioo (-π) π)), P (cylPoint p.1 θ p.2) := by
  have h1 : ∀ᵐ q ∂CellAnalysis.LowEntry.Internal.muU, P (CellAnalysis.LowEntry.Internal.cylArg q) :=
    CellAnalysis.LowEntry.Internal.qmp.ae hP
  rw [CellAnalysis.LowEntry.Internal.muU_def] at h1
  have h2 := Measure.ae_ae_of_ae_prod h1
  rw [ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)] at h2
  rw [ae_restrict_iff' (show MeasurableSet K.rect from measurableSet_Icc.prod measurableSet_Icc)]
  filter_upwards [h2, ae_fst_ne] with p hp hne hmem
  exact hp ⟨lt_of_le_of_ne (hK.r_order.1.trans hmem.1.1) (Ne.symm hne), Set.mem_univ _⟩

theorem pin_slice {k N : ℕ} (c : FracCellData k N) (hm : 3 ≤ c.order) (x : FieldTuple k) (p : ℝ × ℝ)
    (hd : IsCircleSliceData c x p) (i : Fin k) :
    (∫ θ in (0 : ℝ)..(2 * π), entryInner (x.2.1 (cylPoint p.1 θ p.2)) (c.modelPinField i (cylPoint p.1 θ p.2)))
      = 2 * π * modeFieldPair c x.2.1 (c.modelPinField i) p := by
  have H := slice_pair (by omega) x.2.1 (c.modelPinField i) p.1 p.2 hd.2.1 (fun a b => (hd.2.2.2.2.2.1 i a b).2)
  unfold modeFieldPair gradMode
  rw [H.tsum_eq, Complex.ofReal_re]
  field_simp

theorem actuator_slice {k N : ℕ} (c : FracCellData k N) (hm : 3 ≤ c.order) (x : FieldTuple k) (p : ℝ × ℝ)
    (hd : IsCircleSliceData c x p) (i : Fin k) :
    IntervalIntegrable (fun θ => entryInner (x.2.1 (cylPoint p.1 θ p.2)) (c.modelActuatorGrad i (cylPoint p.1 θ p.2)))
      volume 0 (2 * π) ∧
    (∫ θ in (0 : ℝ)..(2 * π), entryInner (x.2.1 (cylPoint p.1 θ p.2)) (c.modelActuatorGrad i (cylPoint p.1 θ p.2)))
      = 2 * π * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p := by
  refine ⟨?_, ?_⟩
  · have h := IntervalIntegrable.sum (Finset.univ) fun a _ => IntervalIntegrable.sum (Finset.univ) fun b _ =>
      product_integrable ((hd.2.1 a b).1) ((hd.2.2.2.2.2.1 i a b).1)
    refine h.congr fun θ _ => ?_
    simp only [Finset.sum_apply]
    exact (frame_entryInner θ _ _).symm
  · have H := slice_pair (by omega) x.2.1 (c.modelActuatorGrad i) p.1 p.2 hd.2.1
      (fun a b => (hd.2.2.2.2.2.1 i a b).1)
    unfold modeFieldPair gradMode
    rw [H.tsum_eq, Complex.ofReal_re]
    field_simp

end Breakdown.FracInternal.DensitySlice

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly FracInternal.DensitySlice

theorem densitySlice_of (hR : CircleSliceRegularStatement) (hJ : CircleSliceCouplingStatement) :
    DensitySliceStatement := by
  have hQ : CircleSliceQuadraticStatement := quadratic_slice
  intro α hα₁ hα₂ k N c hc K hK hw hmm hsub x hx
  have hreg := hR α hα₁ hα₂ c hc K hK hw hmm hsub x hx
  have hm : 3 ≤ c.order := hc.base.order_ge
  refine ⟨hreg.mono fun p hp => ?_, fun i => hreg.mono fun p hp => pin_slice c hm x p hp i⟩
  obtain ⟨hqi, hqs⟩ := hQ α c hm x p hp
  obtain ⟨hji, hje⟩ := hJ c hm x p hp
  have hai := fun i => (actuator_slice c hm x p hp i).1
  have hae := fun i => (actuator_slice c hm x p hp i).2
  have hsplit : ∀ θ, CellSplit.localDensity c α x (cylPoint p.1 θ p.2) =
      quadraticDensity c α x (cylPoint p.1 θ p.2)
        + jForm (c.modelStrain (cylPoint p.1 θ p.2)) (c.modelCurlGrad (cylPoint p.1 θ p.2))
          (x.2.1 (cylPoint p.1 θ p.2)) (x.1 (cylPoint p.1 θ p.2))
        + ∑ i, x.2.2.2.1 i * entryInner (x.2.1 (cylPoint p.1 θ p.2)) (c.modelActuatorGrad i (cylPoint p.1 θ p.2)) :=
    fun θ => rfl
  have hsi : IntervalIntegrable (fun θ => ∑ i, x.2.2.2.1 i *
      entryInner (x.2.1 (cylPoint p.1 θ p.2)) (c.modelActuatorGrad i (cylPoint p.1 θ p.2))) volume 0 (2 * π) := by
    have h := IntervalIntegrable.sum (Finset.univ) fun i _ => (hai i).const_mul (x.2.2.2.1 i)
    refine h.congr fun θ _ => ?_
    simp only [Finset.sum_apply]
  simp only [hsplit]
  rw [intervalIntegral.integral_add (hqi.add hji) hsi, intervalIntegral.integral_add hqi hji,
    intervalIntegral.integral_finsetSum fun i _ => (hai i).const_mul (x.2.2.2.1 i), hje, hqs.tsum_eq]
  simp only [intervalIntegral.integral_const_mul, hae]
  have hpi : (2 * π) ≠ 0 := circle_len_pos.ne'
  rw [mul_add, mul_add, ← mul_assoc (2 * π) (2 * π)⁻¹, mul_inv_cancel₀ hpi, one_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

end Breakdown.CellCert.CellAnalysis
