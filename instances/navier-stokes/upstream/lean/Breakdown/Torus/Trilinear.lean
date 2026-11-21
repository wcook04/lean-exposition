import Breakdown.Torus.StatementsCoeff
import Breakdown.Torus.StatementsAnalysis

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.Periodic

namespace Trilinear.Internal

theorem inner_freq (k : Lattice) (x : Space) : inner ℝ (freq k) x = ∑ i, (k i : ℝ) * x i := by
  simp [freq, unitVector, sum_inner, inner_smul_left, EuclideanSpace.inner_single_left]

theorem character_eq_prod (n : Lattice) (x : Space) :
    character n x = ∏ i, Complex.exp (-(2 * π * Complex.I * (((n i : ℝ) * x i : ℝ) : ℂ))) := by
  rw [character, inner_freq, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
    Complex.exp_sum]

theorem character_add (a b : Lattice) (x : Space) :
    character (a + b) x = character a x * character b x := by
  rw [character, character, character, ← Complex.exp_add, inner_freq, inner_freq, inner_freq]
  congr 1
  simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib, Complex.ofReal_add]
  ring

theorem conj_character (a : Lattice) (x : Space) :
    starRingEnd ℂ (character a x) = character (-a) x := by
  rw [character, character, ← Complex.exp_conj, inner_freq, inner_freq]
  congr 1
  simp [Finset.sum_neg_distrib, map_ofNat]

theorem continuous_character (n : Lattice) : Continuous (character n) := by
  unfold character
  fun_prop

theorem cell_eq : cell = WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin 3 => Icc (0 : ℝ) 1) := by
  ext x
  simp only [cell, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi]

theorem isCompact_cell : IsCompact cell := by
  have h : cell = WithLp.toLp 2 '' (univ.pi fun _ : Fin 3 => Icc (0 : ℝ) 1) := by
    rw [cell_eq]
    ext x
    constructor
    · intro hx
      exact ⟨WithLp.ofLp x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [h]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp _ _)

theorem integrableOn_cell {E : Type*} [NormedAddCommGroup E] {f : Space → E} (hf : Continuous f) :
    IntegrableOn f cell :=
  hf.continuousOn.integrableOn_compact isCompact_cell

theorem integral_Icc_char (m : ℤ) :
    ∫ t in Icc (0 : ℝ) 1, Complex.exp (-(2 * π * Complex.I * (((m : ℝ) * t : ℝ) : ℂ))) =
      if m = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hm
  · subst hm
    simp
  · have hc : (-(2 * π * Complex.I * (m : ℂ)) : ℂ) ≠ 0 := by
      simp [hm, Real.pi_ne_zero, Complex.I_ne_zero]
    have e : ∀ t : ℝ, Complex.exp (-(2 * π * Complex.I * (((m : ℝ) * t : ℝ) : ℂ))) =
        Complex.exp ((-(2 * π * Complex.I * (m : ℂ))) * t) := by
      intro t
      push_cast
      ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((-(2 * π * Complex.I * (m : ℂ))) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one,
        show -(2 * ↑π * Complex.I * (m : ℂ)) = ((-m : ℤ) : ℂ) * (2 * π * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-m)
    rw [h1]
    simp

theorem integral_character (n : Lattice) :
    ∫ x in cell, character n x = if n = 0 then 1 else 0 := by
  have hm : MeasurableEmbedding (WithLp.ofLp : Space → (Fin 3 → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
  have key := (PiLp.volume_preserving_ofLp (Fin 3)).setIntegral_preimage_emb hm
    (fun y : Fin 3 → ℝ => ∏ i, Complex.exp (-(2 * π * Complex.I * (((n i : ℝ) * y i : ℝ) : ℂ))))
    (univ.pi fun _ : Fin 3 => Icc (0 : ℝ) 1)
  simp_rw [character_eq_prod, cell_eq]
  rw [key, volume_pi, Measure.restrict_pi_pi]
  have hp := integral_fintype_prod_eq_prod (𝕜 := ℂ) (E := fun _ : Fin 3 => ℝ)
    (fun i t => Complex.exp (-(2 * π * Complex.I * (((n i : ℝ) * t : ℝ) : ℂ))))
    (μ := fun _ => volume.restrict (Icc (0 : ℝ) 1))
  rw [hp]
  simp_rw [integral_Icc_char]
  rw [Fintype.prod_boole]
  congr 1
  simp [funext_iff]


theorem inner_smul_character (a b : Lattice) (x : Space) (c d : Coef) :
    inner ℂ (character (-a) x • c) (character (-b) x • d) = character (a - b) x * inner ℂ c d := by
  rw [inner_smul_left, inner_smul_right, conj_character, neg_neg, ← mul_assoc, ← character_add,
    sub_eq_add_neg]

theorem integral_inner_sums {ι : Type*} (s : Finset Lattice) (t : Finset ι) (a : Lattice → Coef)
    (σ : ι → Lattice) (b : ι → Coef) :
    ∫ x in cell, inner ℂ (∑ k ∈ s, character (-k) x • a k) (∑ p ∈ t, character (-σ p) x • b p) =
      ∑ k ∈ s, ∑ p ∈ t, if k = σ p then inner ℂ (a k) (b p) else 0 := by
  simp_rw [sum_inner, inner_sum, inner_smul_character]
  have hi : ∀ k p, Integrable (fun x => character (k - σ p) x * inner ℂ (a k) (b p))
      (volume.restrict cell) := fun k p => integrableOn_cell ((continuous_character _).mul continuous_const)
  rw [integral_finsetSum s (fun k _ => integrable_finsetSum t (fun p _ => hi k p))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_finsetSum t (fun p _ => hi k p)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [integral_mul_const, integral_character]
  by_cases h : k = σ p
  · simp [h]
  · simp [h, sub_eq_zero]

theorem integral_norm_sq_sum (s : Finset Lattice) (a : Lattice → Coef) :
    ∫ x in cell, ‖∑ k ∈ s, character (-k) x • a k‖ ^ 2 = ∑ k ∈ s, ‖a k‖ ^ 2 := by
  have h := integral_inner_sums s s a id a
  have h2 : (∑ k ∈ s, ∑ p ∈ s, if k = id p then inner ℂ (a k) (a p) else 0) =
      ∑ k ∈ s, ((‖a k‖ ^ 2 : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [id]
    rw [Finset.sum_ite_eq, if_pos hk, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [h2] at h
  simp only [id, inner_self_eq_norm_sq_to_K] at h
  have h3 : ((∫ x in cell, ‖∑ k ∈ s, character (-k) x • a k‖ ^ 2 : ℝ) : ℂ) =
      ((∑ k ∈ s, ‖a k‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    push_cast at h ⊢
    exact h
  exact_mod_cast h3

theorem freq_apply (k : Lattice) (i : Fin 3) : freq k i = k i := by
  simp [freq, unitVector, Pi.single_apply]

theorem norm_freq_sq (k : Lattice) : ‖freq k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_eq, sq_sqrt (by positivity)]
  simp [freq_apply]

theorem norm_freq_eq (k : Lattice) : ‖freq k‖ = √(∑ i, ((k i : ℝ)) ^ 2) := by
  rw [← norm_freq_sq, sqrt_sq (norm_nonneg _)]

theorem norm_divPairing_le (j : Lattice) (c : Coef) : ‖divPairing j c‖ ≤ ‖freq j‖ * ‖c‖ := by
  calc ‖divPairing j c‖ ≤ ∑ i, |(j i : ℝ)| * ‖c i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [norm_mul]
        simp
    _ ≤ √(∑ i, |(j i : ℝ)| ^ 2) * √(∑ i, ‖c i‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = ‖freq j‖ * ‖c‖ := by
        rw [norm_freq_eq, EuclideanSpace.norm_eq]
        simp [sq_abs]

theorem weight_pos (k : Lattice) : 0 < weight k := by
  unfold weight
  positivity

theorem one_le_weight (k : Lattice) : 1 ≤ weight k := by
  unfold weight
  have : 0 ≤ 4 * π ^ 2 * ‖freq k‖ ^ 2 := by positivity
  linarith

theorem freq_le_weight (k : Lattice) : 4 * π ^ 2 * ‖freq k‖ ^ 2 ≤ weight k := by
  unfold weight
  linarith

theorem weight_mul_norm_coeff_sq (u : V) (k : Lattice) :
    weight k * ‖coeff u k‖ ^ 2 = ‖(u : Seq) k‖ ^ 2 := by
  have hw := weight_pos k
  rw [coeff, norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _),
    inv_pow, sq_sqrt hw.le, ← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]

theorem hasSum_weight_coeff (u : V) :
    HasSum (fun k => weight k * ‖coeff u k‖ ^ 2) (‖u‖ ^ 2) := by
  have h1 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (u : Seq)
  have h2 := (lp.memℓp (u : Seq)).summable (p := 2) (by norm_num)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1 h2
  simp_rw [weight_mul_norm_coeff_sq]
  have h3 : ‖u‖ = ‖(u : Seq)‖ := rfl
  rw [h3, h1]
  exact h2.hasSum

def advTerm (cu cv : Lattice → Coef) (p : Lattice × Lattice) : Coef :=
  ((2 * π : ℝ) * Complex.I * divPairing p.2 (cu p.1)) • cv p.2

def derivCoef (cv : Lattice → Coef) (i : Fin 3) (j : Lattice) : Coef :=
  ((2 * π : ℝ) * Complex.I * (j i : ℂ)) • cv j

theorem norm_advTerm_le (cu cv : Lattice → Coef) (p : Lattice × Lattice) :
    ‖advTerm cu cv p‖ ≤ ‖cu p.1‖ * (2 * π * ‖freq p.2‖ * ‖cv p.2‖) := by
  rw [advTerm, norm_smul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]
  have := norm_divPairing_le p.2 (cu p.1)
  calc 2 * π * ‖divPairing p.2 (cu p.1)‖ * ‖cv p.2‖
      = 2 * π * (‖divPairing p.2 (cu p.1)‖ * ‖cv p.2‖) := by ring
    _ ≤ 2 * π * (‖freq p.2‖ * ‖cu p.1‖ * ‖cv p.2‖) := by gcongr
    _ = _ := by ring

theorem norm_derivCoef_sq (cv : Lattice → Coef) (j : Lattice) :
    ∑ i, ‖derivCoef cv i j‖ ^ 2 = 4 * π ^ 2 * ‖freq j‖ ^ 2 * ‖cv j‖ ^ 2 := by
  rw [norm_freq_sq, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [derivCoef, norm_smul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity), Complex.norm_intCast]
  simp only [mul_pow, sq_abs]
  ring

theorem sum_smul_deriv (s : Finset Lattice) (cu cv : Lattice → Coef) (x : Space) :
    ∑ i, (∑ m ∈ s, character (-m) x • cu m) i • ∑ j ∈ s, character (-j) x • derivCoef cv i j =
      ∑ p ∈ s ×ˢ s, character (-(p.1 + p.2)) x • advTerm cu cv p := by
  rw [Finset.sum_product]
  simp only [advTerm, derivCoef, divPairing, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_smul, Finset.smul_sum, smul_smul, Finset.mul_sum,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [neg_add, character_add]
  congr 1
  ring

def trig (s : Finset Lattice) (c : Lattice → Coef) (x : Space) : Coef :=
  ∑ k ∈ s, character (-k) x • c k

theorem continuous_trig (s : Finset Lattice) (c : Lattice → Coef) : Continuous (trig s c) :=
  continuous_finsetSum _ (fun _ _ => (continuous_character _).smul continuous_const)

theorem norm_sum_smul_le (U : Coef) (D : Fin 3 → Coef) :
    ‖∑ i, U i • D i‖ ≤ ‖U‖ * √(∑ i, ‖D i‖ ^ 2) := by
  calc ‖∑ i, U i • D i‖ ≤ ∑ i, ‖U i‖ * ‖D i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp [norm_smul]
    _ ≤ √(∑ i, ‖U i‖ ^ 2) * √(∑ i, ‖D i‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by rw [EuclideanSpace.norm_eq]

theorem lpProd_four (P Q G : Space → ℝ) (hP : Continuous P) (hQ : Continuous Q)
    (hG : Continuous G) (hP0 : ∀ x, 0 ≤ P x) (hQ0 : ∀ x, 0 ≤ Q x) (hG0 : ∀ x, 0 ≤ G x) :
    ∫ x in cell, P x * (Q x * G x) ≤
      (∫ x in cell, P x ^ 2) ^ (1 / 4 : ℝ) * (∫ x in cell, P x ^ (6 : ℝ)) ^ (1 / 12 : ℝ) *
        (∫ x in cell, Q x ^ (6 : ℝ)) ^ (1 / 6 : ℝ) * (∫ x in cell, G x ^ 2) ^ (1 / 2 : ℝ) := by
  have hint : ∀ f : Space → ℝ, Continuous f → (∀ x, 0 ≤ f x) →
      ∫⁻ x in cell, ENNReal.ofReal (f x) = ENNReal.ofReal (∫ x in cell, f x) :=
    fun f hf hf0 => (ofReal_integral_eq_lintegral_ofReal (integrableOn_cell hf)
      (Filter.Eventually.of_forall hf0)).symm
  have hmeas : ∀ f : Space → ℝ, Continuous f →
      AEMeasurable (fun x => ENNReal.ofReal (f x)) (volume.restrict cell) :=
    fun f hf => (ENNReal.continuous_ofReal.comp hf).measurable.aemeasurable
  have c0 : Continuous (fun x => P x ^ 2) := hP.pow 2
  have c1 : Continuous (fun x => P x ^ (6 : ℝ)) := hP.rpow_const (fun _ => Or.inr (by norm_num))
  have c2 : Continuous (fun x => Q x ^ (6 : ℝ)) := hQ.rpow_const (fun _ => Or.inr (by norm_num))
  have c3 : Continuous (fun x => G x ^ 2) := hG.pow 2
  have n0 : ∀ x, 0 ≤ P x ^ 2 := fun x => sq_nonneg _
  have n1 : ∀ x, 0 ≤ P x ^ (6 : ℝ) := fun x => Real.rpow_nonneg (hP0 x) _
  have n2 : ∀ x, 0 ≤ Q x ^ (6 : ℝ) := fun x => Real.rpow_nonneg (hQ0 x) _
  have n3 : ∀ x, 0 ≤ G x ^ 2 := fun x => sq_nonneg _
  have key : ∀ x, P x * (Q x * G x) = (P x ^ 2) ^ (1 / 4 : ℝ) * (P x ^ (6 : ℝ)) ^ (1 / 12 : ℝ) *
      (Q x ^ (6 : ℝ)) ^ (1 / 6 : ℝ) * (G x ^ 2) ^ (1 / 2 : ℝ) := by
    intro x
    have e1 : (P x ^ 2) ^ (1 / 4 : ℝ) * (P x ^ (6 : ℝ)) ^ (1 / 12 : ℝ) = P x := by
      rw [← Real.rpow_two, ← Real.rpow_mul (hP0 x), ← Real.rpow_mul (hP0 x),
        ← Real.rpow_add' (hP0 x) (by norm_num)]
      norm_num
    have e2 : (Q x ^ (6 : ℝ)) ^ (1 / 6 : ℝ) = Q x := by
      rw [← Real.rpow_mul (hQ0 x)]
      norm_num
    have e3 : (G x ^ 2) ^ (1 / 2 : ℝ) = G x := by
      rw [← Real.rpow_two, ← Real.rpow_mul (hG0 x)]
      norm_num
    rw [e1, e2, e3]
    ring
  have hpt : ∀ x, ENNReal.ofReal (P x * (Q x * G x)) =
      ENNReal.ofReal (P x ^ 2) ^ (1 / 4 : ℝ) * ENNReal.ofReal (P x ^ (6 : ℝ)) ^ (1 / 12 : ℝ) *
        ENNReal.ofReal (Q x ^ (6 : ℝ)) ^ (1 / 6 : ℝ) * ENNReal.ofReal (G x ^ 2) ^ (1 / 2 : ℝ) := by
    intro x
    have b1 := Real.rpow_nonneg (n0 x) (1 / 4 : ℝ)
    have b2 := Real.rpow_nonneg (n1 x) (1 / 12 : ℝ)
    have b3 := Real.rpow_nonneg (n2 x) (1 / 6 : ℝ)
    rw [ENNReal.ofReal_rpow_of_nonneg (n0 x) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (n1 x) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (n2 x) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (n3 x) (by norm_num), ← ENNReal.ofReal_mul b1,
      ← ENNReal.ofReal_mul (mul_nonneg b1 b2), ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg b1 b2) b3),
      key x]
  have H := ENNReal.lintegral_prod_norm_pow_le (μ := volume.restrict cell) Finset.univ
    (f := ![fun x => ENNReal.ofReal (P x ^ 2), fun x => ENNReal.ofReal (P x ^ (6 : ℝ)),
      fun x => ENNReal.ofReal (Q x ^ (6 : ℝ)), fun x => ENNReal.ofReal (G x ^ 2)])
    (p := ![1 / 4, 1 / 12, 1 / 6, 1 / 2])
    (by
      intro i _
      fin_cases i
      · exact hmeas _ c0
      · exact hmeas _ c1
      · exact hmeas _ c2
      · exact hmeas _ c3)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro i _; fin_cases i <;> norm_num)
  simp only [Fin.prod_univ_four, Matrix.cons_val] at H
  simp_rw [← hpt] at H
  rw [hint (fun x => P x * (Q x * G x)) (hP.mul (hQ.mul hG)) (fun x => mul_nonneg (hP0 x) (mul_nonneg (hQ0 x) (hG0 x))),
    hint _ c0 n0, hint _ c1 n1, hint _ c2 n2, hint _ c3 n3] at H
  have i0 := integral_nonneg (μ := volume.restrict cell) (f := fun x => P x ^ 2) n0
  have i1 := integral_nonneg (μ := volume.restrict cell) (f := fun x => P x ^ (6 : ℝ)) n1
  have i2 := integral_nonneg (μ := volume.restrict cell) (f := fun x => Q x ^ (6 : ℝ)) n2
  have i3 := integral_nonneg (μ := volume.restrict cell) (f := fun x => G x ^ 2) n3
  have d1 := Real.rpow_nonneg i0 (1 / 4 : ℝ)
  have d2 := Real.rpow_nonneg i1 (1 / 12 : ℝ)
  have d3 := Real.rpow_nonneg i2 (1 / 6 : ℝ)
  have d4 := Real.rpow_nonneg i3 (1 / 2 : ℝ)
  rw [ENNReal.ofReal_rpow_of_nonneg i0 (by norm_num), ENNReal.ofReal_rpow_of_nonneg i1 (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg i2 (by norm_num), ENNReal.ofReal_rpow_of_nonneg i3 (by norm_num),
    ← ENNReal.ofReal_mul d1, ← ENNReal.ofReal_mul (mul_nonneg d1 d2),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg d1 d2) d3)] at H
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp H

theorem integral_sq_deriv (s : Finset Lattice) (cv : Lattice → Coef) :
    ∫ x in cell, √(∑ i, ‖trig s (derivCoef cv i) x‖ ^ 2) ^ 2 =
      ∑ j ∈ s, 4 * π ^ 2 * ‖freq j‖ ^ 2 * ‖cv j‖ ^ 2 := by
  simp_rw [sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖trig s (derivCoef cv i) _‖))]
  have hi : ∀ i, Integrable (fun x => ‖trig s (derivCoef cv i) x‖ ^ 2) (volume.restrict cell) :=
    fun i => integrableOn_cell ((continuous_trig s _).norm.pow 2)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [trig, integral_norm_sq_sum]
  rw [Finset.sum_comm]
  simp_rw [norm_derivCoef_sq]

theorem finite_est {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (s : Finset Lattice) (c : Lattice → Coef),
      (∫ x in cell, ‖∑ k ∈ s, character (-k) x • c k‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) ≤
        C * (∑ k ∈ s, weight k * ‖c k‖ ^ 2) ^ (1 / 2 : ℝ))
    (s : Finset Lattice) (cu cv φ : Lattice → Coef) :
    ‖∑ p ∈ (s ×ˢ s).filter (fun p => p.1 + p.2 ∈ s), inner ℂ (φ (p.1 + p.2)) (advTerm cu cv p)‖ ≤
      (∑ k ∈ s, ‖φ k‖ ^ 2) ^ (1 / 4 : ℝ) *
        (C * (∑ k ∈ s, weight k * ‖φ k‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
        (C * (∑ k ∈ s, weight k * ‖cu k‖ ^ 2) ^ (1 / 2 : ℝ)) *
        (∑ k ∈ s, 4 * π ^ 2 * ‖freq k‖ ^ 2 * ‖cv k‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have eq1 : ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 + p.2 ∈ s),
      inner ℂ (φ (p.1 + p.2)) (advTerm cu cv p) =
      ∫ x in cell, inner ℂ (trig s φ x) (∑ i, (trig s cu x) i • trig s (derivCoef cv i) x) := by
    simp_rw [trig, sum_smul_deriv]
    rw [integral_inner_sums s (s ×ˢ s) φ (fun p => p.1 + p.2) (advTerm cu cv), Finset.sum_comm,
      Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_ite_eq']
  have hG : Continuous (fun x => √(∑ i, ‖trig s (derivCoef cv i) x‖ ^ 2)) :=
    (continuous_finsetSum _ (fun i _ => (continuous_trig s _).norm.pow 2)).sqrt
  have step2 : ‖∫ x in cell, inner ℂ (trig s φ x) (∑ i, (trig s cu x) i • trig s (derivCoef cv i) x)‖ ≤
      ∫ x in cell, ‖trig s φ x‖ * (‖trig s cu x‖ * √(∑ i, ‖trig s (derivCoef cv i) x‖ ^ 2)) := by
    refine (norm_integral_le_integral_norm _).trans (integral_mono ?_ ?_ ?_)
    · have hc : Continuous (fun x => inner ℂ (trig s φ x)
          (∑ i, (trig s cu x) i • trig s (derivCoef cv i) x)) :=
        (continuous_trig s φ).inner (continuous_finsetSum _ (fun i _ =>
          ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp (continuous_trig s cu)).smul
            (continuous_trig s _)))
      exact (integrableOn_cell hc).norm
    · exact integrableOn_cell ((continuous_trig s φ).norm.mul ((continuous_trig s cu).norm.mul hG))
    · intro x
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (norm_sum_smul_le _ _) (norm_nonneg _))
  have step3 := lpProd_four (fun x => ‖trig s φ x‖) (fun x => ‖trig s cu x‖)
    (fun x => √(∑ i, ‖trig s (derivCoef cv i) x‖ ^ 2)) (continuous_trig s φ).norm
    (continuous_trig s cu).norm hG (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (fun _ => sqrt_nonneg _)
  have hφ6 := hC s φ
  have hu6 := hC s cu
  have i1 : 0 ≤ ∫ x in cell, ‖trig s φ x‖ ^ (6 : ℝ) :=
    integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have h12 : (∫ x in cell, ‖trig s φ x‖ ^ (6 : ℝ)) ^ (1 / 12 : ℝ) =
      ((∫ x in cell, ‖trig s φ x‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul i1]
    norm_num
  simp only [trig] at h12 step3 hφ6 hu6 ⊢
  rw [eq1]
  refine step2.trans (step3.trans ?_)
  have h4 := integral_sq_deriv s cv
  simp only [trig] at h4
  rw [h12, integral_norm_sq_sum, h4]
  have w0 : 0 ≤ ∑ k ∈ s, weight k * ‖φ k‖ ^ 2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (weight_pos k).le (sq_nonneg _))
  have p0 : 0 ≤ (C * (∑ k ∈ s, weight k * ‖φ k‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg hC0 (Real.rpow_nonneg w0 _)) _
  have q0 : 0 ≤ (∫ x in cell, ‖∑ k ∈ s, character (-k) x • φ k‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) _
  have q1 : 0 ≤ (∫ x in cell, ‖∑ k ∈ s, character (-k) x • cu k‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) _
  gcongr

def shiftEquiv : Lattice × Lattice ≃ Lattice × Lattice where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 - p.2, p.2)
  left_inv p := by simp
  right_inv p := by simp

def diffEquiv : Lattice × Lattice ≃ Lattice × Lattice where
  toFun p := (p.1, p.1 - p.2)
  invFun p := (p.1, p.1 - p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem hasSum_pairs (u v : V) (φ : Lattice → Coef) (hφ : Summable (fun k => ‖φ k‖)) :
    HasSum (fun p : Lattice × Lattice => inner ℂ (φ (p.1 + p.2)) (advTerm (coeff u) (coeff v) p))
      (∑' k, inner ℂ (φ k) (advCoef u v k)) := by
  have ha : Summable (fun m => ‖coeff u m‖ ^ 2) :=
    (hasSum_weight_coeff u).summable.of_nonneg_of_le (fun m => sq_nonneg _)
      (fun m => le_mul_of_one_le_left (sq_nonneg _) (one_le_weight m))
  have hb : Summable (fun j => (2 * π * ‖freq j‖ * ‖coeff v j‖) ^ 2) :=
    (hasSum_weight_coeff v).summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => by
      have h1 := freq_le_weight j
      have h0 := sq_nonneg ‖coeff v j‖
      calc (2 * π * ‖freq j‖ * ‖coeff v j‖) ^ 2 = 4 * π ^ 2 * ‖freq j‖ ^ 2 * ‖coeff v j‖ ^ 2 := by
            ring
        _ ≤ weight j * ‖coeff v j‖ ^ 2 := mul_le_mul_of_nonneg_right h1 h0)
  have hw : ∀ m j, ‖advTerm (coeff u) (coeff v) (m, j)‖ ≤
      (‖coeff u m‖ ^ 2 + (2 * π * ‖freq j‖ * ‖coeff v j‖) ^ 2) / 2 := fun m j => by
    have h1 := norm_advTerm_le (coeff u) (coeff v) (m, j)
    have h2 := two_mul_le_add_sq ‖coeff u m‖ (2 * π * ‖freq j‖ * ‖coeff v j‖)
    simp only at h1
    linarith
  have hfib : ∀ k, Summable (fun j => advTerm (coeff u) (coeff v) (k - j, j)) := fun k => by
    refine Summable.of_norm_bounded (g := fun j =>
      (‖coeff u (k - j)‖ ^ 2 + (2 * π * ‖freq j‖ * ‖coeff v j‖) ^ 2) / 2) ?_ (fun j => hw _ _)
    refine (Summable.add ?_ hb).div_const 2
    exact (Equiv.subLeft k).summable_iff.mpr ha
  have hB : Summable (fun q : Lattice × Lattice => ‖φ q.1‖ *
      ((‖coeff u (q.1 - q.2)‖ ^ 2 + (2 * π * ‖freq q.2‖ * ‖coeff v q.2‖) ^ 2) / 2)) := by
    have h1 : Summable (fun r : Lattice × Lattice => ‖φ r.1‖ * ‖coeff u r.2‖ ^ 2) :=
      summable_mul_of_summable_norm (f := fun k => ‖φ k‖) (g := fun m => ‖coeff u m‖ ^ 2)
        (hφ.congr (fun k => (norm_norm _).symm))
        (ha.congr (fun m => (Real.norm_of_nonneg (sq_nonneg _)).symm))
    have h1' : Summable (fun q : Lattice × Lattice => ‖φ q.1‖ * ‖coeff u (q.1 - q.2)‖ ^ 2) :=
      diffEquiv.summable_iff.mpr h1
    have h2 : Summable (fun r : Lattice × Lattice =>
        ‖φ r.1‖ * (2 * π * ‖freq r.2‖ * ‖coeff v r.2‖) ^ 2) :=
      summable_mul_of_summable_norm (f := fun k => ‖φ k‖)
        (g := fun j => (2 * π * ‖freq j‖ * ‖coeff v j‖) ^ 2) (hφ.congr (fun k => (norm_norm _).symm))
        (hb.congr (fun j => (Real.norm_of_nonneg (sq_nonneg _)).symm))
    refine ((h1'.add h2).div_const 2).congr (fun q => ?_)
    ring
  have hg : Summable (fun q : Lattice × Lattice =>
      inner ℂ (φ q.1) (advTerm (coeff u) (coeff v) (q.1 - q.2, q.2))) :=
    Summable.of_norm_bounded hB (fun q => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hw _ _) (norm_nonneg _)))
  have hL : ∑' q : Lattice × Lattice, inner ℂ (φ q.1) (advTerm (coeff u) (coeff v) (q.1 - q.2, q.2)) =
      ∑' k, inner ℂ (φ k) (advCoef u v k) := by
    rw [hg.tsum_prod' (fun k => hg.prod_factor k)]
    refine tsum_congr (fun k => ?_)
    have hadv : advCoef u v k = ∑' j, advTerm (coeff u) (coeff v) (k - j, j) := rfl
    rw [hadv]
    exact ((innerSL ℂ (φ k)).map_tsum (hfib k)).symm
  have h := hg.hasSum
  rw [hL] at h
  have h' := (shiftEquiv.hasSum_iff (f := fun q : Lattice × Lattice =>
    inner ℂ (φ q.1) (advTerm (coeff u) (coeff v) (q.1 - q.2, q.2)))).mpr h
  have e : (fun p : Lattice × Lattice => inner ℂ (φ (p.1 + p.2)) (advTerm (coeff u) (coeff v) p)) =
      (fun q : Lattice × Lattice => inner ℂ (φ q.1)
        (advTerm (coeff u) (coeff v) (q.1 - q.2, q.2))) ∘ shiftEquiv := by
    funext p
    simp [shiftEquiv]
  rw [e]
  exact h'

theorem tendsto_pairs :
    Tendsto (fun s : Finset Lattice => (s ×ˢ s).filter (fun p => p.1 + p.2 ∈ s)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro t
  refine ⟨t.image Prod.fst ∪ t.image Prod.snd ∪ t.image (fun p => p.1 + p.2), fun s hs p hp => ?_⟩
  have h1 : p.1 ∈ s := hs (by simp only [Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl ⟨p, hp, rfl⟩))
  have h2 : p.2 ∈ s := hs (by simp only [Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨p, hp, rfl⟩))
  have h3 : p.1 + p.2 ∈ s := hs (by simp only [Finset.mem_union, Finset.mem_image]; exact Or.inr ⟨p, hp, rfl⟩)
  simp only [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨h1, h2⟩, h3⟩

theorem sq_rpow_half {x : ℝ} (hx : 0 ≤ x) : (x ^ 2) ^ (1 / 2 : ℝ) = x := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx]
  norm_num

end Trilinear.Internal

open Trilinear.Internal in
theorem trilinearBound (hS : TrigHs) : TrilinearBound := by
  obtain ⟨C, hC0, hC⟩ := hS
  refine ⟨C * C ^ (1 / 2 : ℝ), by positivity, fun u v φ hφ1 hφ2 => ?_⟩
  have hφ0 : Summable (fun k => ‖φ k‖ ^ 2) :=
    hφ2.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun k => le_mul_of_one_le_left (sq_nonneg _) (one_le_weight k))
  have hsum := hasSum_pairs u v φ hφ1
  have ht : Tendsto (fun s : Finset Lattice => ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 + p.2 ∈ s),
      inner ℂ (φ (p.1 + p.2)) (advTerm (coeff u) (coeff v) p)) atTop
      (𝓝 (∑' k, inner ℂ (φ k) (advCoef u v k))) :=
    Filter.Tendsto.comp (g := fun t : Finset (Lattice × Lattice) => ∑ p ∈ t,
      inner ℂ (φ (p.1 + p.2)) (advTerm (coeff u) (coeff v) p)) hsum tendsto_pairs
  refine le_of_tendsto' ht.norm (fun s => (finite_est hC0.le hC s (coeff u) (coeff v) φ).trans ?_)
  have hu := sum_le_hasSum s (fun k _ => mul_nonneg (weight_pos k).le (sq_nonneg ‖coeff u k‖))
    (hasSum_weight_coeff u)
  have hv := sum_le_hasSum s (fun k _ => mul_nonneg (weight_pos k).le (sq_nonneg ‖coeff v k‖))
    (hasSum_weight_coeff v)
  have hv' : ∑ k ∈ s, 4 * π ^ 2 * ‖freq k‖ ^ 2 * ‖coeff v k‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    (Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (freq_le_weight k)
      (sq_nonneg _))).trans hv
  have hp0 := sum_le_hasSum s (fun k _ => sq_nonneg ‖φ k‖) hφ0.hasSum
  have hp1 := sum_le_hasSum s (fun k _ => mul_nonneg (weight_pos k).le (sq_nonneg ‖φ k‖)) hφ2.hasSum
  have w0 : 0 ≤ ∑' k, weight k * ‖φ k‖ ^ 2 :=
    tsum_nonneg (fun k => mul_nonneg (weight_pos k).le (sq_nonneg _))
  have su0 : 0 ≤ ∑ k ∈ s, weight k * ‖coeff u k‖ ^ 2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (weight_pos k).le (sq_nonneg _))
  have sφ0 : 0 ≤ ∑ k ∈ s, weight k * ‖φ k‖ ^ 2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (weight_pos k).le (sq_nonneg _))
  calc _ ≤ (∑' k, ‖φ k‖ ^ 2) ^ (1 / 4 : ℝ) *
          (C * (∑' k, weight k * ‖φ k‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
          (C * (‖u‖ ^ 2) ^ (1 / 2 : ℝ)) * (‖v‖ ^ 2) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = C * C ^ (1 / 2 : ℝ) * ‖u‖ * ‖v‖ * (∑' k, ‖φ k‖ ^ 2) ^ (1 / 4 : ℝ) *
          (∑' k, weight k * ‖φ k‖ ^ 2) ^ (1 / 4 : ℝ) := by
        rw [sq_rpow_half (norm_nonneg u), sq_rpow_half (norm_nonneg v),
          Real.mul_rpow hC0.le (Real.rpow_nonneg w0 _), ← Real.rpow_mul w0,
          show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
        ring

end Breakdown.Periodic
