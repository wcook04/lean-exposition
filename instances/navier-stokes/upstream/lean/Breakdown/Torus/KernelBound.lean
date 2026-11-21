import Breakdown.Torus.Basic
import Breakdown.Torus.StatementsAnalysis

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

namespace Internal.KernelEstimate

theorem summable_exp_neg_mul_int_sq {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-(a * (n : ℝ) ^ 2))) := by
  have hpos : 0 < (((a / π : ℝ) : ℂ) * Complex.I).im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re,
      mul_one, mul_zero, add_zero]
    exact div_pos ha Real.pi_pos
  have h := (summable_jacobiTheta₂_term_iff 0 (((a / π : ℝ) : ℂ) * Complex.I)).mpr hpos
  refine (summable_norm_iff.mpr h).congr (fun n => ?_)
  rw [jacobiTheta₂_term, Complex.norm_exp]
  have hπ : (π : ℂ) * ((a : ℂ) / (π : ℂ)) = a := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  have e : (2 * (π : ℂ) * Complex.I * (n : ℂ) * 0 + (π : ℂ) * Complex.I * (n : ℂ) ^ 2 *
      (((a / π : ℝ) : ℂ) * Complex.I)) = ((-(a * (n : ℝ) ^ 2) : ℝ) : ℂ) := by
    push_cast
    linear_combination (Complex.I ^ 2 * (n : ℂ) ^ 2) * hπ + ((a : ℂ) * (n : ℂ) ^ 2) * Complex.I_sq
  rw [e, Complex.ofReal_re]

theorem freq_apply (k : Lattice) (i : Fin 3) : freq k i = (k i : ℝ) := by
  simp [freq, unitVector, Pi.single_apply]

theorem norm_freq_sq (k : Lattice) : ‖freq k‖ ^ 2 = ∑ i, ((k i : ℤ) : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [freq_apply, sq_abs]

def latticeEquiv : Lattice ≃ ℤ × ℤ × ℤ where
  toFun k := (k 0, k 1, k 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv k := by
    funext i
    fin_cases i <;> rfl
  right_inv p := rfl

theorem latticeEquiv_symm_apply (p : ℤ × ℤ × ℤ) :
    latticeEquiv.symm p = ![p.1, p.2.1, p.2.2] := rfl

theorem summable_exp_neg_mul_norm_freq_sq {a : ℝ} (ha : 0 < a) :
    Summable (fun k : Lattice => Real.exp (-(a * ‖freq k‖ ^ 2))) := by
  have hg := summable_exp_neg_mul_int_sq ha
  have hg0 : 0 ≤ (fun n : ℤ => Real.exp (-(a * (n : ℝ) ^ 2))) := fun n => (Real.exp_pos _).le
  have h3 := hg.mul_of_nonneg (hg.mul_of_nonneg hg hg0 hg0) hg0
    (fun p => mul_nonneg (hg0 _) (hg0 _))
  rw [← latticeEquiv.symm.summable_iff]
  refine h3.congr (fun p => ?_)
  simp only [Function.comp, norm_freq_sq, Fin.sum_univ_three, latticeEquiv_symm_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem weight_pos (k : Lattice) : 0 < weight k := by
  unfold weight
  positivity

theorem heatFactor_nonneg (τ : ℝ) (k : Lattice) : 0 ≤ heatFactor τ k :=
  (Real.exp_pos _).le

theorem heatFactor_le_one (τ : ℝ) (k : Lattice) : heatFactor τ k ≤ 1 :=
  (le_abs_self _).trans (abs_heatFactor_le τ k)

theorem summable_heatFactor {τ : ℝ} (hτ : 0 < τ) : Summable (heatFactor τ) := by
  have := summable_exp_neg_mul_norm_freq_sq (a := 4 * π ^ 2 * τ) (by positivity)
  refine this.congr (fun k => ?_)
  rw [heatFactor, max_eq_left hτ.le]
  congr 1
  ring

theorem heat_ineq {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (k : Lattice) :
    τ * (weight k * heatFactor τ k ^ 2) ≤ heatFactor τ k ∧
      τ ^ 2 * (weight k ^ 2 * heatFactor τ k ^ 2) ≤ 1 := by
  rw [heatFactor, max_eq_left hτ.le, Real.exp_neg, weight]
  set r := 4 * π ^ 2 * ‖freq k‖ ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  set E := Real.exp (r * τ) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have h1 : r * τ + 1 ≤ E := Real.add_one_le_exp _
  have h2 : τ * (1 + r) ≤ E := by nlinarith
  have h3 : τ * (1 + r) * E⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hE0]
    exact h2
  have h4 : 0 ≤ E⁻¹ := inv_nonneg.mpr hE0.le
  have h5 : 0 ≤ τ * (1 + r) * E⁻¹ := by positivity
  constructor
  · calc τ * ((1 + r) * E⁻¹ ^ 2) = (τ * (1 + r) * E⁻¹) * E⁻¹ := by ring
      _ ≤ 1 * E⁻¹ := mul_le_mul_of_nonneg_right h3 h4
      _ = E⁻¹ := one_mul _
  · calc τ ^ 2 * ((1 + r) ^ 2 * E⁻¹ ^ 2) = (τ * (1 + r) * E⁻¹) ^ 2 := by ring
      _ ≤ 1 := pow_le_one₀ h5 h3

theorem weight_heat_le_div {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (k : Lattice) :
    weight k * heatFactor τ k ^ 2 ≤ heatFactor τ k / τ := by
  rw [le_div_iff₀ hτ, mul_comm]
  exact (heat_ineq hτ hτ1 k).1

theorem weight_heat_le_inv {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (k : Lattice) :
    weight k * heatFactor τ k ^ 2 ≤ τ⁻¹ := by
  have := weight_heat_le_div hτ hτ1 k
  rw [inv_eq_one_div]
  exact this.trans (div_le_div_of_nonneg_right (heatFactor_le_one τ k) hτ.le)

theorem weight_sq_heat_le_inv {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (k : Lattice) :
    weight k ^ 2 * heatFactor τ k ^ 2 ≤ (τ ^ 2)⁻¹ := by
  rw [inv_eq_one_div, le_div_iff₀ (by positivity), mul_comm]
  exact (heat_ineq hτ hτ1 k).2

theorem divPairing_eq_inner (k : Lattice) (c : Coef) : divPairing k c = inner ℂ (latVec k) c := by
  rw [divPairing, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [RCLike.inner_apply]
  simp [latVec, mul_comm]

theorem inner_latVec_self (k : Lattice) :
    inner ℂ (latVec k) (latVec k) = ((‖freq k‖ ^ 2 : ℝ) : ℂ) := by
  rw [← divPairing_eq_inner, divPairing, norm_freq_sq]
  push_cast
  simp [latVec, sq]

theorem norm_freq_sq_ne_zero {k : Lattice} (hk : k ≠ 0) : ‖freq k‖ ^ 2 ≠ 0 := by
  intro h
  apply hk
  have h0 : freq k = 0 := by simpa using h
  funext i
  have := congrArg (fun x : Space => x i) h0
  simpa [freq_apply] using this

theorem inner_divFree_self (k : Lattice) (x : Coef) :
    inner ℂ (divFree k x) x = ((‖divFree k x‖ ^ 2 : ℝ) : ℂ) := by
  by_cases hk : k = 0
  · rw [divFree, if_pos hk, inner_self_eq_norm_sq_to_K]
    simp
  · have hn : ((‖freq k‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_freq_sq_ne_zero hk)
    have hP : divFree k x = x - (divPairing k x / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • latVec k := by
      rw [divFree, if_neg hk]
    have hl : inner ℂ (latVec k) (divFree k x) = 0 := by
      rw [hP, inner_sub_right, inner_smul_right, inner_latVec_self, ← divPairing_eq_inner,
        div_mul_cancel₀ _ hn, sub_self]
    have hl' : inner ℂ (divFree k x) (latVec k) = 0 := by
      rw [← inner_conj_symm, hl, map_zero]
    have hx : x = divFree k x + (divPairing k x / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • latVec k := by
      rw [hP, sub_add_cancel]
    calc inner ℂ (divFree k x) x
        = inner ℂ (divFree k x) (divFree k x + (divPairing k x / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • latVec k) :=
          congrArg _ hx
      _ = inner ℂ (divFree k x) (divFree k x) := by
          rw [inner_add_right, inner_smul_right, hl', mul_zero, add_zero]
      _ = _ := by
          rw [inner_self_eq_norm_sq_to_K]
          simp

theorem real_smul_coef (r : ℝ) (x : Coef) : r • x = (r : ℂ) • x :=
  RCLike.real_smul_eq_coe_smul (K := ℂ) r x

theorem inner_term (wt s : ℝ) (k : Lattice) (a : Coef) :
    inner ℂ ((wt * s) • (s • divFree k (a + a))) a =
      (((1 / 2) * (wt * ‖s • divFree k (a + a)‖ ^ 2) : ℝ) : ℂ) := by
  have h2 : inner ℂ ((wt * s) • (s • divFree k (a + a))) (a + a) =
      ((wt * ‖s • divFree k (a + a)‖ ^ 2 : ℝ) : ℂ) := by
    rw [real_smul_coef (wt * s), real_smul_coef s,
      inner_smul_left, inner_smul_left, inner_divFree_self, Complex.conj_ofReal, Complex.conj_ofReal,
      norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    push_cast
    ring
  rw [inner_add_right] at h2
  have e : inner ℂ ((wt * s) • (s • divFree k (a + a))) a =
      (1 / 2 : ℂ) * (inner ℂ ((wt * s) • (s • divFree k (a + a))) a +
        inner ℂ ((wt * s) • (s • divFree k (a + a))) a) := by ring
  rw [e, h2]
  push_cast
  ring

def testSeq (τ : ℝ) (c : Lattice → Coef) (k : Lattice) : Coef :=
  (weight k * (-(1 / 2) * heatFactor τ k)) • c k

theorem norm_testSeq (τ : ℝ) (c : Lattice → Coef) (k : Lattice) :
    ‖testSeq τ c k‖ = (1 / 2) * weight k * heatFactor τ k * ‖c k‖ := by
  have h0 : 0 ≤ (1 / 2) * weight k * heatFactor τ k :=
    mul_nonneg (mul_nonneg (by norm_num) (weight_pos k).le) (heatFactor_nonneg τ k)
  rw [testSeq, norm_smul, Real.norm_eq_abs,
    show weight k * (-(1 / 2) * heatFactor τ k) = -((1 / 2) * weight k * heatFactor τ k) by ring,
    abs_neg, abs_of_nonneg h0]

theorem norm_testSeq_sq (τ : ℝ) (c : Lattice → Coef) (k : Lattice) :
    ‖testSeq τ c k‖ ^ 2 = (1 / 4) * (weight k * heatFactor τ k ^ 2) * (weight k * ‖c k‖ ^ 2) := by
  rw [norm_testSeq]
  ring

theorem summable_norm_testSeq {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (c : Lattice → Coef)
    (hc : Summable (fun k => weight k * ‖c k‖ ^ 2)) :
    Summable (fun k => ‖testSeq τ c k‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((((summable_heatFactor hτ).div_const τ).mul_left (1 / 4)).add (hc.mul_left (1 / 4)))
  have h1 := weight_heat_le_div hτ hτ1 k
  have hw := (weight_pos k).le
  have h2 := mul_nonneg hw (sq_nonneg (heatFactor τ k - ‖c k‖))
  rw [norm_testSeq]
  nlinarith

theorem testSeq_sq_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (c : Lattice → Coef) (k : Lattice) :
    ‖testSeq τ c k‖ ^ 2 ≤ τ⁻¹ * (weight k * ‖c k‖ ^ 2) := by
  have h1 := weight_heat_le_inv hτ hτ1 k
  have hX : 0 ≤ weight k * ‖c k‖ ^ 2 := mul_nonneg (weight_pos k).le (sq_nonneg _)
  have hi : 0 ≤ τ⁻¹ := inv_nonneg.mpr hτ.le
  rw [norm_testSeq_sq]
  nlinarith [mul_le_mul_of_nonneg_right h1 hX]

theorem weight_testSeq_sq_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (c : Lattice → Coef)
    (k : Lattice) :
    weight k * ‖testSeq τ c k‖ ^ 2 ≤ (τ ^ 2)⁻¹ * (weight k * ‖c k‖ ^ 2) := by
  have h1 := weight_sq_heat_le_inv hτ hτ1 k
  have hX : 0 ≤ weight k * ‖c k‖ ^ 2 := mul_nonneg (weight_pos k).le (sq_nonneg _)
  have hi : 0 ≤ (τ ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
  have e : weight k * ‖testSeq τ c k‖ ^ 2 =
      (1 / 4) * (weight k ^ 2 * heatFactor τ k ^ 2) * (weight k * ‖c k‖ ^ 2) := by
    rw [norm_testSeq_sq]
    ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_right h1 hX]

theorem summable_weight_coeff (w : V) : Summable (fun k => weight k * ‖coeff w k‖ ^ 2) := by
  have h := (lp.memℓp (w : Seq)).summable (p := 2) (by norm_num)
  refine h.congr (fun k => ?_)
  have hw := weight_pos k
  rw [coeff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    inv_pow, Real.sq_sqrt hw.le]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  field_simp

theorem rpow_combine {τ N : ℝ} (hτ : 0 < τ) (hN : 0 ≤ N) :
    (τ⁻¹ * N ^ 2) ^ (1 / 4 : ℝ) * ((τ ^ 2)⁻¹ * N ^ 2) ^ (1 / 4 : ℝ) = τ ^ (-(3 / 4 : ℝ)) * N := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  have e : τ⁻¹ * N ^ 2 * ((τ ^ 2)⁻¹ * N ^ 2) = (τ ^ (-(3 / 4 : ℝ)) * N) ^ (4 : ℕ) := by
    rw [mul_pow, ← Real.rpow_natCast (τ ^ (-(3 / 4 : ℝ))), ← Real.rpow_mul hτ.le,
      show (-(3 / 4 : ℝ)) * ((4 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hτ.le,
      Real.rpow_natCast]
    field_simp
  rw [e, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]

theorem le_two_mul_of_half_sq_le {N K : ℝ} (hK : 0 ≤ K)
    (h : (1 / 2) * N ^ 2 ≤ K * N) : N ≤ 2 * K := by
  nlinarith

theorem norm_kernel_diag_le (C : ℝ) (hC : 0 < C)
    (hT : ∀ (u v : V) (φ : Lattice → Coef),
      Summable (fun k => ‖φ k‖) → Summable (fun k => weight k * ‖φ k‖ ^ 2) →
      ‖∑' k, inner ℂ (φ k) (advCoef u v k)‖ ≤
        C * ‖u‖ * ‖v‖ * (∑' k, ‖φ k‖ ^ 2) ^ (1 / 4 : ℝ) *
          (∑' k, weight k * ‖φ k‖ ^ 2) ^ (1 / 4 : ℝ))
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (u : V) :
    ‖kernel τ u u‖ ≤ 2 * (C * τ ^ (-(3 / 4 : ℝ))) * ‖u‖ ^ 2 := by
  have hXs := summable_weight_coeff (kernel τ u u)
  have hN := norm_sq_eq_tsum (kernel τ u u)
  have hterm : ∀ k, inner ℂ (testSeq τ (coeff (kernel τ u u)) k) (advCoef u u k) =
      (((1 / 2) * (weight k * ‖coeff (kernel τ u u) k‖ ^ 2) : ℝ) : ℂ) := by
    intro k
    rw [testSeq, coeff_kernel τ hτ u u k]
    exact inner_term _ _ _ _
  have hsum : ∑' k, inner ℂ (testSeq τ (coeff (kernel τ u u)) k) (advCoef u u k) =
      (((1 / 2) * ‖kernel τ u u‖ ^ 2 : ℝ) : ℂ) := by
    rw [tsum_congr hterm, ← Complex.ofReal_tsum, tsum_mul_left, hN]
  have hb := hT u u (testSeq τ (coeff (kernel τ u u)))
    (summable_norm_testSeq hτ hτ1 _ hXs)
    ((hXs.mul_left (τ ^ 2)⁻¹).of_nonneg_of_le
      (fun k => mul_nonneg (weight_pos k).le (sq_nonneg _))
      (fun k => weight_testSeq_sq_le hτ hτ1 _ k))
  rw [hsum, Complex.norm_of_nonneg (by positivity)] at hb
  have hN0 : 0 ≤ ‖kernel τ u u‖ := norm_nonneg _
  have hS1 : ∑' k, ‖testSeq τ (coeff (kernel τ u u)) k‖ ^ 2 ≤ τ⁻¹ * ‖kernel τ u u‖ ^ 2 := by
    rw [hN, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun k => testSeq_sq_le hτ hτ1 _ k)
      ((hXs.mul_left τ⁻¹).of_nonneg_of_le (fun k => sq_nonneg _)
        (fun k => testSeq_sq_le hτ hτ1 _ k)) (hXs.mul_left τ⁻¹)
  have hS2 : ∑' k, weight k * ‖testSeq τ (coeff (kernel τ u u)) k‖ ^ 2 ≤ (τ ^ 2)⁻¹ * ‖kernel τ u u‖ ^ 2 := by
    rw [hN, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun k => weight_testSeq_sq_le hτ hτ1 _ k)
      ((hXs.mul_left (τ ^ 2)⁻¹).of_nonneg_of_le
        (fun k => mul_nonneg (weight_pos k).le (sq_nonneg _))
        (fun k => weight_testSeq_sq_le hτ hτ1 _ k)) (hXs.mul_left (τ ^ 2)⁻¹)
  have hS1' := Real.rpow_le_rpow (tsum_nonneg (fun k => sq_nonneg _)) hS1
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hS2' := Real.rpow_le_rpow
    (tsum_nonneg (fun k => mul_nonneg (weight_pos k).le (sq_nonneg _))) hS2
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hprod := mul_le_mul hS1' hS2' (Real.rpow_nonneg
    (tsum_nonneg (fun k => mul_nonneg (weight_pos k).le (sq_nonneg _))) _)
    (Real.rpow_nonneg (by positivity) _)
  rw [rpow_combine hτ hN0] at hprod
  have hK0 : 0 ≤ C * ‖u‖ * ‖u‖ := by positivity
  have hmain : (1 / 2) * ‖kernel τ u u‖ ^ 2 ≤
      (C * ‖u‖ * ‖u‖ * τ ^ (-(3 / 4 : ℝ))) * ‖kernel τ u u‖ := by
    calc (1 / 2) * ‖kernel τ u u‖ ^ 2 ≤ _ := hb
      _ = C * ‖u‖ * ‖u‖ * ((∑' k, ‖testSeq τ (coeff (kernel τ u u)) k‖ ^ 2) ^ (1 / 4 : ℝ) *
            (∑' k, weight k * ‖testSeq τ (coeff (kernel τ u u)) k‖ ^ 2) ^ (1 / 4 : ℝ)) := by
          ring
      _ ≤ C * ‖u‖ * ‖u‖ * (τ ^ (-(3 / 4 : ℝ)) * ‖kernel τ u u‖) :=
          mul_le_mul_of_nonneg_left hprod hK0
      _ = (C * ‖u‖ * ‖u‖ * τ ^ (-(3 / 4 : ℝ))) * ‖kernel τ u u‖ := by ring
  have hτp : 0 < τ ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hτ _
  have h2 := le_two_mul_of_half_sq_le (by positivity) hmain
  calc ‖kernel τ u u‖ ≤ 2 * (C * ‖u‖ * ‖u‖ * τ ^ (-(3 / 4 : ℝ))) := h2
    _ = 2 * (C * τ ^ (-(3 / 4 : ℝ))) * ‖u‖ ^ 2 := by ring

theorem norm_le_of_diag {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : E →L[ℝ] E →L[ℝ] E} (hsymm : ∀ u v, K u v = K v u) {D : ℝ}
    (hD : 0 ≤ D) (h : ∀ u, ‖K u u‖ ≤ D * ‖u‖ ^ 2) : ‖K‖ ≤ 2 * D := by
  have hpol : ∀ u v, ‖K u v‖ ≤ D * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    intro u v
    have e : K (u + v) (u + v) - K (u - v) (u - v) = (4 : ℝ) • K u v := by
      simp only [map_add, map_sub, add_apply, sub_apply]
      rw [hsymm v u]
      module
    have h4 : ‖(4 : ℝ) • K u v‖ ≤ ‖K (u + v) (u + v)‖ + ‖K (u - v) (u - v)‖ := by
      rw [← e]
      exact norm_sub_le _ _
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at h4
    have h1 := h (u + v)
    have h2 := h (u - v)
    have n1 : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
      nlinarith only [norm_add_le u v, norm_nonneg (u + v), norm_nonneg u, norm_nonneg v,
        sq_nonneg (‖u‖ - ‖v‖)]
    have n2 : ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
      nlinarith only [norm_sub_le u v, norm_nonneg (u - v), norm_nonneg u, norm_nonneg v,
        sq_nonneg (‖u‖ - ‖v‖)]
    linarith only [h4, h1, h2, mul_le_mul_of_nonneg_left n1 hD, mul_le_mul_of_nonneg_left n2 hD]
  refine ContinuousLinearMap.opNorm_le_bound₂ K (by positivity) (fun u v => ?_)
  by_cases hu : u = 0
  · rw [hu, map_zero, zero_apply, norm_zero]
    simp only [mul_zero, zero_mul, le_refl]
  by_cases hv : v = 0
  · rw [hv, map_zero, norm_zero]
    simp only [mul_zero, le_refl]
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have e : K u v = (‖u‖ * ‖v‖) • K (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) := by
    simp only [map_smul, smul_apply, smul_smul]
    convert (one_smul ℝ (K u v)).symm using 2
    field_simp
  have nu : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu'.ne']
  have nv : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv'.ne']
  have hb := hpol (‖u‖⁻¹ • u) (‖v‖⁻¹ • v)
  rw [nu, nv] at hb
  rw [e, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc ‖u‖ * ‖v‖ * ‖K (‖u‖⁻¹ • u) (‖v‖⁻¹ • v)‖ ≤ ‖u‖ * ‖v‖ * (D * (1 ^ 2 + 1 ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 * D * ‖u‖ * ‖v‖ := by ring

end Internal.KernelEstimate

open Internal.KernelEstimate in
theorem kernelSharpBound (hT : TrilinearBound) : KernelSharpBound := by
  obtain ⟨C, hC, hT⟩ := hT
  refine ⟨4 * C, by positivity, fun τ hτ hτ1 => ?_⟩
  have hD : 0 ≤ 2 * (C * τ ^ (-(3 / 4 : ℝ))) := by
    have := Real.rpow_pos_of_pos hτ (-(3 / 4 : ℝ))
    positivity
  have := norm_le_of_diag (kernel_symm τ) hD (fun u => norm_kernel_diag_le C hC hT hτ hτ1 u)
  linarith

end Breakdown.Periodic
