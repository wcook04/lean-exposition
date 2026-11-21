import Mathlib

open MeasureTheory Polynomial
open scoped Interval

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

namespace Internal

namespace UnitIntervalPolynomial

open Finset

def nodeUp (n : ℕ) : ℝ[X] := ∏ k ∈ range (n + 1), (X + C ((k : ℝ) + 1))

def nodeDown (n : ℕ) : ℝ[X] := ∏ i ∈ range (n + 1), (X - C (i : ℝ))

def partUp (n k : ℕ) : ℝ[X] := ∏ l ∈ (range (n + 1)).erase k, (X + C ((l : ℝ) + 1))

def weight (n k : ℕ) : ℝ := -(nodeDown n).eval (-((k : ℝ) + 1)) / (partUp n k).eval (-((k : ℝ) + 1))

lemma monic_nodeUp (n : ℕ) : (nodeUp n).Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

lemma monic_nodeDown (n : ℕ) : (nodeDown n).Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

lemma monic_partUp (n k : ℕ) : (partUp n k).Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

lemma natDegree_nodeUp (n : ℕ) : (nodeUp n).natDegree = n + 1 := by
  rw [nodeUp, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)]
  simp only [natDegree_X_add_C, sum_const, card_range, smul_eq_mul, mul_one]

lemma natDegree_nodeDown (n : ℕ) : (nodeDown n).natDegree = n + 1 := by
  rw [nodeDown, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, sum_const, card_range, smul_eq_mul, mul_one]

lemma natDegree_partUp (n k : ℕ) (hk : k ∈ range (n + 1)) : (partUp n k).natDegree = n := by
  rw [partUp, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)]
  simp only [natDegree_X_add_C, sum_const, card_erase_of_mem hk, card_range, smul_eq_mul, mul_one]
  omega

lemma natDegree_nodeUp_sub_le (n : ℕ) : (nodeUp n - nodeDown n).natDegree ≤ n := by
  have hlt : (nodeUp n - nodeDown n).degree < (nodeUp n).degree := by
    apply degree_sub_lt_left
    · rw [degree_eq_natDegree (monic_nodeUp n).ne_zero, degree_eq_natDegree (monic_nodeDown n).ne_zero,
        natDegree_nodeUp, natDegree_nodeDown]
    · exact (monic_nodeUp n).ne_zero
    · rw [(monic_nodeUp n).leadingCoeff, (monic_nodeDown n).leadingCoeff]
  rw [degree_eq_natDegree (monic_nodeUp n).ne_zero, natDegree_nodeUp] at hlt
  by_cases h0 : nodeUp n - nodeDown n = 0
  · rw [h0]; simp
  · rw [degree_eq_natDegree h0] at hlt
    exact Nat.lt_succ_iff.mp (by exact_mod_cast hlt)

lemma eval_partUp_ne (n j : ℕ) : (partUp n j).eval (-((j : ℝ) + 1)) ≠ 0 := by
  rw [partUp, eval_prod, prod_ne_zero_iff]
  intro l hl
  simp only [eval_add, eval_X, eval_C]
  have hlj : l ≠ j := ne_of_mem_erase hl
  intro h
  apply hlj
  exact_mod_cast (by linarith : (l : ℝ) = j)

lemma eval_partUp_zero (n j k : ℕ) (hj : j ∈ range (n + 1)) (hk : k ≠ j) :
    (partUp n k).eval (-((j : ℝ) + 1)) = 0 := by
  rw [partUp, eval_prod]
  apply prod_eq_zero (i := j) (mem_erase.mpr ⟨hk.symm, hj⟩)
  simp

lemma eval_nodeUp_zero (n j : ℕ) (hj : j ∈ range (n + 1)) : (nodeUp n).eval (-((j : ℝ) + 1)) = 0 := by
  rw [nodeUp, eval_prod]
  apply prod_eq_zero hj
  simp

lemma decomp (n : ℕ) : nodeUp n - nodeDown n = ∑ k ∈ range (n + 1), C (weight n k) * partUp n k := by
  rw [← sub_eq_zero]
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (ι := Fin (n + 1)) (f := fun i => -((i : ℕ) + 1 : ℝ))
  · intro a b h
    simp only [neg_inj, add_left_inj, Nat.cast_inj] at h
    exact Fin.ext h
  · intro i
    have hi : (i : ℕ) ∈ range (n + 1) := mem_range.mpr i.isLt
    simp only [eval_sub, eval_finsetSum, eval_mul, eval_C]
    rw [sum_eq_single (i : ℕ)]
    · rw [eval_nodeUp_zero n i hi, weight, div_mul_cancel₀ _ (eval_partUp_ne n i)]
      ring
    · intro k _ hk
      rw [eval_partUp_zero n i k hi hk, mul_zero]
    · intro h
      exact absurd hi h
  · simp only [Fintype.card_fin]
    refine Nat.lt_succ_of_le ((natDegree_sub_le _ _).trans (max_le (natDegree_nodeUp_sub_le n) ?_))
    refine natDegree_sum_le_of_forall_le _ _ (fun k hk => (natDegree_C_mul_le _ _).trans ?_)
    rw [natDegree_partUp n k hk]

lemma weight_sum_inv (n j : ℕ) (hj : j ∈ range (n + 1)) :
    ∑ k ∈ range (n + 1), weight n k / ((j : ℝ) + k + 1) = 1 := by
  have h := congrArg (eval (j : ℝ)) (decomp n)
  have hdown : (nodeDown n).eval (j : ℝ) = 0 := by
    rw [nodeDown, eval_prod]
    apply prod_eq_zero hj
    simp
  have hpart : ∀ k ∈ range (n + 1), (partUp n k).eval (j : ℝ) = (nodeUp n).eval (j : ℝ) / ((j : ℝ) + k + 1) := by
    intro k hk
    have hpos : (0 : ℝ) < (j : ℝ) + k + 1 := by positivity
    rw [eq_div_iff hpos.ne', nodeUp, ← mul_prod_erase _ _ hk, eval_mul, partUp]
    simp only [eval_add, eval_X, eval_C]
    ring
  have hU : 0 < (nodeUp n).eval (j : ℝ) := by
    rw [nodeUp, eval_prod]
    apply prod_pos
    intro k _
    simp only [eval_add, eval_X, eval_C]
    positivity
  simp only [eval_sub, eval_finsetSum, eval_mul, eval_C, hdown, sub_zero] at h
  rw [sum_congr rfl (fun k hk => by rw [hpart k hk])] at h
  have h2 : (nodeUp n).eval (j : ℝ) * ∑ k ∈ range (n + 1), weight n k / ((j : ℝ) + k + 1)
      = (nodeUp n).eval (j : ℝ) * 1 := by
    rw [mul_sum, mul_one]
    nth_rewrite 2 [h]
    apply sum_congr rfl
    intro k _
    ring
  exact mul_left_cancel₀ hU.ne' h2

lemma sum_odd (n : ℕ) : ∑ k ∈ range (n + 1), ((k : ℝ) + 1 + k) = ((n : ℝ) + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

lemma weight_sum (n : ℕ) : ∑ k ∈ range (n + 1), weight n k = ((n : ℝ) + 1) ^ 2 := by
  have h := congrArg (fun P => coeff P n) (decomp n)
  simp only [coeff_sub, finsetSum_coeff, coeff_C_mul] at h
  have hpart : ∀ k ∈ range (n + 1), (partUp n k).coeff n = 1 := by
    intro k hk
    have := (monic_partUp n k).coeff_natDegree
    rwa [natDegree_partUp n k hk] at this
  rw [sum_congr rfl (fun k hk => by rw [hpart k hk, mul_one])] at h
  rw [← h]
  have hU : (nodeUp n).coeff n = ∑ k ∈ range (n + 1), ((k : ℝ) + 1) := by
    have := Monic.nextCoeff_prod (range (n + 1)) (fun k => X + C ((k : ℝ) + 1)) (fun _ _ => monic_X_add_C _)
    rw [nextCoeff_of_natDegree_pos (by rw [← nodeUp, natDegree_nodeUp]; omega)] at this
    simp only [nextCoeff_X_add_C] at this
    rw [← nodeUp, natDegree_nodeUp] at this
    simpa using this
  have hD : (nodeDown n).coeff n = ∑ k ∈ range (n + 1), -(k : ℝ) := by
    have := Monic.nextCoeff_prod (range (n + 1)) (fun k => X - C (k : ℝ)) (fun _ _ => monic_X_sub_C _)
    rw [nextCoeff_of_natDegree_pos (by rw [← nodeDown, natDegree_nodeDown]; omega)] at this
    simp only [nextCoeff_X_sub_C] at this
    rw [← nodeDown, natDegree_nodeDown] at this
    simpa using this
  rw [hU, hD, ← sum_odd n, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  ring

def kernel (n : ℕ) : ℝ[X] := ∑ k ∈ range (n + 1), C (weight n k) * X ^ k

lemma natDegree_kernel (n : ℕ) : (kernel n).natDegree ≤ n :=
  natDegree_sum_le_of_forall_le _ _ (fun k hk => (natDegree_C_mul_le _ _).trans
    ((natDegree_X_pow_le k).trans (Nat.lt_succ_iff.mp (mem_range.mp hk))))

lemma eval_kernel_one (n : ℕ) : (kernel n).eval 1 = ((n : ℝ) + 1) ^ 2 := by
  rw [kernel, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
  exact weight_sum n

lemma integral_pow_zero_one (m : ℕ) : (∫ y in (0 : ℝ)..1, y ^ m) = 1 / ((m : ℝ) + 1) := by
  rw [integral_pow]
  simp

lemma reproduce (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    (∫ y in (0 : ℝ)..1, p.eval y * (kernel n).eval y) = p.eval 1 := by
  have hlt : p.natDegree < n + 1 := Nat.lt_succ_of_le hp
  have hexp : ∀ y : ℝ, p.eval y * (kernel n).eval y
      = ∑ j ∈ range (n + 1), ∑ k ∈ range (n + 1), (p.coeff j * weight n k) * y ^ (j + k) := by
    intro y
    rw [eval_eq_sum_range' hlt, kernel, eval_finsetSum, sum_mul_sum]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro k _
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum
    (f := fun j y => ∑ k ∈ range (n + 1), p.coeff j * weight n k * y ^ (j + k))
    (fun j _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [eval_eq_sum_range' hlt]
  apply sum_congr rfl
  intro j hj
  rw [intervalIntegral.integral_finsetSum (f := fun k y => p.coeff j * weight n k * y ^ (j + k))
    (fun k _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_pow_zero_one]
  rw [one_pow, mul_one]
  calc ∑ k ∈ range (n + 1), p.coeff j * weight n k * (1 / (((j + k : ℕ) : ℝ) + 1))
      = p.coeff j * ∑ k ∈ range (n + 1), weight n k / ((j : ℝ) + k + 1) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k _
        push_cast
        ring
    _ = p.coeff j := by rw [weight_sum_inv n j hj, mul_one]

lemma polyInner_unit (f g : ℝ[X]) (hc : 0 < ∫ y in (0 : ℝ)..1, g.eval y ^ 2) :
    (∫ y in (0 : ℝ)..1, f.eval y * g.eval y) ^ 2
      ≤ (∫ y in (0 : ℝ)..1, f.eval y ^ 2) * ∫ y in (0 : ℝ)..1, g.eval y ^ 2 := by
  set a := ∫ y in (0 : ℝ)..1, f.eval y ^ 2
  set b := ∫ y in (0 : ℝ)..1, f.eval y * g.eval y
  set c := ∫ y in (0 : ℝ)..1, g.eval y ^ 2
  have h0 : 0 ≤ ∫ y in (0 : ℝ)..1, (c * f.eval y - b * g.eval y) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun y _ => sq_nonneg _)
  have e : ∀ y : ℝ, (c * f.eval y - b * g.eval y) ^ 2
      = c ^ 2 * f.eval y ^ 2 + (-2 * c * b) * (f.eval y * g.eval y) + b ^ 2 * g.eval y ^ 2 := by
    intro y
    ring
  simp_rw [e] at h0
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h0
  · have h1 : 0 ≤ c * (c * a - b ^ 2) := by nlinarith
    have h2 : 0 ≤ c * a - b ^ 2 := by
      by_contra hneg
      rw [not_le] at hneg
      nlinarith
    nlinarith
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

lemma sq_eval_one_le_unit (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    p.eval 1 ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * ∫ y in (0 : ℝ)..1, p.eval y ^ 2 := by
  have hKK : (∫ y in (0 : ℝ)..1, (kernel n).eval y ^ 2) = ((n : ℝ) + 1) ^ 2 := by
    rw [← eval_kernel_one n, ← reproduce n (kernel n) (natDegree_kernel n)]
    congr 1
    ext y
    ring
  have hc : 0 < ∫ y in (0 : ℝ)..1, (kernel n).eval y ^ 2 := by rw [hKK]; positivity
  have h := polyInner_unit p (kernel n) hc
  rw [reproduce n p hp, hKK] at h
  linarith

lemma sq_eval_one_le_sym (q : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ q) :
    p.eval 1 ^ 2 ≤ ((q : ℝ) + 1) ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 := by
  have hdeg : (p.comp (C 2 * X + C (-1))).natDegree ≤ q := by
    refine natDegree_comp_le.trans ?_
    have h1 : (C (2 : ℝ) * X + C (-1)).natDegree ≤ 1 := natDegree_linear_le
    calc p.natDegree * (C (2 : ℝ) * X + C (-1)).natDegree ≤ q * 1 := Nat.mul_le_mul hp h1
      _ = q := mul_one q
  have h := sq_eval_one_le_unit q _ hdeg
  have h1 : (p.comp (C 2 * X + C (-1))).eval 1 = p.eval 1 := by
    simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X]
    norm_num
  have hint : (∫ y in (0 : ℝ)..1, (p.comp (C 2 * X + C (-1))).eval y ^ 2)
      = 2⁻¹ * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 := by
    simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X]
    rw [intervalIntegral.integral_comp_mul_add (f := fun t => p.eval t ^ 2) (by norm_num : (2 : ℝ) ≠ 0) (-1),
      smul_eq_mul]
    norm_num
  rw [h1, hint] at h
  linarith

def orth : ℕ → ℝ[X]
  | 0 => kernel 0
  | m + 1 => kernel (m + 1) - kernel m

lemma natDegree_orth (m : ℕ) : (orth m).natDegree ≤ m := by
  cases m with
  | zero => exact natDegree_kernel 0
  | succ m =>
    exact (natDegree_sub_le _ _).trans (max_le (natDegree_kernel _) ((natDegree_kernel m).trans (Nat.le_succ m)))

lemma integral_orth_eq_zero (m : ℕ) (r : ℝ[X]) (hr : r.natDegree < m) :
    (∫ y in (0 : ℝ)..1, r.eval y * (orth m).eval y) = 0 := by
  cases m with
  | zero => omega
  | succ m =>
    have h1 := reproduce (m + 1) r hr.le
    have h2 := reproduce m r (Nat.lt_succ_iff.mp hr)
    simp only [orth, eval_sub, mul_sub]
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), h1, h2, sub_self]

lemma eval_orth_one (m : ℕ) : (orth m).eval 1 = 2 * m + 1 := by
  cases m with
  | zero => simp [orth, eval_kernel_one]
  | succ m =>
    simp only [orth, eval_sub, eval_kernel_one]
    push_cast
    ring

lemma integral_orth_sq (m : ℕ) : (∫ y in (0 : ℝ)..1, (orth m).eval y * (orth m).eval y) = 2 * m + 1 := by
  cases m with
  | zero =>
    show (∫ y in (0 : ℝ)..1, (kernel 0).eval y * (kernel 0).eval y) = _
    rw [reproduce 0 _ (natDegree_kernel 0), eval_kernel_one]
    push_cast
    ring
  | succ m =>
    have h1 : (∫ y in (0 : ℝ)..1, (orth (m + 1)).eval y * (kernel (m + 1)).eval y) = (orth (m + 1)).eval 1 :=
      reproduce (m + 1) _ (natDegree_orth _)
    have h2 : (∫ y in (0 : ℝ)..1, (kernel m).eval y * (orth (m + 1)).eval y) = 0 :=
      integral_orth_eq_zero (m + 1) _ (Nat.lt_succ_of_le (natDegree_kernel m))
    have e : ∀ y : ℝ, (orth (m + 1)).eval y * (orth (m + 1)).eval y
        = (orth (m + 1)).eval y * (kernel (m + 1)).eval y - (kernel m).eval y * (orth (m + 1)).eval y := by
      intro y
      simp only [orth, eval_sub]
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), h1, h2, sub_zero, eval_orth_one]

lemma integral_orth_mul (m l : ℕ) (h : l ≠ m) :
    (∫ y in (0 : ℝ)..1, (orth l).eval y * (orth m).eval y) = 0 := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact integral_orth_eq_zero m _ ((natDegree_orth l).trans_lt hlt)
  · have e : ∀ y : ℝ, (orth l).eval y * (orth m).eval y = (orth m).eval y * (orth l).eval y := fun y => mul_comm _ _
    simp_rw [e]
    exact integral_orth_eq_zero l _ ((natDegree_orth m).trans_lt hlt)

lemma weight_diag_ne (m : ℕ) : weight m m ≠ 0 := by
  rw [weight]
  refine div_ne_zero (neg_ne_zero.mpr ?_) (eval_partUp_ne m m)
  rw [nodeDown, eval_prod, prod_ne_zero_iff]
  intro i _
  simp only [eval_sub, eval_X, eval_C]
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  intro h
  linarith

lemma coeff_kernel (n j : ℕ) : (kernel n).coeff j = if j < n + 1 then weight n j else 0 := by
  rw [kernel, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · intro hj
      exact absurd (mem_range.mpr h) hj
  · apply sum_eq_zero
    intro k hk
    have : j ≠ k := by
      intro e
      rw [e] at h
      exact h (mem_range.mp hk)
    simp [this]

lemma coeff_orth_ne (m : ℕ) : (orth m).coeff m ≠ 0 := by
  cases m with
  | zero => simp [orth, coeff_kernel, weight_diag_ne]
  | succ m =>
    simp only [orth, coeff_sub, coeff_kernel]
    simp [weight_diag_ne]

lemma expansion (d : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ d) :
    p = ∑ m ∈ range (d + 1),
      C ((∫ y in (0 : ℝ)..1, p.eval y * (orth m).eval y) / (2 * m + 1)) * orth m := by
  induction d generalizing p with
  | zero =>
    rw [sum_range_one]
    have hq : (orth 0).natDegree = 0 := Nat.le_zero.mp (natDegree_orth 0)
    rw [eq_C_of_natDegree_le_zero hp] at *
    have ho : orth 0 = C ((orth 0).coeff 0) := eq_C_of_natDegree_le_zero (natDegree_orth 0)
    have hc := coeff_orth_ne 0
    have h1 := eval_orth_one 0
    rw [ho] at h1
    simp only [eval_C] at h1
    rw [ho]
    simp only [eval_C, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul]
    rw [← C_mul, h1]
    congr 1
    push_cast
    ring
  | succ d ih =>
    set a := p.coeff (d + 1) / (orth (d + 1)).coeff (d + 1) with ha
    set p1 := p - C a * orth (d + 1) with hp1
    have hp1deg : p1.natDegree ≤ d := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hp1, coeff_sub, coeff_C_mul]
      rcases Nat.lt_or_ge (d + 1) N with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt h),
          coeff_eq_zero_of_natDegree_lt ((natDegree_orth _).trans_lt h)]
        ring
      · have : N = d + 1 := by omega
        rw [this, ha]
        field_simp [coeff_orth_ne (d + 1)]
        ring
    have hrep := ih p1 hp1deg
    have hcoef : ∀ m ∈ range (d + 1), (∫ y in (0 : ℝ)..1, p1.eval y * (orth m).eval y)
        = ∫ y in (0 : ℝ)..1, p.eval y * (orth m).eval y := by
      intro m hm
      have hne : d + 1 ≠ m := by have := mem_range.mp hm; omega
      have e : ∀ y : ℝ, p1.eval y * (orth m).eval y
          = p.eval y * (orth m).eval y - a * ((orth (d + 1)).eval y * (orth m).eval y) := by
        intro y
        rw [hp1]
        simp only [eval_sub, eval_mul, eval_C]
        ring
      simp_rw [e]
      rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
        integral_orth_mul m (d + 1) hne, mul_zero, sub_zero]
    have hlast : (∫ y in (0 : ℝ)..1, p.eval y * (orth (d + 1)).eval y) / (2 * ((d + 1 : ℕ) : ℝ) + 1) = a := by
      have e : ∀ y : ℝ, p.eval y * (orth (d + 1)).eval y
          = p1.eval y * (orth (d + 1)).eval y + a * ((orth (d + 1)).eval y * (orth (d + 1)).eval y) := by
        intro y
        rw [hp1]
        simp only [eval_sub, eval_mul, eval_C]
        ring
      simp_rw [e]
      rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
        integral_orth_eq_zero (d + 1) _ (Nat.lt_succ_of_le hp1deg), integral_orth_sq, zero_add]
      have : (2 * ((d + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    have hrep' : p1 = ∑ m ∈ range (d + 1),
        C ((∫ y in (0 : ℝ)..1, p.eval y * (orth m).eval y) / (2 * m + 1)) * orth m := by
      conv_lhs => rw [hrep]
      apply sum_congr rfl
      intro m hm
      rw [hcoef m hm]
    calc p = p1 + C a * orth (d + 1) := by rw [hp1]; ring
      _ = _ := by
        rw [sum_range_succ, hlast]
        conv_lhs => rw [hrep']

lemma eval_nodeDown_neg_one (n : ℕ) :
    (nodeDown n).eval (-1) = (-1) ^ (n + 1) * ((n + 1).factorial : ℝ) := by
  rw [nodeDown, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  have h : ∀ i ∈ range (n + 1), (-1 : ℝ) - i = (-1) * ((i : ℝ) + 1) := by
    intro i _
    ring
  rw [prod_congr rfl h, prod_mul_distrib, prod_const, card_range, ← prod_range_add_one_eq_factorial, Nat.cast_prod]
  push_cast
  rfl

lemma eval_partUp_zero_neg_one (n : ℕ) : (partUp n 0).eval (-1) = (n.factorial : ℝ) := by
  rw [partUp, eval_prod]
  simp only [eval_add, eval_X, eval_C]
  set g : ℕ → ℝ := fun l => if l = 0 then 1 else -1 + ((l : ℝ) + 1) with hg
  have h1 : ∏ l ∈ (range (n + 1)).erase 0, (-1 + ((l : ℝ) + 1)) = ∏ l ∈ (range (n + 1)).erase 0, g l := by
    apply prod_congr rfl
    intro l hl
    simp [hg, ne_of_mem_erase hl]
  have h2 : ∏ l ∈ range (n + 1), g l = g 0 * ∏ l ∈ (range (n + 1)).erase 0, g l :=
    (mul_prod_erase _ _ (mem_range.mpr (Nat.succ_pos n))).symm
  have h3 : ∏ l ∈ range (n + 1), g l = ∏ i ∈ range n, ((i : ℝ) + 1) := by
    rw [prod_range_succ']
    simp only [hg]
    simp
  rw [h1, ← one_mul (∏ l ∈ (range (n + 1)).erase 0, g l)]
  have hg0 : g 0 = 1 := by simp [hg]
  rw [← hg0, ← h2, h3, ← prod_range_add_one_eq_factorial, Nat.cast_prod]
  push_cast
  rfl

lemma weight_zero (n : ℕ) : weight n 0 = (-1) ^ n * ((n : ℝ) + 1) := by
  rw [weight]
  have e : (-((0 : ℕ) : ℝ) - 1) = -1 := by simp
  simp only [Nat.cast_zero, zero_add]
  rw [eval_nodeDown_neg_one, eval_partUp_zero_neg_one, Nat.factorial_succ]
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma eval_kernel_zero (n : ℕ) : (kernel n).eval 0 = weight n 0 := by
  rw [kernel, eval_finsetSum, sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (mem_range.mpr (Nat.succ_pos n)) h

lemma eval_orth_zero_sq (m : ℕ) : (orth m).eval 0 ^ 2 = (2 * (m : ℝ) + 1) ^ 2 := by
  cases m with
  | zero =>
    simp only [orth, eval_kernel_zero, weight_zero]
    norm_num
  | succ m =>
    simp only [orth, eval_sub, eval_kernel_zero, weight_zero]
    push_cast
    have h : ((-1 : ℝ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have e : (-1 : ℝ) ^ (m + 1) * ((m : ℝ) + 1 + 1) - (-1) ^ m * ((m : ℝ) + 1)
        = -((-1) ^ m * (2 * ((m : ℝ) + 1) + 1)) := by ring
    rw [e, neg_sq, mul_pow, h, one_mul]

lemma sq_eval_zero_le_unit (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    p.eval 0 ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * ∫ y in (0 : ℝ)..1, p.eval y ^ 2 := by
  have hdeg : (p.comp (1 - X)).natDegree ≤ n := by
    refine natDegree_comp_le.trans ?_
    have h1 : ((1 : ℝ[X]) - X).natDegree ≤ 1 := by
      rw [show ((1 : ℝ[X]) - X) = C (-1) * X + C 1 by simp; ring]
      exact natDegree_linear_le
    calc p.natDegree * ((1 : ℝ[X]) - X).natDegree ≤ n * 1 := Nat.mul_le_mul hp h1
      _ = n := mul_one n
  have h := sq_eval_one_le_unit n _ hdeg
  have hint : (∫ y in (0 : ℝ)..1, (p.comp (1 - X)).eval y ^ 2) = ∫ y in (0 : ℝ)..1, p.eval y ^ 2 := by
    simp only [eval_comp, eval_sub, eval_one, eval_X]
    rw [intervalIntegral.integral_comp_sub_left (f := fun t => p.eval t ^ 2)]
    norm_num
  rw [hint] at h
  simp only [eval_comp, eval_sub, eval_one, eval_X, sub_self] at h
  exact h

lemma integral_deriv_orth_sq (m : ℕ) :
    (∫ y in (0 : ℝ)..1, (derivative (orth m)).eval y ^ 2) ≤ 4 * (m : ℝ) ^ 2 * (2 * m + 1) ^ 2 := by
  cases m with
  | zero =>
    have : derivative (orth 0) = 0 := derivative_of_natDegree_zero (Nat.le_zero.mp (natDegree_orth 0))
    simp [this]
  | succ k =>
    set Q := orth (k + 1) with hQ
    set u2 := ∫ y in (0 : ℝ)..1, (derivative Q).eval y ^ 2 with hu2
    have hQdeg : Q.natDegree ≤ k + 1 := by rw [hQ]; exact natDegree_orth (k + 1)
    have hdQ : (derivative Q).natDegree ≤ k := by
      have := natDegree_derivative_le Q
      omega
    have hddQ : (derivative (derivative Q)).natDegree < k + 1 := by
      have := natDegree_derivative_le (derivative Q)
      omega
    have hibp := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
      (fun x _ => (Q * derivative Q).hasDerivAt x) ((Polynomial.continuous _).intervalIntegrable _ _)
    have e : ∀ y : ℝ, (derivative (Q * derivative Q)).eval y
        = (derivative Q).eval y ^ 2 + (derivative (derivative Q)).eval y * Q.eval y := by
      intro y
      simp only [derivative_mul, eval_add, eval_mul]
      ring
    simp_rw [e] at hibp
    rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), integral_orth_eq_zero (k + 1) _ hddQ, add_zero] at hibp
    simp only [eval_mul] at hibp
    have ha := sq_eval_one_le_unit k (derivative Q) hdQ
    have hb := sq_eval_zero_le_unit k (derivative Q) hdQ
    rw [← hu2] at ha hb hibp
    have h1 : Q.eval 1 = 2 * ((k + 1 : ℕ) : ℝ) + 1 := eval_orth_one (k + 1)
    have h0 := eval_orth_zero_sq (k + 1)
    push_cast at h1 h0 ⊢
    have hu0 : 0 ≤ u2 := intervalIntegral.integral_nonneg (by norm_num) (fun y _ => sq_nonneg _)
    set v := Real.sqrt u2 with hv
    have hv0 : 0 ≤ v := Real.sqrt_nonneg _
    have hvv : v ^ 2 = u2 := Real.sq_sqrt hu0
    have hK : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    have ha' : |(derivative Q).eval 1| ≤ ((k : ℝ) + 1) * v :=
      abs_le_of_sq_le_sq (by rw [mul_pow, hvv]; exact ha) (mul_nonneg hK hv0)
    have hb' : |(derivative Q).eval 0| ≤ ((k : ℝ) + 1) * v :=
      abs_le_of_sq_le_sq (by rw [mul_pow, hvv]; exact hb) (mul_nonneg hK hv0)
    have hq0 : |Q.eval 0| ≤ 2 * ((k : ℝ) + 1) + 1 :=
      abs_le_of_sq_le_sq (le_of_eq h0) (by positivity)
    have hmain : u2 ≤ (2 * ((k : ℝ) + 1) + 1) * (((k : ℝ) + 1) * v) + (2 * ((k : ℝ) + 1) + 1) * (((k : ℝ) + 1) * v) := by
      have t1 : Q.eval 1 * (derivative Q).eval 1 ≤ (2 * ((k : ℝ) + 1) + 1) * (((k : ℝ) + 1) * v) := by
        rw [h1]
        calc (2 * ((k : ℝ) + 1) + 1) * (derivative Q).eval 1 ≤ (2 * ((k : ℝ) + 1) + 1) * |(derivative Q).eval 1| := by
              gcongr
              exact le_abs_self _
          _ ≤ _ := by gcongr
      have t2 : -(Q.eval 0 * (derivative Q).eval 0) ≤ (2 * ((k : ℝ) + 1) + 1) * (((k : ℝ) + 1) * v) := by
        calc -(Q.eval 0 * (derivative Q).eval 0) ≤ |Q.eval 0 * (derivative Q).eval 0| := neg_le_abs _
          _ = |Q.eval 0| * |(derivative Q).eval 0| := abs_mul _ _
          _ ≤ _ := by gcongr
      linarith
    have hvle : v ≤ 2 * ((k : ℝ) + 1) * (2 * ((k : ℝ) + 1) + 1) := by
      rw [← hvv] at hmain
      nlinarith
    rw [← hvv]
    have : v ^ 2 ≤ (2 * ((k : ℝ) + 1) * (2 * ((k : ℝ) + 1) + 1)) ^ 2 := pow_le_pow_left₀ hv0 hvle 2
    nlinarith

lemma sum_weight_bound (q : ℕ) :
    ∑ m ∈ range (q + 1), 4 * (m : ℝ) ^ 2 * (2 * m + 1) ≤ 2 * ((q : ℝ) + 1) ^ 4 := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [ih, sq_nonneg (n : ℝ), mul_nonneg hn (sq_nonneg (n : ℝ))]

lemma integral_derivative_sq_le_unit (q : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ q) :
    (∫ y in (0 : ℝ)..1, (derivative p).eval y ^ 2)
      ≤ 2 * ((q : ℝ) + 1) ^ 4 * ∫ y in (0 : ℝ)..1, p.eval y ^ 2 := by
  have hexp := expansion q p hp
  set c : ℕ → ℝ := fun m => (∫ y in (0 : ℝ)..1, p.eval y * (orth m).eval y) / (2 * m + 1) with hc
  have hpos : ∀ m : ℕ, (0 : ℝ) < 2 * m + 1 := fun m => by positivity
  have hcm : ∀ m : ℕ, (∫ y in (0 : ℝ)..1, p.eval y * (orth m).eval y) = c m * (2 * m + 1) := by
    intro m
    simp only [hc]
    field_simp [(hpos m).ne']
  have hd : ∀ y : ℝ, (derivative p).eval y = ∑ m ∈ range (q + 1), c m * (derivative (orth m)).eval y := by
    intro y
    conv_lhs => rw [hexp]
    simp only [derivative_sum, derivative_C_mul, eval_finsetSum, eval_mul, eval_C]
    rfl
  have hN : (∫ y in (0 : ℝ)..1, p.eval y ^ 2) = ∑ m ∈ range (q + 1), c m ^ 2 * (2 * m + 1) := by
    have e : ∀ y : ℝ, p.eval y ^ 2 = ∑ m ∈ range (q + 1), c m * (p.eval y * (orth m).eval y) := by
      intro y
      rw [sq]
      nth_rewrite 2 [hexp]
      simp only [eval_finsetSum, eval_mul, eval_C, mul_sum]
      apply sum_congr rfl
      intro m _
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_finsetSum (f := fun m y => c m * (p.eval y * (orth m).eval y))
      (fun m _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
    apply sum_congr rfl
    intro m _
    rw [intervalIntegral.integral_const_mul, hcm m]
    ring
  set S := ∑ m ∈ range (q + 1), c m ^ 2 * (2 * m + 1) with hS
  have hS0 : 0 ≤ S := sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hpos m).le)
  have hpt : ∀ y : ℝ, (derivative p).eval y ^ 2
      ≤ S * ∑ m ∈ range (q + 1), (derivative (orth m)).eval y ^ 2 / (2 * m + 1) := by
    intro y
    rw [hd y]
    have h := sum_mul_sq_le_sq_mul_sq (range (q + 1)) (fun m => c m * Real.sqrt (2 * m + 1))
      (fun m => (derivative (orth m)).eval y / Real.sqrt (2 * m + 1))
    have e1 : ∀ m : ℕ, c m * Real.sqrt (2 * m + 1) * ((derivative (orth m)).eval y / Real.sqrt (2 * m + 1))
        = c m * (derivative (orth m)).eval y := by
      intro m
      have : Real.sqrt (2 * m + 1) ≠ 0 := (Real.sqrt_pos.2 (hpos m)).ne'
      field_simp
    have e2 : ∀ m : ℕ, (c m * Real.sqrt (2 * m + 1)) ^ 2 = c m ^ 2 * (2 * m + 1) := by
      intro m
      rw [mul_pow, Real.sq_sqrt (hpos m).le]
    have e3 : ∀ m : ℕ, ((derivative (orth m)).eval y / Real.sqrt (2 * m + 1)) ^ 2
        = (derivative (orth m)).eval y ^ 2 / (2 * m + 1) := by
      intro m
      rw [div_pow, Real.sq_sqrt (hpos m).le]
    simp only [e1, e2, e3] at h
    exact h
  calc (∫ y in (0 : ℝ)..1, (derivative p).eval y ^ 2)
      ≤ ∫ y in (0 : ℝ)..1, S * ∑ m ∈ range (q + 1), (derivative (orth m)).eval y ^ 2 / (2 * m + 1) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)
        intro y _
        exact hpt y
    _ = S * ∑ m ∈ range (q + 1), (∫ y in (0 : ℝ)..1, (derivative (orth m)).eval y ^ 2) / (2 * m + 1) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_finsetSum (f := fun m y => (derivative (orth m)).eval y ^ 2 / (2 * m + 1))
            (fun m _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
        congr 1
        apply sum_congr rfl
        intro m _
        rw [intervalIntegral.integral_div]
    _ ≤ S * ∑ m ∈ range (q + 1), 4 * (m : ℝ) ^ 2 * (2 * m + 1) := by
        gcongr with m hm
        rw [div_le_iff₀ (hpos m)]
        have := integral_deriv_orth_sq m
        nlinarith
    _ ≤ S * (2 * ((q : ℝ) + 1) ^ 4) := by gcongr; exact sum_weight_bound q
    _ = _ := by rw [hN]; ring

lemma integral_derivative_sq_le_sym (q : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ q) :
    (∫ t in (-1 : ℝ)..1, (derivative p).eval t ^ 2)
      ≤ ((q : ℝ) + 1) ^ 4 / 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 := by
  have hdeg : (p.comp (C 2 * X + C (-1))).natDegree ≤ q := by
    refine natDegree_comp_le.trans ?_
    have h1 : (C (2 : ℝ) * X + C (-1)).natDegree ≤ 1 := natDegree_linear_le
    calc p.natDegree * (C (2 : ℝ) * X + C (-1)).natDegree ≤ q * 1 := Nat.mul_le_mul hp h1
      _ = q := mul_one q
  have h := integral_derivative_sq_le_unit q _ hdeg
  have hint : (∫ y in (0 : ℝ)..1, (p.comp (C 2 * X + C (-1))).eval y ^ 2)
      = 2⁻¹ * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 := by
    simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X]
    rw [intervalIntegral.integral_comp_mul_add (f := fun t => p.eval t ^ 2) (by norm_num : (2 : ℝ) ≠ 0) (-1),
      smul_eq_mul]
    norm_num
  have hintd : (∫ y in (0 : ℝ)..1, (derivative (p.comp (C 2 * X + C (-1)))).eval y ^ 2)
      = 4 * (2⁻¹ * ∫ t in (-1 : ℝ)..1, (derivative p).eval t ^ 2) := by
    have e : (∫ y in (0 : ℝ)..1, (derivative (p.comp (C 2 * X + C (-1)))).eval y ^ 2)
        = ∫ y in (0 : ℝ)..1, 4 * (derivative p).eval (2 * y + -1) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro y _
      simp only [derivative_comp, derivative_add, derivative_mul, derivative_C, derivative_X, eval_mul,
        eval_comp, eval_add, eval_C, eval_X, eval_zero, eval_one]
      ring
    rw [e, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_add (f := fun t => (derivative p).eval t ^ 2) (by norm_num : (2 : ℝ) ≠ 0) (-1),
      smul_eq_mul]
    norm_num
  rw [hint, hintd] at h
  linarith

end UnitIntervalPolynomial

end Internal

namespace IntervalClosedBounds

theorem sq_eval_one_le (q : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ q) :
    p.eval 1 ^ 2 ≤ ((q : ℝ) + 1) ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 :=
  Internal.UnitIntervalPolynomial.sq_eval_one_le_sym q p hp

theorem integral_derivative_sq_le (q : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ q) :
    (∫ t in (-1 : ℝ)..1, (derivative p).eval t ^ 2)
      ≤ ((q : ℝ) + 1) ^ 4 / 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 :=
  Internal.UnitIntervalPolynomial.integral_derivative_sq_le_sym q p hp

lemma sq_eval_le_of_nonneg (q : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ q) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    p.eval x ^ 2 ≤ ((q : ℝ) + 1) ^ 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 := by
  have hc0 : 0 < (x + 1) / 2 := by linarith
  have hrdeg : (p.comp (C ((x + 1) / 2) * X + C ((x - 1) / 2))).natDegree ≤ q := by
    refine natDegree_comp_le.trans ?_
    have h1 : (C ((x + 1) / 2) * X + C ((x - 1) / 2)).natDegree ≤ 1 := natDegree_linear_le
    calc p.natDegree * (C ((x + 1) / 2) * X + C ((x - 1) / 2)).natDegree ≤ q * 1 := Nat.mul_le_mul hp h1
      _ = q := mul_one q
  have hE := sq_eval_one_le q _ hrdeg
  have hr1 : (p.comp (C ((x + 1) / 2) * X + C ((x - 1) / 2))).eval 1 = p.eval x := by
    simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X]
    congr 1
    ring
  have hint : (∫ t in (-1 : ℝ)..1, (p.comp (C ((x + 1) / 2) * X + C ((x - 1) / 2))).eval t ^ 2)
      = ((x + 1) / 2)⁻¹ * ∫ t in (-1 : ℝ)..x, p.eval t ^ 2 := by
    simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X]
    rw [intervalIntegral.integral_comp_mul_add (f := fun t => p.eval t ^ 2) hc0.ne' ((x - 1) / 2), smul_eq_mul]
    congr 2 <;> ring
  have hsub : (∫ t in (-1 : ℝ)..x, p.eval t ^ 2) ≤ ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 := by
    apply intervalIntegral.integral_mono_interval le_rfl (by linarith) hx1
    · exact Filter.Eventually.of_forall (fun t => sq_nonneg _)
    · exact ((Polynomial.continuous p).pow 2).intervalIntegrable _ _
  have hcinv : ((x + 1) / 2)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hc0 (by norm_num)]
    linarith
  have hN0 : 0 ≤ ∫ t in (-1 : ℝ)..x, p.eval t ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => sq_nonneg _)
  rw [← hr1]
  calc _ ≤ ((q : ℝ) + 1) ^ 2 / 2 * (((x + 1) / 2)⁻¹ * ∫ t in (-1 : ℝ)..x, p.eval t ^ 2) := by
        rw [← hint]
        exact hE
    _ ≤ ((q : ℝ) + 1) ^ 2 / 2 * (2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2) := by
        gcongr
    _ = _ := by ring

theorem sq_eval_le (q : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ q) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    p.eval x ^ 2 ≤ ((q : ℝ) + 1) ^ 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 := by
  rcases le_total 0 x with h0 | h0
  · exact sq_eval_le_of_nonneg q p hp x h0 hx.2
  · have hdeg : (p.comp (-X)).natDegree ≤ q := by
      refine natDegree_comp_le.trans ?_
      simp [hp]
    have h := sq_eval_le_of_nonneg q (p.comp (-X)) hdeg (-x) (by linarith) (by linarith [hx.1])
    have hint : (∫ t in (-1 : ℝ)..1, (p.comp (-X)).eval t ^ 2) = ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 := by
      simp only [eval_comp, eval_neg, eval_X]
      rw [intervalIntegral.integral_comp_neg (f := fun t => p.eval t ^ 2)]
      norm_num
    rw [hint] at h
    simpa using h

end IntervalClosedBounds

end Spectral

end CellCert

end Breakdown
