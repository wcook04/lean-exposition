module

public import QuarticQuery.Forrelation.Promise

/-!
# The probability core of Lemma 2.1(ii)

The abstract half of the quantum algorithm: projecting `ψ_z` onto `u` succeeds with
probability `Φ²`, which is at least `δ²` on 1-inputs and at most `δ²/4` on 0-inputs,
and `O_k (1 + log (1/η))` independent repetitions with the threshold `δ²/2` separate
the two cases. The tail bound is proved directly on the binomial sum, by the
exponential moment at `θ = ±1`. Nothing here is an `AdaptiveProgram` yet.
-/

@[expose] public section

namespace QuarticQuery.Forrelation

open Finset Matrix

/-! ## Projection -/

/-- The projection onto the line through `u`. -/
noncomputable def projU (t : ℕ) (v : Fin (mValue t) → ℝ) : Fin (mValue t) → ℝ :=
  (u t ⬝ᵥ v) • u t

/-- Ledger: claim-proj-prob. The squared length of the projection of `ψ_z` onto `u`. -/
noncomputable def successProb {k t : ℕ} (z : BitInput (ForrelationCoord k t)) : ℝ :=
  projU t (psi z) ⬝ᵥ projU t (psi z)

/-- Ledger: claim-proj-prob. The projection succeeds with probability `Φ²`. -/
theorem successProb_eq (k t : ℕ) (hk : 1 ≤ k) (z : BitInput (ForrelationCoord k t)) :
    successProb z = Phi k t z ^ 2 := by
  rw [Phi_eq_matrix_product k t hk]
  change _ = (u t ⬝ᵥ psi z) ^ 2
  simp only [successProb, projU, dotProduct_smul, smul_dotProduct, u_dot_self, smul_eq_mul]
  ring

/-- Ledger: claim-proj-prob. The other outcome has the complementary mass. -/
theorem failureProb_eq (k t : ℕ) (hk : 1 ≤ k) (z : BitInput (ForrelationCoord k t)) :
    (psi z - projU t (psi z)) ⬝ᵥ (psi z - projU t (psi z)) = 1 - Phi k t z ^ 2 := by
  rw [← successProb_eq k t hk, successProb]
  have hc : projU t (psi z) ⬝ᵥ psi z = projU t (psi z) ⬝ᵥ projU t (psi z) := by
    simp only [projU, dotProduct_smul, smul_dotProduct, u_dot_self, smul_eq_mul]
    ring
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, psi_dot_self,
    dotProduct_comm (psi z) (projU t (psi z)), hc]
  ring

theorem successProb_le_one (k t : ℕ) (hk : 1 ≤ k) (z : BitInput (ForrelationCoord k t)) :
    successProb z ≤ 1 := by
  rw [successProb_eq k t hk]
  exact Phi_sq_le_one k t hk z

theorem successProb_nonneg (k t : ℕ) (hk : 1 ≤ k) (z : BitInput (ForrelationCoord k t)) :
    0 ≤ successProb z := by
  rw [successProb_eq k t hk]
  positivity

/-- Ledger: claim-proj-prob. On a 1-input the probability is at least `δ²`. -/
theorem successProb_of_true (k t : ℕ) (hk : 1 ≤ k) (z : BitInput (ForrelationCoord k t))
    (h : P k t z = some true) : delta k ^ 2 ≤ successProb z := by
  rw [successProb_eq k t hk]
  exact pow_le_pow_left₀ (delta_pos k).le ((P_eq_some_true_iff k t z).1 h) 2

/-- Ledger: claim-proj-prob. On a 0-input the probability is at most `δ²/4`. -/
theorem successProb_of_false (k t : ℕ) (hk : 1 ≤ k) (z : BitInput (ForrelationCoord k t))
    (h : P k t z = some false) : successProb z ≤ delta k ^ 2 / 4 := by
  rw [successProb_eq k t hk, ← sq_abs]
  have := pow_le_pow_left₀ (abs_nonneg _) ((P_eq_some_false_iff k t z).1 h) 2
  calc |Phi k t z| ^ 2 ≤ (delta k / 2) ^ 2 := this
    _ = delta k ^ 2 / 4 := by ring

/-! ## Binomial tails -/

/-- The probability of exactly `j` successes in `n` independent trials. -/
noncomputable def binomWeight (n : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

/-- The probability of at least `s` successes in `n` independent trials. -/
noncomputable def binomTail (n : ℕ) (p s : ℝ) : ℝ :=
  ∑ j ∈ (range (n + 1)).filter (fun j : ℕ => s ≤ (j : ℝ)), binomWeight n p j

theorem binomWeight_nonneg (n j : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    0 ≤ binomWeight n p j :=
  mul_nonneg (mul_nonneg (by positivity) (pow_nonneg h0 _)) (pow_nonneg (by linarith) _)

theorem sum_binomWeight_mul (n : ℕ) (p r : ℝ) :
    ∑ j ∈ range (n + 1), binomWeight n p j * r ^ j = (1 - p + p * r) ^ n := by
  rw [add_comm (1 - p), add_pow]
  refine sum_congr rfl fun j _ => ?_
  rw [binomWeight, mul_pow]
  ring

theorem sum_binomWeight (n : ℕ) (p : ℝ) : ∑ j ∈ range (n + 1), binomWeight n p j = 1 := by
  have := sum_binomWeight_mul n p 1
  simpa using this

/-- Exponential moment at `θ = 1`. -/
theorem binomTail_le (n : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (s : ℝ) :
    binomTail n p s ≤ Real.exp (-s) * (1 - p + p * Real.exp 1) ^ n := by
  rw [← sum_binomWeight_mul, mul_sum]
  refine (sum_le_sum fun j hj => ?_).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ =>
      mul_nonneg (Real.exp_pos _).le (mul_nonneg (binomWeight_nonneg n j h0 h1) (by positivity)))
  have hs : s ≤ (j : ℝ) := (mem_filter.1 hj).2
  have hw := binomWeight_nonneg n j h0 h1
  have he : 1 ≤ Real.exp (-s) * Real.exp 1 ^ j := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  calc binomWeight n p j = binomWeight n p j * 1 := by ring
    _ ≤ binomWeight n p j * (Real.exp (-s) * Real.exp 1 ^ j) :=
      mul_le_mul_of_nonneg_left he hw
    _ = _ := by ring

/-- Exponential moment at `θ = -1`. -/
theorem one_sub_binomTail_le (n : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (s : ℝ) :
    1 - binomTail n p s ≤ Real.exp s * (1 - p + p * Real.exp (-1)) ^ n := by
  have hsplit := sum_filter_add_sum_filter_not (range (n + 1)) (fun j : ℕ => s ≤ (j : ℝ))
    (binomWeight n p)
  rw [sum_binomWeight] at hsplit
  have e : 1 - binomTail n p s =
      ∑ j ∈ (range (n + 1)).filter (fun j : ℕ => ¬ s ≤ (j : ℝ)), binomWeight n p j := by
    rw [binomTail]
    linarith
  rw [e, ← sum_binomWeight_mul, mul_sum]
  refine (sum_le_sum fun j hj => ?_).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ =>
      mul_nonneg (Real.exp_pos _).le (mul_nonneg (binomWeight_nonneg n j h0 h1) (by positivity)))
  have hs : (j : ℝ) < s := not_le.1 (mem_filter.1 hj).2
  have hw := binomWeight_nonneg n j h0 h1
  have he : 1 ≤ Real.exp s * Real.exp (-1) ^ j := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  calc binomWeight n p j = binomWeight n p j * 1 := by ring
    _ ≤ binomWeight n p j * (Real.exp s * Real.exp (-1) ^ j) :=
      mul_le_mul_of_nonneg_left he hw
    _ = _ := by ring

/-- Ledger: lem-2.1.ii. Small success probability: few successes. -/
theorem binomTail_small (n : ℕ) {p c : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (hp : p ≤ c / 4) : binomTail n p (n * (c / 2)) ≤ Real.exp (-(n * c / 16)) := by
  refine (binomTail_le n h0 h1 _).trans ?_
  have hb : 1 - p + p * Real.exp 1 ≤ Real.exp (p * (7 / 4)) := by
    have h := Real.add_one_le_exp (p * (7 / 4))
    have he := Real.exp_one_lt_d9
    nlinarith
  have hnn : 0 ≤ 1 - p + p * Real.exp 1 := by
    have := Real.exp_pos 1
    nlinarith
  have hpow := pow_le_pow_left₀ hnn hb n
  rw [← Real.exp_nat_mul] at hpow
  refine (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hp hn]

/-- Ledger: lem-2.1.ii. Large success probability: many successes. -/
theorem binomTail_large (n : ℕ) {p c : ℝ} (h1 : p ≤ 1) (hc : 0 < c) (hp : c ≤ p) :
    1 - binomTail n p (n * (c / 2)) ≤ Real.exp (-(n * c / 16)) := by
  have h0 : 0 ≤ p := hc.le.trans hp
  refine (one_sub_binomTail_le n h0 h1 _).trans ?_
  have hinv : Real.exp (-1) ≤ 2 / 5 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9
    norm_num
    linarith
  have hb : 1 - p + p * Real.exp (-1) ≤ Real.exp (-(p * (3 / 5))) := by
    have h := Real.add_one_le_exp (-(p * (3 / 5)))
    nlinarith
  have hnn : 0 ≤ 1 - p + p * Real.exp (-1) := by
    have := Real.exp_pos (-1)
    nlinarith
  have hpow := pow_le_pow_left₀ hnn hb n
  rw [← Real.exp_nat_mul] at hpow
  refine (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hn : (0 : ℝ) ≤ n := by positivity
  have := mul_le_mul_of_nonneg_left hp hn
  nlinarith [mul_nonneg hn hc.le]

/-! ## Repetitions -/

theorem delta_sq (k : ℕ) : delta k ^ 2 = ((2 : ℝ) ^ (10 * k))⁻¹ := by
  rw [delta_eq, inv_pow, ← pow_mul]
  congr 2
  ring

/-- Ledger: lem-2.1.ii. The repetition count, `O_k (1 + log (1/η))`. -/
noncomputable def repetitions (k : ℕ) (η : ℝ) : ℕ :=
  ⌈16 * (2 : ℝ) ^ (10 * k) * Real.log (1 / η)⌉₊

/-- Ledger: lem-2.1.ii. The count is at most `1 + 16 · 2^(10k) · log (1/η)`. -/
theorem repetitions_le (k : ℕ) {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) :
    (repetitions k η : ℝ) ≤ 1 + 16 * (2 : ℝ) ^ (10 * k) * Real.log (1 / η) := by
  have hl : 0 ≤ Real.log (1 / η) := Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)
  have := Nat.ceil_lt_add_one (a := 16 * (2 : ℝ) ^ (10 * k) * Real.log (1 / η)) (by positivity)
  rw [repetitions]
  linarith

theorem exp_le_of_repetitions_le (k : ℕ) {η : ℝ} (h0 : 0 < η) {n : ℕ}
    (hn : repetitions k η ≤ n) : Real.exp (-(n * delta k ^ 2 / 16)) ≤ η := by
  have hcast : (repetitions k η : ℝ) ≤ n := by exact_mod_cast hn
  have hle : 16 * (2 : ℝ) ^ (10 * k) * Real.log (1 / η) ≤ n := (Nat.le_ceil _).trans hcast
  have hp : (0 : ℝ) < (2 : ℝ) ^ (10 * k) := by positivity
  have hlog : Real.log (1 / η) ≤ n * delta k ^ 2 / 16 := by
    rw [delta_sq]
    field_simp
    linarith
  have := Real.exp_le_exp.2 (neg_le_neg hlog)
  refine this.trans ?_
  rw [one_div, Real.log_inv, neg_neg, Real.exp_log h0]

/-- Ledger: lem-2.1.ii. With at least `repetitions k η` independent repetitions of
the projection and the threshold `δ²/2`, the error is at most `η` on the promise. -/
theorem threshold_correct (k t : ℕ) (hk : 1 ≤ k) {η : ℝ} (h0 : 0 < η) {n : ℕ}
    (hn : repetitions k η ≤ n) (z : BitInput (ForrelationCoord k t)) :
    (P k t z = some true → 1 - η ≤ binomTail n (successProb z) (n * (delta k ^ 2 / 2))) ∧
    (P k t z = some false → binomTail n (successProb z) (n * (delta k ^ 2 / 2)) ≤ η) := by
  have hc : 0 < delta k ^ 2 := pow_pos (delta_pos k) 2
  have hexp := exp_le_of_repetitions_le k h0 hn
  constructor
  · intro h
    have := binomTail_large n (successProb_le_one k t hk z) hc (successProb_of_true k t hk z h)
    linarith
  · intro h
    exact (binomTail_small n (successProb_nonneg k t hk z) (successProb_le_one k t hk z)
      (successProb_of_false k t hk z h)).trans hexp

/-- Ledger: lem-2.1.ii. The concrete count for error `1/3`: `2 ^ (10 k + 5)`
repetitions, each using `k` queries. -/
theorem threshold_correct_third (k t : ℕ) (hk : 1 ≤ k) (z : BitInput (ForrelationCoord k t)) :
    let n := 2 ^ (10 * k + 5)
    (P k t z = some true → 2 / 3 ≤ binomTail n (successProb z) (n * (delta k ^ 2 / 2))) ∧
    (P k t z = some false → binomTail n (successProb z) (n * (delta k ^ 2 / 2)) ≤ 1 / 3) := by
  intro n
  have hc : 0 < delta k ^ 2 := pow_pos (delta_pos k) 2
  have hval : (n : ℝ) * delta k ^ 2 / 16 = 2 := by
    rw [delta_sq]
    simp only [n]
    push_cast
    rw [pow_add]
    field_simp
    norm_num
  have hexp : Real.exp (-((n : ℝ) * delta k ^ 2 / 16)) ≤ 1 / 3 := by
    rw [hval, Real.exp_neg, one_div]
    refine inv_anti₀ (by norm_num) ?_
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  constructor
  · intro h
    have := binomTail_large n (successProb_le_one k t hk z) hc (successProb_of_true k t hk z h)
    linarith
  · intro h
    exact (binomTail_small n (successProb_nonneg k t hk z) (successProb_le_one k t hk z)
      (successProb_of_false k t hk z h)).trans hexp

end QuarticQuery.Forrelation
