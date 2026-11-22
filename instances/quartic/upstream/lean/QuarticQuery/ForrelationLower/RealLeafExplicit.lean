module

public import QuarticQuery.ForrelationLower.RealLeafGrowth
public import QuarticQuery.ForrelationLower.RealLeafAdvantage

/-!
# Explicit constants for bounded-real leaves

Choose `Λ = 2 r log(4n)` in the parameterized estimates.  The residual is
exactly `2⁻ʳ`, not merely bounded by one.  The square-root notation below
is equivalent to the ordinary nonnegative power `(16 r d log(4n))^(r/2)`.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset

namespace QuarticQuery.ForrelationLower

theorem real_leaf_residual (n r : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) * 2) ^ r *
        ((4 * n : ℝ) ^ r * Real.exp (-(2 * r * Real.log (4 * n)))) =
      (1 / 2 : ℝ) ^ r := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hxpos : (0 : ℝ) < 4 * n := by positivity
  have hexp : Real.exp (-(2 * r * Real.log (4 * n))) =
      ((4 * n : ℝ) ^ r)⁻¹ * ((4 * n : ℝ) ^ r)⁻¹ := by
    rw [show -(2 * (r : ℝ) * Real.log (4 * n)) =
        -((r : ℝ) * Real.log (4 * n)) + -((r : ℝ) * Real.log (4 * n)) by ring]
    simp only [Real.exp_add, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hxpos]
  rw [hexp]
  have hpow : ((4 * n : ℝ) ^ r) ≠ 0 := pow_ne_zero _ hxpos.ne'
  calc
    ((n : ℝ) * 2) ^ r *
        ((4 * n : ℝ) ^ r * (((4 * n : ℝ) ^ r)⁻¹ * ((4 * n : ℝ) ^ r)⁻¹)) =
      ((n : ℝ) * 2) ^ r / (4 * n : ℝ) ^ r := by field_simp
    _ = (((n : ℝ) * 2) / (4 * n)) ^ r := (div_pow _ _ _).symm
    _ = (1 / 2 : ℝ) ^ r := by
      congr 1
      field_simp
      norm_num

theorem real_leaf_log_parameters (n r d : ℕ)
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hd : 1 ≤ d) :
    0 < Real.sqrt (16 * (r : ℝ) * d * Real.log (4 * n)) ∧
      (Real.sqrt (16 * (r : ℝ) * d * Real.log (4 * n))) ^ 2 =
        2 * d * (2 : ℝ) ^ 2 * (2 * r * Real.log (4 * n)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hlog : 0 < Real.log (4 * n : ℝ) := Real.log_pos (by linarith)
  have hpos : 0 < 16 * (r : ℝ) * d * Real.log (4 * n) := by positivity
  constructor
  · exact Real.sqrt_pos.mpr hpos
  · rw [Real.sq_sqrt hpos.le]
    ring

theorem sum_abs_ext_Dl_le_real_leaves_explicit
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : Type} [Fintype P] [DecidableEq P]
    (Lp : P → List ι) (hnd : ∀ p, (Lp p).Nodup) {k d : ℕ}
    (hk : 1 ≤ k) (hd : 1 ≤ d) (hlen : ∀ p, (Lp p).length = k)
    (hinj : Function.Injective fun p => (Lp p).toFinset)
    {μ : ι → ℝ} (hμ : ∀ a, |μ a| ≤ 1 / 2)
    (hn : 1 ≤ Fintype.card ι) (T : RealQueryTree ι)
    (hT : T.depth ≤ d) (hbounded : T.Bounded) :
    ∑ p, |ext (Dl (Lp p) T.eval) μ| ≤
      (Real.sqrt (16 * (k : ℝ) * d * Real.log (4 * Fintype.card ι))) ^ k +
        (1 / 2 : ℝ) ^ k := by
  obtain ⟨hK, hKsq⟩ := real_leaf_log_parameters (Fintype.card ι) k d hn hk hd
  have h := sum_abs_ext_Dl_le_real_leaves Lp hnd hlen hinj hμ
    (lt_of_lt_of_le Nat.zero_lt_one hd) hK hKsq hn T hT hbounded
  rwa [real_leaf_residual _ _ hn] at h

theorem advantage_le_sharp_real_leaves_explicit
    {n : Type} [Fintype n] [DecidableEq n] {l d : ℕ}
    (H : Matrix n n ℝ) (hl : 0 < l) (hH : RowsOrth H)
    {ε : ℝ} (hε : 0 ≤ ε) (hHb : ∀ a b, |H a b| ≤ ε)
    (hd : 1 ≤ d) (hn : 1 ≤ Fintype.card (BC l n))
    (T : RealQueryTree (BC l n)) (hT : T.depth ≤ d) (hbounded : T.Bounded) :
    |∫ u, ext T.eval (wv H 1 u) ∂(gP (PC l n)) - ext T.eval 0| ≤
      ((3 / 16 : ℝ) * ε) ^ l *
        ((Real.sqrt (16 * ((l + 1 : ℕ) : ℝ) * d *
            Real.log (4 * Fintype.card (BC l n)))) ^ (l + 1) +
          (1 / 2 : ℝ) ^ (l + 1)) := by
  obtain ⟨hK, hKsq⟩ := real_leaf_log_parameters (Fintype.card (BC l n)) (l + 1) d
    hn (Nat.succ_le_succ (Nat.zero_le l)) hd
  have h := advantage_le_sharp_real_leaves H hl hH hε hHb
    (lt_of_lt_of_le Nat.zero_lt_one hd) hK hKsq hn T hT hbounded
  rwa [real_leaf_residual _ _ hn] at h

end QuarticQuery.ForrelationLower
