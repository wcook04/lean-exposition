module

public import QuarticQuery.ForrelationLower.Cube

/-!
# Independently specified real-valued decision trees

The maintained Boolean `QueryTree` followed by `v : Bool → ℝ` permits only
two output values.  A real-valued tree can have a different value at every
leaf.  The independent syntax below describes that larger class directly.

Every tree with leaf values in `[-1,1]` is an input-independent finite
convex combination of Boolean sign trees of exactly the same syntactic
depth.  Sampling all leaf labels in advance is essential: the mixture
does not depend on the queried input or on the leaf eventually reached.

Zero weights are permitted here, so this is a convex representation,
not a value of `RandomizedProgram`, whose support weights are positive.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace QuarticQuery.ForrelationLower

inductive RealQueryTree (ι : Type) where
  | leaf (value : ℝ)
  | query (index : ι) (onFalse onTrue : RealQueryTree ι)

namespace RealQueryTree

variable {ι : Type}

def eval : RealQueryTree ι → BitInput ι → ℝ
  | .leaf a, _ => a
  | .query i l r, x => if x i then r.eval x else l.eval x

def depth : RealQueryTree ι → ℕ
  | .leaf _ => 0
  | .query _ l r => 1 + max l.depth r.depth

def Bounded : RealQueryTree ι → Prop
  | .leaf a => |a| ≤ 1
  | .query _ l r => l.Bounded ∧ r.Bounded

/-- A label is assigned to every syntactic leaf, including unreachable ones. -/
def Labels : RealQueryTree ι → Type
  | .leaf _ => Bool
  | .query _ l r => l.Labels × r.Labels

instance labelsFintype (T : RealQueryTree ι) : Fintype T.Labels :=
  match T with
  | .leaf _ => inferInstanceAs (Fintype Bool)
  | .query _ l r =>
      letI := labelsFintype l
      letI := labelsFintype r
      inferInstanceAs (Fintype (l.Labels × r.Labels))

/-- This uses the sign convention of the independently specified output;
`false` has value `+1`, and `true` has value `-1`. -/
def answerSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem abs_answerSign (b : Bool) : |answerSign b| = 1 := by
  cases b <;> norm_num [answerSign]

noncomputable def weight : (T : RealQueryTree ι) → T.Labels → ℝ
  | .leaf a, b => (1 + a * answerSign b) / 2
  | .query _ l r, b => l.weight b.1 * r.weight b.2

def booleanTree : (T : RealQueryTree ι) → T.Labels → QueryTree ι
  | .leaf _, b => .leaf b
  | .query i l r, b => .query i (l.booleanTree b.1) (r.booleanTree b.2)

theorem booleanTree_depth (T : RealQueryTree ι) (b : T.Labels) :
    (T.booleanTree b).depth = T.depth := by
  induction T with
  | leaf a => rfl
  | query i l r ihl ihr =>
      simp only [booleanTree, QueryTree.depth, depth, ihl, ihr]

theorem weight_nonneg (T : RealQueryTree ι) (hT : T.Bounded) (b : T.Labels) :
    0 ≤ T.weight b := by
  induction T with
  | leaf a =>
      have ha := abs_le.mp hT
      cases b <;> simp only [weight, answerSign] <;> norm_num <;> linarith
  | query i l r ihl ihr =>
      exact mul_nonneg (ihl hT.1 b.1) (ihr hT.2 b.2)

/-- Normalization holds algebraically even for unbounded leaf labels. -/
theorem sum_weight (T : RealQueryTree ι) : ∑ b : T.Labels, T.weight b = 1 := by
  induction T with
  | leaf a =>
      change (∑ b : Bool, (1 + a * answerSign b) / 2) = 1
      simp only [Fintype.sum_bool, answerSign]
      norm_num
      ring
  | query i l r ihl ihr =>
      change (∑ b : l.Labels × r.Labels, l.weight b.1 * r.weight b.2) = 1
      rw [Fintype.sum_prod_type]
      simp only [← mul_sum, ihr, mul_one, ihl]

/-- The all-input identity. Both the index set and every weight are fixed
before the input is quantified.  This is stronger than pointwise existence
of a convenient mixture after observing the input. -/
theorem eval_eq_convex_sum (T : RealQueryTree ι) (x : BitInput ι) :
    T.eval x = ∑ b : T.Labels,
      T.weight b * answerSign ((T.booleanTree b).eval x) := by
  induction T with
  | leaf a =>
      change a = ∑ b : Bool, (1 + a * answerSign b) / 2 * answerSign b
      simp only [Fintype.sum_bool, answerSign]
      norm_num
      ring
  | query i l r ihl ihr =>
      change (if x i then r.eval x else l.eval x) =
        ∑ b : l.Labels × r.Labels,
          l.weight b.1 * r.weight b.2 *
            answerSign (if x i then (r.booleanTree b.2).eval x
              else (l.booleanTree b.1).eval x)
      rw [Fintype.sum_prod_type]
      cases h : x i
      · simp only [Bool.false_eq_true, ↓reduceIte]
        calc
          l.eval x = ∑ b : l.Labels, l.weight b *
              answerSign ((l.booleanTree b).eval x) := ihl
          _ = _ := by
            apply sum_congr rfl
            intro b _
            rw [show (∑ c : r.Labels,
                l.weight b * r.weight c * answerSign ((l.booleanTree b).eval x)) =
                (l.weight b * answerSign ((l.booleanTree b).eval x)) *
                  ∑ c : r.Labels, r.weight c by
                rw [mul_sum]
                apply sum_congr rfl
                intro c _
                ring, sum_weight, mul_one]
      · simp only [↓reduceIte]
        calc
          r.eval x = ∑ c : r.Labels, r.weight c *
              answerSign ((r.booleanTree c).eval x) := ihr
          _ = _ := by
            simp_rw [mul_assoc, ← mul_sum]
            rw [← sum_mul, sum_weight, one_mul]

theorem abs_eval_le_one (T : RealQueryTree ι) (hT : T.Bounded) (x : BitInput ι) :
    |T.eval x| ≤ 1 := by
  induction T with
  | leaf a => exact hT
  | query i l r ihl ihr =>
      simp only [eval]
      split
      · exact ihr hT.2
      · exact ihl hT.1

/-- Transfer any uniform bound for a real linear functional, without a loss
in the bound or an extra query. -/
theorem linear_bound (T : RealQueryTree ι) (hT : T.Bounded)
    (F : ((BitInput ι) → ℝ) →ₗ[ℝ] ℝ) {B : ℝ}
    (hB : ∀ S : QueryTree ι, S.depth ≤ T.depth →
      |F (fun x => answerSign (S.eval x))| ≤ B) :
    |F T.eval| ≤ B := by
  classical
  have he : T.eval = ∑ b : T.Labels,
      T.weight b • (fun x => answerSign ((T.booleanTree b).eval x)) := by
    funext x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using T.eval_eq_convex_sum x
  rw [he, map_sum]
  calc
    |∑ b : T.Labels, F (T.weight b • (fun x => answerSign ((T.booleanTree b).eval x)))|
        ≤ ∑ b : T.Labels,
          |F (T.weight b • (fun x => answerSign ((T.booleanTree b).eval x)))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : T.Labels, T.weight b * B := by
      apply sum_le_sum
      intro b _
      rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (T.weight_nonneg hT b)]
      exact mul_le_mul_of_nonneg_left
        (hB (T.booleanTree b) (by rw [T.booleanTree_depth b])) (T.weight_nonneg hT b)
    _ = B := by rw [← sum_mul, sum_weight, one_mul]

/-- The same extension for a finite sum of absolute linear functionals.
This form transfers the derivative-growth estimate without a loss. -/
theorem sum_linear_bound {P : Type} [Fintype P]
    (T : RealQueryTree ι) (hT : T.Bounded)
    (F : P → ((BitInput ι) → ℝ) →ₗ[ℝ] ℝ) {B : ℝ}
    (hB : ∀ S : QueryTree ι, S.depth ≤ T.depth →
      (∑ p, |F p (fun x => answerSign (S.eval x))|) ≤ B) :
    (∑ p, |F p T.eval|) ≤ B := by
  classical
  have he : T.eval = ∑ b : T.Labels,
      T.weight b • (fun x => answerSign ((T.booleanTree b).eval x)) := by
    funext x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using T.eval_eq_convex_sum x
  calc
    (∑ p, |F p T.eval|) ≤ ∑ p, ∑ b : T.Labels,
        T.weight b * |F p (fun x => answerSign ((T.booleanTree b).eval x))| := by
      apply sum_le_sum
      intro p _
      rw [he, map_sum]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      apply sum_le_sum
      intro b _
      rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (T.weight_nonneg hT b)]
    _ = ∑ b : T.Labels, T.weight b *
        ∑ p, |F p (fun x => answerSign ((T.booleanTree b).eval x))| := by
      rw [sum_comm]
      simp only [mul_sum]
    _ ≤ ∑ b : T.Labels, T.weight b * B := by
      apply sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left
        (hB (T.booleanTree b) (by rw [T.booleanTree_depth b])) (T.weight_nonneg hT b)
    _ = B := by rw [← sum_mul, sum_weight, one_mul]

end RealQueryTree
end QuarticQuery.ForrelationLower
