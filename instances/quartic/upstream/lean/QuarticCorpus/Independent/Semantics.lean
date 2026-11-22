module

public import QuarticQuery.Model.Classical

/-!
# Independently specified finite semantic expectations

Native validation: `research/adjudication/round3_formal.json`.

These tests import the actual project definitions. Their expected answers come
from the four finite examples in the assignment and the preprint conventions;
they do not import generated Challenges or `Forrelation.Sanity`.

Query units are individual input bits. The budget is the maximum depth of every
positive-weight tree, not an expected query count. Success is at least 2/3 on
each promised input. An algorithm is chosen before the input is quantified.
-/

@[expose] public section

set_option autoImplicit false

namespace QuarticQuery.SemanticReview

open scoped BigOperators

theorem zero_tree_same_answer {ι : Type} (T : QueryTree ι)
    (hT : T.depth ≤ 0) (x y : BitInput ι) : T.eval x = T.eval y := by
  cases T with
  | leaf b => rfl
  | query i l r =>
      change 1 + max l.depth r.depth ≤ 0 at hT
      omega

theorem zero_program_same_success {ι : Type} (A : RandomizedProgram ι)
    (hA : A.depth ≤ 0) (x y : BitInput ι) (b : Bool) :
    A.success x b = A.success y b := by
  unfold RandomizedProgram.success
  apply Finset.sum_congr rfl
  intro j hj
  have hT : (A.tree j).depth ≤ 0 :=
    (Finset.le_sup (f := fun j => (A.tree j).depth) (Finset.mem_univ j)).trans hA
  rw [zero_tree_same_answer (A.tree j) hT x y]

theorem success_masses_sum {ι : Type} (A : RandomizedProgram ι)
    (x : BitInput ι) : A.success x true + A.success x false = 1 := by
  unfold RandomizedProgram.success
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ j, A.weight j := by
      apply Finset.sum_congr rfl
      intro j hj
      cases h : (A.tree j).eval x <;> simp [h]
    _ = 1 := A.weight_sum

theorem both_labels_preclude_zero {ι : Type} (f : PartialBool ι)
    (x₀ x₁ : BitInput ι) (h₀ : f x₀ = some false) (h₁ : f x₁ = some true) :
    ¬ RLe f 0 := by
  rintro ⟨A, hA, hcorrect⟩
  have hfalse := hcorrect x₀ false h₀
  have htrue := hcorrect x₁ true h₁
  have hsame := zero_program_same_success A hA x₁ x₀ true
  rw [hsame] at htrue
  have hsum := success_masses_sum A x₀
  linarith

def oneBitIdentity : PartialBool (Fin 1) := fun x => some (x 0)

/-- Expected answer 1: a single input-independent zero-query distribution
cannot succeed on both labels at the inclusive 2/3 threshold. -/
theorem identity_not_zero : ¬ RLe oneBitIdentity 0 :=
  both_labels_preclude_zero oneBitIdentity (fun _ => false) (fun _ => true) rfl rfl

def readBit {ι : Type} (i : ι) : QueryTree ι :=
  .query i (.leaf false) (.leaf true)

def orTwo : PartialBool (Fin 2) := fun x => some (x 0 || x 1)

/-- The three coins are chosen independently of the input. The first tree is
constant true; the other two read the first and second input bit. -/
noncomputable def orMixture : RandomizedProgram (Fin 2) where
  size := 3
  weight _ := (1 / 3 : ℝ)
  tree j := if j = 0 then .leaf true else if j = 1 then readBit 0 else readBit 1
  weight_pos := by intro j; norm_num
  weight_sum := by norm_num [Fin.sum_univ_succ]

theorem orMixture_depth_le_one : orMixture.depth ≤ 1 := by
  change (Finset.univ.sup fun j : Fin 3 =>
    (if j = 0 then (.leaf true : QueryTree (Fin 2))
      else if j = 1 then readBit 0 else readBit 1).depth) ≤ 1
  apply Finset.sup_le
  intro j hj
  fin_cases j <;> norm_num [readBit, QueryTree.depth]

/-- Expected answers in input order 00, 01, 10, 11 are 2/3, 2/3, 2/3, 1. -/
theorem orMixture_success (x : BitInput (Fin 2)) :
    orMixture.success x (x 0 || x 1) =
      if x 0 && x 1 then (1 : ℝ) else 2 / 3 := by
  change (∑ j : Fin 3,
    if (if j = 0 then (.leaf true : QueryTree (Fin 2))
      else if j = 1 then readBit 0 else readBit 1).eval x = (x 0 || x 1)
    then (1 / 3 : ℝ) else 0) = _
  cases h₀ : x 0 <;> cases h₁ : x 1 <;>
    norm_num [readBit, QueryTree.eval, Fin.sum_univ_succ, h₀, h₁]

/-- Expected answer 2: the specified mixture computes OR with one worst-case
bit query; equality with the success threshold is allowed. -/
theorem orTwo_RLe_one : RLe orTwo 1 := by
  refine ⟨orMixture, orMixture_depth_le_one, ?_⟩
  intro x b hb
  change some (x 0 || x 1) = some b at hb
  have hlabel : (x 0 || x 1) = b := Option.some.inj hb
  rw [← hlabel, orMixture_success]
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> norm_num [h₀, h₁]

theorem orTwo_not_zero : ¬ RLe orTwo 0 :=
  both_labels_preclude_zero orTwo (fun _ => false) (fun _ => true) rfl rfl

theorem orTwo_R_eq_one : R orTwo = 1 := by
  have hlo : 0 < R orTwo := lt_R_of_not_RLe orTwo_not_zero
  have hhi : R orTwo ≤ 1 := R_le_of_RLe orTwo_RLe_one
  omega

def trueOnly : PartialBool (Fin 1) := fun x => if x 0 then some true else none

theorem trueOnly_label (x : BitInput (Fin 1)) (b : Bool)
    (hx : trueOnly x = some b) : b = true := by
  cases h : x 0 with
  | false => simp [trueOnly, h] at hx
  | true =>
      have heq : some true = (some b : Option Bool) := by simpa [trueOnly, h] using hx
      exact (Option.some.inj heq).symm

theorem trueOnly_false_is_unpromised : trueOnly (fun _ => false) = none := rfl

/-- Expected answer 3: correctness is required only when the input bit is true.
The constant-true leaf is a zero-query witness. -/
theorem trueOnly_RLe_zero : RLe trueOnly 0 := by
  refine ⟨RandomizedProgram.ofTree (.leaf true), by simp, ?_⟩
  intro x b hx
  rw [trueOnly_label x b hx, RandomizedProgram.success_ofTree]
  norm_num [QueryTree.eval]

theorem trueOnly_R_eq_zero : R trueOnly = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact R_le_of_RLe trueOnly_RLe_zero

theorem trueOnly_QLe_zero : QLe trueOnly 0 := by
  left
  exact ⟨true, trueOnly_label⟩

theorem trueOnly_Q_eq_zero : Q trueOnly = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.sInf_le trueOnly_QLe_zero

/-- The bit in position zero of each layer is true, hence has sign -1.
The remaining bits are false, hence have sign +1. -/
def negativePair : BitInput (ForrelationCoord 2 1) :=
  fun c => decide (c.2.val = 0)

theorem negativePair_numerator : forrelationNumerator 2 1 negativePair = -8 := by
  decide +kernel

theorem negativePair_denominator : forrelationDenominator 2 1 = 8 := by
  decide +kernel

/-- Expected answer 4a: two copies of (-1, 1, 1, 1) have Phi = -1. -/
theorem negativePair_Phi : Phi 2 1 negativePair = -1 := by
  rw [Phi, negativePair_numerator, negativePair_denominator]
  norm_num

/-- Expected answer 4b: the high promise uses Phi, not |Phi|. -/
theorem negativePair_P_none : P 2 1 negativePair = none := by
  decide +kernel

theorem negativePair_not_promised : ¬ promised (P 2 1) negativePair := by
  simp [promised, negativePair_P_none]

/-- An independent nonvacuity witness for the actual comparison predicate.
Adding an impossible field to that predicate would break this proof. -/
noncomputable def fairComparison (i j : Fin 2) : ℝ := if i = j then 0 else 1 / 2

theorem fairComparison_valid : Tournament.IsComparison fairComparison := by
  constructor
  · intro i j hij
    have hji : j ≠ i := Ne.symm hij
    norm_num [fairComparison, hij, hji]
  · intro i
    simp [fairComparison]

theorem comparison_has_witness :
    ∃ a : Fin 2 → Fin 2 → ℝ, Tournament.IsComparison a :=
  ⟨fairComparison, fairComparison_valid⟩

end QuarticQuery.SemanticReview
