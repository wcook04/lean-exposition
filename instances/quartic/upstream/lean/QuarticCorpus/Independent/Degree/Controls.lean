module

public import QuarticCorpus.Independent.Degree.Spec

/-! Independent literal expectations that discriminate a normalized evaluator,
omission of the empty monomial, the sign basis substituted for the bit basis,
and characteristic-two arithmetic substituted for real arithmetic. -/

@[expose] public section

namespace QuarticQuery.Independent.Degree

open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem empty_coefficient_is_value_at_zero (a : Finset ι → ℝ) :
    evaluate a (fun _ => false) = a ∅ := by
  have he : indicatorInput (∅ : Finset ι) = (fun _ => false) := by
    funext i
    simp [indicatorInput]
  rw [← he, evaluate_indicator]
  simp

theorem constant_one_expectation :
    Represents (fun S : Finset ι => if S = ∅ then 1 else 0) (fun _ => 1) := by
  intro x
  rw [evaluate_single, squarefreeMonomial_empty]

theorem projection_expectation (i : ι) :
    Represents (fun S : Finset ι => if S = {i} then 1 else 0)
      (fun x => if x i then 1 else 0) := by
  intro x
  rw [evaluate_single]
  simp [squarefreeMonomial, bit]

def xorCoefficients (S : Finset (Fin 2)) : ℝ :=
  (if S = {0} then 1 else 0) + (if S = {1} then 1 else 0) +
    (-2) * (if S = Finset.univ then 1 else 0)

theorem two_bit_xor_expectation :
    Represents xorCoefficients (fun x => if Bool.xor (x 0) (x 1) then 1 else 0) := by
  intro x
  change evaluate
    (fun S => ((if S = {0} then 1 else 0) + (if S = {1} then 1 else 0)) +
      (-2) * (if S = Finset.univ then 1 else 0)) x = _
  rw [evaluate_add, evaluate_add, evaluate_smul, evaluate_single,
    evaluate_single, evaluate_single]
  simp only [squarefreeMonomial, Finset.prod_singleton, Fin.prod_univ_two]
  cases h0 : x 0 <;> cases h1 : x 1 <;> norm_num [bit, h0, h1]

end QuarticQuery.Independent.Degree
