module

public import Mathlib

/-!
# Independent squarefree polynomial semantics on the Boolean cube

This specification does not import QuarticQuery or complexitylib. A coefficient
array indexed by finite coordinate sets denotes the literal squarefree polynomial
`∑ S, a S * ∏ i ∈ S, x i`, with bits interpreted as real zero and one.
In particular, the empty monomial is one. These meanings are not aliases of
`BitString.monomial`, `lowDegree`, `totalDegree`, or a Fourier definition.

`coefficients_ext` proves uniqueness by evaluating at the indicator inputs of
all subsets and inducting on subset size. Its proof does not use polynomial
uniqueness from the audited development.
-/

@[expose] public section

namespace QuarticQuery.Independent.Degree

open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bit (b : Bool) : ℝ := if b then 1 else 0

def squarefreeMonomial (S : Finset ι) (x : ι → Bool) : ℝ :=
  ∏ i ∈ S, bit (x i)

noncomputable def evaluate (a : Finset ι → ℝ) (x : ι → Bool) : ℝ :=
  ∑ S, a S * squarefreeMonomial S x

def Represents (a : Finset ι → ℝ) (f : (ι → Bool) → ℝ) : Prop :=
  ∀ x, evaluate a x = f x

def CoefficientsAtMost (a : Finset ι → ℝ) (d : ℕ) : Prop :=
  ∀ S, d < S.card → a S = 0

def encode (useSigns : Bool) (b : Bool) : ℝ :=
  if useSigns then (if b then -1 else 1) else bit b

def signMonomial (S : Finset ι) (x : ι → Bool) : ℝ :=
  ∏ i ∈ S, encode true (x i)

noncomputable def signEvaluate (a : Finset ι → ℝ) (x : ι → Bool) : ℝ :=
  ∑ S, a S * signMonomial S x

def SignRepresents (a : Finset ι → ℝ) (f : (ι → Bool) → ℝ) : Prop :=
  ∀ x, signEvaluate a x = f x

noncomputable def evaluateWith (useSigns : Bool) (a : Finset ι → ℝ)
    (x : ι → Bool) : ℝ :=
  if useSigns then signEvaluate a x else evaluate a x

def RepresentsAs (inputSigns outputSigns : Bool) (a : Finset ι → ℝ)
    (f : (ι → Bool) → Bool) : Prop :=
  ∀ x, evaluateWith inputSigns a x = encode outputSigns (f x)

def indicatorInput (T : Finset ι) : ι → Bool := fun i => decide (i ∈ T)

@[simp] theorem squarefreeMonomial_empty (x : ι → Bool) :
    squarefreeMonomial (∅ : Finset ι) x = 1 := by
  simp [squarefreeMonomial]

theorem squarefreeMonomial_indicator (S T : Finset ι) :
    squarefreeMonomial S (indicatorInput T) = if S ⊆ T then 1 else 0 := by
  simp only [squarefreeMonomial, bit, indicatorInput, decide_eq_true_eq]
  rw [Finset.prod_boole]
  rfl

theorem evaluate_indicator (a : Finset ι → ℝ) (T : Finset ι) :
    evaluate a (indicatorInput T) = ∑ S ∈ T.powerset, a S := by
  classical
  simp only [evaluate, squarefreeMonomial_indicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext S
  simp

/-- Distinct squarefree coefficient arrays cannot agree on every Boolean input. -/
theorem coefficients_ext {a b : Finset ι → ℝ}
    (h : ∀ x, evaluate a x = evaluate b x) : a = b := by
  classical
  have hsum (S : Finset ι) :
      (∑ T ∈ S.powerset, a T) = ∑ T ∈ S.powerset, b T := by
    simpa only [evaluate_indicator] using h (indicatorInput S)
  have aux : ∀ m : ℕ, ∀ S : Finset ι, S.card < m → a S = b S := by
    intro m
    induction m with
    | zero => intro S hS; omega
    | succ m ih =>
      intro S hS
      by_cases hSm : S.card < m
      · exact ih S hSm
      · have hcard : S.card = m := by omega
        have hrest : (∑ T ∈ S.powerset.erase S, a T) =
            ∑ T ∈ S.powerset.erase S, b T := by
          apply Finset.sum_congr rfl
          intro T hT
          have hproper : T ⊂ S :=
            Finset.ssubset_iff_subset_ne.2
              ⟨Finset.mem_powerset.1 (Finset.mem_erase.1 hT).2,
                (Finset.mem_erase.1 hT).1⟩
          apply ih T
          simpa only [hcard] using Finset.card_lt_card hproper
        have hmem : S ∈ S.powerset := Finset.mem_powerset.2 (Finset.Subset.refl S)
        have ha := Finset.sum_erase_add (s := S.powerset) a hmem
        have hb := Finset.sum_erase_add (s := S.powerset) b hmem
        have ht := hsum S
        linarith
  funext S
  exact aux (S.card + 1) S (Nat.lt_succ_self _)

theorem represents_unique {f : (ι → Bool) → ℝ} {a b : Finset ι → ℝ}
    (ha : Represents a f) (hb : Represents b f) : a = b :=
  coefficients_ext fun x => (ha x).trans (hb x).symm

theorem evaluate_zero (x : ι → Bool) : evaluate (fun _ : Finset ι => 0) x = 0 := by
  simp [evaluate]

theorem evaluate_add (a b : Finset ι → ℝ) (x : ι → Bool) :
    evaluate (fun S => a S + b S) x = evaluate a x + evaluate b x := by
  simp [evaluate, add_mul, Finset.sum_add_distrib]

theorem evaluate_smul (c : ℝ) (a : Finset ι → ℝ) (x : ι → Bool) :
    evaluate (fun S => c * a S) x = c * evaluate a x := by
  simp [evaluate, mul_assoc, Finset.mul_sum]

theorem evaluate_single (S : Finset ι) (x : ι → Bool) :
    evaluate (fun T => if T = S then 1 else 0) x = squarefreeMonomial S x := by
  classical
  simp [evaluate]

end QuarticQuery.Independent.Degree
