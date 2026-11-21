/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PolynomialLine
import PCP.Algebraic.PolynomialDistance
import Mathlib.LinearAlgebra.Lagrange

/-!
# Lagrange constraints on polynomial lines

The interpolation weights and identities used by the paper's generator
constraint. The algebraic identities are valid at any evaluation parameter;
the tester specializes the parameter to zero. The rejection-rate seed retains
an unused scalar for the existing finite random-bit encoding.
-/

namespace PCP.Algebraic.LagrangeConstraint

open Finset PolynomialLine

variable {F σ : Type*} [Field F] {c : ℕ} {a : Fin (c + 1) → F}

/-- Interpolate the `c+1` answers at the fixed field parameters. -/
noncomputable def interpolant (a : Fin (c + 1) → F) (f : (σ → F) → F)
    (u v : σ → F) : Polynomial F :=
  Lagrange.interpolate univ a (fun i => f (point u v (a i)))

/-- The Lagrange coefficient of the answer at node `a i`, evaluated at `t`. -/
noncomputable def weight (a : Fin (c + 1) → F) (t : F) (i : Fin (c + 1)) : F :=
  (Lagrange.basis univ a i).eval t

/-- Explicit Lagrange weights, with no division by a difference of coincident nodes
when the parameters are injective. -/
theorem weight_eq_prod (a : Fin (c + 1) → F) (t : F) (i : Fin (c + 1)) :
    weight a t i = ∏ j ∈ univ.erase i, (t - a j) / (a i - a j) := by
  simp only [weight, Lagrange.basis, Polynomial.eval_prod,
    Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, div_eq_mul_inv, mul_comm]

/-- Lagrange interpolation preserves constants at every parameter. -/
theorem sum_weight (ha : Function.Injective a) (t : F) : ∑ i, weight a t i = 1 := by
  simp only [weight, ← Polynomial.eval_finsetSum]
  rw [Lagrange.sum_basis ha.injOn ⟨0, mem_univ _⟩, Polynomial.eval_one]

/-- The interpolant is a formal polynomial of the promised degree. -/
theorem natDegree_interpolant_le (ha : Function.Injective a)
    (f : (σ → F) → F) (u v : σ → F) :
    (interpolant a f u v).natDegree ≤ c := by
  apply Polynomial.natDegree_le_of_degree_le
  simpa [interpolant] using
    Lagrange.degree_interpolate_le (s := univ) (fun i => f (point u v (a i))) ha.injOn

/-- Every queried anchor value is reproduced, even when the line direction is zero. -/
@[simp] theorem eval_interpolant_node (ha : Function.Injective a)
    (f : (σ → F) → F) (u v : σ → F) (i : Fin (c + 1)) :
    (interpolant a f u v).eval (a i) = f (point u v (a i)) := by
  exact Lagrange.eval_interpolate_at_node _ ha.injOn (mem_univ i)

/-- The field-valued identity that is translated into binary Hadamard queries. -/
theorem eval_interpolant_eq_sum (a : Fin (c + 1) → F)
    (f : (σ → F) → F) (u v : σ → F) (t : F) :
    (interpolant a f u v).eval t =
      ∑ i, weight a t i * f (point u v (a i)) := by
  simp only [interpolant, Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, weight, mul_comm]

/-- A bounded-degree polynomial matching the anchor answers is exactly the
constructed interpolant. This is a formal polynomial equality. -/
theorem interpolant_eq_of_eval (ha : Function.Injective a)
    (f : (σ → F) → F) (u v : σ → F) (p : Polynomial F)
    (hp : p.natDegree ≤ c)
    (heval : ∀ i, p.eval (a i) = f (point u v (a i))) :
    interpolant a f u v = p := by
  apply Eq.symm
  apply Lagrange.eq_interpolate_of_eval_eq _ ha.injOn
  · apply lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hp)
    simp only [card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_self c
  · intro i _
    exact heval i

/-- On a low-degree polynomial oracle, interpolation reconstructs its formal line
restriction, not just the values at the anchors. -/
theorem interpolant_eq_restrict (ha : Function.Injective a)
    (P : MvPolynomial σ F) (hP : P.totalDegree ≤ c) (u v : σ → F) :
    interpolant a (fun x => MvPolynomial.eval x P) u v = restrict u v P := by
  apply interpolant_eq_of_eval ha _ u v (restrict u v P)
    (natDegree_restrict_le_of_totalDegree_le u v P hP)
  intro i
  exact eval_restrict u v P (a i)

/-- Evaluation at an arbitrary field element, including zero, agrees for honest
polynomial oracles. -/
@[simp] theorem interpolant_eval (ha : Function.Injective a)
    (P : MvPolynomial σ F) (hP : P.totalDegree ≤ c) (u v : σ → F) (t : F) :
    (interpolant a (fun x => MvPolynomial.eval x P) u v).eval t =
      MvPolynomial.eval (point u v t) P := by
  rw [interpolant_eq_restrict ha P hP, eval_restrict]

/-- The generator check accepts precisely when this residual is zero. -/
noncomputable def check (a : Fin (c + 1) → F) (f : (σ → F) → F)
    (u v : σ → F) (t : F) : F :=
  f (point u v t) - (interpolant a f u v).eval t

theorem check_eq_zero_iff (a : Fin (c + 1) → F) (f : (σ → F) → F)
    (u v : σ → F) (t : F) :
    check a f u v t = 0 ↔ f (point u v t) = (interpolant a f u v).eval t :=
  sub_eq_zero

/-- The weighted oracle identity defining the generator check. -/
theorem check_eq_sub_sum (a : Fin (c + 1) → F) (f : (σ → F) → F)
    (u v : σ → F) (t : F) :
    check a f u v t = f (point u v t) -
      ∑ i, weight a t i * f (point u v (a i)) := by
  rw [check, eval_interpolant_eq_sum]

/-- Perfect completeness, pointwise in all random choices. -/
@[simp] theorem check_eval (ha : Function.Injective a)
    (P : MvPolynomial σ F) (hP : P.totalDegree ≤ c) (u v : σ → F) (t : F) :
    check a (fun x => MvPolynomial.eval x P) u v t = 0 := by
  simp only [check, interpolant_eval ha P hP, sub_self]

/-- The actual oracle query occurrences, with the independently checked point first. -/
def queries (a : Fin (c + 1) → F) (u v : σ → F) (t : F) : List (σ → F) :=
  point u v t :: List.ofFn (fun i : Fin (c + 1) => point u v (a i))

@[simp] theorem queries_length (a : Fin (c + 1) → F) (u v : σ → F) (t : F) :
    (queries a u v t).length = c + 2 := by simp [queries]

theorem queries_length_le (a : Fin (c + 1) → F) (u v : σ → F) (t : F) :
    (queries a u v t).length ≤ c + 2 := by rw [queries_length]

/-- The check depends only on the answers to the stated queries. -/
theorem check_congr (a : Fin (c + 1) → F) (u v : σ → F) (t : F)
    (f g : (σ → F) → F) (h : ∀ x ∈ queries a u v t, f x = g x) :
    check a f u v t = check a g u v t := by
  rw [check_eq_sub_sum, check_eq_sub_sum, h _ (by simp [queries])]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [h _ (by simp only [queries, List.mem_cons, List.mem_ofFn]; exact Or.inr ⟨i, rfl⟩)]

section Finite

variable [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]

/-- Normalized rejection with an independent uniform parameter from all of `F`.  The check is
always made at `0`, so the parameter is unused; see the module header. -/
noncomputable def rejectionRate (a : Fin (c + 1) → F) (f : (σ → F) → F) : ℚ :=
  relativeDistance
    (fun s : ((σ → F) × (σ → F)) × F => check a f s.1.1 s.1.2 0)
    (fun _ => 0)

/-- The residual form is exactly the point-versus-line disagreement probability. -/
theorem rejectionRate_eq_relativeDistance (a : Fin (c + 1) → F) (f : (σ → F) → F) :
    rejectionRate a f = relativeDistance
      (fun s : ((σ → F) × (σ → F)) × F => f (point s.1.1 s.1.2 0))
      (fun s => (interpolant a f s.1.1 s.1.2).eval 0) := by
  simp only [rejectionRate, relativeDistance, hammingDist, check, sub_ne_zero]

theorem rejectionRate_nonneg (a : Fin (c + 1) → F) (f : (σ → F) → F) :
    0 ≤ rejectionRate a f := relativeDistance_nonneg _ _

theorem rejectionRate_le_one (a : Fin (c + 1) → F) (f : (σ → F) → F) :
    rejectionRate a f ≤ 1 := relativeDistance_le_one _ _

@[simp] theorem rejectionRate_eval (ha : Function.Injective a)
    (P : MvPolynomial σ F) (hP : P.totalDegree ≤ c) :
    rejectionRate a (fun x => MvPolynomial.eval x P) = 0 := by
  simp only [rejectionRate, check_eval ha P hP, relativeDistance_self]

/-- Completeness depends on the represented function, not its chosen polynomial. -/
theorem rejectionRate_eq_zero_of_isLowDegree {m : ℕ} (ha : Function.Injective a)
    (f : (Fin m → F) → F) (hf : IsLowDegree c f) : rejectionRate a f = 0 := by
  obtain ⟨P, hP, rfl⟩ := hf
  exact rejectionRate_eval ha P hP

end Finite

end PCP.Algebraic.LagrangeConstraint
