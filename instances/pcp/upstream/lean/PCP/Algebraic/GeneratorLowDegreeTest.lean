/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.LagrangeConstraint
import PCP.Algebraic.PolynomialLineCharacterization
import PCP.Algebraic.WeightedConstraintSoundness
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The generator-based low-degree test

PCP-SOSA27, Fact 2.7 and Lemma 3.3. Interpolate at the consecutive nonzero
powers of a generator and check at zero. The weights are Lagrange evaluations,
including the constant-polynomial case.

Soundness requires only `2*c < |F|`, over any finite field. This is stronger than
the paper's Lemma 3.3, which assumes `q` is a power of two larger than `C*c^3`; the
rejection threshold `1/(2(c+2)^2)` and the distance bound `2δ` are the paper's.
-/

namespace PCP.Algebraic.GeneratorLowDegreeTest

open Finset PolynomialLine

variable {F σ : Type*} [Field F] {c : ℕ}

def nodes (c : ℕ) (ζ : F) (i : Fin (c + 1)) : F := ζ ^ (i.val + 1)

noncomputable def weights (c : ℕ) (ζ : F) : Fin (c + 1) → F :=
  LagrangeConstraint.weight (nodes c ζ) 0

/-- A supplied anchor table is exactly the paper's generator table. -/
def IsGeneratorNodes [Fintype F] (a : Fin (c + 1) → F) : Prop :=
  ∃ ζ : F, IsPrimitiveRoot ζ (Fintype.card F - 1) ∧ a = nodes c ζ

/-- A closed, non-strict rejection threshold convenient for downstream decoding. -/
def smallError (c : ℕ) : ℚ := 1 / (4 * (c + 2 : ℚ) ^ 2)

theorem smallError_pos (c : ℕ) : 0 < smallError c := by unfold smallError; positivity

theorem smallError_lt (c : ℕ) : smallError c < 1 / (2 * (c + 2 : ℚ) ^ 2) := by
  unfold smallError
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith [sq_pos_of_pos (show (0 : ℚ) < c + 2 by positivity)]

noncomputable def correct (c : ℕ) (ζ : F) (f : (σ → F) → F) (u v : σ → F) : F :=
  WeightedConstraint.predict (nodes c ζ) (weights c ζ) f u v

noncomputable def check (c : ℕ) (ζ : F) (f : (σ → F) → F) (u v : σ → F) : F :=
  f u - correct c ζ f u v

theorem check_eq_interpolation (ζ : F) (f : (σ → F) → F) (u v : σ → F) :
    check c ζ f u v = LagrangeConstraint.check (nodes c ζ) f u v 0 := by
  simp only [check, correct, WeightedConstraint.predict,
    LagrangeConstraint.check_eq_sub_sum, weights, point, zero_smul, add_zero]

/-- The center and the `c+1` generator positions are all the queried values. -/
def queries (c : ℕ) (ζ : F) (u v : σ → F) : List (σ → F) :=
  u :: List.ofFn (fun i : Fin (c + 1) => point u v (nodes c ζ i))

@[simp] theorem queries_length (ζ : F) (u v : σ → F) :
    (queries c ζ u v).length = c + 2 := by simp [queries]

theorem check_congr (ζ : F) (u v : σ → F) (f g : (σ → F) → F)
    (h : ∀ x ∈ queries c ζ u v, f x = g x) :
    check c ζ f u v = check c ζ g u v := by
  rw [check_eq_interpolation, check_eq_interpolation]
  apply LagrangeConstraint.check_congr
  simpa only [queries, LagrangeConstraint.queries, point_zero] using h

section Nodes

variable [Fintype F] {ζ : F}

theorem generator_ne_zero (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1)) : ζ ≠ 0 :=
  hζ.ne_zero (by have := Fintype.one_lt_card (α := F); omega)

theorem nodes_ne_zero (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1))
    (i : Fin (c + 1)) : nodes c ζ i ≠ 0 := pow_ne_zero _ (generator_ne_zero hζ)

theorem nodes_injective (hq : 2 * c < Fintype.card F)
    (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1)) : Function.Injective (nodes c ζ) := by
  intro i j hij
  have hcard := Fintype.one_lt_card (α := F)
  apply Fin.ext
  apply hζ.pow_inj (by omega : i.val < Fintype.card F - 1)
    (by omega : j.val < Fintype.card F - 1)
  exact mul_right_cancel₀ (generator_ne_zero hζ) (by simpa only [nodes, pow_succ] using hij)

theorem weights_ne_zero (hq : 2 * c < Fintype.card F)
    (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1)) (i : Fin (c + 1)) :
    weights c ζ i ≠ 0 := by
  classical
  rw [weights, LagrangeConstraint.weight_eq_prod]
  apply prod_ne_zero_iff.mpr
  intro j hj
  exact div_ne_zero (sub_ne_zero.mpr (nodes_ne_zero hζ j).symm)
    (sub_ne_zero.mpr ((nodes_injective hq hζ).ne (mem_erase.mp hj).1.symm))

/-- The noncentral weights sum to one, so with `η₀ = -1` and `0^0 = 1` the weighted sum of the
constant monomial vanishes. The forward direction of Fact 2.7 is proved through uniqueness of
Lagrange interpolation instead and does not use this identity; it is retained for
`PCP/Audit/GeneratorLowDegree.lean`. -/
theorem sum_weights (hq : 2 * c < Fintype.card F)
    (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1)) : ∑ i, weights c ζ i = 1 :=
  LagrangeConstraint.sum_weight (nodes_injective hq hζ) 0

end Nodes

private theorem eval_zero_eq_sum {a : Fin (c + 1) → F} (ha : Function.Injective a)
    (P : Polynomial F) (hP : P.natDegree ≤ c) :
    P.eval 0 = ∑ i, LagrangeConstraint.weight a 0 i * P.eval (a i) := by
  classical
  have hdeg : P.degree < (univ : Finset (Fin (c + 1))).card := by
    apply Polynomial.degree_le_natDegree.trans_lt
    simpa using (show (P.natDegree : WithBot ℕ) < ↑(c + 1) by
      exact_mod_cast (by omega : P.natDegree < c + 1))
  have he := congrArg (fun Q : Polynomial F => Q.eval 0) (Lagrange.eq_interpolate ha.injOn hdeg)
  simpa only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, LagrangeConstraint.weight, mul_comm] using he

theorem polynomial_predict {a : Fin (c + 1) → F} (ha : Function.Injective a)
    (P : Polynomial F) (hP : P.natDegree ≤ c) (u v : F) :
    P.eval u = WeightedConstraint.predict a (LagrangeConstraint.weight a 0) P.eval u v := by
  have hd : (Polynomial.C u + Polynomial.X * Polynomial.C v).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  have hp : (P.comp (Polynomial.C u + Polynomial.X * Polynomial.C v)).natDegree ≤ c :=
    Polynomial.natDegree_comp_le.trans
      ((Nat.mul_le_mul_left P.natDegree hd).trans (by simpa using hP))
  simpa only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, zero_mul, add_zero,
    WeightedConstraint.predict, smul_eq_mul] using
    eval_zero_eq_sum ha _ hp

section Characterization

variable [Fintype F] {ζ : F}

/-- Every finite field has the full multiplicative generator required by the test. -/
theorem exists_generator : ∃ ζ : F, IsPrimitiveRoot ζ (Fintype.card F - 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨g, IsPrimitiveRoot.coe_units_iff.mpr ?_⟩
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Nat.card_eq_fintype_card]

private theorem zero_of_constraints (hq : 2 * c < Fintype.card F)
    (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1)) (f : F → F)
    (h0 : f 0 = 0) (hnodes : ∀ i, f (nodes c ζ i) = 0)
    (hcheck : ∀ v, WeightedConstraint.predict (nodes c ζ) (weights c ζ) f 0 v = 0) :
    ∀ x, f x = 0 := by
  have hp : ∀ n : ℕ, 0 < n → f (ζ ^ n) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hbase : n ≤ c + 1
      · simpa only [nodes, Nat.sub_add_cancel hn] using hnodes ⟨n-1, by omega⟩
      · let r := n - (c + 1)
        have he := hcheck (ζ ^ r)
        have hs : WeightedConstraint.predict (nodes c ζ) (weights c ζ) f 0 (ζ ^ r) =
            weights c ζ (Fin.last c) * f (ζ ^ n) := by
          unfold WeightedConstraint.predict
          rw [sum_eq_single (Fin.last c)]
          · congr 2
            simp only [nodes, Fin.val_last, smul_eq_mul, zero_add, ← pow_add]
            congr 1
            dsimp [r]
            omega
          · intro i _ hi
            have hil : i.val < c := by
              have hine : i.val ≠ c := fun h => hi (Fin.ext h)
              omega
            have hz := ih (i.val + 1 + r) (by dsimp [r]; omega) (by omega)
            simp only [nodes, smul_eq_mul, zero_add, ← pow_add, hz, mul_zero]
          · simp
        rw [hs] at he
        exact (mul_eq_zero.mp he).resolve_left (weights_ne_zero hq hζ _)
  intro x
  by_cases hx : x = 0
  · simpa [hx] using h0
  let : NeZero (Fintype.card F - 1) := ⟨by have := Fintype.one_lt_card (α := F); omega⟩
  obtain ⟨n, _, hn⟩ := hζ.eq_pow_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one x hx)
  by_cases hn0 : n = 0
  · have hx1 : x = 1 := by simpa [hn0] using hn.symm
    rw [hx1, ← hζ.pow_eq_one]
    exact hp _ (NeZero.pos _)
  · rw [← hn]
    exact hp n (Nat.pos_of_ne_zero hn0)

theorem exists_univariate (hq : 2 * c < Fintype.card F)
    (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1)) (f : F → F)
    (hf : ∀ u v, f u = WeightedConstraint.predict (nodes c ζ) (weights c ζ) f u v) :
    ∃ P : Polynomial F, P.natDegree ≤ c ∧ ∀ x, P.eval x = f x := by
  let P := Lagrange.interpolate univ (nodes c ζ) (fun i => f (nodes c ζ i))
  have ha := nodes_injective hq hζ
  have hP : P.natDegree ≤ c := by
    apply Polynomial.natDegree_le_of_degree_le
    simpa [P] using Lagrange.degree_interpolate_le (s := univ)
      (fun i => f (nodes c ζ i)) ha.injOn
  have hnode (i) : P.eval (nodes c ζ i) = f (nodes c ζ i) :=
    Lagrange.eval_interpolate_at_node _ ha.injOn (mem_univ i)
  have he := zero_of_constraints hq hζ (fun x => f x - P.eval x) ?_ ?_ ?_
  · exact ⟨P, hP, fun x => (sub_eq_zero.mp (he x)).symm⟩
  · rw [sub_eq_zero, hf 0 1, polynomial_predict ha P hP 0 1]
    simp only [WeightedConstraint.predict, smul_eq_mul, mul_one, zero_add, weights, hnode]
  · intro i
    rw [hnode, sub_self]
  · intro v
    have hfp := hf 0 v
    have hpp := polynomial_predict ha P hP 0 v
    have h0 : f 0 = P.eval 0 := by
      rw [hf 0 1, polynomial_predict ha P hP 0 1]
      simp only [WeightedConstraint.predict, smul_eq_mul, mul_one, zero_add, weights, hnode]
    simp only [WeightedConstraint.predict, mul_sub, sum_sub_distrib]
    change WeightedConstraint.predict (nodes c ζ) (weights c ζ) f 0 v -
      WeightedConstraint.predict (nodes c ζ) (weights c ζ) P.eval 0 v = 0
    change P.eval 0 = WeightedConstraint.predict (nodes c ζ) (weights c ζ) P.eval 0 v at hpp
    rw [← hfp, ← hpp, h0, sub_self]

theorem exists_polynomial [Finite σ] (hq : 2 * c < Fintype.card F)
    (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1)) (f : (σ → F) → F)
    (hf : ∀ u v, f u = correct c ζ f u v) :
    ∃ P : MvPolynomial σ F, P.totalDegree ≤ c ∧ ∀ x, MvPolynomial.eval x P = f x := by
  apply PolynomialLine.exists_polynomial_of_hasLowDegreeLines_finite f hq
  intro u v
  apply exists_univariate hq hζ (fun t => f (point u v t))
  intro x y
  have he := hf (point u v x) (y • v)
  convert he using 1
  unfold correct WeightedConstraint.predict
  apply sum_congr rfl
  intro i _
  congr 2
  apply congrArg f
  funext j
  simp only [point, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem check_eval (hq : 2 * c < Fintype.card F)
    (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1))
    (P : MvPolynomial σ F) (hP : P.totalDegree ≤ c) (u v : σ → F) :
    check c ζ (fun x => MvPolynomial.eval x P) u v = 0 := by
  rw [check_eq_interpolation]
  exact LagrangeConstraint.check_eval (nodes_injective hq hζ) P hP u v 0

/-- Fact 2.7, for ordinary total degree, including constant polynomials. -/
theorem check_eq_zero_iff_exists_polynomial [Finite σ]
    (hq : 2 * c < Fintype.card F) (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1))
    (f : (σ → F) → F) :
    (∀ u v, check c ζ f u v = 0) ↔
      ∃ P : MvPolynomial σ F, P.totalDegree ≤ c ∧ ∀ x, MvPolynomial.eval x P = f x := by
  constructor
  · intro hf
    apply exists_polynomial hq hζ f
    intro u v
    exact sub_eq_zero.mp (hf u v)
  · rintro ⟨P, hP, he⟩ u v
    have hf : f = fun x => MvPolynomial.eval x P := funext (fun x => (he x).symm)
    rw [hf]
    exact check_eval hq hζ P hP u v

variable [DecidableEq F] [Fintype σ] [DecidableEq σ]

noncomputable def rejectionRate (c : ℕ) (ζ : F) (f : (σ → F) → F) : ℚ :=
  WeightedConstraint.rejectionRate (nodes c ζ) (weights c ζ) f

/-- Lemma 3.3 for the generator-weighted test, strengthened to the linear field-size
hypothesis `q > 2c` (the paper assumes `q > C*c^3`). -/
theorem exists_close (hq : 2 * c < Fintype.card F)
    (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1)) (f : (σ → F) → F)
    {δ : ℚ} (hrej : rejectionRate c ζ f ≤ δ) (hδ : δ < 1 / (2 * (c + 2 : ℚ) ^ 2)) :
    ∃ P : MvPolynomial σ F, P.totalDegree ≤ c ∧
      relativeDistance f (fun x => MvPolynomial.eval x P) ≤ 2 * δ := by
  let g := WeightedConstraint.correction (nodes c ζ) (weights c ζ) f
  have hpos : (0 : ℚ) < 2 * (c + 2 : ℚ) ^ 2 := by positivity
  have hsmall : (2 * (Fintype.card (Fin (c + 1)) : ℚ) + 3) *
      Fintype.card (Fin (c + 1)) * rejectionRate c ζ f < 1 := by
    have hnonneg : 0 ≤ rejectionRate c ζ f := relativeDistance_nonneg _ _
    have hbound := (lt_div_iff₀ hpos).mp (hrej.trans_lt hδ)
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    have hc : (0 : ℚ) ≤ c := Nat.cast_nonneg _
    nlinarith
  obtain ⟨P, hP, he⟩ := exists_polynomial hq hζ g
    (WeightedConstraint.correction_satisfies _ _ (nodes_ne_zero hζ) f hsmall)
  refine ⟨P, hP, ?_⟩
  have hd := WeightedConstraint.distance_correction_le (nodes c ζ) (weights c ζ) f
  simpa only [he] using hd.trans (mul_le_mul_of_nonneg_left hrej (by norm_num))

end Characterization
end PCP.Algebraic.GeneratorLowDegreeTest

namespace PCP.Algebraic.FixedLagrangeConstraint

variable {F σ : Type*} [Field F] {c : ℕ}

noncomputable def check (a : Fin (c + 1) → F) (f : (σ → F) → F)
    (u v : σ → F) : F := LagrangeConstraint.check a f u v 0

variable [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]

/-- An unused uniform scalar preserves the fixed-width seed encoding without changing rejection. -/
noncomputable def rejectionRate (a : Fin (c + 1) → F) (f : (σ → F) → F) : ℚ :=
  relativeDistance (fun s : ((σ → F) × (σ → F)) × F => check a f s.1.1 s.1.2)
    (fun _ => 0)

theorem rejectionRate_nodes (ζ : F) (f : (σ → F) → F) :
    rejectionRate (GeneratorLowDegreeTest.nodes c ζ) f =
      GeneratorLowDegreeTest.rejectionRate c ζ f := by
  rw [rejectionRate, relativeDistance_comp_fst
    (fun s : (σ → F) × (σ → F) => check (GeneratorLowDegreeTest.nodes c ζ) f s.1 s.2)
    (fun _ => 0)]
  simp only [check, ← GeneratorLowDegreeTest.check_eq_interpolation,
    GeneratorLowDegreeTest.check, GeneratorLowDegreeTest.correct,
    GeneratorLowDegreeTest.rejectionRate, WeightedConstraint.rejectionRate,
    relativeDistance, hammingDist, sub_ne_zero]

theorem exists_close (hq : 2 * c < Fintype.card F) {a : Fin (c + 1) → F}
    (ha : GeneratorLowDegreeTest.IsGeneratorNodes a) (f : (σ → F) → F)
    {δ : ℚ} (hrej : rejectionRate a f ≤ δ)
    (hδ : δ < 1 / (2 * (c + 2 : ℚ) ^ 2)) :
    ∃ P : MvPolynomial σ F, P.totalDegree ≤ c ∧
      relativeDistance f (fun x => MvPolynomial.eval x P) ≤ 2 * δ := by
  obtain ⟨ζ, hζ, rfl⟩ := ha
  rw [rejectionRate_nodes] at hrej
  exact GeneratorLowDegreeTest.exists_close hq hζ f hrej hδ

end PCP.Algebraic.FixedLagrangeConstraint
