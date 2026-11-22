module

public import QuarticCorpus.Independent.Degree.Spec
public import Complexity.Computability.QueryComplexity.Degree

/-!
# Canonical degree equals the independent squarefree-polynomial degree

The bridge checks the project's imported degree against a separately authored
coefficient-array semantics. It uses complexitylib's maintained span definition
and interpolation existence theorem. Polynomial uniqueness is supplied by the
independent subset-evaluation argument in Spec, not assumed as a premise.

This is an additional semantic interface for corpus row `def-deg`. It does not
change the quartic theorem, its constants, or any fixed-parameter quantifiers.
-/

@[expose] public section

namespace QuarticQuery.Independent.Degree

open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem squarefreeMonomial_eq_canonical (S : Finset ι) :
    squarefreeMonomial S = Cslib.BitString.monomial ℝ S := rfl

/-- A low-degree span representation supplies an explicit coefficient array,
with every coefficient above the degree bound equal to zero. -/
theorem exists_coefficients_of_lowDegree {f : (ι → Bool) → ℝ} {d : ℕ}
    (hf : f ∈ Cslib.BitString.lowDegree ℝ ι d) :
    ∃ a : Finset ι → ℝ, Represents a f ∧ CoefficientsAtMost a d := by
  classical
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨S, hS, rfl⟩ := hg
    change S.card ≤ d at hS
    refine ⟨fun T => if T = S then 1 else 0, ?_, ?_⟩
    · intro x
      simpa only [squarefreeMonomial_eq_canonical] using evaluate_single S x
    · intro T hT
      have hne : T ≠ S := by
        intro h
        subst T
        omega
      simp [hne]
  | zero =>
    exact ⟨fun _ => 0, fun x => evaluate_zero x, fun _ _ => rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨a, ha, hda⟩ := hf
    obtain ⟨b, hb, hdb⟩ := hg
    refine ⟨fun S => a S + b S, ?_, ?_⟩
    · intro x
      rw [evaluate_add, ha x, hb x]
      rfl
    · intro S hS
      change a S + b S = 0
      rw [hda S hS, hdb S hS, add_zero]
  | smul c f _ hf =>
    obtain ⟨a, ha, hda⟩ := hf
    refine ⟨fun S => c * a S, ?_, ?_⟩
    · intro x
      rw [evaluate_smul, ha x]
      rfl
    · intro S hS
      change c * a S = 0
      rw [hda S hS, mul_zero]

theorem lowDegree_of_coefficients {a : Finset ι → ℝ} {f : (ι → Bool) → ℝ} {d : ℕ}
    (ha : Represents a f) (hd : CoefficientsAtMost a d) :
    f ∈ Cslib.BitString.lowDegree ℝ ι d := by
  classical
  have hfun : f = ∑ S, a S • Cslib.BitString.monomial ℝ S := by
    funext x
    simpa only [evaluate, squarefreeMonomial_eq_canonical, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using (ha x).symm
  rw [hfun]
  apply Submodule.sum_mem
  intro S _
  by_cases hS : S.card ≤ d
  · exact Submodule.smul_mem _ _ (Cslib.BitString.monomial_mem_lowDegree hS)
  · rw [hd S (Nat.lt_of_not_ge hS), zero_smul]
    exact Submodule.zero_mem _

/-- Every real function on a finite Boolean cube has exactly one squarefree
real coefficient array. The empty cube and the zero function are included. -/
theorem exists_unique_coefficients (f : (ι → Bool) → ℝ) :
    ∃! a : Finset ι → ℝ, Represents a f := by
  obtain ⟨a, ha, _⟩ :=
    exists_coefficients_of_lowDegree (Cslib.BitString.mem_lowDegree_self f)
  exact ⟨a, ha, fun b hb => represents_unique hb ha⟩

/-- Exact total-degree characterization for any real function represented by
the independent squarefree coefficient semantics. -/
theorem canonical_totalDegree_le_iff (f : (ι → Bool) → ℝ)
    (a : Finset ι → ℝ) (ha : Represents a f) (d : ℕ) :
    Cslib.BitString.totalDegree f ≤ d ↔ CoefficientsAtMost a d := by
  rw [Cslib.BitString.totalDegree_le_iff_mem_lowDegree]
  constructor
  · intro hf
    obtain ⟨b, hb, hdb⟩ := exists_coefficients_of_lowDegree hf
    have hab := represents_unique ha hb
    simpa only [hab] using hdb
  · exact lowDegree_of_coefficients ha

/-- Exact degree characterization for any coefficient array representing a
Boolean function. No representation-existence or uniqueness premise is hidden. -/
theorem canonical_degree_le_iff {n : ℕ} (f : (Fin n → Bool) → Bool)
    (a : Finset (Fin n) → ℝ) (ha : Represents a (fun x => bit (f x))) (d : ℕ) :
    Cslib.QueryComplexity.degree f ≤ d ↔ CoefficientsAtMost a d :=
  canonical_totalDegree_le_iff (fun x => bit (f x)) a ha d

/-- Full independent polynomial meaning of the maintained degree: a unique
squarefree representation, whose nonzero support sizes characterize the degree. -/
theorem checked_degree {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∃ a : Finset (Fin n) → ℝ,
      Represents a (fun x => bit (f x)) ∧
      (∀ b : Finset (Fin n) → ℝ,
        Represents b (fun x => bit (f x)) → b = a) ∧
      (∀ d : ℕ, Cslib.QueryComplexity.degree f ≤ d ↔ CoefficientsAtMost a d) := by
  obtain ⟨a, ha, hu⟩ := exists_unique_coefficients (fun x => bit (f x))
  exact ⟨a, ha, hu, canonical_degree_le_iff f a ha⟩

theorem signMonomial_eq_character (S : Finset ι) (x : ι → Bool) :
    signMonomial S x = Cslib.BitString.chi ℝ S x := by
  rw [Cslib.BitString.chi_eq_prod_signVal]
  rfl

theorem sign_coefficients_eq_fourier {f : (ι → Bool) → ℝ}
    {a : Finset ι → ℝ} (ha : SignRepresents a f) :
    a = Cslib.BitString.fourierCoeff f := by
  have hfun : f = fun x => ∑ S, a S * Cslib.BitString.chi ℝ S x := by
    funext x
    simpa only [signEvaluate, signMonomial_eq_character] using (ha x).symm
  funext S
  rw [hfun, Cslib.BitString.fourierCoeff_sum_mul_chi]

theorem exists_unique_sign_coefficients (f : (ι → Bool) → ℝ) :
    ∃! a : Finset ι → ℝ, SignRepresents a f := by
  refine ⟨Cslib.BitString.fourierCoeff f, ?_, fun a ha => sign_coefficients_eq_fourier ha⟩
  intro x
  simpa only [signEvaluate, signMonomial_eq_character] using
    Cslib.BitString.sum_fourierCoeff_mul_chi f x

theorem canonical_totalDegree_sign_iff (f : (ι → Bool) → ℝ)
    (a : Finset ι → ℝ) (ha : SignRepresents a f) (d : ℕ) :
    Cslib.BitString.totalDegree f ≤ d ↔ CoefficientsAtMost a d := by
  rw [Cslib.BitString.totalDegree_le_iff_fourierCoeff_eq_zero,
    sign_coefficients_eq_fourier ha]
  rfl

theorem degree_eq_totalDegree_encode {n : ℕ} (f : (Fin n → Bool) → Bool)
    (outputSigns : Bool) :
    Cslib.QueryComplexity.degree f =
      Cslib.BitString.totalDegree (fun x => encode outputSigns (f x)) := by
  cases outputSigns with
  | false => rfl
  | true => exact Cslib.QueryComplexity.degree_eq_totalDegree_signVal f

/-- Complete `def-deg` meaning: for all four choices of bit/sign input and
output conventions, there is a unique real multilinear coefficient array, and
the largest cardinality of its nonzero supports is the same canonical degree.
Natural degree zero is used for the zero polynomial and every constant. -/
theorem checked_degree_conventions {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∀ inputSigns outputSigns : Bool,
      ∃ a : Finset (Fin n) → ℝ,
        RepresentsAs inputSigns outputSigns a f ∧
        (∀ b : Finset (Fin n) → ℝ,
          RepresentsAs inputSigns outputSigns b f → b = a) ∧
        (∀ d : ℕ, Cslib.QueryComplexity.degree f ≤ d ↔ CoefficientsAtMost a d) := by
  intro inputSigns outputSigns
  let g : (Fin n → Bool) → ℝ := fun x => encode outputSigns (f x)
  have hdeg : Cslib.QueryComplexity.degree f = Cslib.BitString.totalDegree g :=
    degree_eq_totalDegree_encode f outputSigns
  cases inputSigns with
  | false =>
    obtain ⟨a, ha, hu⟩ := exists_unique_coefficients g
    refine ⟨a, ha, hu, fun d => ?_⟩
    rw [hdeg]
    exact canonical_totalDegree_le_iff g a ha d
  | true =>
    obtain ⟨a, ha, hu⟩ := exists_unique_sign_coefficients g
    refine ⟨a, ha, hu, fun d => ?_⟩
    rw [hdeg]
    exact canonical_totalDegree_sign_iff g a ha d

end QuarticQuery.Independent.Degree
