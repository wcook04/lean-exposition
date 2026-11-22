/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.List.FinRange

/-!
# Bounded search for primitive roots of prime order

Search the explicit numeric field order given by an equivalence with `Fin q`.
For a prime order `p`, the finite predicate `z^p = 1 ∧ z ≠ 1` characterizes
primitive roots. The search returns `none` exactly when this predicate has no
solution. Its totalized version returns zero in that case.

The definitions are computable relative to the supplied field operations,
equality decision and enumeration. This file proves the search semantics for
those generic inputs. The production three-color verifier supplies concrete
inputs and certifies the resulting search as part of
`PCP.Lang.ThreeColorRuntime.polyTimeAlg`.
-/

namespace PCP.Algebraic.FiniteRootSearch

variable {F : Type*} [Field F] [DecidableEq F] {q : ℕ}

/-- The finite predicate used for prime-order root search. -/
def Candidate (p : ℕ) (z : F) : Prop := z ^ p = 1 ∧ z ≠ 1

instance candidateDecidable (p : ℕ) (z : F) : Decidable (Candidate p z) :=
  inferInstanceAs (Decidable (z ^ p = 1 ∧ z ≠ 1))

/-- Inspect an explicitly supplied list of field indices from left to right. -/
def scan (e : F ≃ Fin q) (p : ℕ) : List (Fin q) → Option F
  | [] => none
  | i :: is => if Candidate p (e.symm i) then some (e.symm i) else scan e p is

/-- Inspect every field element once, in increasing numeric-code order. -/
def search (e : F ≃ Fin q) (p : ℕ) : Option F := scan e p (List.finRange q)

theorem scan_eq_none_iff (e : F ≃ Fin q) (p : ℕ) (is : List (Fin q)) :
    scan e p is = none ↔ ∀ i ∈ is, ¬ Candidate p (e.symm i) := by
  induction is with
  | nil => simp [scan]
  | cons i is ih =>
    by_cases h : Candidate p (e.symm i) <;> simp [scan, h, ih]

theorem scan_spec (e : F ≃ Fin q) (p : ℕ) (is : List (Fin q)) {z : F}
    (h : scan e p is = some z) : Candidate p z := by
  induction is with
  | nil => simp [scan] at h
  | cons i is ih =>
    by_cases hi : Candidate p (e.symm i)
    · have hz : e.symm i = z := by simpa [scan, hi] using h
      exact hz ▸ hi
    · exact ih (by simpa [scan, hi] using h)

/-- Failure has a precise specification, also when the numeric domain is empty. -/
theorem search_eq_none_iff (e : F ≃ Fin q) (p : ℕ) :
    search e p = none ↔ ∀ z : F, ¬ Candidate p z := by
  rw [search, scan_eq_none_iff]
  constructor
  · intro h z
    simpa using h (e z) (List.mem_finRange _)
  · intro h i _
    exact h (e.symm i)

theorem search_spec (e : F ≃ Fin q) (p : ℕ) {z : F}
    (h : search e p = some z) : Candidate p z := scan_spec e p _ h

/-- The fallback is used only when no nontrivial `p`-th root exists. -/
def root (e : F ≃ Fin q) (p : ℕ) : F := (search e p).getD 0

theorem root_eq_zero_of_no_candidate (e : F ≃ Fin q) (p : ℕ)
    (h : ∀ z : F, ¬ Candidate p z) : root e p = 0 := by
  simp [root, (search_eq_none_iff e p).mpr h]

/-- Existence ensures that the finite search's totalized output passes its predicate. -/
theorem root_candidate (e : F ≃ Fin q) (p : ℕ) (h : ∃ z : F, Candidate p z) :
    Candidate p (root e p) := by
  cases hs : search e p with
  | none =>
    obtain ⟨z, hz⟩ := h
    exact False.elim ((search_eq_none_iff e p).mp hs z hz)
  | some z =>
    simpa only [root, hs, Option.getD_some] using search_spec e p hs

omit [DecidableEq F] in
theorem candidate_iff_primitive {p : ℕ} (hp : p.Prime) (z : F) :
    Candidate p z ↔ IsPrimitiveRoot z p := by
  constructor
  · rintro ⟨hz, hne⟩
    exact isPrimitiveRoot_of_mem_nthRootsFinset hp
      ((Polynomial.mem_nthRootsFinset hp.pos (1 : F)).mpr hz) hne
  · intro hz
    exact ⟨hz.pow_eq_one, hz.ne_one hp.one_lt⟩

/-- A proved primitive-root existence theorem supplies the search's correctness. -/
theorem root_spec (e : F ≃ Fin q) {p : ℕ} (hp : p.Prime)
    (h : ∃ z : F, IsPrimitiveRoot z p) : IsPrimitiveRoot (root e p) p := by
  apply (candidate_iff_primitive hp _).mp
  exact root_candidate e p (h.imp fun z hz => (candidate_iff_primitive hp z).mpr hz)

end PCP.Algebraic.FiniteRootSearch
