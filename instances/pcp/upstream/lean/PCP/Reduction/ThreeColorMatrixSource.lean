/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.ThreeColorMatrixLang

/-!
# Typed clause tables for the concrete graph program

A finite NAE formula is stored in the numeric source-list format. Running the
fixed matrix program on this list produces exactly the graph bitstring belonging
to that formula, with an explicit polynomial operational-cost bound.
-/

namespace PCP.Reduction.ThreeColorMatrixSource

open PCP.Lang NAEThreeColor ThreeColorNumericAdjacency

variable {v c : ℕ}

/-- Fixed metadata followed by row-major literal vertex addresses. -/
def source (Q : Fin c → Fin 3 → Literal (Fin v)) : List ℕ :=
  v :: c :: List.ofFn (fun j : Fin (c * 3) =>
    literalAddress (Q (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2))

@[simp] theorem source_variableCount (Q : Fin c → Fin 3 → Literal (Fin v)) :
    ThreeColorMatrixLang.variableCount (source Q) = v := rfl

@[simp] theorem source_clauses (Q : Fin c → Fin 3 → Literal (Fin v)) :
    ThreeColorMatrixLang.clauses (source Q) = c := rfl

@[simp] theorem source_literal (Q : Fin c → Fin 3 → Literal (Fin v))
    (e : Fin c) (i : Fin 3) :
    ThreeColorMatrixLang.literal (source Q) e.val i.val = literalAddress (Q e i) := by
  have hi : 3 * e.val + i.val < c * 3 := by omega
  have hj : (⟨3 * e.val + i.val, hi⟩ : Fin (c * 3)) = finProdFinEquiv (e, i) := by
    ext
    simp [finProdFinEquiv]
    omega
  simp only [ThreeColorMatrixLang.literal, source, List.getD_eq_getElem?_getD]
  have he : 2 + (3 * e.val + i.val) = (3 * e.val + i.val) + 2 := by omega
  rw [he]
  simp only [List.getElem?_cons_succ, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some, hj,
    Equiv.symm_apply_apply]

/-- Numeric literal lookup need only be correct at actual clause positions. -/
theorem encode_eq_of_literal (Q : Fin c → Fin 3 → Literal (Fin v))
    (lookup : ℕ → ℕ → ℕ) (hlookup : ∀ e i, lookup e.val i.val = literalAddress (Q e i)) :
    encode v c lookup = Algebraic.ThreeColorEncoding.encode (indexedGraph Q) := by
  simp only [encode, Algebraic.ThreeColorEncoding.encode,
    Algebraic.ThreeColorEncoding.adjacencyBits]
  congr 2
  apply congrArg List.ofFn
  funext j
  apply Bool.eq_iff_iff.mpr
  let ec := ThreeSATGraphEncoding.vertexCode (Equiv.refl (Fin v)) (Equiv.refl (Fin c))
  let uw := finProdFinEquiv.symm j
  have h := adjacency_correct Q lookup hlookup (ec.symm uw.1) (ec.symm uw.2)
  simp only [address_code, ec, Equiv.apply_symm_apply] at h
  exact h.trans ⟨decide_eq_true, of_decide_eq_true⟩

/-- The actual fixed program outputs the exact verifier input bits for the typed formula. -/
theorem program_run (Q : Fin c → Fin 3 → Literal (Fin v)) :
    ThreeColorMatrixLang.program.run (source Q) =
      (Algebraic.ThreeColorEncoding.encode (indexedGraph Q)).map Bool.toNat := by
  rw [ThreeColorMatrixLang.program_run_encoding, source_variableCount, source_clauses,
    encode_eq_of_literal Q _ (source_literal Q)]

@[simp] theorem source_length (Q : Fin c → Fin 3 → Literal (Fin v)) :
    (source Q).length = 2 + c * 3 := by simp [source]; omega

theorem literalAddress_le (l : Literal (Fin v)) : literalAddress l ≤ 2 * v + 3 := by
  cases l with
  | const b => cases b <;> simp [literalAddress]
  | var i b => cases b <;> simp [literalAddress] <;> omega

theorem source_size_le (Q : Fin c → Fin 3 → Literal (Fin v)) :
    listSize (source Q) ≤ 10 * (v + c + 1) ^ 2 := by
  have hentry : ∀ j : Fin (c * 3),
      Nat.size (literalAddress (Q (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)) + 1 ≤
        2 * v + 4 := fun j => Nat.add_le_add_right
          ((size_le_self _).trans (literalAddress_le _)) 1
  have hsum := List.sum_le_length_nsmul (List.ofFn (fun j : Fin (c * 3) =>
    Nat.size (literalAddress (Q (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)) + 1))
      (2 * v + 4) (by simpa using hentry)
  have hv := size_le_self v
  have hc := size_le_self c
  simp only [List.length_ofFn, nsmul_eq_mul] at hsum
  simp only [source, listSize, List.map_cons, List.sum_cons, List.map_ofFn, Function.comp_def]
  nlinarith

/-- On typed formulas, construction cost is polynomial in variables plus clauses. -/
theorem program_cost : ∃ C : ℕ, ∀ (v c : ℕ) (Q : Fin c → Fin 3 → Literal (Fin v)),
    ThreeColorMatrixLang.program.cost (source Q) ≤ C * (v + c + 1) ^ 6 := by
  obtain ⟨C, hC⟩ := ThreeColorMatrixLang.program_cost
  refine ⟨C * 125000, fun v c Q => ?_⟩
  have hs := source_size_le Q
  have hn : ThreeColorMatrixLang.outputLength (source Q) =
      (3 + 2 * v + 3 * c) + 1 + (3 + 2 * v + 3 * c) ^ 2 := by
    simp [ThreeColorMatrixLang.outputLength, ThreeColorMatrixLang.vertices, pow_two]
  have hsmall : 3 + 2 * v + 3 * c ≤ 3 * (v + c + 1) := by omega
  have hsq := Nat.pow_le_pow_left hsmall 2
  have hlen : listSize (source Q) + ThreeColorMatrixLang.outputLength (source Q) + 2 ≤
      50 * (v + c + 1) ^ 2 := by rw [hn]; nlinarith
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hlen 3)
  calc
    _ ≤ C * (listSize (source Q) + ThreeColorMatrixLang.outputLength (source Q) + 2) ^ 3 := hC _
    _ ≤ C * (50 * (v + c + 1) ^ 2) ^ 3 := hp
    _ = _ := by ring

end PCP.Reduction.ThreeColorMatrixSource
