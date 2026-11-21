/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.ThreeColorMatrixSource

/-!
# Arithmetic indexing of the OR-to-NAE clause split

One private variable and two NAE clauses are added per ternary OR clause. The
numeric literal decoder is a fixed arithmetic expression with source literal
lookup; its indices agree with explicit sum and product codecs.
-/

namespace PCP.Reduction.ThreeSATNumericClauses

open NAEThreeColor ThreeColorNumericAdjacency

variable {v c : ℕ}

def clauseCode (c : ℕ) : Fin c × Bool ≃ Fin (c * 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin c)) ThreeSATGraphEncoding.boolCode).trans finProdFinEquiv

def indexed (Q : Fin c → Fin 3 → Literal (Fin v)) :
    Fin (c * 2) → Fin 3 → Literal (Fin (v + c)) := fun e i =>
  ThreeSATToColor.mapLiteral finSumFinEquiv
    (ThreeSATToColor.splitClauses Q ((clauseCode c).symm e) i)

/-- Source literal addresses are unchanged when source variables are embedded first. -/
theorem source_address (l : Literal (Fin v)) :
    literalAddress (ThreeSATToColor.mapLiteral (finSumFinEquiv : Fin v ⊕ Fin c ≃ Fin (v + c))
      (ThreeSATToColor.mapLiteral Sum.inl l)) = literalAddress l := by
  cases l <;> rfl

/-- The natural-index split decoder, independent of finite-type casts. -/
def address (v : ℕ) (lookup : ℕ → ℕ → ℕ) (e i : ℕ) : ℕ :=
  if e % 2 = 0 then
    if i < 2 then lookup (e / 2) i else 3 + 2 * (v + e / 2)
  else if i = 0 then 3 + (2 * (v + e / 2) + 1) else
    if i = 1 then lookup (e / 2) 2 else 0

theorem clauseCode_val (e : Fin c) (b : Bool) :
    (clauseCode c (e, b)).val = 2 * e.val + b.toNat := by
  cases b <;> simp [clauseCode, ThreeSATGraphEncoding.boolCode, finProdFinEquiv]
  omega

theorem address_correct (Q : Fin c → Fin 3 → Literal (Fin v)) (lookup : ℕ → ℕ → ℕ)
    (hl : ∀ e i, lookup e.val i.val = literalAddress (Q e i)) (e : Fin (c * 2)) (i : Fin 3) :
    address v lookup e.val i.val = literalAddress (indexed Q e i) := by
  obtain ⟨⟨e, b⟩, rfl⟩ := (clauseCode c).surjective e
  simp only [indexed, Equiv.symm_apply_apply, clauseCode_val]
  have hd (b : Bool) : (2 * e.val + b.toNat) / 2 = e.val := by
    cases b <;> simp
    omega
  have hm (b : Bool) : (2 * e.val + b.toNat) % 2 = b.toNat := by
    cases b <;> simp
  unfold address
  rw [hd, hm]
  have h0 : lookup e.val 0 = literalAddress (Q e 0) := hl e 0
  have h1 : lookup e.val 1 = literalAddress (Q e 1) := hl e 1
  have h2 : lookup e.val 2 = literalAddress (Q e 2) := hl e 2
  cases b <;> fin_cases i <;>
    simp only [ThreeSATToColor.splitClauses, Bool.toNat_false, Bool.toNat_true,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, source_address,
      reduceIte, Nat.reduceLT, Nat.reduceEqDiff, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue, h0, h1, h2] <;> rfl

/-- Numeric reindexing preserves the split formula's satisfiability. -/
theorem satisfiable_iff (Q : Fin c → Fin 3 → Literal (Fin v)) :
    (∃ a : Fin (v + c) → Bool, ∀ e, NAE (fun i => (indexed Q e i).eval a)) ↔
      ∃ a : Fin v → Bool, ThreeSATToColor.Satisfies Q a := by
  rw [← ThreeSATToColor.splitClauses_satisfiable_iff Q]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a ∘ finSumFinEquiv, fun e => ?_⟩
    simpa only [indexed, Equiv.symm_apply_apply, ThreeSATToColor.eval_mapLiteral]
      using ha (clauseCode c e)
  · rintro ⟨a, ha⟩
    refine ⟨a ∘ finSumFinEquiv.symm, fun e => ?_⟩
    simpa only [indexed, ThreeSATToColor.eval_mapLiteral, Function.comp_def,
      Equiv.symm_apply_apply] using ha ((clauseCode c).symm e)

/-- The concrete matrix program on the generated NAE table decides the original SAT instance. -/
theorem decoded_colorable_iff (Q : Fin c → Fin 3 → Literal (Fin v)) :
    (Algebraic.ThreeColorEncoding.graph
      (Algebraic.ThreeColorEncoding.encode
        (ThreeColorNumericAdjacency.indexedGraph (indexed Q)))).Colorable 3 ↔
      ∃ a, ThreeSATToColor.Satisfies Q a := by
  rw [Algebraic.ThreeColorEncoding.decode_encode_colorable_iff]
  have hi : NAEThreeColor.graph (indexed Q) ≃g
      ThreeColorNumericAdjacency.indexedGraph (indexed Q) :=
    { toEquiv := ThreeSATGraphEncoding.vertexCode (Equiv.refl _) (Equiv.refl _)
      map_rel_iff' := by intro a b; simp [ThreeColorNumericAdjacency.indexedGraph] }
  exact (SimpleGraph.colorable_congr hi).symm.trans
    ((NAEThreeColor.colorable_iff _).trans (satisfiable_iff Q))

end PCP.Reduction.ThreeSATNumericClauses
