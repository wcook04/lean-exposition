import PCP.Complexity.ReferenceNTMTapeTerms
import PCP.Complexity.ArithmeticFiniteLookup

/-!
# Arithmetic lookup of the fixed reference-machine transition table

A finite symbol tuple is inspected by a fixed case tree. Its leaves are genuine
finite state tables, so no transition-function oracle is present at runtime.
-/

namespace PCP.ReferenceNTM

open Complexity PCP.Lang.ArithmeticExpression

/-- A fixed four-way branch for one read symbol. -/
def symbolCase {n : ℕ} (key : Term n) (f : Γ → Term n) : Term n :=
  .iteEq key (.const 0) (f .blank)
    (.iteEq key (.const 1) (f .zero) (.iteEq key (.const 2) (f .one) (f .start)))

theorem eval_symbolCase {n : ℕ} (key : Term n) (f : Γ → Term n)
    (r : Fin n → ℕ) (s : Γ) (h : key.eval r = symbolCode s) :
    (symbolCase key f).eval r = (f s).eval r := by
  cases s <;> simp [symbolCase, Term.eval_iteEq, Term.eval, h, symbolCode]

/-- Unroll a fixed-length symbol vector into a finite expression tree. -/
def symbolTable {n : ℕ} : (m : ℕ) → ((Fin m → Γ) → Term n) →
    (Fin m → Term n) → Term n
  | 0, f, _ => f Fin.elim0
  | m + 1, f, keys => symbolCase (keys 0) fun a =>
      symbolTable m (fun tail => f (Fin.cons a tail)) (fun i => keys i.succ)

theorem eval_symbolTable {n : ℕ} (m : ℕ) (f : (Fin m → Γ) → Term n)
    (keys : Fin m → Term n) (r : Fin n → ℕ) (s : Fin m → Γ)
    (h : ∀ i, (keys i).eval r = symbolCode (s i)) :
    (symbolTable m f keys).eval r = (f s).eval r := by
  induction m with
  | zero =>
      have hs : s = Fin.elim0 := funext fun i => Fin.elim0 i
      simp only [symbolTable, hs]
  | succ m ih =>
      rw [symbolTable, eval_symbolCase _ _ _ _ (h 0)]
      rw [ih _ _ _ (fun i => h i.succ)]
      exact congrArg (fun v => (f v).eval r) (Fin.cons_self_tail s)

end PCP.ReferenceNTM
