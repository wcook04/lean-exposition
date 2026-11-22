/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ArithmeticExpressionLang
import PCP.Reduction.ThreeColorNumericAdjacency

/-!
# An actual arithmetic program for gadget adjacency

The five inputs are the number of variables, two vertex addresses, and the two
already decoded clause-literal addresses. The generated loop-free program uses
only ordinary language instructions, preserves its inputs, and restores its
scratch list. Its semantics is the exact symmetrized gadget adjacency test.
-/

set_option maxRecDepth 10000

namespace PCP.Reduction.ThreeColorAdjacencyLang

open PCP.Lang PCP.Lang.ArithmeticExpression

private def eqt {n : ℕ} (a b : Term n) := Term.bin .eq a b
private def ltt {n : ℕ} (a b : Term n) := Term.bin .lt a b
private def net {n : ℕ} (a b : Term n) := Term.cond (eqt a b) (.const 0) (.const 1)
private def andt {n : ℕ} (a b : Term n) := Term.bin .mul a b
private def ort {n : ℕ} (a b : Term n) := Term.cond a (.const 1) b

private theorem eqt_eval {n : ℕ} (r : Fin n → ℕ) (a b : Term n) :
    (eqt a b).eval r = (decide (a.eval r = b.eval r)).toNat := by
  simp [eqt, Term.eval, Op.eval, Bool.toNat]

private theorem ltt_eval {n : ℕ} (r : Fin n → ℕ) (a b : Term n) :
    (ltt a b).eval r = (decide (a.eval r < b.eval r)).toNat := by
  simp [ltt, Term.eval, Op.eval, Bool.toNat]

private theorem net_eval {n : ℕ} (r : Fin n → ℕ) (a b : Term n) :
    (net a b).eval r = (decide (a.eval r ≠ b.eval r)).toNat := by
  by_cases h : a.eval r = b.eval r <;> simp [net, eqt, Term.eval, Op.eval, h]

private theorem bool_mul (a b : Bool) : a.toNat * b.toNat = (a && b).toNat := by
  cases a <;> cases b <;> rfl

private theorem bool_ite (a b : Bool) : (if a.toNat ≠ 0 then 1 else b.toNat) = (a || b).toNat := by
  cases a <;> cases b <;> rfl

/-- One directed edge test, with its literal lookup value supplied explicitly. -/
def directValue (v literal u w : ℕ) : Bool :=
  ThreeColorNumericAdjacency.direct v (fun _ _ => literal) u w

/-- The arithmetic syntax of a directed edge test. -/
def directTerm {n : ℕ} (v literal u w : Term n) : Term n :=
  let cb := Term.bin .add (.const 3) (.bin .mul (.const 2) v)
  let ud := Term.bin .sub u (.const 3)
  let wd := Term.bin .sub w (.const 3)
  let uc := Term.bin .sub u cb
  let wc := Term.bin .sub w cb
  .cond (ltt u (.const 3))
    (andt (ltt w (.const 3)) (net u w))
    (.cond (ltt u cb)
      (.cond (ltt w (.const 3)) (eqt w (.const 2))
        (andt (ltt w cb) (andt (eqt (.bin .div ud (.const 2)) (.bin .div wd (.const 2)))
          (net (.bin .mod ud (.const 2)) (.bin .mod wd (.const 2))))))
      (.cond (ltt w cb) (eqt w literal)
        (andt (eqt (.bin .div uc (.const 3)) (.bin .div wc (.const 3)))
          (net (.bin .mod uc (.const 3)) (.bin .mod wc (.const 3))))))

private def directNat (v literal u w : ℕ) : ℕ :=
  let cb := 3 + 2 * v
  let eqn a b := if a = b then 1 else 0
  let ltn a b := if a < b then 1 else 0
  let nen a b := if eqn a b ≠ 0 then 0 else 1
  if ltn u 3 ≠ 0 then ltn w 3 * nen u w else
  if ltn u cb ≠ 0 then
    if ltn w 3 ≠ 0 then eqn w 2 else
      ltn w cb * (eqn ((u - 3) / 2) ((w - 3) / 2) * nen ((u - 3) % 2) ((w - 3) % 2))
  else if ltn w cb ≠ 0 then eqn w literal else
    eqn ((u - cb) / 3) ((w - cb) / 3) * nen ((u - cb) % 3) ((w - cb) % 3)

private theorem bit_nonzero (p : Prop) [Decidable p] :
    ((if p then 1 else 0) : ℕ) ≠ 0 ↔ p := by by_cases h : p <;> simp [h]

private theorem directNat_correct (v literal u w : ℕ) :
    directNat v literal u w = (directValue v literal u w).toNat := by
  simp only [directNat, bit_nonzero, directValue, ThreeColorNumericAdjacency.direct]
  split_ifs <;> simp_all [Bool.toNat] <;>
    simp_all only [← Nat.not_lt, decide_false, Bool.cond_false]


/-- Every arithmetic expression can supply the four directed-test inputs. -/
theorem directTerm_eval {n : ℕ} (r : Fin n → ℕ) (v literal u w : Term n) :
    (directTerm v literal u w).eval r =
      (directValue (v.eval r) (literal.eval r) (u.eval r) (w.eval r)).toNat := by
  change directNat (v.eval r) (literal.eval r) (u.eval r) (w.eval r) = _
  exact directNat_correct _ _ _ _


/-- Inputs are `v,u,w,literal(u),literal(w)` in that order. -/
def adjacencyTerm : Term 5 :=
  andt (net (.input 1) (.input 2))
    (ort (directTerm (.input 0) (.input 3) (.input 1) (.input 2))
      (directTerm (.input 0) (.input 4) (.input 2) (.input 1)))

def adjacencyValue (v u w lu lw : ℕ) : Bool :=
  decide (u ≠ w) && (directValue v lu u w || directValue v lw w u)

theorem adjacencyTerm_eval (r : Fin 5 → ℕ) :
    adjacencyTerm.eval r = (adjacencyValue (r 0) (r 1) (r 2) (r 3) (r 4)).toNat := by
  simp only [adjacencyTerm, andt, ort, Term.eval, Op.eval, net_eval, directTerm_eval,
    bool_ite, bool_mul, adjacencyValue]
  rfl

/-- A fixed program; its source size does not depend on graph size. -/
def code : Stmt 8 2 := scalar adjacencyTerm

set_option maxHeartbeats 2000000 in
-- Unfolding the fixed compiled syntax needs additional elaboration steps.
theorem code_spec (st : State 8 2) :
    (code.run st).1.regs (leftReg 5) =
      (adjacencyValue (st.regs 0) (st.regs 1) (st.regs 2) (st.regs 3) (st.regs 4)).toNat ∧
    (code.run st).1.lists 1 = st.lists 1 := by
  have h := scalar_spec adjacencyTerm st
  rw [adjacencyTerm_eval] at h
  exact h

theorem adjacencyValue_eq (v : ℕ) (literal : ℕ → ℕ → ℕ) (u w : ℕ) :
    adjacencyValue v u w
        (literal ((u - (3 + 2 * v)) / 3) ((u - (3 + 2 * v)) % 3))
        (literal ((w - (3 + 2 * v)) / 3) ((w - (3 + 2 * v)) % 3)) =
      ThreeColorNumericAdjacency.adjacency v literal u w := by
  simp [adjacencyValue, directValue, ThreeColorNumericAdjacency.adjacency,
    ThreeColorNumericAdjacency.direct]

set_option maxHeartbeats 2000000 in
-- The syntactic cost constant expands the complete compiled expression.
/-- The charged operational cost is bounded by a fixed constant times input bit size. -/
theorem code_cost (r : Fin 5 → ℕ) (W : ℕ) (hr : ∀ i, Nat.size (r i) ≤ W) :
    (code.run (inputState r)).2 ≤ code.C * (code.width + code.csize + 1) * (W + 1) :=
  scalar_cost adjacencyTerm r W hr

end PCP.Reduction.ThreeColorAdjacencyLang
