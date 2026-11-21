import PCP.Complexity.ArithmeticExpressionLang
import PCP.Complexity.LangRadixCodec
import PCP.Algebraic.ThreeColorQueryIndex

/-!
# Actual arithmetic programs for the eight physical proof-address constructors

Input registers hold the constructor tag, component cardinalities, and already
encoded tuple/coefficient payloads. The loop-free program computes the exact
production address, including all preceding table offsets.
-/

set_option maxRecDepth 4096

namespace PCP.Lang.QueryAddress

open ArithmeticExpression PCP.Algebraic
open ThreeColorVerifier ThreeColorQueryIndex

/-- Inputs: tag, vertex/pair/proper/inner cardinalities, label cardinalities,
first/second point codes, inner point code, and coefficient code. -/
def term : Term 11 :=
  let tag := Term.input 0
  let a := Term.input 1
  let b := Term.input 2
  let d := Term.input 3
  let i := Term.input 4
  let c1 := Term.input 5
  let c3 := Term.input 6
  let x := Term.input 7
  let y := Term.input 8
  let u := Term.input 9
  let z := Term.input 10
  let add := Term.bin .add
  let mul := Term.bin .mul
  let ac := mul a c3
  let bc := mul b c1
  let bd := mul b c3
  let dc := mul d c1
  let primary := add (add ac bc) (add bd dc)
  let inner := mul i c1
  let al := mul (mul a a) inner
  let bl := mul (mul b b) inner
  let line := fun cardinal => add (add z (mul c1 u)) (mul inner (add y (mul cardinal x)))
  let choose := fun k yes no => Term.cond (Term.bin .eq tag (.const k)) yes no
  choose 0 (add z (mul c3 x))
    (choose 1 (add ac (add z (mul c1 x)))
      (choose 2 (add (add ac bc) (add z (mul c3 x)))
        (choose 3 (add (add ac bc) (add bd (add z (mul c1 x))))
          (choose 4 (add primary (line a))
            (choose 5 (add primary (add al (line b)))
              (choose 6 (add primary (add (add al bl) (line b)))
                (add primary (add (add al bl) (add bl (line d))))))))))

variable {F : Type*} {q n m c t C1 C3 : ℕ}

/-- The exact stored numeric payload of each query constructor. -/
def inputs (eF : F ≃ Fin q) (e1 : BinaryPolynomialSpace.Coefficients t 1 ≃ Fin C1)
    (e3 : BinaryPolynomialSpace.Coefficients t 3 ≃ Fin C3) :
    Query F n m c t → Fin 11 → ℕ
  | .color x z => ![0, q^n, q^(n+n), q^((n+n)+(n+n)), q^(c*m), C1, C3,
      (vertexIndex eF n x).val, 0, 0, (e3 z).val]
  | .validCert x z => ![1, q^n, q^(n+n), q^((n+n)+(n+n)), q^(c*m), C1, C3,
      (pairIndex eF n x).val, 0, 0, (e1 z).val]
  | .difference x z => ![2, q^n, q^(n+n), q^((n+n)+(n+n)), q^(c*m), C1, C3,
      (pairIndex eF n x).val, 0, 0, (e3 z).val]
  | .properCert x z => ![3, q^n, q^(n+n), q^((n+n)+(n+n)), q^(c*m), C1, C3,
      (properIndex eF n x).val, 0, 0, (e1 z).val]
  | .colorLine uv x z => ![4, q^n, q^(n+n), q^((n+n)+(n+n)), q^(c*m), C1, C3,
      (vertexIndex eF n uv.1).val, (vertexIndex eF n uv.2).val,
      (innerIndex eF m c x).val, (e1 z).val]
  | .validLine uv x z => ![5, q^n, q^(n+n), q^((n+n)+(n+n)), q^(c*m), C1, C3,
      (pairIndex eF n uv.1).val, (pairIndex eF n uv.2).val,
      (innerIndex eF m c x).val, (e1 z).val]
  | .differenceLine uv x z => ![6, q^n, q^(n+n), q^((n+n)+(n+n)), q^(c*m), C1, C3,
      (pairIndex eF n uv.1).val, (pairIndex eF n uv.2).val,
      (innerIndex eF m c x).val, (e1 z).val]
  | .properLine uv x z => ![7, q^n, q^(n+n), q^((n+n)+(n+n)), q^(c*m), C1, C3,
      (properIndex eF n uv.1).val, (properIndex eF n uv.2).val,
      (innerIndex eF m c x).val, (e1 z).val]

/-- Constructor offsets and all payload radices match the named production address codec. -/
theorem term_eq (eF : F ≃ Fin q) (e1 : BinaryPolynomialSpace.Coefficients t 1 ≃ Fin C1)
    (e3 : BinaryPolynomialSpace.Coefficients t 3 ≃ Fin C3) (z : Query F n m c t) :
    term.eval (inputs eF e1 e3 z) = (ThreeColorQueryIndex.equiv eF e1 e3 z).val := by
  cases z <;> simp only [term, inputs, Term.eval, Op.eval, Matrix.cons_val_zero,
    ite_true, ite_false, Nat.reduceEqDiff, ne_eq]
  all_goals rfl

/-- Stored point coordinates use exactly the production finite-function address order. -/
theorem tupleIndex_value {σ : Type*} {d : ℕ} (eσ : σ ≃ Fin d) (eF : F ≃ Fin q)
    (x : σ → F) :
    (tupleIndex eσ eF x).val =
      RadixCodec.value q (List.ofFn (fun i => (eF (x (eσ.symm i))).val)) := by
  exact (RadixCodec.value_finFunction q d (fun i => eF (x (eσ.symm i)))).symm

/-- The finite program computes an address and restores its expression scratch stack. -/
def program : Stmt 14 2 := scalar term

theorem program_run (eF : F ≃ Fin q) (e1 : BinaryPolynomialSpace.Coefficients t 1 ≃ Fin C1)
    (e3 : BinaryPolynomialSpace.Coefficients t 3 ≃ Fin C3) (z : Query F n m c t) :
    (program.run (inputState (inputs eF e1 e3 z))).1.regs (leftReg 11) =
      (ThreeColorQueryIndex.equiv eF e1 e3 z).val := by
  rw [program, scalar_inputState, term_eq]

/-- The cost is linear in a bound on the stored component bit lengths. -/
theorem program_cost (r : Fin 11 → ℕ) (W : ℕ) (h : ∀ i, Nat.size (r i) ≤ W) :
    (program.run (inputState r)).2 ≤
      program.C * (program.width + program.csize + 1) * (W + 1) :=
  scalar_cost term r W h

end PCP.Lang.QueryAddress
