/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ArithmeticLookupCost
import PCP.Complexity.LangTabulation
import PCP.Reduction.ThreeColorAdjacencyLang

/-!
# A concrete graph-matrix emission program

The source list contains the variable count, clause count, and a row-major table
of three literal-vertex addresses per NAE clause. One fixed program emits the
unary vertex header, separator, and row-major adjacency bits. Metadata is read
from the source on each kernel call, so no input-dependent program is selected.
-/

set_option maxRecDepth 10000

namespace PCP.Reduction.ThreeColorMatrixLang

open PCP.Lang PCP.Lang.ArithmeticExpression PCP.Lang.ArithmeticLookup


def variableCount (input : List ℕ) : ℕ := input.getD 0 0
def clauses (input : List ℕ) : ℕ := input.getD 1 0
def vertices (input : List ℕ) : ℕ := 3 + 2 * variableCount input + 3 * clauses input

def literal (input : List ℕ) (e i : ℕ) : ℕ := input.getD (2 + (3 * e + i)) 0

def value (input : List ℕ) (j : ℕ) : ℕ :=
  let N := vertices input
  if j < N then 1 else if j = N then 0 else
    (ThreeColorNumericAdjacency.adjacency (variableCount input) (literal input)
      ((j - (N + 1)) / N) ((j - (N + 1)) % N)).toNat

def outputLength (input : List ℕ) : ℕ := vertices input + 1 + vertices input * vertices input

def rowTerm : Term 10 :=
  .bin .div (.bin .sub (.input 0) (.bin .add (.input 5) (.const 1))) (.input 5)

def colTerm : Term 10 :=
  .bin .mod (.bin .sub (.input 0) (.bin .add (.input 5) (.const 1))) (.input 5)

def literalTerm (i : Fin 10) : Term 10 :=
  .bin .add (.const 2)
    (.bin .sub (.input i) (.bin .add (.const 3) (.bin .mul (.const 2) (.input 4))))

def answerTerm : Term 10 :=
  .cond (.bin .lt (.input 0) (.input 5)) (.const 1)
    (.cond (.bin .eq (.input 0) (.input 5)) (.const 0)
      (ThreeColorAdjacencyLang.adjacencyTerm.rename ![4, 6, 7, 8, 9]))

/-- All loops reside in the bounded list-read routines. -/
def beforeAnswer : Code 10 :=
  .seq (.lookup 4 (.const 0))
    (.seq (.lookup 5 (.const 1))
      (.seq (.assign 5 (.bin .add
        (.bin .add (.const 3) (.bin .mul (.const 2) (.input 4)))
        (.bin .mul (.const 3) (.input 5))))
        (.seq (.assign 6 rowTerm)
          (.seq (.assign 7 colTerm)
            (.seq (.lookup 8 (literalTerm 6))
              (.lookup 9 (literalTerm 7)))))))

private theorem literal_offset (input : List ℕ) (j : ℕ) :
    literal input (j / 3) (j % 3) = input.getD (2 + j) 0 := by
  simp only [literal]
  congr 1
  omega

@[irreducible] def kernelCode : Code 10 := .seq beforeAnswer (.assign 1 answerTerm)

def ready (input : List ℕ) (r : Fin 10 → ℕ) : Fin 10 → ℕ :=
  let N := vertices input
  let u := (r 0 - (N + 1)) / N
  let w := (r 0 - (N + 1)) % N
  ![r 0, r 1, r 2, r 3, variableCount input, N, u, w,
    input.getD (2 + (u - (3 + 2 * variableCount input))) 0,
    input.getD (2 + (w - (3 + 2 * variableCount input))) 0]


theorem beforeAnswer_eval (input : List ℕ) (r : Fin 10 → ℕ) :
    beforeAnswer.eval input r = ready input r := by
  funext i
  fin_cases i <;> simp [beforeAnswer, Code.eval, ready, rowTerm, colTerm, literalTerm,
    Term.eval, Op.eval, vertices, variableCount, clauses, Function.update]

theorem answerTerm_eval (input : List ℕ) (r : Fin 10 → ℕ) :
    answerTerm.eval (ready input r) = value input (r 0) := by
  have hadj := ThreeColorAdjacencyLang.adjacencyValue_eq (variableCount input) (literal input)
    ((r 0 - (vertices input + 1)) / vertices input)
    ((r 0 - (vertices input + 1)) % vertices input)
  rw [literal_offset, literal_offset] at hadj
  have hs : (ready input r ∘ ![4, 6, 7, 8, 9]) =
      ![variableCount input, ((r 0 - (vertices input + 1)) / vertices input),
        ((r 0 - (vertices input + 1)) % vertices input),
        input.getD (2 + ((r 0 - (vertices input + 1)) / vertices input -
          (3 + 2 * variableCount input))) 0,
        input.getD (2 + ((r 0 - (vertices input + 1)) % vertices input -
          (3 + 2 * variableCount input))) 0] := by
    funext i
    fin_cases i <;> rfl
  simp only [answerTerm, Term.eval, Term.eval_rename, hs,
    ThreeColorAdjacencyLang.adjacencyTerm_eval]
  change (if (if r 0 < vertices input then 1 else 0) ≠ 0 then 1 else
      if (if r 0 = vertices input then 1 else 0) ≠ 0 then 0 else
        (ThreeColorAdjacencyLang.adjacencyValue _ _ _ _ _).toNat) = _
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [hadj]
  by_cases hlt : r 0 < vertices input <;> by_cases heq : r 0 = vertices input <;>
    simp [value, hlt, heq]

/-- The fixed arithmetic/read computation returns the requested graph bit. -/
theorem kernelCode_eval (input : List ℕ) (r : Fin 10 → ℕ) :
    (kernelCode.eval input r) 0 = r 0 ∧
    (kernelCode.eval input r) 1 = value input (r 0) ∧
    (kernelCode.eval input r) 2 = r 2 ∧
    (kernelCode.eval input r) 3 = r 3 := by
  simp only [kernelCode, Code.eval, beforeAnswer_eval, answerTerm_eval]
  simp [Function.update, ready]

/-- Caller source slots used as scratch are cleared before the certified finite computation. -/
def reset : Stmt 14 3 :=
  .seq (.assign 1 (.const 0)) (.seq (.assign 4 (.const 0))
    (.seq (.assign 5 (.const 0)) (.seq (.assign 6 (.const 0))
      (.seq (.assign 7 (.const 0)) (.seq (.assign 8 (.const 0)) (.assign 9 (.const 0)))))))

def kernel : Stmt 14 3 := .seq reset kernelCode.compile

theorem reset_lists (st : State 14 3) : (reset.run st).1.lists = st.lists := by
  simp [reset, Stmt.run]

theorem reset_inputs (st : State 14 3) (i : Fin 10) :
    inputs (reset.run st).1 i = if i = 0 ∨ i = 2 ∨ i = 3 then inputs st i else 0 := by
  fin_cases i <;> simp [inputs, reset, Stmt.run, Expr.eval, Function.update]

theorem reset_cost (st : State 14 3) : (reset.run st).2 = 13 := by
  simp [reset, Stmt.run, Expr.eval, Expr.cost, Expr.readSize]

set_option maxHeartbeats 2000000 in
-- The fixed compiler term is large although its scalar semantics is already proved.
/-- The exact scalar contract required by the counted output loop. -/
theorem kernel_spec (input : List ℕ) :
    Tabulation.KernelSpec kernel input (outputLength input) (value input) := by
  intro st hs h2 h3 _
  simp only [kernel, run_seq_fst]
  have hc := kernelCode.spec (reset.run st).1
  have hl : (reset.run st).1.lists 0 = input := congrFun (reset_lists st) 0 |>.trans hs
  have hr := hc.1.trans (congrArg (fun l => kernelCode.eval l (inputs (reset.run st).1)) hl)
  have he := kernelCode_eval input (inputs (reset.run st).1)
  have h0 : inputs (reset.run st).1 0 = st.regs 0 := by
    rw [reset_inputs]
    simp [inputs]
  have htwo : inputs (reset.run st).1 2 = 1 := by
    rw [reset_inputs]
    simp [inputs, h2]
  have hthree : inputs (reset.run st).1 3 = outputLength input := by
    rw [reset_inputs]
    simp [inputs, h3]
  exact ⟨(congrFun hr 0).trans (he.1.trans h0),
    (congrFun hr 1).trans (he.2.1.trans (congrArg (value input) h0)),
    (congrFun hr 2).trans (he.2.2.1.trans htwo),
    (congrFun hr 3).trans (he.2.2.2.trans hthree),
    hc.2.1.trans hl, hc.2.2.trans (congrFun (reset_lists st) 1)⟩

/-- A uniform per-bit bound for the concrete kernel, with no oracle premise. -/
theorem kernel_cost : ∃ K : ℕ, ∀ input : List ℕ,
    Tabulation.KernelCost kernel input (outputLength input)
      (K * (listSize input + Nat.size (outputLength input) + 2) ^ 2) := by
  obtain ⟨K, hK, hcost⟩ := kernelCode.cost_bound
  refine ⟨K + 14, fun input st hs h2 h3 hj => ?_⟩
  let W := listSize input + Nat.size (outputLength input) + 1
  have hr : ∀ i : Fin 10, Nat.size (inputs (reset.run st).1 i) ≤ W := by
    intro i
    rw [reset_inputs]
    by_cases hi : i = 0 ∨ i = 2 ∨ i = 3
    · rcases hi with rfl | rfl | rfl
      · simp only [ite_true, true_or, eq_self, inputs]
        have h := Nat.size_le_size hj.le
        dsimp [W]
        exact h.trans (by omega)
      · simp [inputs, h2, W]
      · change Nat.size (st.regs 3) ≤ W
        rw [h3]
        dsimp [W]
        omega
    · simp [hi]
  have hl : listSize ((reset.run st).1.lists 0) ≤ W := by
    rw [reset_lists, hs]
    dsimp [W]
    omega
  have hc := (hcost (reset.run st).1 W hr hl).1
  simp only [kernel, run_seq_snd, reset_cost]
  dsimp [W] at hc
  have hq : 1 ≤ (listSize input + Nat.size (outputLength input) + 2) ^ 2 :=
    Nat.succ_le_of_lt (pow_pos (by omega) _)
  have heq : listSize input + Nat.size (outputLength input) + 1 + 1 =
      listSize input + Nat.size (outputLength input) + 2 := by omega
  rw [heq] at hc
  calc
    13 + (kernelCode.compile.run (reset.run st).1).2 + 1 ≤
        K * (listSize input + Nat.size (outputLength input) + 2) ^ 2 + 14 := by omega
    _ ≤ _ := by nlinarith

theorem value_size (input : List ℕ) (j : ℕ) : Nat.size (value input j) ≤ 1 := by
  apply size_le_one_of_le_one
  dsimp only [value]
  split_ifs <;> try decide
  cases ThreeColorNumericAdjacency.adjacency (variableCount input) (literal input)
    ((j - (vertices input + 1)) / vertices input) ((j - (vertices input + 1)) % vertices input)
    <;> decide

@[irreducible] def setupCode : Code 10 :=
  .seq (.lookup 4 (.const 0))
    (.seq (.lookup 5 (.const 1))
      (.seq (.assign 5 (.bin .add
        (.bin .add (.const 3) (.bin .mul (.const 2) (.input 4)))
        (.bin .mul (.const 3) (.input 5))))
        (.assign 3 (.bin .add (.bin .add (.input 5) (.const 1))
          (.bin .mul (.input 5) (.input 5))))))

theorem setupCode_eval (input : List ℕ) (r : Fin 10 → ℕ) :
    setupCode.eval input r 3 = outputLength input := by
  simp [setupCode, Code.eval, Term.eval, Op.eval, Function.update, outputLength,
    vertices, variableCount, clauses]

def program : Prog where
  R := 14
  Q := 3
  hQ := by decide
  body := .seq setupCode.compile (Tabulation.tabulate kernel)

/-- The executable program emits exactly the ordered scalar answers. -/
theorem program_run (input : List ℕ) :
    program.run input = (List.range (outputLength input)).map (value input) := by
  let initial : State 14 3 := ⟨fun _ => 0, fun L => if L = 0 then input else []⟩
  have hs := setupCode.spec initial
  have hreg := congrFun hs.1 3
  have hcount : (setupCode.compile.run initial).1.regs 3 = outputLength input :=
    hreg.trans (setupCode_eval input _)
  have h0 : (setupCode.compile.run initial).1.lists 0 = input := hs.2.1
  have h1 : (setupCode.compile.run initial).1.lists 1 = [] := hs.2.2
  have ht := (Tabulation.tabulate_spec (kernel_spec input)
    (setupCode.compile.run initial).1 h0 hcount h1).1
  exact ht

/-- The whole program has a polynomial bound in source size plus its actual output length. -/
theorem program_cost : ∃ C : ℕ, ∀ input : List ℕ,
    program.cost input ≤ C * (listSize input + outputLength input + 2) ^ 3 := by
  obtain ⟨A, _, ha⟩ := setupCode.cost_bound
  obtain ⟨B, hb⟩ := kernel_cost
  refine ⟨A + B + 30, fun input => ?_⟩
  let initial : State 14 3 := ⟨fun _ => 0, fun L => if L = 0 then input else []⟩
  let S := listSize input
  let L := outputLength input
  let M := S + L + 2
  have hinit : ∀ i : Fin 10, Nat.size (inputs initial i) ≤ S := by simp [inputs, initial]
  have hlist : listSize (initial.lists 0) ≤ S := by simp [initial, S]
  have hsetup := (ha initial S hinit hlist).1
  have hs := setupCode.spec initial
  have hcount : (setupCode.compile.run initial).1.regs 3 = L :=
    (congrFun hs.1 3).trans (setupCode_eval input _)
  have h0 : (setupCode.compile.run initial).1.lists 0 = input := hs.2.1
  have h1 : (setupCode.compile.run initial).1.lists 1 = [] := hs.2.2
  have htab := Tabulation.tabulate_cost (kernel_spec input) (hb input)
    (fun j _ => value_size input j) (setupCode.compile.run initial).1 h0 hcount h1
  have hsize : Nat.size L ≤ L := size_le_self L
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hSL : S + Nat.size L + 2 ≤ M := by dsimp [M]; omega
  have hSM : S + 1 ≤ M := by dsimp [M]; omega
  have hLM : L ≤ M := by dsimp [M]; omega
  have hBM := Nat.mul_le_mul_left B (Nat.pow_le_pow_left hSL 2)
  have hAM := Nat.mul_le_mul_left A (Nat.pow_le_pow_left hSM 2)
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hM3 : M ^ 2 ≤ M ^ 3 := by nlinarith
  have hconst : 3 * Nat.size L + 9 ≤ 12 * M ^ 2 := by nlinarith
  have hbody : B * (S + Nat.size L + 2) ^ 2 + 2 * 1 + 3 * Nat.size L + 7 ≤
      (B + 12) * M ^ 2 := by nlinarith
  have hloop := Nat.mul_le_mul hLM hbody
  have hA3 := Nat.mul_le_mul_left A hM3
  dsimp only [program, Prog.cost, Prog.init, Prog.inL]
  rw [run_seq_snd]
  change (setupCode.compile.run initial).2 +
      ((Tabulation.tabulate kernel).run (setupCode.compile.run initial).1).2 + 1 ≤
    (A + B + 30) * M ^ 3
  change (setupCode.compile.run initial).2 ≤ A * (S + 1) ^ 2 at hsetup
  change ((Tabulation.tabulate kernel).run (setupCode.compile.run initial).1).2 ≤
    L * (B * (S + Nat.size L + 2) ^ 2 + 2 * 1 + 3 * Nat.size L + 7) +
      Nat.size L + 9 at htab
  nlinarith

/-- The emitted natural-number bits have exactly the production unary-header layout. -/
theorem output_format (input : List ℕ) :
    (List.range (outputLength input)).map (value input) =
      (ThreeColorNumericAdjacency.encode (variableCount input) (clauses input)
        (literal input)).map Bool.toNat := by
  let N := vertices input
  have hhead : (List.range N).map (value input) = List.replicate N 1 := by
    apply List.ext_getElem (by simp)
    intro i hi _
    have hin : i < N := by simpa using hi
    simp [value, N, hin]
  have hsep : value input N = 0 := by simp [value, N]
  have htail : (List.range (N * N)).map (fun j => value input (N + 1 + j)) =
      List.ofFn (fun j : Fin (N * N) =>
        (ThreeColorNumericAdjacency.adjacency (variableCount input) (literal input)
          (j.val / N) (j.val % N)).toNat) := by
    apply List.ext_getElem (by simp)
    intro i _ _
    have hlt : ¬N + 1 + i < vertices input := by dsimp [N]; omega
    have hne : N + 1 + i ≠ vertices input := by dsimp [N]; omega
    simp [value, hlt, hne, N]
  change (List.range (N + 1 + N * N)).map (value input) = _
  rw [List.range_add, List.map_append, List.range_succ, List.map_append,
    List.map_singleton, hhead, hsep]
  simp only [List.map_map, Function.comp_def]
  rw [htail]
  simp [ThreeColorNumericAdjacency.encode, List.map_ofFn, N, vertices, Function.comp_def]

/-- Exact execution result, expressed in graph-encoding bits. -/
theorem program_run_encoding (input : List ℕ) :
    program.run input =
      (ThreeColorNumericAdjacency.encode (variableCount input) (clauses input)
        (literal input)).map Bool.toNat := (program_run input).trans (output_format input)

end PCP.Reduction.ThreeColorMatrixLang
