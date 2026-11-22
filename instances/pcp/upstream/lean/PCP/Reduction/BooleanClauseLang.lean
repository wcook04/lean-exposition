/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.BooleanClauseTerms
import PCP.Complexity.ArithmeticLookupCost
import PCP.Complexity.LangTabulation
import PCP.Reduction.ThreeColorMatrixSource

/-!
# A concrete Boolean-constraint clause-table generator

One fixed program per local arity reads the stored truth tables and scope entries,
then emits the literal table for the two NAE clauses replacing every generated
ternary clause. All source reads use the bounded list lookup implementation.
-/

set_option maxRecDepth 20000

namespace PCP.Reduction.BooleanClauseLang

open PCP.Lang PCP.Lang.ArithmeticExpression PCP.Lang.ArithmeticLookup

def variableCount (input : List ℕ) : ℕ := input.getD 0 0
def constraintCount (input : List ℕ) : ℕ := input.getD 1 0
def ternaryVariables (k : ℕ) (input : List ℕ) : ℕ :=
  variableCount input + constraintCount input * 2 ^ k * (k + 1)
def ternaryClauses (k : ℕ) (input : List ℕ) : ℕ :=
  constraintCount input * 2 ^ k * (3 * k + 2)
def originalLiteral (k : ℕ) (input : List ℕ) (e i : ℕ) : ℕ :=
  BooleanClauseArithmetic.address (variableCount input) k e i
    (BooleanClauseSource.scope input k) (BooleanClauseSource.pattern k)
    (BooleanClauseSource.relation input k)
def value (k : ℕ) (input : List ℕ) (j : ℕ) : ℕ :=
  if j = 0 then ternaryVariables k input + ternaryClauses k input
  else if j = 1 then 2 * ternaryClauses k input
  else ThreeSATNumericClauses.address (ternaryVariables k input) (originalLiteral k input)
    ((j - 2) / 3) ((j - 2) % 3)
def outputLength (k : ℕ) (input : List ℕ) : ℕ := 2 + 6 * ternaryClauses k input

def metadataCode (k : ℕ) : Code 18 :=
  .seq (.lookup 4 (.const 0)) (.seq (.lookup 5 (.const 1))
    (.seq (.assign 6 (.bin .add (.input 4)
      (.bin .mul (.bin .mul (.input 5) (.const (2 ^ k))) (.const (k + 1)))))
      (.assign 5 (.bin .mul (.bin .mul (.input 5) (.const (2 ^ k)))
        (.const (3 * k + 2))))))

def selectedPosition : Term 18 :=
  .cond (.bin .eq (.bin .mod (.input 7) (.const 2)) (.const 0)) (.input 8) (.const 2)

private theorem bit_test (p : Prop) [Decidable p] :
    ((if p then 1 else 0) : ℕ) ≠ 0 ↔ p := by by_cases h : p <;> simp [h]

theorem selectedPosition_eval (r : Fin 18 → ℕ) :
    selectedPosition.eval r = if r 7 % 2 = 0 then r 8 else 2 := by
  change (if (if r 7 % 2 = 0 then 1 else 0) ≠ 0 then r 8 else 2) = _
  simp only [bit_test]

def indexCode (k : ℕ) : Code 18 :=
  .seq (.assign 7 (.bin .div (.bin .sub (.input 0) (.const 2)) (.const 3)))
    (.seq (.assign 8 (.bin .mod (.bin .sub (.input 0) (.const 2)) (.const 3)))
      (.seq (.assign 9 (.bin .div (.input 7) (.const 2)))
        (.seq (.assign 10 selectedPosition)
          (.seq (.assign 11 (.bin .div (.bin .div (.input 9) (.const (3 * k + 2)))
            (.const (2 ^ k))))
            (.seq (.assign 12 (.bin .mod (.bin .div (.input 9) (.const (3 * k + 2)))
              (.const (2 ^ k))))
              (.assign 13 (.bin .mod (.input 9) (.const (3 * k + 2)))))))))

def scopeTerm (k : ℕ) : Term 18 :=
  .bin .add (.const 2) (.bin .add (.bin .mul (.input 11) (.const (BooleanClauseSource.width k)))
    (.bin .add (.const (2 ^ k)) (.bin .div (.input 13) (.const 3))))
def relationTerm (k : ℕ) : Term 18 :=
  .bin .add (.const 2) (.bin .add (.bin .mul (.input 11) (.const (BooleanClauseSource.width k)))
    (.input 12))
def localTerm (k : ℕ) : Term 18 :=
  BooleanClauseTerms.localTerm k (.input 4) (.input 11) (.input 12) (.input 13) (.input 10)
    (.input 14) (.input 15) (.input 16)
def entryCode (k : ℕ) : Code 18 :=
  .seq (.lookup 14 (scopeTerm k))
    (.seq (.assign 15 (BooleanClauseSource.patternTerm k (.input 12)
      (.bin .div (.input 13) (.const 3))))
      (.seq (.lookup 16 (relationTerm k)) (.assign 17 (localTerm k))))
def beforeAnswer (k : ℕ) : Code 18 :=
  .seq (metadataCode k) (.seq (indexCode k) (entryCode k))

def ready (k : ℕ) (input : List ℕ) (r : Fin 18 → ℕ) : Fin 18 → ℕ :=
  let e := (r 0 - 2) / 3
  let i := (r 0 - 2) % 3
  let a := e / 2
  let j := if e % 2 = 0 then i else 2
  let t := a / (3 * k + 2) / 2 ^ k
  let p := a / (3 * k + 2) % 2 ^ k
  let q := a % (3 * k + 2)
  let s := BooleanClauseSource.scope input k t (q / 3)
  let b := BooleanClauseSource.pattern k p (q / 3)
  let z := BooleanClauseSource.relation input k t p
  ![r 0, r 1, r 2, r 3, variableCount input, ternaryClauses k input,
    ternaryVariables k input, e, i, a, j, t, p, q, s, b, z,
    BooleanClauseTerms.localValue (variableCount input) k t p q j s b z]

set_option maxHeartbeats 4000000 in
-- Normalize the fixed eighteen-register instruction sequence once.
theorem beforeAnswer_eval (k : ℕ) (input : List ℕ) (r : Fin 18 → ℕ) :
    (beforeAnswer k).eval input r = ready k input r := by
  simp only [beforeAnswer, metadataCode, indexCode, entryCode, Code.eval, localTerm,
    BooleanClauseSource.patternTerm_eval, BooleanClauseTerms.localTerm_eval,
    selectedPosition_eval]
  funext i
  fin_cases i <;> simp [ready, Term.eval, Op.eval, scopeTerm, relationTerm,
    variableCount, constraintCount, ternaryVariables, ternaryClauses,
    BooleanClauseSource.scope, BooleanClauseSource.relation, Function.update]

theorem localValue_eq (v k e p q i : ℕ) (scope pattern : ℕ → ℕ) (relation : ℕ) :
    BooleanClauseTerms.localValue v k e p q i (scope (q / 3)) (pattern (q / 3)) relation =
      BooleanClauseArithmetic.localAddress v k e p q i scope pattern relation := by
  simp only [BooleanClauseTerms.localValue, BooleanClauseArithmetic.localAddress]

def answerTerm : Term 18 :=
  .cond (.bin .eq (.input 0) (.const 0)) (.bin .add (.input 6) (.input 5))
    (.cond (.bin .eq (.input 0) (.const 1)) (.bin .mul (.const 2) (.input 5))
      (BooleanClauseTerms.splitTerm (.input 6) (.input 7) (.input 8) (.input 17)))

theorem answerTerm_eval (k : ℕ) (input : List ℕ) (r : Fin 18 → ℕ) :
    answerTerm.eval (ready k input r) = value k input (r 0) := by
  simp only [answerTerm, Term.eval, Op.eval, BooleanClauseTerms.splitTerm_eval]
  change (if (if r 0 = 0 then 1 else 0) ≠ 0 then _ else
    if (if r 0 = 1 then 1 else 0) ≠ 0 then _ else _) = _
  simp only [bit_test]
  dsimp only [ready, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [localValue_eq]
  change (if r 0 = 0 then _ else if r 0 = 1 then _ else
    BooleanClauseTerms.splitValue _ _ _ (originalLiteral k input
      (((r 0 - 2) / 3) / 2) (if (r 0 - 2) / 3 % 2 = 0 then (r 0 - 2) % 3 else 2))) = _
  rw [BooleanClauseTerms.splitValue_eq]
  rfl

@[irreducible] def kernelCode (k : ℕ) : Code 18 :=
  .seq (beforeAnswer k) (.assign 1 answerTerm)

theorem kernelCode_eval (k : ℕ) (input : List ℕ) (r : Fin 18 → ℕ) :
    ((kernelCode k).eval input r) 0 = r 0 ∧
    ((kernelCode k).eval input r) 1 = value k input (r 0) ∧
    ((kernelCode k).eval input r) 2 = r 2 ∧
    ((kernelCode k).eval input r) 3 = r 3 := by
  simp only [kernelCode, Code.eval, beforeAnswer_eval, answerTerm_eval]
  simp [Function.update, ready]


/-- Scratch source slots are reset so successive iterations do not inflate their cost. -/
def reset : Stmt 22 3 :=
  .seq (.assign 1 (.const 0))
    (.seq (.assign 4 (.const 0))
    (.seq (.assign 5 (.const 0))
    (.seq (.assign 6 (.const 0))
    (.seq (.assign 7 (.const 0))
    (.seq (.assign 8 (.const 0))
    (.seq (.assign 9 (.const 0))
    (.seq (.assign 10 (.const 0))
    (.seq (.assign 11 (.const 0))
    (.seq (.assign 12 (.const 0))
    (.seq (.assign 13 (.const 0))
    (.seq (.assign 14 (.const 0))
    (.seq (.assign 15 (.const 0))
    (.seq (.assign 16 (.const 0))
    (.assign 17 (.const 0)))))))))))))))

def kernel (k : ℕ) : Stmt 22 3 := .seq reset (kernelCode k).compile

theorem reset_lists (st : State 22 3) : (reset.run st).1.lists = st.lists := by
  simp [reset, Stmt.run]

theorem reset_inputs (st : State 22 3) (i : Fin 18) :
    inputs (reset.run st).1 i = if i = 0 ∨ i = 2 ∨ i = 3 then inputs st i else 0 := by
  fin_cases i <;> simp [inputs, reset, Stmt.run, Expr.eval, Function.update]

theorem reset_cost (st : State 22 3) : (reset.run st).2 = 29 := by
  simp [reset, Stmt.run, Expr.eval, Expr.cost, Expr.readSize]

/-- The counted loop receives exactly the requested literal address. -/
theorem kernel_spec (k : ℕ) (input : List ℕ) :
    Tabulation.KernelSpec (kernel k) input (outputLength k input) (value k input) := by
  intro st hs h2 h3 _
  simp only [kernel, run_seq_fst]
  have hc := (kernelCode k).spec (reset.run st).1
  have hl : (reset.run st).1.lists 0 = input := congrFun (reset_lists st) 0 |>.trans hs
  have hr := hc.1.trans (congrArg (fun l => (kernelCode k).eval l (inputs (reset.run st).1)) hl)
  have he := kernelCode_eval k input (inputs (reset.run st).1)
  have h0 : inputs (reset.run st).1 0 = st.regs 0 := by
    rw [reset_inputs]
    simp [inputs]
  have htwo : inputs (reset.run st).1 2 = 1 := by
    rw [reset_inputs]
    simp [inputs, h2]
  have hthree : inputs (reset.run st).1 3 = outputLength k input := by
    rw [reset_inputs]
    simp [inputs, h3]
  exact ⟨(congrFun hr 0).trans (he.1.trans h0),
    (congrFun hr 1).trans (he.2.1.trans (congrArg (value k input) h0)),
    (congrFun hr 2).trans (he.2.2.1.trans htwo),
    (congrFun hr 3).trans (he.2.2.2.trans hthree),
    hc.2.1.trans hl, hc.2.2.trans (congrFun (reset_lists st) 1)⟩

theorem kernel_cost (k : ℕ) : ∃ K : ℕ, ∀ input : List ℕ,
    Tabulation.KernelCost (kernel k) input (outputLength k input)
      (K * (listSize input + Nat.size (outputLength k input) + 2) ^ 2) := by
  obtain ⟨K, _, hcost⟩ := (kernelCode k).cost_bound
  refine ⟨K + 30, fun input st hs h2 h3 hj => ?_⟩
  let W := listSize input + Nat.size (outputLength k input) + 1
  have hr : ∀ i : Fin 18, Nat.size (inputs (reset.run st).1 i) ≤ W := by
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
  have hq : 1 ≤ (listSize input + Nat.size (outputLength k input) + 2) ^ 2 :=
    Nat.succ_le_of_lt (pow_pos (by omega) _)
  have heq : listSize input + Nat.size (outputLength k input) + 1 + 1 =
      listSize input + Nat.size (outputLength k input) + 2 := by omega
  rw [heq] at hc
  calc
    29 + ((kernelCode k).compile.run (reset.run st).1).2 + 1 ≤
        K * (listSize input + Nat.size (outputLength k input) + 2) ^ 2 + 30 := by omega
    _ ≤ _ := by nlinarith

/-- Output addresses have uniformly bounded bit length, including for malformed sources. -/
theorem value_size (k : ℕ) : ∃ D : ℕ, ∀ (input : List ℕ) (j : ℕ),
    j < outputLength k input → Nat.size (value k input j) ≤
      D * (listSize input + Nat.size (outputLength k input) + 2) := by
  obtain ⟨K, _, hcost⟩ := (kernelCode k).cost_bound
  refine ⟨K, fun input j hj => ?_⟩
  let st : State 22 3 := ⟨fun i => if i = 0 then j else 0,
    fun L => if L = 0 then input else []⟩
  let W := listSize input + Nat.size (outputLength k input) + 1
  have hr : ∀ i : Fin 18, Nat.size (inputs st i) ≤ W := by
    intro i
    simp only [inputs, st]
    split_ifs
    · exact (Nat.size_le_size hj.le).trans (by dsimp [W]; omega)
    · simp
  have hl : listSize (st.lists 0) ≤ W := by
    dsimp [st, W]
    omega
  have hb := (hcost st W hr hl).2 1
  have hs := (kernelCode k).spec st
  have he := (kernelCode_eval k input (inputs st)).2.1
  have hh : inputs ((kernelCode k).compile.run st).1 1 = value k input j :=
    (congrFun hs.1 1).trans he
  rw [hh] at hb
  exact hb

@[irreducible] def setupCode (k : ℕ) : Code 18 :=
  .seq (metadataCode k) (.assign 3 (.bin .add (.const 2) (.bin .mul (.const 6) (.input 5))))

theorem setupCode_eval (k : ℕ) (input : List ℕ) (r : Fin 18 → ℕ) :
    (setupCode k).eval input r 3 = outputLength k input := by
  simp [setupCode, metadataCode, Code.eval, Term.eval, Op.eval, Function.update,
    outputLength, ternaryClauses, constraintCount]

def program (k : ℕ) : Prog where
  R := 22
  Q := 3
  hQ := by decide
  body := .seq (setupCode k).compile (Tabulation.tabulate (kernel k))

/-- Exact execution semantics of the complete clause-source generator. -/
theorem program_run (k : ℕ) (input : List ℕ) :
    (program k).run input = (List.range (outputLength k input)).map (value k input) := by
  let initial : State 22 3 := ⟨fun _ => 0, fun L => if L = 0 then input else []⟩
  have hs := (setupCode k).spec initial
  have hreg := congrFun hs.1 3
  have hcount : ((setupCode k).compile.run initial).1.regs 3 = outputLength k input :=
    hreg.trans (setupCode_eval k input _)
  have h0 : ((setupCode k).compile.run initial).1.lists 0 = input := hs.2.1
  have h1 : ((setupCode k).compile.run initial).1.lists 1 = [] := hs.2.2
  exact (Tabulation.tabulate_spec (kernel_spec k input)
    ((setupCode k).compile.run initial).1 h0 hcount h1).1

/-- Charged cost is polynomial in source size plus the actual number of emitted entries. -/
theorem program_cost (k : ℕ) : ∃ C : ℕ, ∀ input : List ℕ,
    (program k).cost input ≤ C * (listSize input + outputLength k input + 2) ^ 3 := by
  obtain ⟨A, _, ha⟩ := (setupCode k).cost_bound
  obtain ⟨B, hb⟩ := kernel_cost k
  obtain ⟨D, hd⟩ := value_size k
  refine ⟨A + B + 2 * D + 30, fun input => ?_⟩
  let initial : State 22 3 := ⟨fun _ => 0, fun L => if L = 0 then input else []⟩
  let S := listSize input
  let L := outputLength k input
  let M := S + L + 2
  have hinit : ∀ i : Fin 18, Nat.size (inputs initial i) ≤ S := by simp [inputs, initial]
  have hlist : listSize (initial.lists 0) ≤ S := by simp [initial, S]
  have hsetup := (ha initial S hinit hlist).1
  have hs := (setupCode k).spec initial
  have hcount : ((setupCode k).compile.run initial).1.regs 3 = L :=
    (congrFun hs.1 3).trans (setupCode_eval k input _)
  have h0 : ((setupCode k).compile.run initial).1.lists 0 = input := hs.2.1
  have h1 : ((setupCode k).compile.run initial).1.lists 1 = [] := hs.2.2
  have htab := Tabulation.tabulate_cost (kernel_spec k input) (hb input)
    (hd input) ((setupCode k).compile.run initial).1 h0 hcount h1
  have hsize : Nat.size L ≤ L := size_le_self L
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hSL : S + Nat.size L + 2 ≤ M := by dsimp [M]; omega
  have hSM : S + 1 ≤ M := by dsimp [M]; omega
  have hLM : L ≤ M := by dsimp [M]; omega
  have hBM := Nat.mul_le_mul_left B (Nat.pow_le_pow_left hSL 2)
  have hAM := Nat.mul_le_mul_left A (Nat.pow_le_pow_left hSM 2)
  have hDM := Nat.mul_le_mul_left D hSL
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hM3 : M ^ 2 ≤ M ^ 3 := by nlinarith
  have hD2 := Nat.mul_le_mul_left D hM2
  have hbody : B * (S + Nat.size L + 2) ^ 2 +
      2 * (D * (S + Nat.size L + 2)) + 3 * Nat.size L + 7 ≤
      (B + 2 * D + 10) * M ^ 2 := by nlinarith
  have hloop := Nat.mul_le_mul hLM hbody
  have hA3 := Nat.mul_le_mul_left A hM3
  dsimp only [program, Prog.cost, Prog.init, Prog.inL]
  rw [run_seq_snd]
  change ((setupCode k).compile.run initial).2 +
      ((Tabulation.tabulate (kernel k)).run ((setupCode k).compile.run initial).1).2 + 1 ≤
    (A + B + 2 * D + 30) * M ^ 3
  change ((setupCode k).compile.run initial).2 ≤ A * (S + 1) ^ 2 at hsetup
  change ((Tabulation.tabulate (kernel k)).run ((setupCode k).compile.run initial).1).2 ≤
    L * (B * (S + Nat.size L + 2) ^ 2 + 2 * (D * (S + Nat.size L + 2)) +
      3 * Nat.size L + 7) + Nat.size L + 9 at htab
  nlinarith


variable {v c k : ℕ}

@[simp] theorem source_variableCount (R : Fin c → FiniteBooleanConstraints.Pattern k → Bool)
    (s : Fin c → Fin k → Fin v) : variableCount (BooleanClauseSource.source R s) = v := rfl

@[simp] theorem source_constraintCount (R : Fin c → FiniteBooleanConstraints.Pattern k → Bool)
    (s : Fin c → Fin k → Fin v) : constraintCount (BooleanClauseSource.source R s) = c := rfl

/-- Every emitted non-header entry is the exact typed NAE literal address. -/
theorem source_value (R : Fin c → FiniteBooleanConstraints.Pattern k → Bool)
    (s : Fin c → Fin k → Fin v) (e : Fin (c * 2 ^ k * (3 * k + 2) * 2)) (i : Fin 3) :
    value k (BooleanClauseSource.source R s) (2 + (3 * e.val + i.val)) =
      ThreeColorNumericAdjacency.literalAddress
        (ThreeSATNumericClauses.indexed (FiniteBooleanEncoding.indexedClauses R s) e i) := by
  have h0 : 2 + (3 * e.val + i.val) ≠ 0 := by omega
  have h1 : 2 + (3 * e.val + i.val) ≠ 1 := by omega
  have he : (2 + (3 * e.val + i.val) - 2) / 3 = e.val := by omega
  have hi : (2 + (3 * e.val + i.val) - 2) % 3 = i.val := by omega
  simp only [value, ite_eq_right h0, ite_eq_right h1, he, hi, ternaryVariables,
    source_variableCount, source_constraintCount]
  exact ThreeSATNumericClauses.address_correct (FiniteBooleanEncoding.indexedClauses R s)
    (originalLiteral k (BooleanClauseSource.source R s))
    (BooleanClauseSource.address_correct R s) e i

/-- Executing the generator produces the exact stored source consumed by the graph program. -/
theorem program_run_source (R : Fin c → FiniteBooleanConstraints.Pattern k → Bool)
    (s : Fin c → Fin k → Fin v) :
    (program k).run (BooleanClauseSource.source R s) =
      ThreeColorMatrixSource.source
        (ThreeSATNumericClauses.indexed (FiniteBooleanEncoding.indexedClauses R s)) := by
  rw [program_run]
  apply List.ext_getElem
  · simp [outputLength, ternaryClauses]
    omega
  · intro j hj hj'
    simp only [List.length_map, List.length_range] at hj
    by_cases h0 : j = 0
    · subst j
      simp [value, ThreeColorMatrixSource.source, ternaryVariables, ternaryClauses]
    by_cases h1 : j = 1
    · subst j
      simp [value, ThreeColorMatrixSource.source, ternaryClauses, Nat.mul_comm]
    obtain ⟨a, rfl⟩ : ∃ a, j = a + 2 := ⟨j - 2, by omega⟩
    have ha : a < c * 2 ^ k * (3 * k + 2) * 2 * 3 := by
      simp only [outputLength, ternaryClauses, source_constraintCount] at hj
      omega
    let z : Fin (c * 2 ^ k * (3 * k + 2) * 2 * 3) := ⟨a, ha⟩
    let e := (finProdFinEquiv.symm z).1
    let i := (finProdFinEquiv.symm z).2
    have hz : 3 * e.val + i.val = a := by
      have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply z)
      change i.val + 3 * e.val = a at h
      omega
    simp only [List.getElem_map, List.getElem_range, ThreeColorMatrixSource.source,
      List.getElem_cons_succ, List.getElem_ofFn]
    change value k (BooleanClauseSource.source R s) (a + 2) =
      ThreeColorNumericAdjacency.literalAddress
        (ThreeSATNumericClauses.indexed (FiniteBooleanEncoding.indexedClauses R s) e i)
    rw [show a + 2 = 2 + (3 * e.val + i.val) by omega]
    exact source_value R s e i

/-- Size of the stored Boolean tables, polynomial at each fixed local arity. -/
theorem source_size_le (R : Fin c → FiniteBooleanConstraints.Pattern k → Bool)
    (s : Fin c → Fin k → Fin v) :
    listSize (BooleanClauseSource.source R s) ≤
      (BooleanClauseSource.width k + 4) * (v + c + 1) ^ 2 := by
  have hrecord (e : Fin c) (i : Fin (BooleanClauseSource.width k)) :
      Nat.size (BooleanClauseSource.record R s e i) + 1 ≤ v + 2 := by
    unfold BooleanClauseSource.record
    split_ifs
    · cases R e _ <;> simp
    · have hs (j : Fin k) : Nat.size (s e j).val ≤ v :=
        (size_le_self _).trans (s e j).isLt.le
      exact (Nat.add_le_add_right (hs _) 1).trans (by omega)
  have hsum := List.sum_le_length_nsmul
    (List.ofFn (fun j : Fin (c * BooleanClauseSource.width k) =>
      Nat.size (BooleanClauseSource.record R s (finProdFinEquiv.symm j).1
        (finProdFinEquiv.symm j).2) + 1)) (v + 2) (by
        simpa only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff] using
          fun j : Fin (c * BooleanClauseSource.width k) =>
            hrecord (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
  have hv := size_le_self v
  have hc := size_le_self c
  simp only [List.length_ofFn, nsmul_eq_mul] at hsum
  simp only [BooleanClauseSource.source, listSize, List.map_cons, List.sum_cons,
    List.map_ofFn, Function.comp_def]
  have hq : c * (v + 2) ≤ (v + c + 1) ^ 2 := by nlinarith only
  have hm := Nat.mul_le_mul_left (BooleanClauseSource.width k) hq
  have hn : v + c + 1 ≤ (v + c + 1) ^ 2 := by nlinarith only
  nlinarith only [hsum, hv, hc, hm, hn]

/-- On valid constraint tables, the concrete program has polynomial construction cost. -/
theorem program_cost_source (k : ℕ) : ∃ C : ℕ,
    ∀ (v c : ℕ) (R : Fin c → FiniteBooleanConstraints.Pattern k → Bool)
      (s : Fin c → Fin k → Fin v),
      (program k).cost (BooleanClauseSource.source R s) ≤ C * (v + c + 1) ^ 6 := by
  obtain ⟨C, hC⟩ := program_cost k
  let A := BooleanClauseSource.width k + 6 * (2 ^ k * (3 * k + 2)) + 8
  refine ⟨C * A ^ 3, fun v c R s => ?_⟩
  have hs := source_size_le R s
  have h := hC (BooleanClauseSource.source R s)
  have hlinear : v + c + 1 ≤ (v + c + 1) ^ 2 := by
    simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left (v + c + 1)
      (show 1 ≤ v + c + 1 by omega)
  have hc : c ≤ (v + c + 1) ^ 2 := (by omega : c ≤ v + c + 1).trans hlinear
  have hcl := Nat.mul_le_mul_left (6 * (2 ^ k * (3 * k + 2))) hc
  have hq : 1 ≤ (v + c + 1) ^ 2 := (by omega : 1 ≤ v + c + 1).trans hlinear
  have hbound : listSize (BooleanClauseSource.source R s) +
      outputLength k (BooleanClauseSource.source R s) + 2 ≤ A * (v + c + 1) ^ 2 := by
    simp only [outputLength, ternaryClauses, source_constraintCount]
    dsimp [A]
    nlinarith
  calc
    _ ≤ C * (listSize (BooleanClauseSource.source R s) +
        outputLength k (BooleanClauseSource.source R s) + 2) ^ 3 := h
    _ ≤ C * (A * (v + c + 1) ^ 2) ^ 3 :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbound 3)
    _ = _ := by ring

end PCP.Reduction.BooleanClauseLang
