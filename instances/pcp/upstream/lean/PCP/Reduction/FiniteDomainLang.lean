/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.FiniteDomainSource
import PCP.Complexity.ArithmeticLookupCost
import PCP.Complexity.LangTabulation

/-!
# A concrete finite-domain to one-hot Boolean table program

For each fixed alphabet and local arity, one program reads the finite-domain
truth tables and emits the exact one-hot Boolean constraint source. Its finite
pattern tables depend only on those two fixed constants.
-/

set_option maxRecDepth 20000

namespace PCP.Reduction.FiniteDomainLang

open PCP.Lang PCP.Lang.ArithmeticExpression PCP.Lang.ArithmeticLookup
open FiniteDomainConstraints

def outputLength (a d : ℕ) (input : List ℕ) : ℕ :=
  2 + (FiniteDomainSource.constraintCount input + FiniteDomainSource.variableCount input) *
    BooleanClauseSource.width (arity a d)

def value (a d : ℕ) (input : List ℕ) (j : ℕ) : ℕ :=
  if j = 0 then (FiniteDomainSource.variableCount input + 1) * a
  else if j = 1 then
    FiniteDomainSource.constraintCount input + FiniteDomainSource.variableCount input
  else
    let e := (j - 2) / BooleanClauseSource.width (arity a d)
    let i := (j - 2) % BooleanClauseSource.width (arity a d)
    if i < 2 ^ arity a d then FiniteDomainSource.booleanRelation a d input e i
    else FiniteDomainSource.booleanScope a d input e (i - 2 ^ arity a d)

def relationValue (e c decoded truth valid : ℕ) : ℕ :=
  if e < c then if decoded = 0 then 0 else truth else valid

def scopeValue (a d v c e i symbol : ℕ) : ℕ :=
  (if e < c then if i / a < d then symbol else v else e - c) * a + i % a

private theorem bit_test (p : Prop) [Decidable p] :
    ((if p then 1 else 0) : ℕ) ≠ 0 ↔ p := by by_cases h : p <;> simp [h]

def relationTerm : Term 12 :=
  .cond (.bin .lt (.input 6) (.input 5))
    (.cond (.bin .eq (.input 8) (.const 0)) (.const 0) (.input 9)) (.input 10)

theorem relationTerm_eval (r : Fin 12 → ℕ) :
    relationTerm.eval r = relationValue (r 6) (r 5) (r 8) (r 9) (r 10) := by
  change (if (if r 6 < r 5 then 1 else 0) ≠ 0 then
    if (if r 8 = 0 then 1 else 0) ≠ 0 then 0 else r 9 else r 10) = _
  simp only [bit_test, relationValue]

def scopeTerm (a d : ℕ) : Term 12 :=
  let i := Term.bin .sub (.input 7) (.const (2 ^ arity a d))
  .bin .add (.bin .mul
    (.cond (.bin .lt (.input 6) (.input 5))
      (.cond (.bin .lt (.bin .div i (.const a)) (.const d)) (.input 11) (.input 4))
      (.bin .sub (.input 6) (.input 5))) (.const a)) (.bin .mod i (.const a))

theorem scopeTerm_eval (a d : ℕ) (r : Fin 12 → ℕ) :
    (scopeTerm a d).eval r = scopeValue a d (r 4) (r 5) (r 6)
      (r 7 - 2 ^ arity a d) (r 11) := by
  change ((if (if r 6 < r 5 then 1 else 0) ≠ 0 then
    if (if (r 7 - 2 ^ arity a d) / a < d then 1 else 0) ≠ 0 then r 11 else r 4
    else r 6 - r 5) * a + (r 7 - 2 ^ arity a d) % a) = _
  simp only [bit_test, scopeValue]

def relationAddress (a d : ℕ) : Term 12 :=
  .bin .add (.const 2) (.bin .add
    (.bin .mul (.input 6) (.const (FiniteDomainSource.width a d)))
    (.bin .sub (.input 8) (.const 1)))

def scopeAddress (a d : ℕ) : Term 12 :=
  .bin .add (.const 2) (.bin .add
    (.bin .mul (.input 6) (.const (FiniteDomainSource.width a d)))
    (.bin .add (.const (a ^ d))
      (.bin .div (.bin .sub (.input 7) (.const (2 ^ arity a d))) (.const a))))

def beforeAnswer (a d : ℕ) : Code 12 :=
  .seq (.lookup 4 (.const 0)) (.seq (.lookup 5 (.const 1))
    (.seq (.assign 6 (.bin .div (.bin .sub (.input 0) (.const 2))
      (.const (BooleanClauseSource.width (arity a d)))))
      (.seq (.assign 7 (.bin .mod (.bin .sub (.input 0) (.const 2))
        (.const (BooleanClauseSource.width (arity a d)))))
        (.seq (.assign 8 (.table (FiniteDomainSource.decodeTable a d) (.input 7)))
          (.seq (.lookup 9 (relationAddress a d))
            (.seq (.assign 10 (.table (FiniteDomainSource.validityTable a d) (.input 7)))
              (.lookup 11 (scopeAddress a d))))))))

def ready (a d : ℕ) (input : List ℕ) (r : Fin 12 → ℕ) : Fin 12 → ℕ :=
  let e := (r 0 - 2) / BooleanClauseSource.width (arity a d)
  let i := (r 0 - 2) % BooleanClauseSource.width (arity a d)
  let decoded := (FiniteDomainSource.decodeTable a d).getD i 0
  ![r 0, r 1, r 2, r 3, FiniteDomainSource.variableCount input,
    FiniteDomainSource.constraintCount input, e, i, decoded,
    FiniteDomainSource.relation input a d e (decoded - 1),
    (FiniteDomainSource.validityTable a d).getD i 0,
    FiniteDomainSource.scope input a d e ((i - 2 ^ arity a d) / a)]

set_option maxHeartbeats 2000000 in
-- Normalize the fixed twelve-register source-read sequence once.
theorem beforeAnswer_eval (a d : ℕ) (input : List ℕ) (r : Fin 12 → ℕ) :
    (beforeAnswer a d).eval input r = ready a d input r := by
  simp only [beforeAnswer, Code.eval, Term.eval_table]
  funext i
  fin_cases i <;> simp [ready, Term.eval, Op.eval, relationAddress, scopeAddress,
    FiniteDomainSource.variableCount, FiniteDomainSource.constraintCount,
    FiniteDomainSource.scope, FiniteDomainSource.relation, Function.update]

def answerTerm (a d : ℕ) : Term 12 :=
  .cond (.bin .eq (.input 0) (.const 0))
    (.bin .mul (.bin .add (.input 4) (.const 1)) (.const a))
    (.cond (.bin .eq (.input 0) (.const 1)) (.bin .add (.input 5) (.input 4))
      (.cond (.bin .lt (.input 7) (.const (2 ^ arity a d))) relationTerm (scopeTerm a d)))

theorem answerTerm_eval (a d : ℕ) (input : List ℕ) (r : Fin 12 → ℕ) :
    (answerTerm a d).eval (ready a d input r) = value a d input (r 0) := by
  simp only [answerTerm, Term.eval, Op.eval, relationTerm_eval, scopeTerm_eval]
  change (if (if r 0 = 0 then 1 else 0) ≠ 0 then _ else
    if (if r 0 = 1 then 1 else 0) ≠ 0 then _ else
      if (if _ < _ then 1 else 0) ≠ 0 then _ else _) = _
  simp only [bit_test]
  change (if r 0 = 0 then _ else if r 0 = 1 then _ else
    if (if (r 0 - 2) % BooleanClauseSource.width (arity a d) < 2 ^ arity a d
      then 1 else 0) ≠ 0 then _ else _) = _
  simp only [bit_test]
  rfl

@[irreducible] def kernelCode (a d : ℕ) : Code 12 :=
  .seq (beforeAnswer a d) (.assign 1 (answerTerm a d))

theorem kernelCode_eval (a d : ℕ) (input : List ℕ) (r : Fin 12 → ℕ) :
    ((kernelCode a d).eval input r) 0 = r 0 ∧
    ((kernelCode a d).eval input r) 1 = value a d input (r 0) ∧
    ((kernelCode a d).eval input r) 2 = r 2 ∧
    ((kernelCode a d).eval input r) 3 = r 3 := by
  simp only [kernelCode, Code.eval, beforeAnswer_eval, answerTerm_eval]
  simp [Function.update, ready]

/-- Scratch source slots are reset so successive iterations do not inflate their cost. -/
def reset : Stmt 16 3 :=
  .seq (.assign 1 (.const 0))
    (.seq (.assign 4 (.const 0))
    (.seq (.assign 5 (.const 0))
    (.seq (.assign 6 (.const 0))
    (.seq (.assign 7 (.const 0))
    (.seq (.assign 8 (.const 0))
    (.seq (.assign 9 (.const 0))
    (.seq (.assign 10 (.const 0))
    (.assign 11 (.const 0)))))))))

def kernel (a d : ℕ) : Stmt 16 3 := .seq reset (kernelCode a d).compile

theorem reset_lists (st : State 16 3) : (reset.run st).1.lists = st.lists := by
  simp [reset, Stmt.run]

theorem reset_inputs (st : State 16 3) (i : Fin 12) :
    inputs (reset.run st).1 i = if i = 0 ∨ i = 2 ∨ i = 3 then inputs st i else 0 := by
  fin_cases i <;> simp [inputs, reset, Stmt.run, Expr.eval, Function.update]

theorem reset_cost (st : State 16 3) : (reset.run st).2 = 17 := by
  simp [reset, Stmt.run, Expr.eval, Expr.cost, Expr.readSize]

/-- The counted loop receives exactly the requested literal address. -/
theorem kernel_spec (a d : ℕ) (input : List ℕ) :
    Tabulation.KernelSpec (kernel a d) input (outputLength a d input) (value a d input) := by
  intro st hs h2 h3 _
  simp only [kernel, run_seq_fst]
  have hc := (kernelCode a d).spec (reset.run st).1
  have hl : (reset.run st).1.lists 0 = input := congrFun (reset_lists st) 0 |>.trans hs
  have hr := hc.1.trans (congrArg (fun l => (kernelCode a d).eval l (inputs (reset.run st).1)) hl)
  have he := kernelCode_eval a d input (inputs (reset.run st).1)
  have h0 : inputs (reset.run st).1 0 = st.regs 0 := by
    rw [reset_inputs]
    simp [inputs]
  have htwo : inputs (reset.run st).1 2 = 1 := by
    rw [reset_inputs]
    simp [inputs, h2]
  have hthree : inputs (reset.run st).1 3 = outputLength a d input := by
    rw [reset_inputs]
    simp [inputs, h3]
  exact ⟨(congrFun hr 0).trans (he.1.trans h0),
    (congrFun hr 1).trans (he.2.1.trans (congrArg (value a d input) h0)),
    (congrFun hr 2).trans (he.2.2.1.trans htwo),
    (congrFun hr 3).trans (he.2.2.2.trans hthree),
    hc.2.1.trans hl, hc.2.2.trans (congrFun (reset_lists st) 1)⟩

theorem kernel_cost (a d : ℕ) : ∃ K : ℕ, ∀ input : List ℕ,
    Tabulation.KernelCost (kernel a d) input (outputLength a d input)
      (K * (listSize input + Nat.size (outputLength a d input) + 2) ^ 2) := by
  obtain ⟨K, _, hcost⟩ := (kernelCode a d).cost_bound
  refine ⟨K + 18, fun input st hs h2 h3 hj => ?_⟩
  let W := listSize input + Nat.size (outputLength a d input) + 1
  have hr : ∀ i : Fin 12, Nat.size (inputs (reset.run st).1 i) ≤ W := by
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
  have hq : 1 ≤ (listSize input + Nat.size (outputLength a d input) + 2) ^ 2 :=
    Nat.succ_le_of_lt (pow_pos (by omega) _)
  have heq : listSize input + Nat.size (outputLength a d input) + 1 + 1 =
      listSize input + Nat.size (outputLength a d input) + 2 := by omega
  rw [heq] at hc
  calc
    17 + ((kernelCode a d).compile.run (reset.run st).1).2 + 1 ≤
        K * (listSize input + Nat.size (outputLength a d input) + 2) ^ 2 + 18 := by omega
    _ ≤ _ := by nlinarith

/-- Output addresses have uniformly bounded bit length, including for malformed sources. -/
theorem value_size (a d : ℕ) : ∃ D : ℕ, ∀ (input : List ℕ) (j : ℕ),
    j < outputLength a d input → Nat.size (value a d input j) ≤
      D * (listSize input + Nat.size (outputLength a d input) + 2) := by
  obtain ⟨K, _, hcost⟩ := (kernelCode a d).cost_bound
  refine ⟨K, fun input j hj => ?_⟩
  let st : State 16 3 := ⟨fun i => if i = 0 then j else 0,
    fun L => if L = 0 then input else []⟩
  let W := listSize input + Nat.size (outputLength a d input) + 1
  have hr : ∀ i : Fin 12, Nat.size (inputs st i) ≤ W := by
    intro i
    simp only [inputs, st]
    split_ifs
    · exact (Nat.size_le_size hj.le).trans (by dsimp [W]; omega)
    · simp
  have hl : listSize (st.lists 0) ≤ W := by
    dsimp [st, W]
    omega
  have hb := (hcost st W hr hl).2 1
  have hs := (kernelCode a d).spec st
  have he := (kernelCode_eval a d input (inputs st)).2.1
  have hh : inputs ((kernelCode a d).compile.run st).1 1 = value a d input j :=
    (congrFun hs.1 1).trans he
  rw [hh] at hb
  exact hb

@[irreducible] def setupCode (a d : ℕ) : Code 12 :=
  .seq (.lookup 4 (.const 0)) (.seq (.lookup 5 (.const 1))
    (.assign 3 (.bin .add (.const 2) (.bin .mul (.bin .add (.input 5) (.input 4))
      (.const (BooleanClauseSource.width (arity a d)))))))

theorem setupCode_eval (a d : ℕ) (input : List ℕ) (r : Fin 12 → ℕ) :
    (setupCode a d).eval input r 3 = outputLength a d input := by
  simp [setupCode, Code.eval, Term.eval, Op.eval, Function.update,
    outputLength, FiniteDomainSource.variableCount, FiniteDomainSource.constraintCount]

def program (a d : ℕ) : Prog where
  R := 16
  Q := 3
  hQ := by decide
  body := .seq (setupCode a d).compile (Tabulation.tabulate (kernel a d))

/-- Exact execution semantics of the complete clause-source generator. -/
theorem program_run (a d : ℕ) (input : List ℕ) :
    (program a d).run input = (List.range (outputLength a d input)).map (value a d input) := by
  let initial : State 16 3 := ⟨fun _ => 0, fun L => if L = 0 then input else []⟩
  have hs := (setupCode a d).spec initial
  have hreg := congrFun hs.1 3
  have hcount : ((setupCode a d).compile.run initial).1.regs 3 = outputLength a d input :=
    hreg.trans (setupCode_eval a d input _)
  have h0 : ((setupCode a d).compile.run initial).1.lists 0 = input := hs.2.1
  have h1 : ((setupCode a d).compile.run initial).1.lists 1 = [] := hs.2.2
  exact (Tabulation.tabulate_spec (kernel_spec a d input)
    ((setupCode a d).compile.run initial).1 h0 hcount h1).1

/-- Charged cost is polynomial in source size plus the actual number of emitted entries. -/
theorem program_cost (a d : ℕ) : ∃ C : ℕ, ∀ input : List ℕ,
    (program a d).cost input ≤ C * (listSize input + outputLength a d input + 2) ^ 3 := by
  obtain ⟨A, _, ha⟩ := (setupCode a d).cost_bound
  obtain ⟨B, hb⟩ := kernel_cost a d
  obtain ⟨D, hd⟩ := value_size a d
  refine ⟨A + B + 2 * D + 30, fun input => ?_⟩
  let initial : State 16 3 := ⟨fun _ => 0, fun L => if L = 0 then input else []⟩
  let S := listSize input
  let L := outputLength a d input
  let M := S + L + 2
  have hinit : ∀ i : Fin 12, Nat.size (inputs initial i) ≤ S := by simp [inputs, initial]
  have hlist : listSize (initial.lists 0) ≤ S := by simp [initial, S]
  have hsetup := (ha initial S hinit hlist).1
  have hs := (setupCode a d).spec initial
  have hcount : ((setupCode a d).compile.run initial).1.regs 3 = L :=
    (congrFun hs.1 3).trans (setupCode_eval a d input _)
  have h0 : ((setupCode a d).compile.run initial).1.lists 0 = input := hs.2.1
  have h1 : ((setupCode a d).compile.run initial).1.lists 1 = [] := hs.2.2
  have htab := Tabulation.tabulate_cost (kernel_spec a d input) (hb input)
    (hd input) ((setupCode a d).compile.run initial).1 h0 hcount h1
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
  change ((setupCode a d).compile.run initial).2 +
      ((Tabulation.tabulate (kernel a d)).run ((setupCode a d).compile.run initial).1).2 + 1 ≤
    (A + B + 2 * D + 30) * M ^ 3
  change ((setupCode a d).compile.run initial).2 ≤ A * (S + 1) ^ 2 at hsetup
  change ((Tabulation.tabulate (kernel a d)).run ((setupCode a d).compile.run initial).1).2 ≤
    L * (B * (S + Nat.size L + 2) ^ 2 + 2 * (D * (S + Nat.size L + 2)) +
      3 * Nat.size L + 7) + Nat.size L + 9 at htab
  nlinarith



variable {v c a d : ℕ}

def booleanRelation (R : Fin c → (Fin d → Fin a) → Bool) :
    Fin (c + v) → FiniteBooleanConstraints.Pattern (arity a d) → Bool :=
  FiniteDomainEncoding.indexedRelation (Equiv.refl (Fin v)) (Equiv.refl (Fin c)) R

def booleanScope (s : Fin c → Fin d → Fin v) :
    Fin (c + v) → Fin (arity a d) → Fin ((v + 1) * a) :=
  FiniteDomainEncoding.indexedScope (Equiv.refl (Fin v)) (Equiv.refl (Fin c)) s

/-- Each emitted table entry equals the stored one-hot compiler record. -/
theorem source_record (R : Fin c → (Fin d → Fin a) → Bool)
    (s : Fin c → Fin d → Fin v) (e : Fin (c + v))
    (i : Fin (BooleanClauseSource.width (arity a d))) :
    value a d (FiniteDomainSource.source R s)
        (2 + (e.val * BooleanClauseSource.width (arity a d) + i.val)) =
      BooleanClauseSource.record (booleanRelation R) (booleanScope s) e i := by
  have hw : 0 < BooleanClauseSource.width (arity a d) := by
    have h := Nat.two_pow_pos (arity a d)
    dsimp [BooleanClauseSource.width]
    omega
  have hd : (e.val * BooleanClauseSource.width (arity a d) + i.val) /
      BooleanClauseSource.width (arity a d) = e.val := by
    rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
  have hm : (e.val * BooleanClauseSource.width (arity a d) + i.val) %
      BooleanClauseSource.width (arity a d) = i.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
  simp only [value, ite_eq_right (by omega : 2 +
      (e.val * BooleanClauseSource.width (arity a d) + i.val) ≠ 0),
    ite_eq_right (by omega : 2 + (e.val * BooleanClauseSource.width (arity a d) + i.val) ≠ 1),
    Nat.add_sub_cancel_left, hd, hm, BooleanClauseSource.record]
  split_ifs with hi
  · have h := FiniteDomainSource.booleanRelation_correct R s e
      ((FiniteBooleanEncoding.patternCode (arity a d)).symm ⟨i.val, hi⟩)
    simpa only [Equiv.apply_symm_apply, booleanRelation] using h
  · exact FiniteDomainSource.booleanScope_correct R s e ⟨i.val - 2 ^ arity a d,
      by have := i.isLt; dsimp [BooleanClauseSource.width] at *; omega⟩

/-- The actual program emits exactly the Boolean source format required downstream. -/
theorem program_run_source (R : Fin c → (Fin d → Fin a) → Bool)
    (s : Fin c → Fin d → Fin v) :
    (program a d).run (FiniteDomainSource.source R s) =
      BooleanClauseSource.source (booleanRelation R) (booleanScope s) := by
  rw [program_run]
  apply List.ext_getElem
  · simp [outputLength]
  · intro j hj hj'
    simp only [List.length_map, List.length_range] at hj
    by_cases h0 : j = 0
    · subst j
      simp [value, BooleanClauseSource.source]
    by_cases h1 : j = 1
    · subst j
      simp [value, BooleanClauseSource.source]
    obtain ⟨z, rfl⟩ : ∃ z, j = z + 2 := ⟨j - 2, by omega⟩
    have hz : z < (c + v) * BooleanClauseSource.width (arity a d) := by
      simp only [outputLength, FiniteDomainSource.source_constraintCount,
        FiniteDomainSource.source_variableCount] at hj
      omega
    let f : Fin ((c + v) * BooleanClauseSource.width (arity a d)) := ⟨z, hz⟩
    let e := (finProdFinEquiv.symm f).1
    let i := (finProdFinEquiv.symm f).2
    have he : e.val * BooleanClauseSource.width (arity a d) + i.val = z := by
      have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply f)
      change i.val + BooleanClauseSource.width (arity a d) * e.val = z at h
      simpa only [Nat.mul_comm, Nat.add_comm] using h
    simp only [List.getElem_map, List.getElem_range, BooleanClauseSource.source,
      List.getElem_cons_succ, List.getElem_ofFn]
    change value a d (FiniteDomainSource.source R s) (z + 2) =
      BooleanClauseSource.record (booleanRelation R) (booleanScope s) e i
    rw [show z + 2 = 2 + (e.val * BooleanClauseSource.width (arity a d) + i.val) by omega]
    exact source_record R s e i

/-- Fixed-width finite-domain source tables have polynomial stored size. -/
theorem source_size_le (R : Fin c → (Fin d → Fin a) → Bool)
    (s : Fin c → Fin d → Fin v) :
    listSize (FiniteDomainSource.source R s) ≤
      (FiniteDomainSource.width a d + 4) * (v + c + 1) ^ 2 := by
  have hrecord (e : Fin c) (i : Fin (FiniteDomainSource.width a d)) :
      Nat.size (FiniteDomainSource.record R s e i) + 1 ≤ v + 2 := by
    unfold FiniteDomainSource.record
    split_ifs
    · cases R e _ <;> simp
    · have hs (j : Fin d) : Nat.size (s e j).val ≤ v :=
        (size_le_self _).trans (s e j).isLt.le
      exact (Nat.add_le_add_right (hs _) 1).trans (by omega)
  have hsum := List.sum_le_length_nsmul
    (List.ofFn (fun j : Fin (c * FiniteDomainSource.width a d) =>
      Nat.size (FiniteDomainSource.record R s (finProdFinEquiv.symm j).1
        (finProdFinEquiv.symm j).2) + 1)) (v + 2) (by
        simpa only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff] using
          fun j : Fin (c * FiniteDomainSource.width a d) =>
            hrecord (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
  have hv := size_le_self v
  have hc := size_le_self c
  simp only [List.length_ofFn, nsmul_eq_mul] at hsum
  simp only [FiniteDomainSource.source, listSize, List.map_cons, List.sum_cons,
    List.map_ofFn, Function.comp_def]
  have hq : c * (v + 2) ≤ (v + c + 1) ^ 2 := by nlinarith only
  have hm := Nat.mul_le_mul_left (FiniteDomainSource.width a d) hq
  have hn : v + c + 1 ≤ (v + c + 1) ^ 2 := by nlinarith only
  nlinarith only [hsum, hv, hc, hm, hn]

/-- No running-time premise remains for the one-hot source generator. -/
theorem program_cost_source (a d : ℕ) : ∃ C : ℕ,
    ∀ (v c : ℕ) (R : Fin c → (Fin d → Fin a) → Bool) (s : Fin c → Fin d → Fin v),
      (program a d).cost (FiniteDomainSource.source R s) ≤ C * (v + c + 1) ^ 6 := by
  obtain ⟨C, hC⟩ := program_cost a d
  let A := FiniteDomainSource.width a d + BooleanClauseSource.width (arity a d) + 8
  refine ⟨C * A ^ 3, fun v c R s => ?_⟩
  have hs := source_size_le R s
  have h := hC (FiniteDomainSource.source R s)
  have hlinear : v + c + 1 ≤ (v + c + 1) ^ 2 := by
    simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left (v + c + 1)
      (show 1 ≤ v + c + 1 by omega)
  have hc : c + v ≤ (v + c + 1) ^ 2 := (by omega : c + v ≤ v + c + 1).trans hlinear
  have hcl := Nat.mul_le_mul_right (BooleanClauseSource.width (arity a d)) hc
  have hq : 1 ≤ (v + c + 1) ^ 2 := (by omega : 1 ≤ v + c + 1).trans hlinear
  have hbound : listSize (FiniteDomainSource.source R s) +
      outputLength a d (FiniteDomainSource.source R s) + 2 ≤ A * (v + c + 1) ^ 2 := by
    simp only [outputLength, FiniteDomainSource.source_constraintCount,
      FiniteDomainSource.source_variableCount]
    dsimp [A]
    nlinarith
  calc
    _ ≤ C * (listSize (FiniteDomainSource.source R s) +
        outputLength a d (FiniteDomainSource.source R s) + 2) ^ 3 := h
    _ ≤ C * (A * (v + c + 1) ^ 2) ^ 3 :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbound 3)
    _ = _ := by ring

end PCP.Reduction.FiniteDomainLang
