/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.TableauArithmeticTerms
import PCP.Complexity.ArithmeticLookupCost
import PCP.Complexity.LangTabulation
import PCP.Reduction.FiniteDomainSource

/-!
# A fixed program emitting finite-domain tableau constraints

The input is `[time, space, witness, inputLength] ++ inputBits`. Every relation
entry comes from one machine-fixed truth table; every variable index is computed
by the certified arithmetic scope decoder. The program is total on arbitrary
natural-number input lists as well.
-/

set_option maxRecDepth 20000

namespace PCP.Machine.TableauSourceLang

open PCP.Lang PCP.Lang.ArithmeticExpression PCP.Lang.ArithmeticLookup

/-- All fields are constants of one fixed checker machine. -/
structure Parameters where
  stackCount : ℕ
  window : ℕ
  output : ℕ
  stack₀ : ℕ
  radius : ℕ
  alphabet : ℕ
  arity : ℕ
  table : List ℕ

def width (p : Parameters) : ℕ := p.alphabet ^ p.arity + p.arity

def variableCount (p : Parameters) (input : List ℕ) : ℕ :=
  TableauNumericIndex.variableCount p.stackCount (input.getD 0 0) (input.getD 1 0)

def constraints (p : Parameters) (input : List ℕ) : ℕ :=
  TableauNumericIndex.constraints p.stackCount p.window (input.getD 0 0) (input.getD 1 0) +
    input.getD 2 0

def outputLength (p : Parameters) (input : List ℕ) : ℕ := 2 + constraints p input * width p

def descriptor (p : Parameters) (input : List ℕ) (e : ℕ) : ℕ × ℕ × ℕ :=
  TableauDescriptorArithmetic.select p.stackCount p.window p.output p.stack₀
    (input.getD 0 0) (input.getD 1 0) (input.getD 2 0) (input.getD 3 0)
    (fun j => input.getD (4 + j) 0) e

def relation (p : Parameters) (input : List ℕ) (e i : ℕ) : ℕ :=
  let q := descriptor p input e
  p.table.getD (((q.1 * p.stackCount + q.2.1) * p.radius + q.2.2) *
    p.alphabet ^ p.arity + i) 0

def scope (p : Parameters) (input : List ℕ) (e i : ℕ) : ℕ :=
  TableauNumericIndex.scope p.stackCount p.window p.stack₀
    (input.getD 0 0) (input.getD 1 0) (input.getD 3 0) e i

def value (p : Parameters) (input : List ℕ) (j : ℕ) : ℕ :=
  if j = 0 then variableCount p input else if j = 1 then constraints p input else
    let e := (j - 2) / width p
    let i := (j - 2) % width p
    if i < p.alphabet ^ p.arity then relation p input e i
    else scope p input e (i - p.alphabet ^ p.arity)

def relationTerm (p : Parameters) : Term 12 :=
  let q := TableauArithmeticTerms.select p.stackCount p.window p.output p.stack₀
    (.input 4) (.input 5) (.input 6) (.input 7) (.input 8) (.input 10)
  .table p.table (.bin .add (.bin .mul
    (.bin .add (.bin .mul (.bin .add (.bin .mul q.1 (.const p.stackCount)) q.2.1)
      (.const p.radius)) q.2.2) (.const (p.alphabet ^ p.arity))) (.input 9))

theorem relationTerm_eval (p : Parameters) (r : Fin 12 → ℕ) :
    (relationTerm p).eval r =
      let q := TableauDescriptorArithmetic.select p.stackCount p.window p.output p.stack₀
        (r 4) (r 5) (r 6) (r 7) (fun _ => r 10) (r 8)
      p.table.getD (((q.1 * p.stackCount + q.2.1) * p.radius + q.2.2) *
        p.alphabet ^ p.arity + r 9) 0 := by
  have h := TableauArithmeticTerms.select_eval p.stackCount p.window p.output p.stack₀
    (.input 4) (.input 5) (.input 6) (.input 7) (.input 8) (.input 10) r
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg (fun q => q.2.1) h
  have h₃ := congrArg (fun q => q.2.2) h
  simp only [TableauArithmeticTerms.Triple.eval] at h₁ h₂ h₃
  simp only [relationTerm, Term.eval_table, Term.eval, Op.eval, h₁, h₂, h₃]

def beforeAnswer (p : Parameters) : Code 12 :=
  .seq (.lookup 4 (.const 0)) (.seq (.lookup 5 (.const 1))
    (.seq (.lookup 6 (.const 2)) (.seq (.lookup 7 (.const 3))
      (.seq (.assign 8 (.bin .div (.bin .sub (.input 0) (.const 2)) (.const (width p))))
        (.seq (.assign 9 (.bin .mod (.bin .sub (.input 0) (.const 2)) (.const (width p))))
          (.seq (.lookup 10 (.bin .add (.const 4)
            (TableauArithmeticTerms.publicPosition p.stackCount p.window
              (.input 4) (.input 5) (.input 8))))
            (.assign 11 (relationTerm p))))))))

def ready (p : Parameters) (input : List ℕ) (r : Fin 12 → ℕ) : Fin 12 → ℕ :=
  let e := (r 0 - 2) / width p
  let i := (r 0 - 2) % width p
  ![r 0, r 1, r 2, r 3, input.getD 0 0, input.getD 1 0, input.getD 2 0,
    input.getD 3 0, e, i,
    input.getD (4 + TableauDescriptorArithmetic.publicPosition p.stackCount p.window
      (input.getD 0 0) (input.getD 1 0) e) 0,
    relation p input e i]

set_option maxHeartbeats 2000000 in
-- The fixed twelve-register source-read sequence is normalized once.
theorem beforeAnswer_eval (p : Parameters) (input : List ℕ) (r : Fin 12 → ℕ) :
    (beforeAnswer p).eval input r = ready p input r := by
  have h := TableauDescriptorArithmetic.select_publicPosition p.stackCount p.window p.output
    p.stack₀ (input.getD 0 0) (input.getD 1 0) (input.getD 2 0) (input.getD 3 0)
    (fun j => input.getD (4 + j) 0) ((r 0 - 2) / width p)
  simp only [List.getD_eq_getElem?_getD] at h
  simp only [beforeAnswer, Code.eval, relationTerm_eval]
  funext i
  fin_cases i <;> simp [ready, Term.eval, Op.eval,
    TableauArithmeticTerms.publicPosition_eval, Function.update, relation, descriptor, h]

def answerTerm (p : Parameters) : Term 12 :=
  .iteEq (.input 0) (.const 0)
    (.bin .add (.bin .mul (.bin .add (.input 4) (.const 1))
      (TableauArithmeticTerms.sites p.stackCount (.input 5))) (.const 1))
    (.iteEq (.input 0) (.const 1)
      (.bin .add (TableauArithmeticTerms.constraints p.stackCount p.window
        (.input 4) (.input 5)) (.input 6))
      (.iteLt (.input 9) (.const (p.alphabet ^ p.arity)) (.input 11)
        (TableauArithmeticTerms.scope p.stackCount p.window p.stack₀
          (.input 4) (.input 5) (.input 7) (.input 8)
          (.bin .sub (.input 9) (.const (p.alphabet ^ p.arity))))))

theorem answerTerm_eval (p : Parameters) (input : List ℕ) (r : Fin 12 → ℕ) :
    (answerTerm p).eval (ready p input r) = value p input (r 0) := by
  simp only [answerTerm, Term.eval_iteEq, Term.eval_iteLt,
    TableauArithmeticTerms.sites_eval, TableauArithmeticTerms.constraints_eval,
    TableauArithmeticTerms.scope_eval, Term.eval, Op.eval]
  rfl

@[irreducible] def kernelCode (p : Parameters) : Code 12 :=
  .seq (beforeAnswer p) (.assign 1 (answerTerm p))

theorem kernelCode_eval (p : Parameters) (input : List ℕ) (r : Fin 12 → ℕ) :
    ((kernelCode p).eval input r) 0 = r 0 ∧
    ((kernelCode p).eval input r) 1 = value p input (r 0) ∧
    ((kernelCode p).eval input r) 2 = r 2 ∧
    ((kernelCode p).eval input r) 3 = r 3 := by
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

def kernel (p : Parameters) : Stmt 16 3 := .seq reset (kernelCode p).compile

theorem reset_lists (st : State 16 3) : (reset.run st).1.lists = st.lists := by
  simp [reset, Stmt.run]

theorem reset_inputs (st : State 16 3) (i : Fin 12) :
    inputs (reset.run st).1 i = if i = 0 ∨ i = 2 ∨ i = 3 then inputs st i else 0 := by
  fin_cases i <;> simp [inputs, reset, Stmt.run, Expr.eval, Function.update]

theorem reset_cost (st : State 16 3) : (reset.run st).2 = 17 := by
  simp [reset, Stmt.run, Expr.eval, Expr.cost, Expr.readSize]

/-- The counted loop receives exactly the requested literal address. -/
theorem kernel_spec (p : Parameters) (input : List ℕ) :
    Tabulation.KernelSpec (kernel p) input (outputLength p input) (value p input) := by
  intro st hs h2 h3 _
  simp only [kernel, run_seq_fst]
  have hc := (kernelCode p).spec (reset.run st).1
  have hl : (reset.run st).1.lists 0 = input := congrFun (reset_lists st) 0 |>.trans hs
  have hr := hc.1.trans (congrArg (fun l => (kernelCode p).eval l (inputs (reset.run st).1)) hl)
  have he := kernelCode_eval p input (inputs (reset.run st).1)
  have h0 : inputs (reset.run st).1 0 = st.regs 0 := by
    rw [reset_inputs]
    simp [inputs]
  have htwo : inputs (reset.run st).1 2 = 1 := by
    rw [reset_inputs]
    simp [inputs, h2]
  have hthree : inputs (reset.run st).1 3 = outputLength p input := by
    rw [reset_inputs]
    simp [inputs, h3]
  exact ⟨(congrFun hr 0).trans (he.1.trans h0),
    (congrFun hr 1).trans (he.2.1.trans (congrArg (value p input) h0)),
    (congrFun hr 2).trans (he.2.2.1.trans htwo),
    (congrFun hr 3).trans (he.2.2.2.trans hthree),
    hc.2.1.trans hl, hc.2.2.trans (congrFun (reset_lists st) 1)⟩

theorem kernel_cost (p : Parameters) : ∃ K : ℕ, ∀ input : List ℕ,
    Tabulation.KernelCost (kernel p) input (outputLength p input)
      (K * (listSize input + Nat.size (outputLength p input) + 2) ^ 2) := by
  obtain ⟨K, _, hcost⟩ := (kernelCode p).cost_bound
  refine ⟨K + 18, fun input st hs h2 h3 hj => ?_⟩
  let W := listSize input + Nat.size (outputLength p input) + 1
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
  have hq : 1 ≤ (listSize input + Nat.size (outputLength p input) + 2) ^ 2 :=
    Nat.succ_le_of_lt (pow_pos (by omega) _)
  have heq : listSize input + Nat.size (outputLength p input) + 1 + 1 =
      listSize input + Nat.size (outputLength p input) + 2 := by omega
  rw [heq] at hc
  calc
    17 + ((kernelCode p).compile.run (reset.run st).1).2 + 1 ≤
        K * (listSize input + Nat.size (outputLength p input) + 2) ^ 2 + 18 := by omega
    _ ≤ _ := by nlinarith

/-- Output addresses have uniformly bounded bit length, including for malformed sources. -/
theorem value_size (p : Parameters) : ∃ D : ℕ, ∀ (input : List ℕ) (j : ℕ),
    j < outputLength p input → Nat.size (value p input j) ≤
      D * (listSize input + Nat.size (outputLength p input) + 2) := by
  obtain ⟨K, _, hcost⟩ := (kernelCode p).cost_bound
  refine ⟨K, fun input j hj => ?_⟩
  let st : State 16 3 := ⟨fun i => if i = 0 then j else 0,
    fun L => if L = 0 then input else []⟩
  let W := listSize input + Nat.size (outputLength p input) + 1
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
  have hs := (kernelCode p).spec st
  have he := (kernelCode_eval p input (inputs st)).2.1
  have hh : inputs ((kernelCode p).compile.run st).1 1 = value p input j :=
    (congrFun hs.1 1).trans he
  rw [hh] at hb
  exact hb

@[irreducible] def setupCode (p : Parameters) : Code 12 :=
  .seq (.lookup 4 (.const 0)) (.seq (.lookup 5 (.const 1))
    (.seq (.lookup 6 (.const 2))
      (.assign 3 (.bin .add (.const 2) (.bin .mul
        (.bin .add (TableauArithmeticTerms.constraints p.stackCount p.window
          (.input 4) (.input 5)) (.input 6)) (.const (width p)))))))

theorem setupCode_eval (p : Parameters) (input : List ℕ) (r : Fin 12 → ℕ) :
    (setupCode p).eval input r 3 = outputLength p input := by
  simp only [setupCode, Code.eval, Term.eval, Op.eval,
    TableauArithmeticTerms.constraints_eval]
  simp [Function.update, outputLength, constraints]

def program (p : Parameters) : Prog where
  R := 16
  Q := 3
  hQ := by decide
  body := .seq (setupCode p).compile (Tabulation.tabulate (kernel p))

/-- Exact execution semantics of the complete clause-source generator. -/
theorem program_run (p : Parameters) (input : List ℕ) :
    (program p).run input = (List.range (outputLength p input)).map (value p input) := by
  let initial : State 16 3 := ⟨fun _ => 0, fun L => if L = 0 then input else []⟩
  have hs := (setupCode p).spec initial
  have hreg := congrFun hs.1 3
  have hcount : ((setupCode p).compile.run initial).1.regs 3 = outputLength p input :=
    hreg.trans (setupCode_eval p input _)
  have h0 : ((setupCode p).compile.run initial).1.lists 0 = input := hs.2.1
  have h1 : ((setupCode p).compile.run initial).1.lists 1 = [] := hs.2.2
  exact (Tabulation.tabulate_spec (kernel_spec p input)
    ((setupCode p).compile.run initial).1 h0 hcount h1).1

/-- Charged cost is polynomial in source size plus the actual number of emitted entries. -/
theorem program_cost (p : Parameters) : ∃ C : ℕ, ∀ input : List ℕ,
    (program p).cost input ≤ C * (listSize input + outputLength p input + 2) ^ 3 := by
  obtain ⟨A, _, ha⟩ := (setupCode p).cost_bound
  obtain ⟨B, hb⟩ := kernel_cost p
  obtain ⟨D, hd⟩ := value_size p
  refine ⟨A + B + 2 * D + 30, fun input => ?_⟩
  let initial : State 16 3 := ⟨fun _ => 0, fun L => if L = 0 then input else []⟩
  let S := listSize input
  let L := outputLength p input
  let M := S + L + 2
  have hinit : ∀ i : Fin 12, Nat.size (inputs initial i) ≤ S := by simp [inputs, initial]
  have hlist : listSize (initial.lists 0) ≤ S := by simp [initial, S]
  have hsetup := (ha initial S hinit hlist).1
  have hs := (setupCode p).spec initial
  have hcount : ((setupCode p).compile.run initial).1.regs 3 = L :=
    (congrFun hs.1 3).trans (setupCode_eval p input _)
  have h0 : ((setupCode p).compile.run initial).1.lists 0 = input := hs.2.1
  have h1 : ((setupCode p).compile.run initial).1.lists 1 = [] := hs.2.2
  have htab := Tabulation.tabulate_cost (kernel_spec p input) (hb input)
    (hd input) ((setupCode p).compile.run initial).1 h0 hcount h1
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
  change ((setupCode p).compile.run initial).2 +
      ((Tabulation.tabulate (kernel p)).run ((setupCode p).compile.run initial).1).2 + 1 ≤
    (A + B + 2 * D + 30) * M ^ 3
  change ((setupCode p).compile.run initial).2 ≤ A * (S + 1) ^ 2 at hsetup
  change ((Tabulation.tabulate (kernel p)).run ((setupCode p).compile.run initial).1).2 ≤
    L * (B * (S + Nat.size L + 2) ^ 2 + 2 * (D * (S + Nat.size L + 2)) +
      3 * Nat.size L + 7) + Nat.size L + 9 at htab
  nlinarith



/-- The fixed local record width is positive, including empty alphabets or arities. -/
theorem width_pos (p : Parameters) : 0 < width p := by
  by_cases h : p.arity = 0
  · simp [width, h]
  · dsimp [width]
    omega

section Source

variable (p : Parameters) (input : List ℕ) {v c : ℕ}
  (R : Fin c → (Fin p.arity → Fin p.alphabet) → Bool)
  (s : Fin c → Fin p.arity → Fin v)
  (hv : variableCount p input = v) (hc : constraints p input = c)
  (hr : ∀ (e : Fin c) (x : Fin p.arity → Fin p.alphabet),
    relation p input e.val (finFunctionFinEquiv x).val = (R e x).toNat)
  (hs : ∀ (e : Fin c) (i : Fin p.arity), scope p input e.val i.val = (s e i).val)

include hr hs in
/-- Correct scalar relation and scope operations give each exact finite-domain record. -/
theorem source_record (e : Fin c) (i : Fin (width p)) :
    value p input (2 + (e.val * width p + i.val)) =
      PCP.Reduction.FiniteDomainSource.record R s e i := by
  have hw := width_pos p
  have hd : (e.val * width p + i.val) / width p = e.val := by
    rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
  have hm : (e.val * width p + i.val) % width p = i.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
  simp only [value, ite_eq_right (by omega : 2 + (e.val * width p + i.val) ≠ 0),
    ite_eq_right (by omega : 2 + (e.val * width p + i.val) ≠ 1), Nat.add_sub_cancel_left,
    hd, hm, PCP.Reduction.FiniteDomainSource.record]
  split_ifs with hi
  · have h := hr e (finFunctionFinEquiv.symm ⟨i.val, hi⟩)
    simpa only [Equiv.apply_symm_apply] using h
  · exact hs e ⟨i.val - p.alphabet ^ p.arity,
      by have := i.isLt; dsimp [width] at *; omega⟩

include hv hc hr hs in
/-- The emitter returns the exact source format consumed by the graph-construction program. -/
theorem program_run_source :
    (program p).run input = PCP.Reduction.FiniteDomainSource.source R s := by
  rw [program_run]
  apply List.ext_getElem
  · simp [outputLength, hc, PCP.Reduction.FiniteDomainSource.source,
      width, PCP.Reduction.FiniteDomainSource.width, Nat.add_comm, Nat.add_left_comm]
  · intro j hj hj'
    simp only [List.length_map, List.length_range] at hj
    by_cases h0 : j = 0
    · subst j
      simp [value, hv, PCP.Reduction.FiniteDomainSource.source]
    by_cases h1 : j = 1
    · subst j
      simp [value, hc, PCP.Reduction.FiniteDomainSource.source]
    obtain ⟨z, rfl⟩ : ∃ z, j = z + 2 := ⟨j - 2, by omega⟩
    have hz : z < c * width p := by
      simp only [outputLength, hc] at hj
      omega
    let f : Fin (c * width p) := ⟨z, hz⟩
    let e := (finProdFinEquiv.symm f).1
    let i := (finProdFinEquiv.symm f).2
    have he : e.val * width p + i.val = z := by
      have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply f)
      change i.val + width p * e.val = z at h
      simpa only [Nat.mul_comm, Nat.add_comm] using h
    simp only [List.getElem_map, List.getElem_range, PCP.Reduction.FiniteDomainSource.source,
      List.getElem_cons_succ, List.getElem_ofFn]
    change value p input (z + 2) = PCP.Reduction.FiniteDomainSource.record R s e i
    rw [show z + 2 = 2 + (e.val * width p + i.val) by omega]
    exact source_record p input R s hr hs e i

end Source

end PCP.Machine.TableauSourceLang
