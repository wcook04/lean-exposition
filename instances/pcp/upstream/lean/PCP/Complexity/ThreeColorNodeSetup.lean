import PCP.Complexity.ThreeColorFieldSetup

/-!
# Materializing the five production interpolation-node codes

Five fixed binary-power calls use the multiplicative generator already found by field setup.
The output list follows the production `Fin 5` order exactly.
-/

namespace PCP.Lang.ThreeColorContext

open PCP.Algebraic ThreeColorParameters BinaryFieldCode

def powerRegs : Fin 42 → Fin 50 := Fin.castAdd 8
def powerCall : Stmt 50 15 := BinaryFieldCodePower.program.rename powerRegs fieldLists

theorem powerCall_result (st : State 50 15) :
    ((powerCall.run st).1.restrict powerRegs fieldLists, (powerCall.run st).2) =
      BinaryFieldCodePower.program.run (st.restrict powerRegs fieldLists) := by
  unfold powerCall
  exact BinaryFieldCodePower.program.run_rename powerRegs fieldLists
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) st

theorem powerCall_state (st : State 50 15) :
    (powerCall.run st).1.restrict powerRegs fieldLists =
      (BinaryFieldCodePower.program.run (st.restrict powerRegs fieldLists)).1 :=
  congrArg Prod.fst (powerCall_result st)

def nodePrepare (i : Fin 5) : Stmt 50 15 :=
  .seq (.assign 24 (.var 49)) (.seq (.assign 36 (.const (i.val+1))) (.assign 37 (.const 3)))

def nodeStep (i : Fin 5) : Stmt 50 15 :=
  .seq (nodePrepare i) (.seq powerCall (.seq (.assign 28 (.var 47)) (.push 14 26)))

theorem nodeStep_value (a : ℕ) (i : Fin 5) (st : State 50 15) (h : Roots a st) :
    ((nodeStep i).run st).1.lists 14 = (fieldCode a (nodes a i)).val :: st.lists 14 := by
  have h20 : ((nodePrepare i).run st).1.regs 20 = binaryDimension a := by
    simpa [nodePrepare, Stmt.run, Function.update] using h.1.1
  have h24 : ((nodePrepare i).run st).1.regs 24 =
      (fieldEquiv (binaryDimension a) (generator a)).val := by
    have hp : ((nodePrepare i).run st).1.regs 24 = st.regs 49 := by
      simp [nodePrepare, Stmt.run, Expr.eval, Function.update]
    rw [hp, ProductionGrid.fieldEquiv_eq_fieldCode]
    exact h.2.2.2
  have h36 : ((nodePrepare i).run st).1.regs 36 = i.val+1 := by
    simp [nodePrepare, Stmt.run, Expr.eval, Function.update]
  have h37 : ((nodePrepare i).run st).1.regs 37 = 3 := by
    simp [nodePrepare, Stmt.run, Expr.eval, Function.update]
  have hm : ((nodePrepare i).run st).1.lists 3 =
      BinaryField.encode (BinaryWordMaterialization.modulus (binaryDimension a)) := h.1.2.2.1
  have he : ((nodePrepare i).run st).1.lists 7 = [] := h.1.2.2.2
  have h14 : ((nodePrepare i).run st).1.lists 14 = st.lists 14 := rfl
  have hn : Nat.size (i.val+1) ≤ 3 := Nat.size_le.mpr (by have := i.isLt; omega)
  generalize hu : ((nodePrepare i).run st).1 = u at *
  have hp := BinaryFieldCodePower.program_run (t := binaryDimension a)
    (u.restrict powerRegs fieldLists) (generator a) (i.val+1) 3 h20 h24 h36 h37 hn hm he
  have ht := congrArg (fun u : State 42 11 => u.regs 26) (powerCall_state u)
  simp only [State.restrict_regs,
    show powerRegs 26 = (26 : Fin 50) from rfl] at ht
  have ho : (powerCall.run u).1.regs 26 =
      (fieldEquiv (binaryDimension a) (generator a ^ (i.val+1))).val := by
    rw [ht, hp]
    rfl
  rw [ProductionGrid.fieldEquiv_eq_fieldCode] at ho
  have h14' := run_lists_frame powerCall 14 (by decide) u
  generalize hv : (powerCall.run u).1 = v at *
  simp only [nodeStep, run_seq_fst, hu, hv, run_assign_fst, Expr.eval, run_push_fst,
    setList_lists, Function.update_self, setReg_regs, setReg_lists,
    Function.update_of_ne (by decide : (26 : Fin 50) ≠ 28), ho, h14', h14]
  rfl

theorem nodeStep_roots (a : ℕ) (i : Fin 5) (st : State 50 15) (h : Roots a st) :
    Roots a ((nodeStep i).run st).1 := by
  have h20 := run_regs_frame (nodeStep i) 20 (by fin_cases i <;> decide) st
  have h3 := run_lists_frame (nodeStep i) 3 (by fin_cases i <;> decide) st
  have h7 := run_lists_frame (nodeStep i) 7 (by fin_cases i <;> decide) st
  have h47 := run_regs_frame (nodeStep i) 47 (by fin_cases i <;> decide) st
  have h48 := run_regs_frame (nodeStep i) 48 (by fin_cases i <;> decide) st
  have h49 := run_regs_frame (nodeStep i) 49 (by fin_cases i <;> decide) st
  have hp47 := run_regs_frame powerCall 47 (by decide) ((nodePrepare i).run st).1
  have hprep47 : ((nodePrepare i).run st).1.regs 47 = st.regs 47 := by
    simp [nodePrepare, Stmt.run, Function.update]
  generalize hu : ((nodePrepare i).run st).1 = u at *
  generalize hv : (powerCall.run u).1 = v at *
  have h28 : ((nodeStep i).run st).1.regs 28 = st.regs 47 := by
    simp only [nodeStep, run_seq_fst, hu, hv, run_assign_fst, Expr.eval, run_push_fst,
      setList_regs, setReg_regs, Function.update_self, hp47, hprep47]
  generalize hw : ((nodeStep i).run st).1 = w at *
  exact ⟨⟨h20.trans h.1.1, h28.trans h.2.1, h3.trans h.1.2.2.1, h7.trans h.1.2.2.2⟩,
    h47.trans h.2.1, h48.trans h.2.2.1, h49.trans h.2.2.2⟩

theorem nodeStep_code (a : ℕ) (i : Fin 5) (st : State 50 15) (h : Roots a st) :
    ((nodeStep i).run st).1.regs 26 = (fieldCode a (nodes a i)).val := by
  have hv := nodeStep_value a i st h
  simp only [nodeStep, run_seq_fst] at hv ⊢
  generalize hu : ((nodePrepare i).run st).1 = u at *
  generalize hw : (powerCall.run u).1 = w at *
  simp only [run_assign_fst, Expr.eval, run_push_fst, setList_regs, setReg_regs,
    setList_lists, Function.update_self, setReg_lists,
    Function.update_of_ne (by decide : (26 : Fin 50) ≠ 28)] at hv ⊢
  exact (List.cons.inj hv).1

def nodeSequence : List (Fin 5) → Stmt 50 15
  | [] => .skip
  | i :: is => .seq (nodeStep i) (nodeSequence is)

theorem nodeSequence_run (a : ℕ) (is : List (Fin 5)) (st : State 50 15)
    (h : Roots a st) :
    Roots a ((nodeSequence is).run st).1 ∧
      ((nodeSequence is).run st).1.lists 14 =
        (is.map (fun i => (fieldCode a (nodes a i)).val)).reverse ++ st.lists 14 := by
  induction is generalizing st with
  | nil => simpa [nodeSequence, Stmt.run] using h
  | cons i is ih =>
    have hv := nodeStep_value a i st h
    have hc := nodeStep_roots a i st h
    have ht := ih ((nodeStep i).run st).1 hc
    simp only [nodeSequence, run_seq_fst]
    refine ⟨ht.1, ?_⟩
    rw [ht.2, hv]
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

def storeNodes : Stmt 50 15 :=
  .seq (.copy 7 14) (.seq (nodeSequence (List.finRange 5)) (.rev 14))

theorem storeNodes_run (a : ℕ) (st : State 50 15) (h : Roots a st) :
    Roots a (storeNodes.run st).1 ∧ (storeNodes.run st).1.lists 14 =
      List.ofFn (fun i : Fin 5 => (fieldCode a (nodes a i)).val) := by
  let s := setList st 14 []
  have hs : Roots a s := by simpa [Roots, FieldContext, s, Function.update] using h
  have hp := nodeSequence_run a (List.finRange 5) s hs
  have hout : ((nodeSequence (List.finRange 5)).run s).1.lists 14 =
      (List.ofFn (fun i : Fin 5 => (fieldCode a (nodes a i)).val)).reverse := by
    simpa only [List.ofFn_eq_map, s, setList_lists, Function.update_self,
      List.append_nil] using hp.2
  simp only [storeNodes, run_seq_fst, run_copy_fst, h.1.2.2.2]
  change Roots a ((Stmt.rev 14).run ((nodeSequence (List.finRange 5)).run s).1).1 ∧ _
  generalize hu : ((nodeSequence (List.finRange 5)).run s).1 = u at *
  constructor
  · simpa [Roots, FieldContext, Stmt.run, Function.update] using hp.1
  · simp [Stmt.run, hout]

theorem storeNodes_metadata (N : ℕ) (st : State 50 15) (h : Metadata N st) :
    Metadata N (storeNodes.run st).1 := by
  have h42 := run_regs_frame storeNodes 42 (by decide) st
  have h43 := run_regs_frame storeNodes 43 (by decide) st
  have h44 := run_regs_frame storeNodes 44 (by decide) st
  have h45 := run_regs_frame storeNodes 45 (by decide) st
  have h46 := run_regs_frame storeNodes 46 (by decide) st
  generalize hu : (storeNodes.run st).1 = u at *
  exact ⟨h42.trans h.1, h43.trans h.2.1, h44.trans h.2.2.1,
    h45.trans h.2.2.2.1, h46.trans h.2.2.2.2⟩

theorem storeNodes_public_lists (st : State 50 15) (L : Fin 15)
    (hL : 11 ≤ L.val) (hU : L.val ≤ 13) : (storeNodes.run st).1.lists L = st.lists L := by
  apply run_lists_frame
  fin_cases L <;> dsimp only at hL hU <;> first | omega | decide

end PCP.Lang.ThreeColorContext
