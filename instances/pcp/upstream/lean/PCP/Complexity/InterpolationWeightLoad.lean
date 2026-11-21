import PCP.Complexity.InterpolationWeightLang
import PCP.Complexity.LangRenaming

/-!
# Loading the five generator-power nodes and computing an interpolation weight

The field width, independent parameter, and five node codes are stored inputs.
The finite field expression performs all arithmetic and preserves its sources.
-/

namespace PCP.Lang.InterpolationWeightLoad

open PCP.Algebraic BinaryFieldCode FieldExpression

variable {t : ℕ} [NeZero t]

def load : Stmt 48 14 := .seq (.copy 12 0)
  (.seq (.pop 0 0 44) (.seq (.pop 0 1 44) (.seq (.pop 0 2 44)
    (.seq (.pop 0 3 44) (.seq (.pop 0 4 44)
      (.seq (.assign 5 (.var 43)) (.assign 26 (.var 42))))))))

def weight (i : Fin 5) : Stmt 48 14 :=
  (FieldExpression.interpolation 4 i).rename (Fin.castAdd 6) (Fin.castAdd 2)

def program (i : Fin 5) : Stmt 48 14 := .seq load (weight i)

def Context (a : Fin 5 → BinaryMaterializedField.Element t)
    (z : BinaryMaterializedField.Element t) (st : State 48 14) : Prop :=
  st.regs 42 = t ∧ st.regs 43 = (fieldEquiv t z).val ∧
  st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t) ∧
  st.lists 7 = [] ∧ st.lists 12 = List.ofFn (fun i => (fieldEquiv t (a i)).val)

theorem load_view (a : Fin 5 → BinaryMaterializedField.Element t)
    (z : BinaryMaterializedField.Element t) (st : State 48 14) (hc : Context a z st) :
    FieldExpression.View t (interpolationEnv a z)
      ((load.run st).1.restrict (Fin.castAdd 6) (Fin.castAdd 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [load, Stmt.run, Expr.eval, Function.update, State.restrict,
        interpolationEnv, hc.2.2.2.2, hc.2.1] <;> rfl
  · simpa [load, Stmt.run, Expr.eval, Function.update, State.restrict, slot,
      hc.2.2.2.2] using hc.1
  · simpa [load, Stmt.run, Expr.eval, Function.update, State.restrict,
      hc.2.2.2.2] using hc.2.2.1
  · simpa [load, Stmt.run, Expr.eval, Function.update, State.restrict,
      hc.2.2.2.2] using hc.2.2.2.1

theorem weight_result (i : Fin 5) (st : State 48 14) :
    (((weight i).run st).1.restrict (Fin.castAdd 6) (Fin.castAdd 2),
      ((weight i).run st).2) = (FieldExpression.interpolation 4 i).run
        (st.restrict (Fin.castAdd 6) (Fin.castAdd 2)) := by
  exact Stmt.run_rename _ _ _ (Fin.castAdd_injective 42 6) (Fin.castAdd_injective 12 2) st

theorem program_run (a : Fin 5 → BinaryMaterializedField.Element t)
    (z : BinaryMaterializedField.Element t) (i : Fin 5) (st : State 48 14)
    (hc : Context a z st) :
    ((program i).run st).1.regs 32 =
      (fieldEquiv t (FieldQueryArithmetic.interpolationWeight a z i)).val := by
  have hv := load_view a z st hc
  have hr := weight_result i (load.run st).1
  have hp := (FieldExpression.interpolation_run a z i _ hv).1
  exact (congrArg (fun p : State 42 12 × ℕ => p.1.regs 32) hr).trans hp

/-- Node values are still available after arithmetic, including the selected node. -/
theorem program_node (a : Fin 5 → BinaryMaterializedField.Element t)
    (z : BinaryMaterializedField.Element t) (i j : Fin 5) (st : State 48 14)
    (hc : Context a z st) :
    ((program i).run st).1.regs (j.castAdd 43) = (fieldEquiv t (a j)).val := by
  have hv := load_view a z st hc
  have hr := weight_result i (load.run st).1
  have hp := (FieldExpression.interpolation_run a z i _ hv).2.2.1 j.castSucc
  rw [← hr] at hp
  simpa only [program, run_seq_fst, Prod.fst, State.restrict_regs,
    show (j.castSucc.castAdd 36).castAdd 6 = j.castAdd 43 from rfl,
    interpolationEnv, Fin.lastCases_castSucc] using hp

theorem program_context (a : Fin 5 → BinaryMaterializedField.Element t)
    (z : BinaryMaterializedField.Element t) (i : Fin 5) (st : State 48 14)
    (hc : Context a z st) : Context a z ((program i).run st).1 := by
  have hv := load_view a z st hc
  have hr := weight_result i (load.run st).1
  have hp := (FieldExpression.interpolation_run a z i _ hv).2.2
  rw [← hr] at hp
  have h42 := (FieldExpression.interpolation 4 i).run_rename_reg_outside
    (Fin.castAdd 6) (Fin.castAdd 2) 42 (by
      intro j hj
      have := congrArg Fin.val hj
      simp only [Fin.val_castAdd] at this
      norm_num at this
      omega)
    (load.run st).1
  have h43 := (FieldExpression.interpolation 4 i).run_rename_reg_outside
    (Fin.castAdd 6) (Fin.castAdd 2) 43 (by
      intro j hj
      have := congrArg Fin.val hj
      simp only [Fin.val_castAdd] at this
      norm_num at this
      omega)
    (load.run st).1
  have h12 := (FieldExpression.interpolation 4 i).run_rename_list_outside
    (Fin.castAdd 6) (Fin.castAdd 2) 12 (by
      intro j hj
      have := congrArg Fin.val hj
      simp only [Fin.val_castAdd] at this
      norm_num at this
      omega)
    (load.run st).1
  have hl42 : (load.run st).1.regs 42 = st.regs 42 := run_regs_frame load 42 (by decide) st
  have hl43 : (load.run st).1.regs 43 = st.regs 43 := run_regs_frame load 43 (by decide) st
  have hl12 : (load.run st).1.lists 12 = st.lists 12 := run_lists_frame load 12 (by decide) st
  exact ⟨h42.trans (hl42.trans hc.1), h43.trans (hl43.trans hc.2.1),
    hp.2.2.1, hp.2.2.2, h12.trans (hl12.trans hc.2.2.2.2)⟩

end PCP.Lang.InterpolationWeightLoad
