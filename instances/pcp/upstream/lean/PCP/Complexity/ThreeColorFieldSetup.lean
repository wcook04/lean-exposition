import PCP.Complexity.ThreeColorContextLang
import PCP.Complexity.BinaryRootConstruction
import PCP.Complexity.BinaryFieldCodePowerCost

/-!
# Constructing the verifier's actual field and roots

The caller supplies only the integer degree and an empty work list. The program
constructs the least irreducible modulus and finds both production roots by the
proved numeric-order searches. Stored public input lists 11 through 13 survive.
-/

namespace PCP.Lang.ThreeColorContext

open PCP.Algebraic ThreeColorParameters BinaryField

def fieldRegs : Fin 36 → Fin 50 := Fin.castAdd 14
def fieldLists : Fin 11 → Fin 15 := Fin.castAdd 4
def fieldCall (p : Stmt 36 11) : Stmt 50 15 := p.rename fieldRegs fieldLists

theorem fieldCall_state (p : Stmt 36 11) (st : State 50 15) :
    ((fieldCall p).run st).1.restrict fieldRegs fieldLists =
      (p.run (st.restrict fieldRegs fieldLists)).1 :=
  congrArg Prod.fst (p.run_rename fieldRegs fieldLists
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) st)

theorem fieldCall_cost (p : Stmt 36 11) (st : State 50 15) :
    ((fieldCall p).run st).2 = (p.run (st.restrict fieldRegs fieldLists)).2 :=
  p.run_rename_cost fieldRegs fieldLists
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) st

def FieldContext (a : ℕ) (st : State 50 15) : Prop :=
  st.regs 20 = binaryDimension a ∧ st.regs 28 = 2 ^ binaryDimension a ∧
    st.lists 3 = encode (BinaryWordMaterialization.modulus (binaryDimension a)) ∧
    st.lists 7 = []

def buildField : Stmt 50 15 := fieldCall BinaryRootSearch.buildModulus

theorem buildField_run (a : ℕ) (st : State 50 15)
    (ht : st.regs 20 = binaryDimension a) (he : st.lists 7 = []) :
    FieldContext a (buildField.run st).1 := by
  have h3 := congrArg (fun u : State 36 11 => u.lists 3)
    (fieldCall_state BinaryRootSearch.buildModulus st)
  have h28 := congrArg (fun u : State 36 11 => u.regs 28)
    (fieldCall_state BinaryRootSearch.buildModulus st)
  have hm := BinaryRootSearch.buildModulus_run (st.restrict fieldRegs fieldLists) ht he
  have hc := BinaryRootSearch.buildModulus_cardinality (st.restrict fieldRegs fieldLists)
  change (buildField.run st).1.lists 3 = _ at h3
  change (buildField.run st).1.regs 28 = _ at h28
  have h20 := run_regs_frame buildField 20 (by decide) st
  have h7 := run_lists_frame buildField 7 (by decide) st
  refine ⟨h20.trans ht, ?_, h3.trans hm, h7.trans he⟩
  exact h28.trans (hc.trans (congrArg (fun t => 2 ^ t) ht))

def rootSlot (full : Bool) : Fin 50 := if full then 49 else 48

def rootStep (full : Bool) : Stmt 50 15 :=
  .seq (fieldCall (BinaryRootSearch.searchRoot full)) (.assign (rootSlot full) (.var 35))

theorem rootStep_run (a : ℕ) (full : Bool) (st : State 50 15) (h : FieldContext a st) :
    ((rootStep full).run st).1.regs (rootSlot full) =
      (fieldCode a (if full then generator a else cubeRoot a)).val := by
  have hp := congrArg (fun u : State 36 11 => u.regs 35)
    (fieldCall_state (BinaryRootSearch.searchRoot full) st)
  have hr := BinaryRootSearch.searchRoot_run (fieldIndex a) full
    (st.restrict fieldRegs fieldLists) h.1 h.2.1 h.2.2.1 h.2.2.2
  change ((fieldCall (BinaryRootSearch.searchRoot full)).run st).1.regs 35 = _ at hp
  simp only [rootStep, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update_self]
  exact hp.trans hr

theorem rootStep_context (a : ℕ) (full : Bool) (st : State 50 15)
    (h : FieldContext a st) : FieldContext a ((rootStep full).run st).1 := by
  exact ⟨(run_regs_frame (rootStep full) 20 (by cases full <;> decide) st).trans h.1,
    (run_regs_frame (rootStep full) 28 (by cases full <;> decide) st).trans h.2.1,
    (run_lists_frame (rootStep full) 3 (by cases full <;> decide) st).trans h.2.2.1,
    (run_lists_frame (rootStep full) 7 (by cases full <;> decide) st).trans h.2.2.2⟩

def roots : Stmt 50 15 := .seq buildField (.seq (.assign 47 (.var 28))
  (.seq (rootStep false) (rootStep true)))

def Roots (a : ℕ) (st : State 50 15) : Prop :=
  FieldContext a st ∧ st.regs 47 = 2 ^ binaryDimension a ∧
    st.regs 48 = (fieldCode a (cubeRoot a)).val ∧
    st.regs 49 = (fieldCode a (generator a)).val

theorem roots_run (a : ℕ) (st : State 50 15)
    (ht : st.regs 20 = binaryDimension a) (he : st.lists 7 = []) :
    Roots a (roots.run st).1 := by
  have hb := buildField_run a st ht he
  generalize hu : (buildField.run st).1 = u at *
  let s := setReg u 47 (u.regs 28)
  have hs : FieldContext a s := by simpa [FieldContext, s, Function.update] using hb
  have hs47 : s.regs 47 = 2 ^ binaryDimension a := by simpa [s] using hb.2.1
  have hc := rootStep_run a false s hs
  have hcctx := rootStep_context a false s hs
  have hc47 := run_regs_frame (rootStep false) 47 (by decide) s
  generalize hv : ((rootStep false).run s).1 = v at *
  have hf := rootStep_run a true v hcctx
  have hfctx := rootStep_context a true v hcctx
  have hf47 := run_regs_frame (rootStep true) 47 (by decide) v
  have hf48 := run_regs_frame (rootStep true) 48 (by decide) v
  simp only [roots, run_seq_fst, run_assign_fst, Expr.eval, hu]
  change Roots a ((rootStep true).run ((rootStep false).run s).1).1
  rw [hv]
  exact ⟨hfctx, hf47.trans (hc47.trans hs47), hf48.trans hc, hf⟩

/-- The root builder retains all previously prepared permanent dimensions. -/
theorem roots_metadata (N : ℕ) (st : State 50 15) (h : Metadata N st) :
    Metadata N (roots.run st).1 := by
  exact ⟨(run_regs_frame roots 42 (by decide) st).trans h.1,
    (run_regs_frame roots 43 (by decide) st).trans h.2.1,
    (run_regs_frame roots 44 (by decide) st).trans h.2.2.1,
    (run_regs_frame roots 45 (by decide) st).trans h.2.2.2.1,
    (run_regs_frame roots 46 (by decide) st).trans h.2.2.2.2⟩

theorem roots_public_lists (st : State 50 15) (L : Fin 15) (hL : 11 ≤ L.val) :
    (roots.run st).1.lists L = st.lists L := by
  apply run_lists_frame
  simp only [roots, Stmt.listWrites, List.mem_append, List.not_mem_nil, false_or,
    rootStep, List.append_nil, buildField, fieldCall, Stmt.listWrites_rename, List.mem_map]
  rintro (⟨i, _, he⟩ | ⟨i, _, he⟩ | ⟨i, _, he⟩)
  all_goals
    have hv := congrArg Fin.val he
    have hi := i.isLt
    dsimp [fieldLists] at hv
    omega

end PCP.Lang.ThreeColorContext
