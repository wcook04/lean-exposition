import PCP.Complexity.ThreeColorNodeSetup
import PCP.Complexity.GraphHeaderLang

/-!
# Complete production setup from the stored public graph

This fixed program parses the vertex count, chooses the dimensions, constructs
the field modulus and both roots, and stores all five interpolation nodes.
The input graph, random bits, and answer history in lists 11, 12, and 13 survive.
-/

namespace PCP.Lang.ThreeColorContext

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters

def prepare : Stmt 50 15 := .seq metadata (.seq roots storeNodes)

def Prepared (N : ℕ) (st : State 50 15) : Prop :=
  Metadata N st ∧ Roots (exponent N) st ∧
    st.lists 14 = List.ofFn (fun i : Fin 5 => (fieldCode (exponent N) (nodes (exponent N) i)).val)

theorem prepare_run (N : ℕ) (st : State 50 15) (hN : st.regs 42 = N)
    (he : st.lists 7 = []) : Prepared N (prepare.run st).1 := by
  have hm := metadata_run N st hN
  have h7 := (metadata_lists st 7).trans he
  generalize hu : (metadata.run st).1 = u at *
  have hr := roots_run (exponent N) u hm.2 h7
  have hrm := roots_metadata N u hm.1
  generalize hv : (roots.run u).1 = v at *
  have hn := storeNodes_run (exponent N) v hr
  have hnm := storeNodes_metadata N v hrm
  simp only [prepare, run_seq_fst, hu, hv]
  generalize hw : (storeNodes.run v).1 = w at *
  exact ⟨hnm, hn⟩

theorem prepare_public_lists (st : State 50 15) (L : Fin 15)
    (hL : 11 ≤ L.val) (hU : L.val ≤ 13) : (prepare.run st).1.lists L = st.lists L := by
  simp only [prepare, run_seq_fst, storeNodes_public_lists _ L hL hU,
    roots_public_lists _ L hL, metadata_lists]

def headerRegs : Fin 6 → Fin 50 := Fin.castAdd 44
def headerLists (L : Fin 2) : Fin 15 := if L = 0 then 11 else 0

theorem headerLists_injective : Function.Injective headerLists := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [headerLists]

def header : Stmt 50 15 := GraphHeader.program.rename headerRegs headerLists

theorem header_run (x : List Bool) (st : State 50 15)
    (hx : st.lists 11 = x.map Bool.toNat) :
    (header.run st).1.regs 1 = ThreeColorEncoding.vertexCount x := by
  have hp := GraphHeader.program.run_rename headerRegs headerLists
    (Fin.castAdd_injective _ _) headerLists_injective st
  have hr := congrArg (fun z : State 6 2 × ℕ => z.1.regs 1) hp
  exact hr.trans (GraphHeader.program_bits x (st.restrict headerRegs headerLists) hx)

theorem header_lists (st : State 50 15) (L : Fin 15) (hL : L ≠ 0) :
    (header.run st).1.lists L = st.lists L := by
  apply run_lists_frame
  simpa [header, GraphHeader.program, GraphHeader.setup, GraphHeader.body,
    Stmt.listWrites, headerLists] using hL

def setup : Stmt 50 15 := .seq header (.seq (.assign 42 (.var 1)) prepare)

/-- Every field datum is constructed from the public input by this one fixed source program. -/
theorem setup_run (x : List Bool) (st : State 50 15)
    (hx : st.lists 11 = x.map Bool.toNat) (he : st.lists 7 = []) :
    Prepared (ThreeColorEncoding.vertexCount x) (setup.run st).1 := by
  have hn := header_run x st hx
  have h7 := (header_lists st 7 (by decide)).trans he
  generalize hu : (header.run st).1 = u at *
  simp only [setup, run_seq_fst, run_assign_fst, Expr.eval, hu]
  apply prepare_run
  · simpa using hn
  · exact h7

theorem setup_public_lists (st : State 50 15) (L : Fin 15)
    (hL : 11 ≤ L.val) (hU : L.val ≤ 13) : (setup.run st).1.lists L = st.lists L := by
  have hn : L ≠ 0 := by intro he; subst L; norm_num at hL
  simp only [setup, run_seq_fst, prepare_public_lists _ L hL hU,
    run_assign_fst, setReg_lists, header_lists _ L hn]

end PCP.Lang.ThreeColorContext
