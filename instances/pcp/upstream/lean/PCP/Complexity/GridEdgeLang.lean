import PCP.Complexity.GridEdgeLoop
import PCP.Complexity.GraphHeaderLang

/-!
# Executable public edge-extension evaluation

From the encoded public graph, the field width, grid size, dimension and point
coordinates, this program computes both address capacities and the unary header,
then executes the certified finite interpolation sum.
-/

namespace PCP.Lang.GridEdge

open PCP.Algebraic BinaryFieldCode

variable {t h n : ℕ} [NeZero t]

def headerRegs : Fin 6 → Fin 70 := ![64, 53, 65, 66, 67, 68]
def headerLists : Fin 2 → Fin 20 := ![16, 17]

theorem headerRegs_injective : Function.Injective headerRegs := by decide
theorem headerLists_injective : Function.Injective headerLists := by decide

def header : Stmt 70 20 := GraphHeader.program.rename headerRegs headerLists

def powerBody : Stmt 70 20 := .assign 55 (.mul 55 45)
def capacity : Stmt 70 20 := .seq (.assign 55 (.const 1)) (.loop 54 powerBody)

def finishSetup : Stmt 70 20 :=
  .seq (.assign 52 (.mul 55 55)) (.seq (.assign 54 (.add 54 54))
    (.seq (.assign 69 (.const 1)) (.seq (.assign 50 (.const 0)) (.assign 51 (.const 0)))))

def setup : Stmt 70 20 := .seq header (.seq capacity finishSetup)

def program : Stmt 70 20 := .seq setup loop

/-- These are stored source inputs; all derived metadata is computed by `setup`. -/
def Input (t h n : ℕ) [NeZero t] (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t) (st : State 70 20) : Prop :=
  st.regs 44 = t ∧ st.regs 45 = h ∧ st.regs 54 = n ∧
  st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t) ∧
  st.lists 7 = [] ∧ st.lists 12 = List.ofFn (fun i => (fieldEquiv t (z i)).val) ∧
  st.lists 16 = x.map Bool.toNat

theorem header_run (x : List Bool) (st : State 70 20)
    (hx : st.lists 16 = x.map Bool.toNat) :
    (header.run st).1.regs 53 = ThreeColorEncoding.vertexCount x ∧
      (header.run st).1.lists 16 = st.lists 16 := by
  have hr := GraphHeader.program.run_rename headerRegs headerLists
    headerRegs_injective headerLists_injective st
  have hp := GraphHeader.program_bits x (st.restrict headerRegs headerLists) hx
  have hl := (GraphHeader.program_run (st.restrict headerRegs headerLists)).2
  exact ⟨(congrArg (fun r : State 6 2 × ℕ => r.1.regs 1) hr).trans hp,
    (congrArg (fun r : State 6 2 × ℕ => r.1.lists 0) hr).trans hl⟩

theorem header_input (x : List Bool) (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (st : State 70 20) (hi : Input t h n x z st) : Input t h n x z (header.run st).1 := by
  exact ⟨(run_regs_frame header 44 (by decide) st).trans hi.1,
    (run_regs_frame header 45 (by decide) st).trans hi.2.1,
    (run_regs_frame header 54 (by decide) st).trans hi.2.2.1,
    (run_lists_frame header 3 (by decide) st).trans hi.2.2.2.1,
    (run_lists_frame header 7 (by decide) st).trans hi.2.2.2.2.1,
    (run_lists_frame header 12 (by decide) st).trans hi.2.2.2.2.2.1,
    (header_run x st hi.2.2.2.2.2.2).2.trans hi.2.2.2.2.2.2⟩

omit [NeZero t] in
/-- Repeated multiplication computes the actual capacity; no power primitive is assumed. -/
theorem power_iterate (k c : ℕ) (st : State 70 20) :
    (iterate powerBody.run c k st).1.regs 55 = st.regs 55 * st.regs 45 ^ k := by
  induction k generalizing st with
  | zero => simp [iterate]
  | succ k ih =>
    rw [iterate_succ_fst, ih]
    simp [powerBody, Stmt.run, Expr.eval, Function.update, pow_succ, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm]

omit [NeZero t] in
theorem capacity_run (st : State 70 20) :
    (capacity.run st).1.regs 55 = st.regs 45 ^ st.regs 54 := by
  simp only [capacity, run_seq_fst, run_assign_fst, run_loop_fst, Expr.eval]
  rw [power_iterate]
  simp [Function.update]

theorem capacity_input (x : List Bool) (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (st : State 70 20) (hi : Input t h n x z st) : Input t h n x z (capacity.run st).1 := by
  exact ⟨(run_regs_frame capacity 44 (by decide) st).trans hi.1,
    (run_regs_frame capacity 45 (by decide) st).trans hi.2.1,
    (run_regs_frame capacity 54 (by decide) st).trans hi.2.2.1,
    (run_lists_frame capacity 3 (by decide) st).trans hi.2.2.2.1,
    (run_lists_frame capacity 7 (by decide) st).trans hi.2.2.2.2.1,
    (run_lists_frame capacity 12 (by decide) st).trans hi.2.2.2.2.2.1,
    (run_lists_frame capacity 16 (by decide) st).trans hi.2.2.2.2.2.2⟩

/-- The concrete preprocessing supplies every input of the interpolation loop. -/
theorem setup_run (x : List Bool) (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (st : State 70 20) (hi : Input t h n x z st) :
    Context t h n x z (setup.run st).1 ∧ (setup.run st).1.regs 51 = 0 ∧
      (setup.run st).1.regs 50 = (fieldEquiv t (0 : BinaryMaterializedField.Element t)).val := by
  have hsi := header_input x z st hi
  have hsn := (header_run x st hi.2.2.2.2.2.2).1
  simp only [setup, run_seq_fst]
  generalize hs : (header.run st).1 = s at *
  have hui := capacity_input x z s hsi
  have hup := capacity_run s
  rw [hsi.2.1, hsi.2.2.1] at hup
  have hun := (run_regs_frame capacity 53 (by decide) s).trans hsn
  generalize hu : (capacity.run s).1 = u at *
  rcases hui with ⟨ht, hh, hn, hm, he, hz, hx⟩
  simp only [finishSetup, run_seq_fst, run_assign_fst, Expr.eval, Context,
    setReg_regs, setReg_lists, Function.update, Fin.reduceEq, dite_false, dite_true,
    ht, hh, hn, hm, he, hz, hx, hup, hun, pow_add, FieldExpression.code_zero,
    and_self]

/-- Exact executable public-input arithmetic, for every encoded graph and every field point. -/
theorem program_run (hh : h ≤ 2 ^ t) (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t) (st : State 70 20)
    (hi : Input t h n x z st) :
    (program.run st).1.regs 50 = (fieldEquiv t
      (FieldQueryArithmetic.edgeValue (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh)
        (ThreeColorGridIndex.pad (FiniteAlphabetIndex.code (fieldEquiv t) hh) n
          (ThreeColorEncoding.graph x)) z)).val := by
  have hs := setup_run x z st hi
  exact loop_run hh x z (setup.run st).1 hs.1 hs.2.1 hs.2.2

end PCP.Lang.GridEdge
