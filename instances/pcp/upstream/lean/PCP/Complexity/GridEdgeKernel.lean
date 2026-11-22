import PCP.Complexity.GraphAdjacencyLang
import PCP.Complexity.UniformRadixLang
import PCP.Complexity.GridTensorSemantics
import PCP.Complexity.GridTensorCost

/-!
# One concrete interpolation-sum step for the public edge extension

An arithmetic public-graph read, fixed-width address decoding, a tensor basis
evaluation and materialized field addition operate on one shared state layout.
-/

namespace PCP.Lang.GridEdge

open PCP.Algebraic BinaryFieldCode

variable {t h n : ℕ} [NeZero t]

def readerRegs : Fin 11 → Fin 70 := ![51, 53, 55, 56, 57, 58, 59, 60, 61, 62, 63]
def readerLists : Fin 3 → Fin 20 := ![16, 19, 18]
def digitRegs : Fin 5 → Fin 70 := ![64, 65, 66, 67, 68]
def digitLists : Fin 2 → Fin 20 := ![17, 13]

theorem readerRegs_injective : Function.Injective readerRegs := by decide
theorem readerLists_injective : Function.Injective readerLists := by decide
theorem digitRegs_injective : Function.Injective digitRegs := by decide
theorem digitLists_injective : Function.Injective digitLists := by decide

def reader : Stmt 70 20 := GraphAdjacency.program.rename readerRegs readerLists
def digits : Stmt 70 20 := UniformRadix.program.rename digitRegs digitLists
def tensor : Stmt 70 20 :=
  GridTensor.program.rename (Fin.castLE (by decide)) (Fin.castLE (by decide))
def add : Stmt 70 20 := (binary .add).rename (Fin.castLE (by decide)) (Fin.castLE (by decide))

def digitCall : Stmt 70 20 :=
  .seq (.assign 64 (.var 51)) (.seq (.assign 65 (.var 54))
    (.seq (.assign 66 (.var 45)) (.seq (.copy 7 17) (.seq (.copy 7 13) digits))))

def addCall : Stmt 70 20 :=
  .seq (.assign 20 (.var 44)) (.seq (.assign 24 (.var 50))
    (.seq (.assign 25 (.var 40)) (.seq add (.assign 50 (.var 26)))))

def accumulate : Stmt 70 20 := .ite 57 addCall .skip

def kernel : Stmt 70 20 := .seq reader (.seq digitCall (.seq tensor accumulate))

/-- Read-only metadata and the two actual stored inputs. -/
def Context (t h n : ℕ) [NeZero t] (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t) (st : State 70 20) : Prop :=
  st.regs 44 = t ∧ st.regs 45 = h ∧
  st.regs 52 = h ^ (n + n) ∧ st.regs 53 = ThreeColorEncoding.vertexCount x ∧
  st.regs 54 = n + n ∧ st.regs 55 = h ^ n ∧ st.regs 69 = 1 ∧
  st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t) ∧
  st.lists 7 = [] ∧
  st.lists 12 = List.ofFn (fun i => (fieldEquiv t (z i)).val) ∧
  st.lists 16 = x.map Bool.toNat

def ReadOnly (s : Stmt 70 20) : Prop :=
  (∀ (st : State 70 20) (i : Fin 70), i ∈ [44, 45, 52, 53, 54, 55, 69] →
    (s.run st).1.regs i = st.regs i) ∧
  (∀ (st : State 70 20) (i : Fin 20), i ∈ [3, 7, 12, 16] →
    (s.run st).1.lists i = st.lists i)

theorem context_readOnly {s : Stmt 70 20} (hr : ReadOnly s)
    (x : List Bool) (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (st : State 70 20) (hc : Context t h n x z st) : Context t h n x z (s.run st).1 := by
  rcases hc with ⟨h44, h45, h52, h53, h54, h55, h69, h3, h7, h12, h16⟩
  exact ⟨(hr.1 st 44 (by simp)).trans h44, (hr.1 st 45 (by simp)).trans h45,
    (hr.1 st 52 (by simp)).trans h52, (hr.1 st 53 (by simp)).trans h53,
    (hr.1 st 54 (by simp)).trans h54, (hr.1 st 55 (by simp)).trans h55,
    (hr.1 st 69 (by simp)).trans h69, (hr.2 st 3 (by simp)).trans h3,
    (hr.2 st 7 (by simp)).trans h7, (hr.2 st 12 (by simp)).trans h12,
    (hr.2 st 16 (by simp)).trans h16⟩

theorem reader_readOnly : ReadOnly reader := by
  constructor
  · intro st i hi
    apply run_regs_frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (unfold reader GraphAdjacency.program GraphAdjacency.code; decide)
  · intro st i hi
    rcases (by simpa using hi : i = 3 ∨ i = 7 ∨ i = 12 ∨ i = 16) with rfl | rfl | rfl | rfl
    · exact run_lists_frame reader 3 (by
        unfold reader GraphAdjacency.program GraphAdjacency.code
        decide) st
    · exact run_lists_frame reader 7 (by
        unfold reader GraphAdjacency.program GraphAdjacency.code
        decide) st
    · exact run_lists_frame reader 12 (by
        unfold reader GraphAdjacency.program GraphAdjacency.code
        decide) st
    · have hr := GraphAdjacency.program.run_rename readerRegs readerLists
        readerRegs_injective readerLists_injective st
      have hp := (GraphAdjacency.program_run (st.restrict readerRegs readerLists)).2.2.2.2.1
      exact (congrArg (fun r : State 11 3 × ℕ => r.1.lists 0) hr).trans hp

theorem digitCall_readOnly : ReadOnly digitCall := by
  constructor
  · intro st i hi
    apply run_regs_frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro st i hi
    apply run_lists_frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide

theorem tensor_readOnly : ReadOnly tensor := by
  constructor
  · intro st i hi
    apply run_regs_frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro st i hi
    apply run_lists_frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide

theorem addCall_readOnly : ReadOnly addCall := by
  constructor
  · intro st i hi
    apply run_regs_frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro st i hi
    apply run_lists_frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide

/-- Actual decoded adjacency for the two grid addresses selected by the loop counter. -/
theorem reader_run (x : List Bool) (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (st : State 70 20) (hc : Context t h n x z st) :
    (reader.run st).1.regs 57 =
      if GridEdgeArithmetic.Adj (ThreeColorEncoding.graph x)
        (st.regs 51 % h ^ n) (st.regs 51 / h ^ n) then 1 else 0 := by
  have hr := GraphAdjacency.program.run_rename readerRegs readerLists
    readerRegs_injective readerLists_injective st
  have hp := (GraphAdjacency.program_run (st.restrict readerRegs readerLists)).1
  have hh := (congrArg (fun r : State 11 3 × ℕ => r.1.regs 4) hr).trans hp
  change (reader.run st).1.regs 57 = GraphAdjacency.bit (st.lists 16)
    (st.regs 53) (st.regs 51 % st.regs 55) (st.regs 51 / st.regs 55) at hh
  rw [hc.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2, GraphAdjacency.bit_correct] at hh
  exact hh

/-- The address decoder creates precisely the coordinate list required by the tensor program. -/
theorem digitCall_run (x : List Bool) (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (j : Fin (h ^ (n + n))) (st : State 70 20) (hc : Context t h n x z st)
    (hj : st.regs 51 = j.val) :
    (digitCall.run st).1.lists 13 =
      List.ofFn (fun i : Fin (n + n) => ((finFunctionFinEquiv.symm j) i).val) := by
  let s := setList (setList
    (setReg (setReg (setReg st 64 (st.regs 51)) 65 (st.regs 54)) 66 (st.regs 45))
    17 (st.lists 7)) 13 (st.lists 7)
  have hr := UniformRadix.program.run_rename digitRegs digitLists
    digitRegs_injective digitLists_injective s
  have hp := UniformRadix.program_finFunction h (n + n) j
    (s.restrict digitRegs digitLists)
    (by simpa [s, digitRegs, Function.update] using hj)
    (by simpa [s, digitRegs, Function.update] using hc.2.2.2.2.1)
    (by simpa [s, digitRegs, Function.update] using hc.2.1)
    (by simpa [s, digitLists, Function.update] using hc.2.2.2.2.2.2.2.2.1)
    (by simpa [s, digitLists, Function.update] using hc.2.2.2.2.2.2.2.2.1)
  change (digits.run s).1.lists 13 = _
  exact (congrArg (fun r : State 5 2 × ℕ => r.1.lists 1) hr).trans hp


/-- Decode a numeric address into the actual prefix grid alphabet. -/
def gridPoint (hh : h ≤ 2 ^ t) (j : Fin (h ^ (n + n))) :
    Fin (n + n) → FiniteAlphabetIndex.alphabet (fieldEquiv t) hh :=
  (ThreeColorGridIndex.gridEquiv (FiniteAlphabetIndex.code (fieldEquiv t) hh) (n + n)).symm j

omit [NeZero t] in
theorem gridPoint_codes (hh : h ≤ 2 ^ t) (j : Fin (h ^ (n + n))) :
    List.ofFn (fun i => ((FiniteAlphabetIndex.code (fieldEquiv t) hh) (gridPoint hh j i)).val) =
      List.ofFn (fun i : Fin (n + n) => ((finFunctionFinEquiv.symm j) i).val) := by
  congr 1
  funext i
  change ((FiniteAlphabetIndex.code (fieldEquiv t) hh)
    ((FiniteAlphabetIndex.code (fieldEquiv t) hh).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Actual tensor interpolation at the selected numeric grid address. -/
theorem tensor_run (hh : h ≤ 2 ^ t) (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (j : Fin (h ^ (n + n))) (st : State 70 20) (hc : Context t h n x z st)
    (hj : st.lists 13 = List.ofFn
      (fun i : Fin (n + n) => ((finFunctionFinEquiv.symm j) i).val)) :
    (tensor.run st).1.regs 40 = (fieldEquiv t
      (FieldQueryArithmetic.gridBasis (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh)
        (gridPoint hh j) z)).val := by
  rcases hc with ⟨h44, h45, _, _, _, _, _, h3, h7, h12, _⟩
  have hr := GridTensor.program.run_rename (Fin.castLE (by decide : 50 ≤ 70))
    (Fin.castLE (by decide : 16 ≤ 20)) (Fin.castLE_injective _) (Fin.castLE_injective _) st
  have hp := GridTensor.program_run_gridBasis hh (gridPoint hh j) z
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    ⟨h44, h45, h3, h7⟩ h12 (by
      change st.lists 13 = _
      simpa only [gridPoint_codes] using hj)
  exact (congrArg (fun r : State 50 16 × ℕ => r.1.regs 40) hr).trans hp

/-- The accumulator update uses the concrete materialized characteristic-two field operation. -/
theorem addCall_run (x : List Bool) (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (a b : BinaryMaterializedField.Element t) (st : State 70 20)
    (hc : Context t h n x z st) (ha : st.regs 50 = (fieldEquiv t a).val)
    (hb : st.regs 40 = (fieldEquiv t b).val) :
    (addCall.run st).1.regs 50 = (fieldEquiv t (a + b)).val := by
  let s := setReg (setReg (setReg st 20 (st.regs 44)) 24 (st.regs 50)) 25 (st.regs 40)
  have hr := (binary .add).run_rename (Fin.castLE (by decide : 36 ≤ 70))
    (Fin.castLE (by decide : 11 ≤ 20)) (Fin.castLE_injective _) (Fin.castLE_injective _) s
  have hp := binary_run_field .add
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) a b
    (by simpa [s, Function.update] using hc.1)
    (by simpa [s, Function.update] using ha)
    (by simpa [s, Function.update] using hb)
    hc.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.1
  have ho := congrArg (fun r : State 36 11 × ℕ => r.1.regs 26) hr
  simp only [State.restrict_regs,
    show Fin.castLE (by decide : 36 ≤ 70) (26 : Fin 36) = (26 : Fin 70) from rfl] at ho
  simp only [addCall, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update, Fin.reduceEq, dite_false, dite_true]
  dsimp only [s] at ho hp
  rw [add, ho, hp]
  rfl

theorem readOnly_seq {s u : Stmt 70 20} (hs : ReadOnly s) (hu : ReadOnly u) :
    ReadOnly (.seq s u) := by
  constructor
  · intro st i hi
    exact (hu.1 (s.run st).1 i hi).trans (hs.1 st i hi)
  · intro st i hi
    exact (hu.2 (s.run st).1 i hi).trans (hs.2 st i hi)

theorem accumulate_readOnly : ReadOnly accumulate := by
  constructor
  · intro st i hi
    by_cases hcond : st.regs 57 ≠ 0
    · simpa only [accumulate, Stmt.run, ite_eq_left hcond] using addCall_readOnly.1 st i hi
    · simp only [accumulate, Stmt.run, ite_eq_right hcond]
  · intro st i hi
    by_cases hcond : st.regs 57 ≠ 0
    · simpa only [accumulate, Stmt.run, ite_eq_left hcond] using addCall_readOnly.2 st i hi
    · simp only [accumulate, Stmt.run, ite_eq_right hcond]

theorem kernel_readOnly : ReadOnly kernel :=
  readOnly_seq reader_readOnly (readOnly_seq digitCall_readOnly
    (readOnly_seq tensor_readOnly accumulate_readOnly))

theorem reader_counter (st : State 70 20) : (reader.run st).1.regs 51 = st.regs 51 := by
  exact run_regs_frame reader 51
    (by
        unfold reader GraphAdjacency.program GraphAdjacency.code
        decide) st

theorem kernel_counter (st : State 70 20) : (kernel.run st).1.regs 51 = st.regs 51 := by
  apply run_regs_frame
  unfold kernel reader GraphAdjacency.program GraphAdjacency.code
  decide

/-- The field summand used by the arithmetic interpolation loop. -/
def summand (hh : h ≤ 2 ^ t) (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t) (j : Fin (h ^ (n + n))) :
    BinaryMaterializedField.Element t :=
  GridEdgeArithmetic.summand (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh)
    (FiniteAlphabetIndex.code (fieldEquiv t) hh) (ThreeColorEncoding.graph x) z j

set_option maxHeartbeats 1000000 in
-- The four subprogram traces are connected through their exact shared-layout frames.
/-- One actual kernel pass adds precisely the selected public edge-extension summand. -/
theorem kernel_run (hh : h ≤ 2 ^ t) (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t) (j : Fin (h ^ (n + n)))
    (a : BinaryMaterializedField.Element t) (st : State 70 20)
    (hc : Context t h n x z st) (hj : st.regs 51 = j.val)
    (ha : st.regs 50 = (fieldEquiv t a).val) :
    (kernel.run st).1.regs 50 = (fieldEquiv t (a + summand hh x z j)).val := by
  have hsc := context_readOnly reader_readOnly x z st hc
  have hsj := (reader_counter st).trans hj
  have hs50 := run_regs_frame reader 50
    (by unfold reader GraphAdjacency.program GraphAdjacency.code; decide) st
  have hflag := reader_run x z st hc
  rw [hj] at hflag
  simp only [kernel, run_seq_fst]
  generalize hs : (reader.run st).1 = s at *
  have huc := context_readOnly digitCall_readOnly x z s hsc
  have hnodes := digitCall_run x z j s hsc hsj
  have hu50 := run_regs_frame digitCall 50 (by decide) s
  have hu57 := run_regs_frame digitCall 57 (by decide) s
  generalize hu : (digitCall.run s).1 = u at *
  have hvc := context_readOnly tensor_readOnly x z u huc
  have hvalue := tensor_run hh x z j u huc hnodes
  have hv50 := run_regs_frame tensor 50 (by decide) u
  have hv57 := run_regs_frame tensor 57 (by decide) u
  generalize hv : (tensor.run u).1 = v at *
  have hacc : v.regs 50 = (fieldEquiv t a).val := hv50.trans (hu50.trans (hs50.trans ha))
  have hflag' := hv57.trans (hu57.trans hflag)
  by_cases hadj : GridEdgeArithmetic.Adj (ThreeColorEncoding.graph x)
      (j.val % h ^ n) (j.val / h ^ n)
  · have hcond : v.regs 57 ≠ 0 := by rw [hflag', ite_eq_left hadj]; decide
    simp only [accumulate, run_ite_fst, ite_eq_left hcond]
    have hadd := addCall_run x z a _ v hvc hacc hvalue
    simpa only [summand, GridEdgeArithmetic.summand, ite_eq_left hadj, gridPoint] using hadd
  · have hcond : ¬v.regs 57 ≠ 0 := by
      rw [hflag', ite_eq_right hadj]
      exact not_not_intro rfl
    simpa only [accumulate, run_ite_fst, ite_eq_right hcond, Stmt.run, summand,
      GridEdgeArithmetic.summand, ite_eq_right hadj, add_zero] using hacc

end PCP.Lang.GridEdge
