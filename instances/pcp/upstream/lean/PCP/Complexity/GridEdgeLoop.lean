import PCP.Complexity.GridEdgeKernel

/-!
# The complete counted public edge interpolation sum

The loop traverses the explicit numeric codes of all pairs of grid vertices.
Its field accumulator equals the mathematical edge extension on every input.
-/

namespace PCP.Lang.GridEdge

open PCP.Algebraic BinaryFieldCode

variable {t h n : ℕ} [NeZero t]

def bump : Stmt 70 20 := .assign 51 (.add 51 69)

def body : Stmt 70 20 := .seq kernel bump

def loop : Stmt 70 20 := .loop 52 body

theorem bump_readOnly : ReadOnly bump := by
  constructor
  · intro st i hi
    apply run_regs_frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro st i hi
    exact run_lists_frame bump i (by simp [bump, Stmt.listWrites]) st

theorem body_readOnly : ReadOnly body := readOnly_seq kernel_readOnly bump_readOnly

/-- Extend the bounded summand by zero solely for indexing finite range sums. -/
def term (hh : h ≤ 2 ^ t) (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t) (j : ℕ) :
    BinaryMaterializedField.Element t :=
  if hj : j < h ^ (n + n) then summand hh x z ⟨j, hj⟩ else 0

theorem term_eq (hh : h ≤ 2 ^ t) (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t) (j : Fin (h ^ (n + n))) :
    term hh x z j.val = summand hh x z j := dite_eq_left j.isLt

/-- Each pass advances exactly one address and adds its certified field summand. -/
theorem body_run (hh : h ≤ 2 ^ t) (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t) (j : Fin (h ^ (n + n)))
    (a : BinaryMaterializedField.Element t) (st : State 70 20)
    (hc : Context t h n x z st) (hj : st.regs 51 = j.val)
    (ha : st.regs 50 = (fieldEquiv t a).val) :
    Context t h n x z (body.run st).1 ∧
      (body.run st).1.regs 51 = j.val + 1 ∧
      (body.run st).1.regs 50 = (fieldEquiv t (a + term hh x z j.val)).val := by
  have hkc := context_readOnly kernel_readOnly x z st hc
  have hki := (kernel_counter st).trans hj
  have hka := kernel_run hh x z j a st hc hj ha
  refine ⟨context_readOnly body_readOnly x z st hc, ?_, ?_⟩
  · simp only [body, run_seq_fst, bump, run_assign_fst, Expr.eval,
      setReg_regs, Function.update_self]
    rw [hki, hkc.2.2.2.2.2.2.1]
  · rw [body, run_seq_fst, run_regs_frame bump 50 (by decide)]
    simpa only [term_eq] using hka

/-- The explicit counted loop computes the range sum without an enumeration oracle. -/
theorem iterate_run (hh : h ≤ 2 ^ t) (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t) (k j : ℕ)
    (hjk : j + k ≤ h ^ (n + n)) (a : BinaryMaterializedField.Element t)
    (c : ℕ) (st : State 70 20) (hc : Context t h n x z st)
    (hj : st.regs 51 = j) (ha : st.regs 50 = (fieldEquiv t a).val) :
    Context t h n x z (iterate body.run c k st).1 ∧
      (iterate body.run c k st).1.regs 51 = j + k ∧
      (iterate body.run c k st).1.regs 50 =
        (fieldEquiv t (a + ∑ i ∈ Finset.range k, term hh x z (j + i))).val := by
  induction k generalizing j a st with
  | zero => simpa only [iterate, add_zero, Finset.range_zero, Finset.sum_empty] using
      And.intro hc (And.intro hj ha)
  | succ k ih =>
    have hjlt : j < h ^ (n + n) := by omega
    have hb := body_run hh x z ⟨j, hjlt⟩ a st hc hj ha
    have hout := ih (j + 1) (by omega) (a + term hh x z j) (body.run st).1
      hb.1 hb.2.1 hb.2.2
    rw [iterate_succ_fst]
    refine ⟨hout.1, ?_, ?_⟩
    · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hout.2.1
    · rw [hout.2.2, Finset.sum_range_succ']
      congr 2
      simp only [Nat.add_zero, Nat.add_assoc]
      abel_nf

/-- The executable loop returns the actual public graph's edge extension. -/
theorem loop_run (hh : h ≤ 2 ^ t) (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t) (st : State 70 20)
    (hc : Context t h n x z st) (hj : st.regs 51 = 0)
    (ha : st.regs 50 = (fieldEquiv t (0 : BinaryMaterializedField.Element t)).val) :
    (loop.run st).1.regs 50 = (fieldEquiv t
      (FieldQueryArithmetic.edgeValue (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh)
        (ThreeColorGridIndex.pad (FiniteAlphabetIndex.code (fieldEquiv t) hh) n
          (ThreeColorEncoding.graph x)) z)).val := by
  have hout := iterate_run hh x z (h ^ (n + n)) 0 (by omega) 0
    (Nat.size (h ^ (n + n)) + 1) st hc hj ha
  rw [loop, run_loop_fst, hc.2.2.1, hout.2.2]
  congr 1
  rw [GridEdgeArithmetic.edgeValue_sum]
  simp only [zero_add]
  rw [← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact term_eq hh x z j

end PCP.Lang.GridEdge
