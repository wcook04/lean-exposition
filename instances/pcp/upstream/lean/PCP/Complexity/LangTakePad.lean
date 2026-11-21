import PCP.Complexity.LangCost

/-!
# Taking a stored word with zero padding and retaining its suffix

The loop runs for the requested output length, never for a numeric address.
An exhausted source contributes zero. This implements repetition seed blocks
and exact answer-history consumption with the same concrete list primitives.
-/

namespace PCP.Lang.TakePad

def take (n : ℕ) (xs : List ℕ) : List ℕ :=
  xs.take n ++ List.replicate (n-xs.length) 0

@[simp] theorem take_zero (xs : List ℕ) : take 0 xs = [] := by simp [take]

theorem take_succ (n : ℕ) (xs : List ℕ) :
    take (n+1) xs = xs.headD 0 :: take n xs.tail := by
  cases xs with
  | nil => simp [take, List.replicate_succ]
  | cons x xs => simp [take, Nat.add_sub_add_right]

@[simp] theorem length_take (n : ℕ) (xs : List ℕ) : (take n xs).length = n := by
  simp [take]
  omega

theorem size_take (n : ℕ) (xs : List ℕ) : listSize (take n xs) ≤ listSize xs+n := by
  induction n generalizing xs with
  | zero => simp [listSize]
  | succ n ih =>
      rw [take_succ]
      cases xs with
      | nil =>
          have h := ih []
          simp only [show listSize ([] : List ℕ) = 0 from rfl, Nat.zero_add] at h
          simp only [List.headD_nil, List.tail_nil, listSize, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, Nat.size_zero, Nat.zero_add]
          simp only [listSize] at h
          omega
      | cons x xs =>
          simp only [List.headD_cons, List.tail_cons, listSize, List.map_cons, List.sum_cons]
          have h := ih xs
          simp only [listSize] at h
          omega

/-- Reading within the requested prefix observes the source, with the same zero default. -/
theorem getD_take (n i : ℕ) (xs : List ℕ) (hi : i < n) :
    (take n xs).getD i 0 = xs.getD i 0 := by
  induction n generalizing xs i with
  | zero => omega
  | succ n ih =>
      rw [take_succ]
      cases i with
      | zero => cases xs <;> rfl
      | succ i =>
          simp only [List.getD_cons_succ]
          rw [ih i xs.tail (by omega)]
          cases xs <;> simp


def body : Stmt 3 3 := .seq (.pop 0 1 2) (.push 1 1)

def program : Stmt 3 3 := .seq (.copy 2 1) (.seq (.loop 0 body) (.rev 1))

theorem body_run (st : State 3 3) :
    (body.run st).1.lists 0 = (st.lists 0).tail ∧
    (body.run st).1.lists 1 = (st.lists 0).headD 0 :: st.lists 1 ∧
    (body.run st).1.lists 2 = st.lists 2 ∧ (body.run st).1.regs 0 = st.regs 0 := by
  cases h : st.lists 0 <;> simp [body, Stmt.run, h, Function.update]

theorem iterate_run (n c : ℕ) (st : State 3 3) :
    (iterate body.run c n st).1.lists 0 = (st.lists 0).drop n ∧
    (iterate body.run c n st).1.lists 1 = (take n (st.lists 0)).reverse ++ st.lists 1 ∧
    (iterate body.run c n st).1.lists 2 = st.lists 2 ∧
    (iterate body.run c n st).1.regs 0 = st.regs 0 := by
  induction n generalizing st with
  | zero => simp [iterate]
  | succ n ih =>
      have hb := body_run st
      have hi := ih (body.run st).1
      rw [iterate_succ_fst]
      refine ⟨?_, ?_, hi.2.2.1.trans hb.2.2.1, hi.2.2.2.trans hb.2.2.2⟩
      · rw [hi.1, hb.1]
        simp only [List.drop_tail]
      · rw [hi.2.1, hb.1, hb.2.1, take_succ, List.reverse_cons]
        simp only [List.append_assoc, List.singleton_append]

/-- Source list zero is consumed; list one receives the exact padded prefix. -/
theorem program_run (st : State 3 3) (he : st.lists 2 = []) :
    (program.run st).1.lists 0 = (st.lists 0).drop (st.regs 0) ∧
    (program.run st).1.lists 1 = take (st.regs 0) (st.lists 0) ∧
    (program.run st).1.lists 2 = [] ∧ (program.run st).1.regs 0 = st.regs 0 := by
  let s := setList st 1 []
  have hi := iterate_run (st.regs 0) (Nat.size (st.regs 0)+1) s
  have hs0 : s.lists 0 = st.lists 0 := by simp [s, Function.update]
  have hs1 : s.lists 1 = [] := by simp [s]
  have hs2 : s.lists 2 = [] := by simpa [s, Function.update] using he
  rw [hs0, hs1, List.append_nil, hs2] at hi
  simp only [program, run_seq_fst, run_copy_fst, he, run_loop_fst, setList_regs, run_rev_fst]
  change (setList (iterate body.run (Nat.size (st.regs 0)+1) (st.regs 0) s).1 1
    ((iterate body.run (Nat.size (st.regs 0)+1) (st.regs 0) s).1.lists 1).reverse).lists 0 = _ ∧ _
  constructor
  · simpa only [setList_lists, Function.update, Fin.reduceEq, dite_false] using hi.1
  constructor
  · simpa only [setList_lists, Function.update, dite_true, List.reverse_reverse] using
      congrArg List.reverse hi.2.1
  constructor
  · simpa only [setList_lists, Function.update, Fin.reduceEq, dite_false] using hi.2.2.1
  · simpa only [setList_regs, s] using hi.2.2.2

theorem body_cost (st : State 3 3) :
    (body.run st).2 ≤ 2*listSize (st.lists 0)+3 := by
  cases h : st.lists 0 with
  | nil => simp [body, Stmt.run, Function.update, h]
  | cons x xs => simp [body, Stmt.run, Function.update, h, listSize]; omega

theorem body_space (st : State 3 3) :
    listSize ((body.run st).1.lists 0) ≤ listSize (st.lists 0) := by
  rw [(body_run st).1]
  cases st.lists 0 <;> simp [listSize]

/-- Charged quadratic cost in the stored source and requested output length. -/
theorem program_cost (st : State 3 3) (he : st.lists 2 = []) :
    (program.run st).2 ≤ 20*(listSize (st.lists 0)+st.regs 0+1)^2 := by
  let n := st.regs 0
  let S := listSize (st.lists 0)
  let s := setList st 1 []
  have hs : listSize (s.lists 0) = S := by simp [s, S, Function.update]
  have hi := iterate_cost_le body.run (Nat.size n+1) (2*S+3)
    (fun u : State 3 3 => listSize (u.lists 0) ≤ S)
    (fun u hu => (body_space u).trans hu)
    (fun u hu => (body_cost u).trans (by omega)) n s hs.le
  have hout := (iterate_run n (Nat.size n+1) s).2.1
  have hs1 : s.lists 1 = [] := by simp [s]
  rw [hs1, List.append_nil] at hout
  have ho : listSize ((iterate body.run (Nat.size n+1) n s).1.lists 1) ≤ S+n := by
    rw [hout, listSize_reverse]
    have h := size_take n (s.lists 0)
    rw [hs] at h
    exact h
  have hn := size_le_self n
  simp only [program, run_seq_snd, run_copy_snd, run_copy_fst, he, run_loop_snd,
    setList_regs, run_loop_fst, run_rev_snd, show listSize ([] : List ℕ) = 0 from rfl]
  change 0+1+(((iterate body.run (Nat.size n+1) n s).2+Nat.size n+1)+
    (listSize ((iterate body.run (Nat.size n+1) n s).1.lists 1)+1)+1)+1 ≤ 20*(S+n+1)^2
  nlinarith

end PCP.Lang.TakePad
