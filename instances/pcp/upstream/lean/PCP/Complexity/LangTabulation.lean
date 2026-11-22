/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.LangCost

/-!
# Counted enumeration with a certified scalar kernel

The tabulator calls a supplied `Lang` kernel on consecutive numeric indices and
stores its answers in order. The interface states exact effects and a per-call
cost bound; no semantic oracle is inserted into the program. This combinator is
the matrix-emission part of the graph-construction program, whose concrete
adjacency kernel must satisfy the displayed interface.
-/

namespace PCP.Lang.Tabulation

variable {R Q : ℕ}

private theorem reg_ne (i j : ℕ) (hi : i < 4) (hj : j < 4) (hne : i ≠ j) :
    Fin.ofNat (R + 4) i ≠ Fin.ofNat (R + 4) j := by
  intro h
  have he := congrArg Fin.val h
  change i % (R + 4) = j % (R + 4) at he
  rw [Nat.mod_eq_of_lt (by omega : i < R + 4),
    Nat.mod_eq_of_lt (by omega : j < R + 4)] at he
  exact hne he

/-- Register 0 is the index, 1 the answer, 2 the constant one, and 3 the count.
List 0 contains the preserved public input and list 1 collects the answers. -/
def body (kernel : Stmt (R + 4) (Q + 2)) : Stmt (R + 4) (Q + 2) :=
  .seq kernel (.seq (.push 1 1) (.assign 0 (.add 0 2)))

def tabulate (kernel : Stmt (R + 4) (Q + 2)) : Stmt (R + 4) (Q + 2) :=
  .seq (.assign 0 (.const 0)) (.seq (.assign 2 (.const 1))
    (.seq (.loop 3 (body kernel)) (.rev 1)))

/-- A kernel computes one answer and preserves the loop's control and output storage. -/
def KernelSpec (kernel : Stmt (R + 4) (Q + 2)) (input : List ℕ) (n : ℕ)
    (f : ℕ → ℕ) : Prop :=
  ∀ st : State (R + 4) (Q + 2), st.lists 0 = input → st.regs 2 = 1 → st.regs 3 = n →
    st.regs 0 < n →
    (kernel.run st).1.regs 0 = st.regs 0 ∧
    (kernel.run st).1.regs 1 = f (st.regs 0) ∧
    (kernel.run st).1.regs 2 = 1 ∧ (kernel.run st).1.regs 3 = n ∧
    (kernel.run st).1.lists 0 = input ∧ (kernel.run st).1.lists 1 = st.lists 1

theorem body_spec {kernel : Stmt (R + 4) (Q + 2)} {input : List ℕ} {n : ℕ} {f : ℕ → ℕ}
    (hk : KernelSpec kernel input n f) (st : State (R + 4) (Q + 2))
    (hi : st.lists 0 = input) (h1 : st.regs 2 = 1) (hn : st.regs 3 = n)
    (hj : st.regs 0 < n) :
    ((body kernel).run st).1.regs 0 = st.regs 0 + 1 ∧
    ((body kernel).run st).1.regs 2 = 1 ∧ ((body kernel).run st).1.regs 3 = n ∧
    ((body kernel).run st).1.lists 0 = input ∧
    ((body kernel).run st).1.lists 1 = f (st.regs 0) :: st.lists 1 := by
  obtain ⟨h0, ho, h2, h3, hl0, hl1⟩ := hk st hi h1 hn hj
  have h20 : (2 : Fin (R + 4)) ≠ 0 := reg_ne 2 0 (by decide) (by decide) (by decide)
  have h30 : (3 : Fin (R + 4)) ≠ 0 := reg_ne 3 0 (by decide) (by decide) (by decide)
  simp [body, run_seq_fst, run_push_fst, run_assign_fst, Expr.eval,
    Function.update, h0, ho, h2, h3, hl0, hl1, h20, h30]

/-- The concrete loop invariant includes every emitted value and the preserved source input. -/
def Inv (input : List ℕ) (n : ℕ) (f : ℕ → ℕ) (j : ℕ)
    (st : State (R + 4) (Q + 2)) : Prop :=
  st.regs 0 = j ∧ st.regs 2 = 1 ∧ st.regs 3 = n ∧ st.lists 0 = input ∧
    st.lists 1 = ((List.range j).map f).reverse

theorem body_inv {kernel : Stmt (R + 4) (Q + 2)} {input : List ℕ} {n : ℕ} {f : ℕ → ℕ}
    (hk : KernelSpec kernel input n f) (j : ℕ) (st : State (R + 4) (Q + 2))
    (hj : j < n) (hst : Inv input n f j st) :
    Inv input n f (j + 1) ((body kernel).run st).1 := by
  obtain ⟨h0, h2, h3, hl0, hl1⟩ := body_spec hk st hst.2.2.2.1 hst.2.1 hst.2.2.1
    (by rw [hst.1]; exact hj)
  refine ⟨by rw [h0, hst.1], h2, h3, hl0, ?_⟩
  rw [hl1, hst.1, hst.2.2.2.2]
  simp [List.range_succ]

/-- The tabulator emits exactly the ordered sequence of kernel answers. -/
theorem tabulate_spec {kernel : Stmt (R + 4) (Q + 2)} {input : List ℕ} {n : ℕ} {f : ℕ → ℕ}
    (hk : KernelSpec kernel input n f) (st : State (R + 4) (Q + 2))
    (hi : st.lists 0 = input) (hn : st.regs 3 = n) (ho : st.lists 1 = []) :
    ((tabulate kernel).run st).1.lists 1 = (List.range n).map f ∧
      ((tabulate kernel).run st).1.lists 0 = input := by
  let initial := setReg (setReg st 0 0) 2 1
  have hinitial : Inv input n f 0 initial := by
    have h02 : (0 : Fin (R + 4)) ≠ 2 := reg_ne 0 2 (by decide) (by decide) (by decide)
    have h32 : (3 : Fin (R + 4)) ≠ 2 := reg_ne 3 2 (by decide) (by decide) (by decide)
    have h30 : (3 : Fin (R + 4)) ≠ 0 := reg_ne 3 0 (by decide) (by decide) (by decide)
    simp [Inv, initial, Function.update, hi, hn, ho, h02, h32, h30]
  have hout := iterate_inv (body kernel).run (Nat.size n + 1) n (Inv input n f)
    (body_inv hk) initial hinitial
  simp only [tabulate, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst, run_rev_fst]
  change (setList (iterate (body kernel).run (Nat.size (initial.regs 3) + 1)
    (initial.regs 3) initial).1 1
    ((iterate (body kernel).run (Nat.size (initial.regs 3) + 1)
      (initial.regs 3) initial).1.lists 1).reverse).lists 1 = _ ∧ _
  rw [hinitial.2.2.1]
  constructor
  · simp [Function.update, hout.2.2.2.2]
  · change (iterate (body kernel).run (Nat.size n + 1) n initial).1.lists 0 = input
    exact hout.2.2.2.1


/-- A per-call bound for the actual supplied kernel, on precisely the states it receives. -/
def KernelCost (kernel : Stmt (R + 4) (Q + 2)) (input : List ℕ) (n B : ℕ) : Prop :=
  ∀ st : State (R + 4) (Q + 2), st.lists 0 = input → st.regs 2 = 1 → st.regs 3 = n →
    st.regs 0 < n → (kernel.run st).2 ≤ B

theorem body_cost {kernel : Stmt (R + 4) (Q + 2)} {input : List ℕ} {n B D : ℕ}
    {f : ℕ → ℕ} (hk : KernelSpec kernel input n f) (hc : KernelCost kernel input n B)
    (hf : ∀ j < n, Nat.size (f j) ≤ D) (st : State (R + 4) (Q + 2))
    (hi : st.lists 0 = input) (h1 : st.regs 2 = 1) (hn : st.regs 3 = n)
    (hj : st.regs 0 < n) :
    ((body kernel).run st).2 ≤ B + D + 2 * Nat.size n + 5 := by
  obtain ⟨h0, ho, h2, _, _, _⟩ := hk st hi h1 hn hj
  have hkcost := hc st hi h1 hn hj
  have hvalue := hf (st.regs 0) hj
  have hindex := Nat.size_le_size hj.le
  have hnext := Nat.size_le_size (Nat.succ_le_of_lt hj)
  simp only [Nat.succ_eq_add_one] at hnext
  simp only [body, setList_regs, Stmt.run,
    Expr.cost, Expr.readSize, Expr.eval, h0, ho, h2, Nat.size_one]
  omega

theorem answers_size_le (n D : ℕ) (f : ℕ → ℕ) (hf : ∀ j < n, Nat.size (f j) ≤ D) :
    listSize ((List.range n).map f) ≤ n * (D + 1) := by
  induction n with
  | zero => simp [listSize]
  | succ n ih =>
      have hprev := ih (fun j hj => hf j (by omega))
      have hlast := hf n (by omega)
      simp only [List.range_succ, List.map_append, List.map_singleton, listSize,
        List.sum_append, List.sum_cons, List.sum_nil] at hprev ⊢
      nlinarith

/-- The output loop adds polynomial overhead to a certified concrete scalar kernel. -/
theorem tabulate_cost {kernel : Stmt (R + 4) (Q + 2)} {input : List ℕ} {n B D : ℕ}
    {f : ℕ → ℕ} (hk : KernelSpec kernel input n f) (hc : KernelCost kernel input n B)
    (hf : ∀ j < n, Nat.size (f j) ≤ D) (st : State (R + 4) (Q + 2))
    (hi : st.lists 0 = input) (hn : st.regs 3 = n) (ho : st.lists 1 = []) :
    ((tabulate kernel).run st).2 ≤
      n * (B + 2 * D + 3 * Nat.size n + 7) + Nat.size n + 9 := by
  let initial := setReg (setReg st 0 0) 2 1
  have hinitial : Inv input n f 0 initial := by
    have h02 : (0 : Fin (R + 4)) ≠ 2 := reg_ne 0 2 (by decide) (by decide) (by decide)
    have h32 : (3 : Fin (R + 4)) ≠ 2 := reg_ne 3 2 (by decide) (by decide) (by decide)
    have h30 : (3 : Fin (R + 4)) ≠ 0 := reg_ne 3 0 (by decide) (by decide) (by decide)
    simp [Inv, initial, Function.update, hi, hn, ho, h02, h32, h30]
  have hiter := iterate_cost_idx (body kernel).run (Nat.size n + 1)
    (B + D + 2 * Nat.size n + 5) n (Inv input n f)
    (fun j s hj hs => ⟨body_inv hk j s hj hs,
      body_cost hk hc hf s hs.2.2.2.1 hs.2.1 hs.2.2.1 (by rw [hs.1]; exact hj)⟩)
    initial hinitial
  have hout := iterate_inv (body kernel).run (Nat.size n + 1) n (Inv input n f)
    (body_inv hk) initial hinitial
  have hsize := answers_size_le n D f hf
  have houtput : listSize ((iterate (body kernel).run (Nat.size n + 1) n initial).1.lists 1) ≤
      n * (D + 1) := by
    rw [hout.2.2.2.2, listSize_reverse]
    exact hsize
  simp only [tabulate, run_seq_snd, run_assign_fst, Expr.eval,
    run_loop_snd, run_loop_fst, run_rev_snd]
  have hc0 : ((Stmt.assign 0 (.const 0)).run st).2 = 1 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  have hc1 : ((Stmt.assign 2 (.const 1)).run (setReg st 0 0)).2 = 3 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  rw [hc0, hc1]
  change 1 + (3 + ((iterate (body kernel).run (Nat.size (initial.regs 3) + 1)
    (initial.regs 3) initial).2 + Nat.size (initial.regs 3) + 1 +
    (listSize ((iterate (body kernel).run (Nat.size (initial.regs 3) + 1)
      (initial.regs 3) initial).1.lists 1) + 1) + 1) + 1) + 1 ≤ _
  rw [hinitial.2.2.1]
  nlinarith

end PCP.Lang.Tabulation
