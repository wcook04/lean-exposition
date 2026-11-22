import PCP.Complexity.LangTabulation

/-!
# Counted scalar tabulation with preserved caller data

The kernel receives an explicit invariant for stored parameters, such as the
field width and modulus. The invariant is proved for every intermediate state;
it is not an assumption inserted into the executed program.
-/

namespace PCP.Lang.FramedTabulation

open Tabulation

variable {R Q : ℕ}

private theorem reg_ne (i j : ℕ) (hi : i < 4) (hj : j < 4) (hne : i ≠ j) :
    Fin.ofNat (R + 4) i ≠ Fin.ofNat (R + 4) j := by
  intro h
  have he := congrArg Fin.val h
  change i % (R + 4) = j % (R + 4) at he
  rw [Nat.mod_eq_of_lt (by omega : i < R + 4),
    Nat.mod_eq_of_lt (by omega : j < R + 4)] at he
  exact hne he

/-- Caller data is independent of the tabulator's index, unit, and output storage. -/
def Stable (J : State (R + 4) (Q + 2) → Prop) : Prop :=
  (∀ st, J st → ∀ v, J (setReg st 0 v)) ∧
  (∀ st, J st → ∀ v, J (setReg st 2 v)) ∧
  (∀ st, J st → ∀ xs, J (setList st 1 xs))

/-- The concrete kernel preserves both loop storage and the caller's invariant. -/
def KernelSpec (kernel : Stmt (R + 4) (Q + 2)) (input : List ℕ) (n : ℕ)
    (f : ℕ → ℕ) (J : State (R + 4) (Q + 2) → Prop) : Prop :=
  ∀ st, st.lists 0 = input → st.regs 2 = 1 → st.regs 3 = n → st.regs 0 < n → J st →
    (kernel.run st).1.regs 0 = st.regs 0 ∧
    (kernel.run st).1.regs 1 = f (st.regs 0) ∧
    (kernel.run st).1.regs 2 = 1 ∧ (kernel.run st).1.regs 3 = n ∧
    (kernel.run st).1.lists 0 = input ∧ (kernel.run st).1.lists 1 = st.lists 1 ∧
    J (kernel.run st).1

def Inv (input : List ℕ) (n : ℕ) (f : ℕ → ℕ)
    (J : State (R + 4) (Q + 2) → Prop) (j : ℕ) (st : State (R + 4) (Q + 2)) : Prop :=
  Tabulation.Inv input n f j st ∧ J st

theorem body_inv {kernel : Stmt (R + 4) (Q + 2)} {input : List ℕ} {n : ℕ}
    {f : ℕ → ℕ} {J : State (R + 4) (Q + 2) → Prop}
    (hk : KernelSpec kernel input n f J) (hJ : Stable J)
    (j : ℕ) (st : State (R + 4) (Q + 2)) (hj : j < n) (hs : Inv input n f J j st) :
    Inv input n f J (j + 1) ((body kernel).run st).1 := by
  obtain ⟨h0, ho, h2, h3, hl0, hl1, hJK⟩ := hk st hs.1.2.2.2.1 hs.1.2.1 hs.1.2.2.1
    (by rw [hs.1.1]; exact hj) hs.2
  have h20 : (2 : Fin (R + 4)) ≠ 0 := reg_ne 2 0 (by decide) (by decide) (by decide)
  have h30 : (3 : Fin (R + 4)) ≠ 0 := reg_ne 3 0 (by decide) (by decide) (by decide)
  constructor
  · simp only [Tabulation.Inv, body, run_seq_fst, run_push_fst, run_assign_fst,
      Expr.eval, setReg_regs, setReg_lists, setList_regs, setList_lists]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Function.update, h0, hs.1.1, h2]
    · simp [Function.update, h20, h2]
    · simp [Function.update, h30, h3]
    · simpa using hl0
    · simp [Function.update, ho, hl1, hs.1.1, hs.1.2.2.2.2, List.range_succ]
  · simp only [body, run_seq_fst, run_push_fst, run_assign_fst]
    exact hJ.1 _ (hJ.2.2 _ hJK _) _

private theorem initial_inv {input : List ℕ} {n : ℕ} {f : ℕ → ℕ}
    {J : State (R + 4) (Q + 2) → Prop} (hJ : Stable J) (st : State (R + 4) (Q + 2))
    (hi : st.lists 0 = input) (hn : st.regs 3 = n) (ho : st.lists 1 = []) (hj : J st) :
    Inv input n f J 0 (setReg (setReg st 0 0) 2 1) := by
  have h02 : (0 : Fin (R + 4)) ≠ 2 := reg_ne 0 2 (by decide) (by decide) (by decide)
  have h32 : (3 : Fin (R + 4)) ≠ 2 := reg_ne 3 2 (by decide) (by decide) (by decide)
  have h30 : (3 : Fin (R + 4)) ≠ 0 := reg_ne 3 0 (by decide) (by decide) (by decide)
  constructor
  · simp [Tabulation.Inv, Function.update, hi, hn, ho, h02, h32, h30]
  · exact hJ.2.1 _ (hJ.1 _ hj _) _

/-- Actual enumeration in increasing numeric order, retaining all caller data. -/
theorem tabulate_spec {kernel : Stmt (R + 4) (Q + 2)} {input : List ℕ} {n : ℕ}
    {f : ℕ → ℕ} {J : State (R + 4) (Q + 2) → Prop}
    (hk : KernelSpec kernel input n f J) (hJ : Stable J)
    (st : State (R + 4) (Q + 2)) (hi : st.lists 0 = input) (hn : st.regs 3 = n)
    (ho : st.lists 1 = []) (hj : J st) :
    ((tabulate kernel).run st).1.lists 1 = (List.range n).map f ∧
    ((tabulate kernel).run st).1.lists 0 = input ∧ J ((tabulate kernel).run st).1 := by
  let initial := setReg (setReg st 0 0) 2 1
  have hinitial : Inv input n f J 0 initial := initial_inv hJ st hi hn ho hj
  have hout := iterate_inv (body kernel).run (Nat.size n + 1) n (Inv input n f J)
    (body_inv hk hJ) initial hinitial
  simp only [tabulate, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst, run_rev_fst]
  change (setList (iterate (body kernel).run (Nat.size (initial.regs 3) + 1)
    (initial.regs 3) initial).1 1
    ((iterate (body kernel).run (Nat.size (initial.regs 3) + 1)
      (initial.regs 3) initial).1.lists 1).reverse).lists 1 = _ ∧ _
  rw [hinitial.1.2.2.1]
  refine ⟨?_, ?_, hJ.2.2 _ hout.2 _⟩
  · simp [Function.update, hout.1.2.2.2.2]
  · exact hout.1.2.2.2.1

/-- Per-call charged cost for states satisfying the proved caller invariant. -/
def KernelCost (kernel : Stmt (R + 4) (Q + 2)) (input : List ℕ) (n B : ℕ)
    (J : State (R + 4) (Q + 2) → Prop) : Prop :=
  ∀ st, st.lists 0 = input → st.regs 2 = 1 → st.regs 3 = n → st.regs 0 < n → J st →
    (kernel.run st).2 ≤ B

theorem body_cost {kernel : Stmt (R + 4) (Q + 2)} {input : List ℕ} {n B D : ℕ}
    {f : ℕ → ℕ} {J : State (R + 4) (Q + 2) → Prop}
    (hk : KernelSpec kernel input n f J) (hc : KernelCost kernel input n B J)
    (hf : ∀ j < n, Nat.size (f j) ≤ D) (st : State (R + 4) (Q + 2))
    (hi : st.lists 0 = input) (h1 : st.regs 2 = 1) (hn : st.regs 3 = n)
    (hi' : st.regs 0 < n) (hj : J st) :
    ((body kernel).run st).2 ≤ B + D + 2 * Nat.size n + 5 := by
  obtain ⟨h0, ho, h2, _, _, _, _⟩ := hk st hi h1 hn hi' hj
  have hkcost := hc st hi h1 hn hi' hj
  have hvalue := hf (st.regs 0) hi'
  have hindex := Nat.size_le_size hi'.le
  have hnext := Nat.size_le_size (Nat.succ_le_of_lt hi')
  simp only [Nat.succ_eq_add_one] at hnext
  simp only [body, setList_regs, Stmt.run,
    Expr.cost, Expr.readSize, Expr.eval, h0, ho, h2, Nat.size_one]
  omega

/-- Polynomial enumeration overhead, with the concrete kernel bound charged at every call. -/
theorem tabulate_cost {kernel : Stmt (R + 4) (Q + 2)} {input : List ℕ} {n B D : ℕ}
    {f : ℕ → ℕ} {J : State (R + 4) (Q + 2) → Prop}
    (hk : KernelSpec kernel input n f J) (hJ : Stable J) (hc : KernelCost kernel input n B J)
    (hf : ∀ j < n, Nat.size (f j) ≤ D) (st : State (R + 4) (Q + 2))
    (hi : st.lists 0 = input) (hn : st.regs 3 = n) (ho : st.lists 1 = []) (hj : J st) :
    ((tabulate kernel).run st).2 ≤
      n * (B + 2 * D + 3 * Nat.size n + 7) + Nat.size n + 9 := by
  let initial := setReg (setReg st 0 0) 2 1
  have hinitial : Inv input n f J 0 initial := initial_inv hJ st hi hn ho hj
  have hiter := iterate_cost_idx (body kernel).run (Nat.size n + 1)
    (B + D + 2 * Nat.size n + 5) n (Inv input n f J)
    (fun j s hj hs => ⟨body_inv hk hJ j s hj hs,
      body_cost hk hc hf s hs.1.2.2.2.1 hs.1.2.1 hs.1.2.2.1
        (by rw [hs.1.1]; exact hj) hs.2⟩) initial hinitial
  have hout := iterate_inv (body kernel).run (Nat.size n + 1) n (Inv input n f J)
    (body_inv hk hJ) initial hinitial
  have hsize := answers_size_le n D f hf
  have houtput : listSize ((iterate (body kernel).run (Nat.size n + 1) n initial).1.lists 1) ≤
      n * (D + 1) := by
    rw [hout.1.2.2.2.2, listSize_reverse]
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
  rw [hinitial.1.2.2.1]
  nlinarith

end PCP.Lang.FramedTabulation
