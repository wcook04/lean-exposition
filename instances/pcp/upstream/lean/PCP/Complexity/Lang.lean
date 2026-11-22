import Mathlib.Data.Nat.Size
import Mathlib.Data.Fin.Basic

/-!
# A small structured language with an explicit cost

Raw `FinTM2` programming does not scale to the transformations of the forward construction
(`jmPrep`, `prep₁`, powering, composition, the verifier).  The route chosen on 1 Oct 2026 is a
**verified compiler**: programs are written here, in a small structured language, and a single
theorem (COMPILE, `LangCompile.lean`) turns any program into a `FinTM2` machine whose step count is
polynomial in the program's **cost** plus the input length.  The cost of a particular program is
then a program-level quantity, bounded by ordinary reasoning about this semantics.

## The language

A program has `R` natural-number registers and `Q ≥ 2` list registers (stacks of naturals).  List
register `0` holds the input at the start and register `1` is read as the output at the end.

* `assign x e` — `e` an expression over registers: constant, variable, `+`, truncated `−`, `*`,
  `/`, `%`, `=` and `<` (as `0`/`1`);
* `push L x`, `pop L x flag` (head into `x`, `flag := 1` if the list was nonempty), `len L x`,
  `rev L`, `copy L L'` (`L' := L`), `revApp L L'` (`L' := reverse L ++ L'`);
* `seq`, `ite x s t` (branch on `x ≠ 0`), and `loop x s` — run `s` exactly `v` times, `v` the value
  of `x` **on entry**.  There is no unbounded loop, so every program terminates.

## The cost, and why the compiler theorem can be true

Each operation is charged the **bit sizes** (`Nat.size`) of what it reads and writes, plus one;
`len`, `rev`, `copy` and `revApp` are charged the whole source list's size. Every loop iteration
pays the counter's bit size plus one. Consequences the compiler relies on:

* every register's bit size and every list's total size stays within (input size + cost so far),
  proved in `LangSpace.lean` and for operational prefixes in `LangStep.lean`;
* so each operation's machine work is polynomial in cost + input length (multiplication and division
  are quadratic in bit size);
* repeated squaring `x := x * x` is charged its own exponentially growing result sizes, so it cannot
  hide exponential work behind a small cost.

The semantics is computable, so programs can be run on fixtures with `#guard`.
-/

namespace PCP.Lang

/-- Expressions over `R` natural registers. -/
inductive Expr (R : ℕ)
  | const (c : ℕ)
  | var (x : Fin R)
  | add (x y : Fin R)
  | sub (x y : Fin R)
  | mul (x y : Fin R)
  | div (x y : Fin R)
  | mod (x y : Fin R)
  | eq (x y : Fin R)
  | lt (x y : Fin R)
  deriving DecidableEq, Repr

/-- Statements over `R` natural registers and `Q` list registers. -/
inductive Stmt (R Q : ℕ)
  | skip
  | seq (s t : Stmt R Q)
  | assign (x : Fin R) (e : Expr R)
  | push (L : Fin Q) (x : Fin R)
  | pop (L : Fin Q) (x flag : Fin R)
  | len (L : Fin Q) (x : Fin R)
  | rev (L : Fin Q)
  | copy (L L' : Fin Q)
  | revApp (L L' : Fin Q)
  | ite (x : Fin R) (s t : Stmt R Q)
  | loop (x : Fin R) (s : Stmt R Q)
  deriving Repr

/-- A machine state: registers and lists. -/
structure State (R Q : ℕ) where
  regs : Fin R → ℕ
  lists : Fin Q → List ℕ

variable {R Q : ℕ}

/-- The value of an expression. -/
def Expr.eval (r : Fin R → ℕ) : Expr R → ℕ
  | .const c => c
  | .var x => r x
  | .add x y => r x + r y
  | .sub x y => r x - r y
  | .mul x y => r x * r y
  | .div x y => r x / r y
  | .mod x y => r x % r y
  | .eq x y => if r x = r y then 1 else 0
  | .lt x y => if r x < r y then 1 else 0

/-- The bit sizes an expression reads. -/
def Expr.readSize (r : Fin R → ℕ) : Expr R → ℕ
  | .const c => Nat.size c
  | .var x => Nat.size (r x)
  | .add x y | .sub x y | .mul x y | .div x y | .mod x y | .eq x y | .lt x y =>
      Nat.size (r x) + Nat.size (r y)

/-- **The cost of an expression**: operand sizes, result size, plus one. -/
def Expr.cost (r : Fin R → ℕ) (e : Expr R) : ℕ := e.readSize r + Nat.size (e.eval r) + 1

/-- The total bit size of a list, one extra per entry. -/
def listSize (l : List ℕ) : ℕ := (l.map fun x => Nat.size x + 1).sum

/-- Set one register. -/
def setReg (st : State R Q) (x : Fin R) (v : ℕ) : State R Q :=
  { st with regs := Function.update st.regs x v }

/-- Set one list. -/
def setList (st : State R Q) (L : Fin Q) (l : List ℕ) : State R Q :=
  { st with lists := Function.update st.lists L l }

/-- Run a body `n` times, accumulating cost; each iteration also pays `c`. -/
def iterate (body : State R Q → State R Q × ℕ) (c : ℕ) : ℕ → State R Q → State R Q × ℕ
  | 0, st => (st, 0)
  | n + 1, st =>
      let (st₁, c₁) := body st
      let (st₂, c₂) := iterate body c n st₁
      (st₂, c + c₁ + c₂)

/-- **The big-step semantics with cost**: the final state and the total cost. -/
def Stmt.run : Stmt R Q → State R Q → State R Q × ℕ
  | .skip, st => (st, 1)
  | .seq s t, st =>
      let (st₁, c₁) := s.run st
      let (st₂, c₂) := t.run st₁
      (st₂, c₁ + c₂ + 1)
  | .assign x e, st => (setReg st x (e.eval st.regs), e.cost st.regs)
  | .push L x, st =>
      (setList st L (st.regs x :: st.lists L), Nat.size (st.regs x) + 1)
  | .pop L x flag, st =>
      match st.lists L with
      | [] => (setReg (setReg st x 0) flag 0, 1)
      | v :: l => (setReg (setReg (setList st L l) x v) flag 1, Nat.size v + 1)
  | .len L x, st =>
      (setReg st x (st.lists L).length, listSize (st.lists L) + Nat.size (st.lists L).length + 1)
  | .rev L, st => (setList st L (st.lists L).reverse, listSize (st.lists L) + 1)
  | .copy L L', st => (setList st L' (st.lists L), listSize (st.lists L) + 1)
  | .revApp L L', st =>
      (setList st L' ((st.lists L).reverse ++ st.lists L'), listSize (st.lists L) + 1)
  | .ite x s t, st =>
      let (st₁, c₁) := if st.regs x ≠ 0 then s.run st else t.run st
      (st₁, c₁ + Nat.size (st.regs x) + 1)
  | .loop x s, st =>
      let n := st.regs x
      let (st₁, c₁) := iterate s.run (Nat.size n + 1) n st
      (st₁, c₁ + Nat.size n + 1)

/-! ## Step lemmas

Program proofs rewrite with these rather than unfolding `Stmt.run`, whose unfolding under `iterate`
is unmanageable. -/

section StepLemmas

variable (st : State R Q)

theorem iterate_zero_fst (f : State R Q → State R Q × ℕ) (c : ℕ) : (iterate f c 0 st).1 = st :=
  rfl

theorem iterate_succ_fst (f : State R Q → State R Q × ℕ) (c n : ℕ) :
    (iterate f c (n + 1) st).1 = (iterate f c n (f st).1).1 := rfl

theorem run_seq_fst (s t : Stmt R Q) : ((Stmt.seq s t).run st).1 = (t.run (s.run st).1).1 := rfl

theorem run_assign_fst (x : Fin R) (e : Expr R) :
    ((Stmt.assign x e).run st).1 = setReg st x (e.eval st.regs) := rfl

theorem run_push_fst (L : Fin Q) (x : Fin R) :
    ((Stmt.push L x).run st).1 = setList st L (st.regs x :: st.lists L) := rfl

theorem run_pop_cons_fst (L : Fin Q) (x flag : Fin R) {v : ℕ} {l : List ℕ}
    (h : st.lists L = v :: l) :
    ((Stmt.pop L x flag).run st).1 = setReg (setReg (setList st L l) x v) flag 1 := by
  simp [Stmt.run, h]

theorem run_pop_nil_fst (L : Fin Q) (x flag : Fin R) (h : st.lists L = []) :
    ((Stmt.pop L x flag).run st).1 = setReg (setReg st x 0) flag 0 := by
  simp [Stmt.run, h]

theorem run_len_fst (L : Fin Q) (x : Fin R) :
    ((Stmt.len L x).run st).1 = setReg st x (st.lists L).length := rfl

theorem run_rev_fst (L : Fin Q) :
    ((Stmt.rev L).run st).1 = setList st L (st.lists L).reverse := rfl

theorem run_copy_fst (L L' : Fin Q) :
    ((Stmt.copy L L').run st).1 = setList st L' (st.lists L) := rfl

theorem run_revApp_fst (L L' : Fin Q) :
    ((Stmt.revApp L L').run st).1 = setList st L' ((st.lists L).reverse ++ st.lists L') := rfl

theorem run_ite_fst (x : Fin R) (s t : Stmt R Q) :
    ((Stmt.ite x s t).run st).1 = if st.regs x ≠ 0 then (s.run st).1 else (t.run st).1 := by
  simp only [Stmt.run]; split_ifs <;> rfl

theorem run_loop_fst (x : Fin R) (s : Stmt R Q) :
    ((Stmt.loop x s).run st).1 = (iterate s.run (Nat.size (st.regs x) + 1) (st.regs x) st).1 := rfl

@[simp] theorem setReg_lists (x : Fin R) (v : ℕ) : (setReg st x v).lists = st.lists := rfl
@[simp] theorem setList_regs (L : Fin Q) (l : List ℕ) : (setList st L l).regs = st.regs := rfl
@[simp] theorem setReg_regs (x : Fin R) (v : ℕ) :
    (setReg st x v).regs = Function.update st.regs x v := rfl
@[simp] theorem setList_lists (L : Fin Q) (l : List ℕ) :
    (setList st L l).lists = Function.update st.lists L l := rfl

end StepLemmas

/-! ## Cost lemmas -/

section CostLemmas

variable (st : State R Q)

theorem run_seq_snd (s t : Stmt R Q) :
    ((Stmt.seq s t).run st).2 = (s.run st).2 + (t.run (s.run st).1).2 + 1 := rfl

theorem run_len_snd (L : Fin Q) (x : Fin R) :
    ((Stmt.len L x).run st).2
      = listSize (st.lists L) + Nat.size (st.lists L).length + 1 := rfl

theorem run_rev_snd (L : Fin Q) : ((Stmt.rev L).run st).2 = listSize (st.lists L) + 1 := rfl

theorem run_copy_snd (L L' : Fin Q) :
    ((Stmt.copy L L').run st).2 = listSize (st.lists L) + 1 := rfl

theorem run_revApp_snd (L L' : Fin Q) :
    ((Stmt.revApp L L').run st).2 = listSize (st.lists L) + 1 := rfl

theorem run_push_snd (L : Fin Q) (x : Fin R) :
    ((Stmt.push L x).run st).2 = Nat.size (st.regs x) + 1 := rfl

theorem run_loop_snd (x : Fin R) (s : Stmt R Q) :
    ((Stmt.loop x s).run st).2
      = (iterate s.run (Nat.size (st.regs x) + 1) (st.regs x) st).2 + Nat.size (st.regs x) + 1 :=
  rfl

/-- **Indexed loop invariant**: if each iteration takes `Inv j` to `Inv (j + 1)` for `j < N`, then
`N` iterations take `Inv 0` to `Inv N`. -/
theorem iterate_inv (f : State R Q → State R Q × ℕ) (c N : ℕ) (Inv : ℕ → State R Q → Prop)
    (hstep : ∀ j st, j < N → Inv j st → Inv (j + 1) (f st).1) :
    ∀ st, Inv 0 st → Inv N (iterate f c N st).1 := by
  suffices h : ∀ k j st, j + k = N → Inv j st → Inv N (iterate f c k st).1 by
    intro st h0; exact h N 0 st (by omega) h0
  intro k
  induction k with
  | zero => intro j st hj h; simp only [iterate]; rwa [show N = j by omega]
  | succ k ih =>
    intro j st hj h
    exact ih (j + 1) (f st).1 (by omega) (hstep j st (by omega) h)

/-- **Loop cost**: if the body costs at most `B` on every state satisfying an invariant it
preserves, `n` iterations cost at most `n · (c + B)`. -/
theorem iterate_cost_le (f : State R Q → State R Q × ℕ) (c B : ℕ) (P : State R Q → Prop)
    (hinv : ∀ s, P s → P (f s).1) (hB : ∀ s, P s → (f s).2 ≤ B) :
    ∀ n st, P st → (iterate f c n st).2 ≤ n * (c + B) := by
  intro n
  induction n with
  | zero => intro st _; simp [iterate]
  | succ n ih =>
    intro st hst
    have h1 := hB st hst
    have h2 := ih (f st).1 (hinv st hst)
    simp only [iterate]
    rw [Nat.succ_mul]
    omega

theorem listSize_reverse (l : List ℕ) : listSize l.reverse = listSize l := by
  simp [listSize, List.map_reverse, List.sum_reverse]

theorem size_le_listSize {l : List ℕ} {v : ℕ} (h : v ∈ l) : Nat.size v ≤ listSize l := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [listSize, List.map_cons, List.sum_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem length_le_listSize (l : List ℕ) : l.length ≤ listSize l := by
  induction l with
  | nil => simp [listSize]
  | cons a t ih =>
    simp only [listSize, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

theorem size_le_self (x : ℕ) : Nat.size x ≤ x := Nat.size_le.2 Nat.lt_two_pow_self

end CostLemmas

/-! ## Frames: what a statement can write -/

/-- The registers a statement can write, syntactically. -/
def Stmt.regWrites : Stmt R Q → List (Fin R)
  | .skip | .push _ _ | .rev _ | .copy _ _ | .revApp _ _ => []
  | .seq s t | .ite _ s t => s.regWrites ++ t.regWrites
  | .assign x _ | .len _ x => [x]
  | .pop _ x flag => [x, flag]
  | .loop _ s => s.regWrites

/-- The lists a statement can write, syntactically. -/
def Stmt.listWrites : Stmt R Q → List (Fin Q)
  | .skip | .assign _ _ | .len _ _ => []
  | .seq s t | .ite _ s t => s.listWrites ++ t.listWrites
  | .push L _ | .pop L _ _ | .rev L => [L]
  | .copy _ L' | .revApp _ L' => [L']
  | .loop _ s => s.listWrites

theorem iterate_frame (f : State R Q → State R Q × ℕ) (c : ℕ) (P : State R Q → Prop)
    (h : ∀ st, P st → P (f st).1) : ∀ n st, P st → P (iterate f c n st).1 := by
  intro n
  induction n with
  | zero => intro st hst; exact hst
  | succ n ih => intro st hst; exact ih _ (h st hst)

/-- **Register frame**: a register a statement does not write keeps its value. -/
theorem run_regs_frame (s : Stmt R Q) (r : Fin R) (h : r ∉ s.regWrites) :
    ∀ st : State R Q, (s.run st).1.regs r = st.regs r := by
  induction s with
  | skip => intro st; rfl
  | seq s t ihs iht =>
    intro st
    simp only [Stmt.regWrites, List.mem_append, not_or] at h
    rw [run_seq_fst, iht h.2, ihs h.1]
  | assign x e =>
    intro st
    simp only [Stmt.regWrites, List.mem_singleton] at h
    rw [run_assign_fst]; simp [Function.update, h]
  | push L x => intro st; rfl
  | pop L x flag =>
    intro st
    simp only [Stmt.regWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [Stmt.run]
    split <;> simp [Function.update, h.1, h.2]
  | len L x =>
    intro st
    simp only [Stmt.regWrites, List.mem_singleton] at h
    rw [run_len_fst]; simp [Function.update, h]
  | rev L => intro st; rfl
  | copy L L' => intro st; rfl
  | revApp L L' => intro st; rfl
  | ite x s t ihs iht =>
    intro st
    simp only [Stmt.regWrites, List.mem_append, not_or] at h
    rw [run_ite_fst]; split_ifs
    · exact ihs h.1 st
    · exact iht h.2 st
  | loop x s ih =>
    intro st
    simp only [Stmt.regWrites] at h
    rw [run_loop_fst]
    exact iterate_frame _ _ (fun st' => st'.regs r = st.regs r)
      (fun st' h' => (ih h st').trans h') _ st rfl

/-- **List frame**: a list a statement does not write is unchanged. -/
theorem run_lists_frame (s : Stmt R Q) (L : Fin Q) (h : L ∉ s.listWrites) :
    ∀ st : State R Q, (s.run st).1.lists L = st.lists L := by
  induction s with
  | skip => intro st; rfl
  | seq s t ihs iht =>
    intro st
    simp only [Stmt.listWrites, List.mem_append, not_or] at h
    rw [run_seq_fst, iht h.2, ihs h.1]
  | assign x e => intro st; rfl
  | push L' x =>
    intro st
    simp only [Stmt.listWrites, List.mem_singleton] at h
    rw [run_push_fst]; simp [Function.update, h]
  | pop L' x flag =>
    intro st
    simp only [Stmt.listWrites, List.mem_singleton] at h
    simp only [Stmt.run]
    split <;> simp [Function.update, h]
  | len L' x => intro st; rfl
  | rev L' =>
    intro st
    simp only [Stmt.listWrites, List.mem_singleton] at h
    rw [run_rev_fst]; simp [Function.update, h]
  | copy L₁ L₂ =>
    intro st
    simp only [Stmt.listWrites, List.mem_singleton] at h
    rw [run_copy_fst]; simp [Function.update, h]
  | revApp L₁ L₂ =>
    intro st
    simp only [Stmt.listWrites, List.mem_singleton] at h
    rw [run_revApp_fst]; simp [Function.update, h]
  | ite x s t ihs iht =>
    intro st
    simp only [Stmt.listWrites, List.mem_append, not_or] at h
    rw [run_ite_fst]; split_ifs
    · exact ihs h.1 st
    · exact iht h.2 st
  | loop x s ih =>
    intro st
    simp only [Stmt.listWrites] at h
    rw [run_loop_fst]
    exact iterate_frame _ _ (fun st' => st'.lists L = st.lists L)
      (fun st' h' => (ih h st').trans h') _ st rfl

/-- **A program**: registers, at least two lists (input `0`, output `1`), and a body. -/
structure Prog where
  R : ℕ
  Q : ℕ
  hQ : 2 ≤ Q
  body : Stmt R Q

namespace Prog

variable (P : Prog)

/-- The input list register. -/
def inL : Fin P.Q := ⟨0, by have := P.hQ; omega⟩

/-- The output list register. -/
def outL : Fin P.Q := ⟨1, by have := P.hQ; omega⟩

/-- The initial state on input `l`: registers zero, the input in list `0`, other lists empty. -/
def init (l : List ℕ) : State P.R P.Q :=
  ⟨fun _ => 0, fun L => if L = P.inL then l else []⟩

/-- **What a program computes**: list register `1` at the end. -/
def run (l : List ℕ) : List ℕ := ((P.body.run (P.init l)).1).lists P.outL

/-- **What a program costs** on input `l`. -/
def cost (l : List ℕ) : ℕ := (P.body.run (P.init l)).2

end Prog

end PCP.Lang
