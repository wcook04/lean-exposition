/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.Lang
import Mathlib.Tactic

/-!
# Embedding language subprograms in larger register files

Injective register and list renamings preserve both the result and the exact
charged cost. Thus a small verified routine can be reused inside the complete
verifier without reproving its operational semantics for a new register layout.
-/

namespace PCP.Lang

variable {R Q R' Q' : ℕ}

def Expr.rename (r : Fin R → Fin R') : Expr R → Expr R'
  | .const c => .const c
  | .var x => .var (r x)
  | .add x y => .add (r x) (r y)
  | .sub x y => .sub (r x) (r y)
  | .mul x y => .mul (r x) (r y)
  | .div x y => .div (r x) (r y)
  | .mod x y => .mod (r x) (r y)
  | .eq x y => .eq (r x) (r y)
  | .lt x y => .lt (r x) (r y)

def Stmt.rename (r : Fin R → Fin R') (q : Fin Q → Fin Q') : Stmt R Q → Stmt R' Q'
  | .skip => .skip
  | .seq s t => .seq (s.rename r q) (t.rename r q)
  | .assign x e => .assign (r x) (e.rename r)
  | .push L x => .push (q L) (r x)
  | .pop L x flag => .pop (q L) (r x) (r flag)
  | .len L x => .len (q L) (r x)
  | .rev L => .rev (q L)
  | .copy L L' => .copy (q L) (q L')
  | .revApp L L' => .revApp (q L) (q L')
  | .ite x s t => .ite (r x) (s.rename r q) (t.rename r q)
  | .loop x s => .loop (r x) (s.rename r q)

/-- View only the registers and lists assigned to the subprogram. -/
def State.restrict (r : Fin R → Fin R') (q : Fin Q → Fin Q') (st : State R' Q') :
    State R Q := ⟨st.regs ∘ r, st.lists ∘ q⟩

@[simp] theorem State.restrict_regs (r : Fin R → Fin R') (q : Fin Q → Fin Q')
    (st : State R' Q') (x : Fin R) : (st.restrict r q).regs x = st.regs (r x) := rfl

@[simp] theorem State.restrict_lists (r : Fin R → Fin R') (q : Fin Q → Fin Q')
    (st : State R' Q') (L : Fin Q) : (st.restrict r q).lists L = st.lists (q L) := rfl

@[simp] theorem Expr.eval_rename (r : Fin R → Fin R') (e : Expr R) (v : Fin R' → ℕ) :
    (e.rename r).eval v = e.eval (v ∘ r) := by cases e <;> rfl

@[simp] theorem Expr.cost_rename (r : Fin R → Fin R') (e : Expr R) (v : Fin R' → ℕ) :
    (e.rename r).cost v = e.cost (v ∘ r) := by cases e <;> rfl

@[simp] theorem State.restrict_setReg (r : Fin R → Fin R') (q : Fin Q → Fin Q')
    (hr : Function.Injective r) (st : State R' Q') (x : Fin R) (v : ℕ) :
    (setReg st (r x) v).restrict r q = setReg (st.restrict r q) x v := by
  unfold State.restrict setReg
  congr 1
  funext i
  simp only [Function.comp_apply, Function.update_apply, hr.eq_iff]

@[simp] theorem State.restrict_setList (r : Fin R → Fin R') (q : Fin Q → Fin Q')
    (hq : Function.Injective q) (st : State R' Q') (L : Fin Q) (l : List ℕ) :
    (setList st (q L) l).restrict r q = setList (st.restrict r q) L l := by
  unfold State.restrict setList
  congr 1
  funext i
  simp only [Function.comp_apply, Function.update_apply, hq.eq_iff]

private theorem iterate_restrict (r : Fin R → Fin R') (q : Fin Q → Fin Q')
    (f : State R' Q' → State R' Q' × ℕ) (g : State R Q → State R Q × ℕ)
    (h : ∀ st, ((f st).1.restrict r q, (f st).2) = g (st.restrict r q))
    (c n : ℕ) (st : State R' Q') :
    ((iterate f c n st).1.restrict r q, (iterate f c n st).2) =
      iterate g c n (st.restrict r q) := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih =>
    have h1 := congrArg Prod.fst (h st)
    have h2 := congrArg Prod.snd (h st)
    have i1 := congrArg Prod.fst (ih (f st).1)
    have i2 := congrArg Prod.snd (ih (f st).1)
    dsimp only at h1 h2 i1 i2
    simp only [iterate, i1, i2, h1, h2]

/-- Exact subprogram semantics, including nested loops and coincident source/destination slots. -/
theorem Stmt.run_rename (s : Stmt R Q) (r : Fin R → Fin R') (q : Fin Q → Fin Q')
    (hr : Function.Injective r) (hq : Function.Injective q) (st : State R' Q') :
    (((s.rename r q).run st).1.restrict r q, ((s.rename r q).run st).2) =
      s.run (st.restrict r q) := by
  induction s generalizing st with
  | skip => rfl
  | seq s t ihs iht =>
    have h1 := congrArg Prod.fst (ihs st)
    have h2 := congrArg Prod.snd (ihs st)
    have k1 := congrArg Prod.fst (iht ((s.rename r q).run st).1)
    have k2 := congrArg Prod.snd (iht ((s.rename r q).run st).1)
    dsimp only at h1 h2 k1 k2
    simp only [Stmt.rename, Stmt.run, k1, k2, h1, h2]
  | assign x e =>
    simp only [Stmt.rename, Stmt.run, Expr.eval_rename, Expr.cost_rename,
      State.restrict_setReg r q hr]
    rfl
  | push L x =>
    simp only [Stmt.rename, Stmt.run, State.restrict_setList r q hq, State.restrict_regs,
      State.restrict_lists]
  | pop L x flag =>
    cases hl : st.lists (q L) with
    | nil =>
      simp only [Stmt.rename, Stmt.run, hl, State.restrict_setReg r q hr]
      simp only [State.restrict_lists, hl]
    | cons v l =>
      simp only [Stmt.rename, Stmt.run, hl, State.restrict_setReg r q hr,
        State.restrict_setList r q hq]
      simp only [State.restrict_lists, hl]
  | len L x =>
    simp only [Stmt.rename, Stmt.run, State.restrict_setReg r q hr, State.restrict_lists]
  | rev L =>
    simp only [Stmt.rename, Stmt.run, State.restrict_setList r q hq, State.restrict_lists]
  | copy L L' =>
    simp only [Stmt.rename, Stmt.run, State.restrict_setList r q hq, State.restrict_lists]
  | revApp L L' =>
    simp only [Stmt.rename, Stmt.run, State.restrict_setList r q hq, State.restrict_lists]
  | ite x s t ihs iht =>
    have h1 := congrArg Prod.fst (ihs st)
    have h2 := congrArg Prod.snd (ihs st)
    have k1 := congrArg Prod.fst (iht st)
    have k2 := congrArg Prod.snd (iht st)
    dsimp only at h1 h2 k1 k2
    by_cases hx : st.regs (r x) ≠ 0 <;>
      simp [Stmt.rename, Stmt.run, hx, h1, h2, k1, k2]
  | loop x s ih =>
    have h := iterate_restrict r q (s.rename r q).run s.run ih
      (Nat.size (st.regs (r x)) + 1) (st.regs (r x)) st
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    dsimp only at h1 h2
    simp only [Stmt.rename, Stmt.run, State.restrict_regs, h1, h2]

theorem Stmt.run_rename_cost (s : Stmt R Q) (r : Fin R → Fin R') (q : Fin Q → Fin Q')
    (hr : Function.Injective r) (hq : Function.Injective q) (st : State R' Q') :
    ((s.rename r q).run st).2 = (s.run (st.restrict r q)).2 :=
  congrArg Prod.snd (s.run_rename r q hr hq st)

@[simp] theorem Stmt.regWrites_rename (s : Stmt R Q) (r : Fin R → Fin R')
    (q : Fin Q → Fin Q') : (s.rename r q).regWrites = s.regWrites.map r := by
  induction s <;> simp_all [Stmt.rename, regWrites]

@[simp] theorem Stmt.listWrites_rename (s : Stmt R Q) (r : Fin R → Fin R')
    (q : Fin Q → Fin Q') : (s.rename r q).listWrites = s.listWrites.map q := by
  induction s <;> simp_all [Stmt.rename, listWrites]

/-- Every register outside a renamed subprogram's allocation is a caller-owned frame. -/
theorem Stmt.run_rename_reg_outside (s : Stmt R Q) (r : Fin R → Fin R')
    (q : Fin Q → Fin Q') (x : Fin R') (hx : ∀ i, r i ≠ x) (st : State R' Q') :
    ((s.rename r q).run st).1.regs x = st.regs x := by
  apply run_regs_frame
  simp only [regWrites_rename, List.mem_map]
  rintro ⟨i, _, hi⟩
  exact hx i hi

/-- Every list outside a renamed subprogram's allocation is a caller-owned frame. -/
theorem Stmt.run_rename_list_outside (s : Stmt R Q) (r : Fin R → Fin R')
    (q : Fin Q → Fin Q') (L : Fin Q') (hL : ∀ i, q i ≠ L) (st : State R' Q') :
    ((s.rename r q).run st).1.lists L = st.lists L := by
  apply run_lists_frame
  simp only [listWrites_rename, List.mem_map]
  rintro ⟨i, _, hi⟩
  exact hL i hi

end PCP.Lang
