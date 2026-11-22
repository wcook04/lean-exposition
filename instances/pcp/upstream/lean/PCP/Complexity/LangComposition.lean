/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.LangRenaming

/-!
# Exact composition of concrete language programs

Two programs receive disjoint register and list allocations. The first output
is copied into the second input, and the second output is copied back to the
public output slot. Thus both components run from their specified initial states.
-/

namespace PCP.Lang.Prog

variable (P Q : Prog)

def compose : Prog where
  R := P.R + Q.R
  Q := P.Q + Q.Q
  hQ := by have := P.hQ; omega
  body := .seq (P.body.rename (Fin.castAdd Q.R) (Fin.castAdd Q.Q))
    (.seq (.copy (P.outL.castAdd Q.Q) (Fin.natAdd P.Q Q.inL))
      (.seq (Q.body.rename (Fin.natAdd P.R) (Fin.natAdd P.Q))
        (.copy (Fin.natAdd P.Q Q.outL) (P.outL.castAdd Q.Q))))

private theorem add_injective (m n : ℕ) : Function.Injective (@Fin.natAdd n m) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa using this

private theorem left_ne_right {m n : ℕ} (i : Fin m) (j : Fin n) :
    i.castAdd n ≠ Fin.natAdd m j := by
  intro h
  have he := congrArg Fin.val h
  change i.val = m + j.val at he
  have := i.isLt
  omega

private def initial (l : List ℕ) : State (P.R + Q.R) (P.Q + Q.Q) :=
  ⟨fun _ => 0, fun L => if L.val = 0 then l else []⟩

private theorem init_compose (l : List ℕ) : (compose P Q).init l = initial P Q l := by
  unfold init initial
  congr 1
  funext L
  simp only [Fin.ext_iff, inL]

private theorem initial_left (l : List ℕ) :
    (initial P Q l).restrict (Fin.castAdd Q.R) (Fin.castAdd Q.Q) = P.init l := by
  unfold State.restrict initial init
  congr 1
  funext L
  simp only [Function.comp_apply, Fin.val_castAdd, Fin.ext_iff, inL]

private theorem first_result (l : List ℕ) :
    (((P.body.rename (Fin.castAdd Q.R) (Fin.castAdd Q.Q)).run (initial P Q l)).1.restrict
      (Fin.castAdd Q.R) (Fin.castAdd Q.Q),
      ((P.body.rename (Fin.castAdd Q.R) (Fin.castAdd Q.Q)).run (initial P Q l)).2) =
        P.body.run (P.init l) := by
  rw [P.body.run_rename _ _ (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _),
    initial_left]

private def firstState (l : List ℕ) : State (P.R + Q.R) (P.Q + Q.Q) :=
  ((P.body.rename (Fin.castAdd Q.R) (Fin.castAdd Q.Q)).run (initial P Q l)).1

private theorem first_output (l : List ℕ) :
    (firstState P Q l).lists (P.outL.castAdd Q.Q) = P.run l :=
  congrArg (fun z => z.1.lists P.outL) (first_result P Q l)

private theorem first_right_reg (l : List ℕ) (i : Fin Q.R) :
    (firstState P Q l).regs (Fin.natAdd P.R i) = 0 := by
  exact P.body.run_rename_reg_outside _ _ _ (fun j => left_ne_right j i) _

private theorem first_right_list (l : List ℕ) (L : Fin Q.Q) :
    (firstState P Q l).lists (Fin.natAdd P.Q L) = [] := by
  rw [firstState, P.body.run_rename_list_outside _ _ _ (fun j => left_ne_right j L)]
  change (if P.Q + L.val = 0 then l else []) = []
  have hQ := P.hQ
  simp only [ite_eq_right (by omega : P.Q + L.val ≠ 0)]

private def secondState (l : List ℕ) : State (P.R + Q.R) (P.Q + Q.Q) :=
  setList (firstState P Q l) (Fin.natAdd P.Q Q.inL) (P.run l)

private theorem initial_right (l : List ℕ) :
    (secondState P Q l).restrict (Fin.natAdd P.R) (Fin.natAdd P.Q) = Q.init (P.run l) := by
  unfold State.restrict secondState setList init
  congr 1
  · funext i
    exact first_right_reg P Q l i
  · funext L
    simp only [Function.comp_apply, Function.update_apply, (add_injective _ _).eq_iff,
      first_right_list]

private theorem second_result (l : List ℕ) :
    (((Q.body.rename (Fin.natAdd P.R) (Fin.natAdd P.Q)).run (secondState P Q l)).1.restrict
      (Fin.natAdd P.R) (Fin.natAdd P.Q),
      ((Q.body.rename (Fin.natAdd P.R) (Fin.natAdd P.Q)).run (secondState P Q l)).2) =
        Q.body.run (Q.init (P.run l)) := by
  rw [Q.body.run_rename _ _ (add_injective _ _) (add_injective _ _), initial_right]

/-- The composition is one actual program and computes function composition exactly. -/
theorem run_compose (l : List ℕ) : (compose P Q).run l = Q.run (P.run l) := by
  have hs := congrArg (fun z => z.1.lists Q.outL) (second_result P Q l)
  have hout : (compose P Q).outL = P.outL.castAdd Q.Q := by apply Fin.ext; rfl
  change _ = Q.run (P.run l) at hs
  unfold run
  rw [init_compose]
  simp only [compose, run_seq_fst, run_copy_fst]
  change (setList ((Q.body.rename (Fin.natAdd P.R) (Fin.natAdd P.Q)).run
    (setList (firstState P Q l) (Fin.natAdd P.Q Q.inL)
      ((firstState P Q l).lists (P.outL.castAdd Q.Q)))).1
    (P.outL.castAdd Q.Q)
    (((Q.body.rename (Fin.natAdd P.R) (Fin.natAdd P.Q)).run
      (setList (firstState P Q l) (Fin.natAdd P.Q Q.inL)
        ((firstState P Q l).lists (P.outL.castAdd Q.Q)))).1.lists
          (Fin.natAdd P.Q Q.outL))).lists (compose P Q).outL = _
  rw [first_output, hout]
  exact hs

/-- Exact charged cost includes both public list copies and three sequencing steps. -/
theorem cost_compose (l : List ℕ) :
    (compose P Q).cost l = P.cost l + Q.cost (P.run l) +
      listSize (P.run l) + listSize (Q.run (P.run l)) + 5 := by
  have hfirst := congrArg Prod.snd (first_result P Q l)
  have hsecond := congrArg Prod.snd (second_result P Q l)
  have hout := congrArg (fun z => z.1.lists Q.outL) (second_result P Q l)
  change _ = P.cost l at hfirst
  change _ = Q.cost (P.run l) at hsecond
  change _ = Q.run (P.run l) at hout
  unfold cost
  rw [init_compose]
  simp only [compose, run_seq_snd, run_copy_snd, run_copy_fst]
  change _ + (listSize ((firstState P Q l).lists (P.outL.castAdd Q.Q)) + 1 +
    (((Q.body.rename (Fin.natAdd P.R) (Fin.natAdd P.Q)).run
      (setList (firstState P Q l) (Fin.natAdd P.Q Q.inL)
        ((firstState P Q l).lists (P.outL.castAdd Q.Q)))).2 +
      (listSize (((Q.body.rename (Fin.natAdd P.R) (Fin.natAdd P.Q)).run
        (setList (firstState P Q l) (Fin.natAdd P.Q Q.inL)
          ((firstState P Q l).lists (P.outL.castAdd Q.Q)))).1.lists
          (Fin.natAdd P.Q Q.outL)) + 1) + 1) + 1) + 1 = _
  rw [first_output]
  change _ + (listSize (P.run l) + 1 +
    (((Q.body.rename (Fin.natAdd P.R) (Fin.natAdd P.Q)).run (secondState P Q l)).2 +
      (listSize (((Q.body.rename (Fin.natAdd P.R) (Fin.natAdd P.Q)).run
        (secondState P Q l)).1.lists (Fin.natAdd P.Q Q.outL)) + 1) + 1) + 1) + 1 = _
  dsimp only [Prod.fst, Prod.snd, State.restrict_lists] at hfirst hsecond hout
  rw [hfirst, hsecond, hout]
  simp only [cost]
  omega

end PCP.Lang.Prog
