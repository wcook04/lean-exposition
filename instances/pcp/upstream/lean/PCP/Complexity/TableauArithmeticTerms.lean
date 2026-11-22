/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ArithmeticConditionals
import PCP.Complexity.TableauDescriptorArithmetic

/-!
# Arithmetic syntax for the concrete tableau address decoder

All growing indices are compiled from natural arithmetic and conditionals.
Machine constants remain literal constants in one fixed program.
-/

namespace PCP.Machine.TableauArithmeticTerms

open PCP.Lang.ArithmeticExpression

variable {r : ℕ}

local infixl:65 " ⊞ " => Term.bin Op.add
local infixl:65 " ⊟ " => Term.bin Op.sub
local infixl:70 " ⊠ " => Term.bin Op.mul
local infixl:70 " ⊘ " => Term.bin Op.div
local infixl:70 " %ₜ " => Term.bin Op.mod

def sites (k : ℕ) (B : Term r) : Term r := .const 1 ⊞ .const k ⊠ B

def links (k window : ℕ) (T : Term r) : Term r :=
  (T ⊞ .const 1) ⊠ .const (k * window)

def boundary (k window : ℕ) (T B : Term r) : Term r :=
  .const 1 ⊞ links k window T ⊞ T ⊞ T ⊠ (.const k ⊠ B)

def constraints (k window : ℕ) (T B : Term r) : Term r :=
  boundary k window T B ⊞ .const 2 ⊠ sites k B

def prefixAddress (k : ℕ) (B t : Term r) : Term r := t ⊠ sites k B

def cell (k : ℕ) (T B t stack j : Term r) : Term r :=
  .iteLt j B (t ⊠ sites k B ⊞ .const 1 ⊞ stack ⊠ B ⊞ j)
    ((T ⊞ .const 1) ⊠ sites k B)

theorem sites_eval (k : ℕ) (B : Term r) (env : Fin r → ℕ) :
    (sites k B).eval env = TableauNumericIndex.sites k (B.eval env) := rfl

theorem links_eval (k window : ℕ) (T : Term r) (env : Fin r → ℕ) :
    (links k window T).eval env = TableauNumericIndex.links k window (T.eval env) := rfl

theorem boundary_eval (k window : ℕ) (T B : Term r) (env : Fin r → ℕ) :
    (boundary k window T B).eval env =
      TableauNumericIndex.boundaryOffset k window (T.eval env) (B.eval env) := rfl

theorem constraints_eval (k window : ℕ) (T B : Term r) (env : Fin r → ℕ) :
    (constraints k window T B).eval env =
      TableauNumericIndex.constraints k window (T.eval env) (B.eval env) := rfl

theorem prefixAddress_eval (k : ℕ) (B t : Term r) (env : Fin r → ℕ) :
    (prefixAddress k B t).eval env =
      TableauNumericIndex.prefixAddress k (B.eval env) (t.eval env) := rfl

theorem cell_eval (k : ℕ) (T B t stack j : Term r) (env : Fin r → ℕ) :
    (cell k T B t stack j).eval env = TableauNumericIndex.cell k (T.eval env)
      (B.eval env) (t.eval env) (stack.eval env) (j.eval env) := by
  simp only [cell, Term.eval_iteLt, Term.eval, Op.eval]
  rfl

/-- All tableau and witness scopes, as one fixed arithmetic term. -/
def scope (k window stack₀ : ℕ) (T B n e i : Term r) : Term r :=
  let L := .const 1 ⊞ links k window T
  let C := L ⊞ T
  let D := boundary k window T B
  let N := constraints k window T B
  let zlink := e ⊟ .const 1
  let zcell := e ⊟ C
  let zbound := e ⊟ D
  let tcell := zcell ⊘ (.const k ⊠ B)
  let kcell := (zcell %ₜ (.const k ⊠ B)) ⊘ B
  let jcell := zcell %ₜ B
  let bbound := zbound ⊘ sites k B
  let sbound := zbound %ₜ sites k B
  let tbound := Term.iteEq bbound (.const 0) (.const 0) T
  .iteEq e (.const 0) ((T ⊞ .const 1) ⊠ sites k B)
    (.iteLt e L
      (.iteEq i (.const 0) (prefixAddress k B (zlink ⊘ .const (k * window)))
        (cell k T B (zlink ⊘ .const (k * window))
          ((zlink %ₜ .const (k * window)) ⊘ .const window) (zlink %ₜ .const window)))
      (.iteLt e C
        (prefixAddress k B (.iteEq i (.const 0) (e ⊟ L) ((e ⊟ L) ⊞ .const 1)))
        (.iteLt e D
          (.iteEq i (.const 0) (prefixAddress k B tcell)
            (.iteEq i (.const 1) (cell k T B (tcell ⊞ .const 1) kcell jcell)
              (cell k T B tcell kcell (.const window ⊞ (jcell ⊟ (i ⊟ .const 2))))))
          (.iteLt e N
            (.iteEq sbound (.const 0) (prefixAddress k B tbound)
              (cell k T B tbound ((sbound ⊟ .const 1) ⊘ B) ((sbound ⊟ .const 1) %ₜ B)))
            (cell k T B (.const 0) (.const stack₀)
              (n ⊞ .const 1 ⊞ (e ⊟ N) ⊞ .iteEq i (.const 0) (.const 0) (.const 1)))))))

/-- The compiled address term computes the already certified arithmetic scope. -/
theorem scope_eval (k window stack₀ : ℕ) (T B n e i : Term r) (env : Fin r → ℕ) :
    (scope k window stack₀ T B n e i).eval env = TableauNumericIndex.scope k window stack₀
      (T.eval env) (B.eval env) (n.eval env) (e.eval env) (i.eval env) := by
  simp only [scope, Term.eval_iteEq, Term.eval_iteLt, cell_eval, prefixAddress_eval,
    sites_eval, links_eval, boundary_eval, constraints_eval, Term.eval, Op.eval]
  rfl


/-- Three scalar terms describe a local-relation table address. -/
abbrev Triple (r : ℕ) := Term r × Term r × Term r

def Triple.eval (v : Triple r) (env : Fin r → ℕ) : ℕ × ℕ × ℕ :=
  (v.1.eval env, v.2.1.eval env, v.2.2.eval env)

def iteEqTriple (a b : Term r) (yes no : Triple r) : Triple r :=
  (.iteEq a b yes.1 no.1, .iteEq a b yes.2.1 no.2.1, .iteEq a b yes.2.2 no.2.2)

def iteLtTriple (a b : Term r) (yes no : Triple r) : Triple r :=
  (.iteLt a b yes.1 no.1, .iteLt a b yes.2.1 no.2.1, .iteLt a b yes.2.2 no.2.2)

theorem eval_iteEqTriple (a b : Term r) (yes no : Triple r) (env : Fin r → ℕ) :
    (iteEqTriple a b yes no).eval env =
      if a.eval env = b.eval env then yes.eval env else no.eval env := by
  simp only [iteEqTriple, Triple.eval, Term.eval_iteEq]
  split_ifs <;> rfl

theorem eval_iteLtTriple (a b : Term r) (yes no : Triple r) (env : Fin r → ℕ) :
    (iteLtTriple a b yes no).eval env =
      if a.eval env < b.eval env then yes.eval env else no.eval env := by
  simp only [iteLtTriple, Triple.eval, Term.eval_iteLt]
  split_ifs <;> rfl

def inputSelector (n W j bit : Term r) : Term r :=
  .iteLt j n bit (.iteEq j n (.const 2) (.iteLt j (n ⊞ .const 1 ⊞ W) (.const 3) (.const 4)))

theorem inputSelector_eval (n W j bit : Term r) (env : Fin r → ℕ) :
    (inputSelector n W j bit).eval env = TableauDescriptorArithmetic.inputSelector
      (n.eval env) (W.eval env) (j.eval env) (bit.eval env) := by
  simp only [inputSelector, Term.eval_iteLt, Term.eval_iteEq, Term.eval, Op.eval]
  rfl

def publicPosition (k window : ℕ) (T B e : Term r) : Term r :=
  (((e ⊟ boundary k window T B) %ₜ sites k B) ⊟ .const 1) %ₜ B

theorem publicPosition_eval (k window : ℕ) (T B e : Term r) (env : Fin r → ℕ) :
    (publicPosition k window T B e).eval env = TableauDescriptorArithmetic.publicPosition
      k window (T.eval env) (B.eval env) (e.eval env) := rfl

/-- Relation descriptors contain only fixed constants and arithmetic in input metadata. -/
def select (k window output stack₀ : ℕ) (T B W n e bit : Term r) : Triple r :=
  let L := .const 1 ⊞ links k window T
  let C := L ⊞ T
  let D := boundary k window T B
  let N := constraints k window T B
  let zl := e ⊟ .const 1
  let zc := e ⊟ C
  let zb := e ⊟ D
  let b := zb ⊘ sites k B
  let s := zb %ₜ sites k B
  let j := (s ⊟ .const 1) %ₜ B
  iteEqTriple e (.const 0) (.const 0, .const stack₀, .const 0)
    (iteLtTriple e L
      (.const 1, (zl %ₜ .const (k * window)) ⊘ .const window, zl %ₜ .const window)
      (iteLtTriple e C (.const 2, .const stack₀, .const 0)
        (iteLtTriple e D
          (.const 3, (zc %ₜ (.const k ⊠ B)) ⊘ B, .minimum (zc %ₜ B) (.const output))
          (iteLtTriple e N
            (iteEqTriple s (.const 0)
              (.iteEq b (.const 0) (.const 4) (.const 6), .const stack₀, .const 0)
              (iteEqTriple b (.const 0)
                (.const 5, (s ⊟ .const 1) ⊘ B, inputSelector n W j bit)
                (.const 7, (s ⊟ .const 1) ⊘ B, .minimum j (.const 1))))
            (.const 8, .const stack₀, .const 0)))))

/-- The scalar descriptor syntax has the exact arithmetic selection semantics. -/
theorem select_eval (k window output stack₀ : ℕ) (T B W n e bit : Term r)
    (env : Fin r → ℕ) :
    (select k window output stack₀ T B W n e bit).eval env =
      TableauDescriptorArithmetic.select k window output stack₀
        (T.eval env) (B.eval env) (W.eval env) (n.eval env) (fun _ => bit.eval env)
        (e.eval env) := by
  simp only [select, eval_iteEqTriple, eval_iteLtTriple]
  simp only [Triple.eval, Term.eval_iteEq,
    inputSelector_eval, Term.eval_minimum, sites_eval, links_eval, boundary_eval,
    constraints_eval, Term.eval, Op.eval]
  rfl

end PCP.Machine.TableauArithmeticTerms
