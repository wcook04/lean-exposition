import PCP.Complexity.ReferenceNTMTape
import PCP.Complexity.ArithmeticConditionals

/-!
# Arithmetic expressions for one reference tape

The three coordinates are updated simultaneously from the old numeral, head,
and cached place value. These are finite expression trees, including the
reference convention that writes at the left-end marker are ignored.
-/

namespace PCP.ReferenceNTM

open Complexity PCP.Lang.ArithmeticExpression

/-- Direction digits used in finite transition tables. -/
def directionCode : Dir3 → ℕ
  | .left => 0
  | .right => 1
  | .stay => 2

/-- Three arithmetic expressions representing one numeric tape. -/
structure TapeTerms (n : ℕ) where
  code : Term n
  head : Term n
  power : Term n

namespace TapeTerms

variable {n : ℕ}

def eval (t : TapeTerms n) (r : Fin n → ℕ) : Tape :=
  ⟨t.code.eval r, t.head.eval r, t.power.eval r⟩

def read (t : TapeTerms n) : Term n :=
  .bin .mod (.bin .div t.code t.power) (.const 4)

def write (t : TapeTerms n) (s : Term n) : TapeTerms n :=
  { t with code := (.iteEq t.head (.const 0) t.code
      (.bin .add (.bin .sub t.code (.bin .mul t.read t.power)) (.bin .mul s t.power))) }

def move (t : TapeTerms n) (d : Term n) : TapeTerms n :=
  { t with
    head := .iteEq d (.const 0) (.bin .sub t.head (.const 1))
      (.iteEq d (.const 1) (.bin .add t.head (.const 1)) t.head)
    power := .iteEq d (.const 0)
      (.iteEq t.head (.const 0) t.power (.bin .div t.power (.const 4)))
      (.iteEq d (.const 1) (.bin .mul t.power (.const 4)) t.power) }

def writeAndMove (t : TapeTerms n) (s d : Term n) : TapeTerms n := (t.write s).move d

theorem eval_read (t : TapeTerms n) (r : Fin n → ℕ) :
    t.read.eval r = symbolCode (t.eval r).read := by
  change _ = symbolCode (symbol _)
  exact (symbolCode_symbol _ (Nat.mod_lt _ (by decide))).symm

theorem eval_write (t : TapeTerms n) (s : Term n) (r : Fin n → ℕ)
    (a : Γ) (hs : s.eval r = symbolCode a) :
    (t.write s).eval r = (t.eval r).write a := by
  by_cases h : t.head.eval r = 0
  · simp [write, eval, Tape.write, Term.eval_iteEq, Term.eval, h]
  · simp [write, eval, Tape.write, Term.eval_iteEq, Term.eval, Op.eval, read, h, hs]

theorem eval_move (t : TapeTerms n) (d : Term n) (r : Fin n → ℕ)
    (a : Dir3) (hd : d.eval r = directionCode a) :
    (t.move d).eval r = (t.eval r).move a := by
  cases a with
  | left =>
      by_cases h : t.head.eval r = 0
      · simp [move, eval, Tape.move, Term.eval_iteEq, Term.eval, Op.eval, hd,
          directionCode, h]
      · simp [move, eval, Tape.move, Term.eval_iteEq, Term.eval, Op.eval, hd,
          directionCode, h]
  | right => simp [move, eval, Tape.move, Term.eval_iteEq, Term.eval, Op.eval, hd,
      directionCode]
  | stay => simp [move, eval, Tape.move, Term.eval_iteEq, Term.eval, hd,
      directionCode]

theorem eval_writeAndMove (t : TapeTerms n) (s d : Term n) (r : Fin n → ℕ)
    (a : Γ) (b : Dir3) (hs : s.eval r = symbolCode a)
    (hd : d.eval r = directionCode b) :
    (t.writeAndMove s d).eval r = (t.eval r).writeAndMove a b := by
  rw [writeAndMove, eval_move _ _ _ _ hd, eval_write _ _ _ _ hs]
  rfl

end TapeTerms
end PCP.ReferenceNTM
