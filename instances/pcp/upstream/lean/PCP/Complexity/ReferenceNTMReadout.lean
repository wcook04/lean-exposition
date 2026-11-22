import PCP.Complexity.ReferenceNTMArithmetic
import PCP.Complexity.ArithmeticStream

/-!
# Initialization and acceptance expressions for the reference NTM

Acceptance reads the halt state and the output symbol at cell one, exactly as in
the vendored definition. A boolean choice stream realizes the numeric trace.
-/

namespace PCP.ReferenceNTM.Arithmetic

open Complexity PCP.Lang.ArithmeticExpression PCP.Lang.ArithmeticStream

variable {k q : ℕ} (tm : NTM k) (eQ : tm.Q ≃ Fin q)

/-- The reference acceptance convention: halted, with one in output cell one. -/
def verdict : Term (Cfg.width k) :=
  .bin .mul (.bin .eq (.input 0) (.const (eQ tm.qhalt).val))
    (.bin .eq (.bin .mod (.bin .div (.input (Cfg.codeIndex 1)) (.const 4))
      (.const 4)) (.const 2))

theorem eval_verdict (c : Cfg tm) :
    (verdict tm eQ).eval (Cfg.encode eQ c) =
      (decide (c.state = tm.qhalt ∧ digit c.output.code 1 = 2)).toNat := by
  have he : (eQ c.state).val = (eQ tm.qhalt).val ↔ c.state = tm.qhalt := by
    constructor
    · intro h
      exact eQ.injective (Fin.ext h)
    · intro h
      rw [h]
  simp only [verdict, Term.eval, Op.eval, Cfg.encode_state, Cfg.encode_code, he]
  by_cases hs : c.state = tm.qhalt <;>
    by_cases hd : digit c.output.code 1 = 2 <;>
    simp_all [digit, Cfg.output]

theorem next_encode (c : Cfg tm) (b : Bool) :
    next (transition tm eQ) (Cfg.encode eQ c) b.toNat = Cfg.encode eQ (Cfg.step b c) := by
  funext r
  have hv : withSymbol (Cfg.encode eQ c) b.toNat = values tm eQ c b := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [withSymbol, values]
  simpa only [next, hv] using eval_transition tm eQ c b r

theorem foldl_encode (c : Cfg tm) (bs : List Bool) :
    (bs.map Bool.toNat).foldl (next (transition tm eQ)) (Cfg.encode eQ c) =
      Cfg.encode eQ (Cfg.run bs c) := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, List.foldl_cons, next_encode, Cfg.run, ih]

theorem verdict_foldl (x bs : List Bool) :
    (verdict tm eQ).eval
      ((bs.map Bool.toNat).foldl (next (transition tm eQ)) (Cfg.encode eQ (Cfg.init tm x))) =
      (Cfg.accepts tm x bs).toNat := by
  rw [foldl_encode, eval_verdict]
  rfl

/-- All initial coordinates are fixed constants apart from the input numeral. -/
def initial (inputCode : ℕ) (r : Fin (Cfg.width k)) : ℕ :=
  if r.val = 0 then (eQ tm.qstart).val
  else if r.val = 1 then inputCode
  else if (r.val - 1) % 3 = 0 then 3
  else if (r.val - 1) % 3 = 1 then 0 else 1

theorem encode_init_input (x : List Bool) :
    Cfg.encode eQ (Cfg.init tm x) = initial tm eQ (Tape.init (x.map Γ.ofBool)).code := by
  funext r
  simp only [Cfg.encode, Cfg.init, initial]
  split_ifs <;> simp_all [Tape.init]
  all_goals
    have hr : r.val ≠ 0 := by
      intro he
      have : r = 0 := Fin.ext he
      contradiction
    omega

theorem encode_init_nil : Cfg.encode eQ (Cfg.init tm []) = initial tm eQ 3 := by
  simpa [Tape.init] using encode_init_input tm eQ []

end PCP.ReferenceNTM.Arithmetic
