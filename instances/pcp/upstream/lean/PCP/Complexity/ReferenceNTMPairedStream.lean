import PCP.Complexity.ReferenceNTMPairedTerms

/-!
# Exact paired-stream execution of the reference NTM

The finite stream is the input word, separator 2, and choice word. No clock
polynomial is evaluated by this program: its loop count is the stream length.
-/

namespace PCP.ReferenceNTM.PairedStream

open Complexity PCP.Lang.ArithmeticExpression PCP.Lang.ArithmeticStream

variable {k q : ℕ} (tm : NTM k) (eQ : tm.Q ≃ Fin q)

/-- Initial numeric configuration with an empty input, before the separator. -/
def initial : Fin (width k) → ℕ := encode tm eQ (Cfg.init tm []) 0 4

def verdict : Term (width k) := (Arithmetic.verdict tm eQ).rename sourceIndex

def pair (x choices : List Bool) : List ℕ :=
  x.map Bool.toNat ++ [2] ++ choices.map Bool.toNat

@[simp] theorem initial_input (code : ℕ) : Arithmetic.initial tm eQ code 1 = code := by
  have h : 1 < Cfg.width k := by dsimp [Cfg.width]; omega
  have he : (1 : Fin (Cfg.width k)).val = 1 := Nat.mod_eq_of_lt h
  simp only [Arithmetic.initial, he, Nat.one_ne_zero, ite_false, ite_true]

theorem update_initial (old fresh : ℕ) :
    Function.update (Arithmetic.initial tm eQ old) 1 fresh = Arithmetic.initial tm eQ fresh := by
  funext r
  by_cases h : r = 1
  · subst r
    simp only [Function.update_self, initial_input]
  · have hv : r.val ≠ 1 := by
      intro he
      exact h (Fin.ext he)
    simp [Function.update_of_ne h, Arithmetic.initial, hv]

theorem next_input (x : List Bool) (b : Bool) :
    next (terms tm eQ) (encode tm eQ (Cfg.init tm x) 0 (4 ^ (x.length + 1))) b.toNat =
      encode tm eQ (Cfg.init tm (x ++ [b])) 0 (4 ^ ((x ++ [b]).length + 1)) := by
  rw [encode, next_load, encode, Arithmetic.encode_init_input,
    Arithmetic.encode_init_input, update_initial]
  have ha := Cfg.init_input_code_append tm x b
  change (Tape.init ((x ++ [b]).map Γ.ofBool)).code =
    (Tape.init (x.map Γ.ofBool)).code + (b.toNat + 1) * 4 ^ (x.length + 1) at ha
  rw [ha]
  simp [List.length_append, pow_succ]

theorem foldl_input (x : List Bool) :
    (x.map Bool.toNat).foldl (next (terms tm eQ)) (initial tm eQ) =
      encode tm eQ (Cfg.init tm x) 0 (4 ^ (x.length + 1)) := by
  induction x using List.reverseRecOn with
  | nil => simp [initial]
  | append_singleton x b ih =>
      rw [List.map_append, List.foldl_append, ih]
      simpa using next_input tm eQ x b

theorem foldl_choices (c : Cfg tm) (place : ℕ) (choices : List Bool) :
    (choices.map Bool.toNat).foldl (next (terms tm eQ)) (encode tm eQ c 1 place) =
      encode tm eQ (Cfg.run choices c) 1 place := by
  induction choices generalizing c with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, List.foldl_cons, next_run, Cfg.run, ih]

theorem foldl_pair (x choices : List Bool) :
    (pair x choices).foldl (next (terms tm eQ)) (initial tm eQ) =
      encode tm eQ (Cfg.run choices (Cfg.init tm x)) 1 (4 ^ (x.length + 1)) := by
  rw [pair, List.foldl_append, List.foldl_append, foldl_input]
  simp only [List.foldl_cons, List.foldl_nil, encode]
  rw [next_separator]
  exact foldl_choices tm eQ _ _ _

theorem eval_verdict (c : Cfg tm) (phase place : ℕ) :
    (verdict tm eQ).eval (encode tm eQ c phase place) =
      (decide (c.state = tm.qhalt ∧ digit c.output.code 1 = 2)).toNat := by
  rw [verdict, Term.eval_rename]
  have h : encode tm eQ c phase place ∘ sourceIndex = Cfg.encode eQ c := by
    funext i
    simp [encode]
  rw [h, Arithmetic.eval_verdict]

def program : PCP.Lang.Prog :=
  PCP.Lang.ArithmeticStream.program (initial tm eQ) (terms tm eQ) (verdict tm eQ)

/-- An actual counted-loop program verifies the supplied reference-machine path. -/
theorem program_run (x choices : List Bool) :
    (program tm eQ).run (pair x choices) = [(Cfg.accepts tm x choices).toNat] := by
  rw [program, PCP.Lang.ArithmeticStream.program_run, foldl_pair, eval_verdict]
  rfl

end PCP.ReferenceNTM.PairedStream
