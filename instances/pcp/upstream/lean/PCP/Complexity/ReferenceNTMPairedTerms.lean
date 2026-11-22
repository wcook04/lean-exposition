import PCP.Complexity.ReferenceNTMReadout

/-!
# Arithmetic terms for a paired input and choice stream

Before separator 2, symbols 0 and 1 construct the reference input numeral from
left to right. Afterwards they supply nondeterministic choices. The finite
control consists of one phase bit and one cached input place value.
-/

namespace PCP.ReferenceNTM.PairedStream

open Complexity PCP.Lang.ArithmeticExpression PCP.Lang.ArithmeticStream

variable {k q : ℕ} (tm : NTM k) (eQ : tm.Q ≃ Fin q)

abbrev width (k : ℕ) : ℕ := Cfg.width k + 2

def encodeRegs (r : Fin (Cfg.width k) → ℕ) (phase place : ℕ) : Fin (width k) → ℕ :=
  Fin.snoc (Fin.snoc r phase) place

def encode (c : Cfg tm) (phase place : ℕ) : Fin (width k) → ℕ :=
  encodeRegs (Cfg.encode eQ c) phase place

def phaseIndex : Fin (width k) := (Fin.last (Cfg.width k)).castSucc

def placeIndex : Fin (width k) := Fin.last (Cfg.width k + 1)

def sourceIndex (i : Fin (Cfg.width k)) : Fin (width k) := i.castSucc.castSucc

def phaseTerm : Term (width k + 1) := .input (phaseIndex (k := k)).castSucc

def placeTerm : Term (width k + 1) := .input (placeIndex (k := k)).castSucc

def symbolTerm : Term (width k + 1) := .input (Fin.last (width k))

def inputCodeTerm : Term (width k + 1) :=
  .input (sourceIndex (k := k) 1).castSucc

/-- Embed a reference transition's old configuration and current choice. -/
def transitionIndex : Fin (Cfg.width k + 1) → Fin (width k + 1) :=
  Fin.lastCases (Fin.last (width k)) (fun i => (sourceIndex i).castSucc)

def configTerm (i : Fin (Cfg.width k)) : Term (width k + 1) :=
  .iteEq phaseTerm (.const 0)
    (.iteEq symbolTerm (.const 2) (.input (sourceIndex i).castSucc)
      (if i = 1 then .bin .add inputCodeTerm
        (.bin .mul (.bin .add symbolTerm (.const 1)) placeTerm)
      else .input (sourceIndex i).castSucc))
    ((Arithmetic.transition tm eQ i).rename transitionIndex)

def terms : Fin (width k) → Term (width k + 1) :=
  Fin.lastCases
    (.iteEq phaseTerm (.const 0)
      (.iteEq symbolTerm (.const 2) placeTerm (.bin .mul placeTerm (.const 4))) placeTerm)
    (Fin.lastCases
      (.iteEq phaseTerm (.const 0) (.iteEq symbolTerm (.const 2) (.const 1) (.const 0))
        phaseTerm)
      (configTerm tm eQ))

@[simp] theorem encodeRegs_source (r : Fin (Cfg.width k) → ℕ) (p v : ℕ)
    (i : Fin (Cfg.width k)) : encodeRegs r p v (sourceIndex i) = r i := by
  simp [encodeRegs, sourceIndex]

@[simp] theorem encodeRegs_phase (r : Fin (Cfg.width k) → ℕ) (p v : ℕ) :
    encodeRegs r p v phaseIndex = p := by simp [encodeRegs, phaseIndex]

@[simp] theorem encodeRegs_place (r : Fin (Cfg.width k) → ℕ) (p v : ℕ) :
    encodeRegs r p v placeIndex = v := by simp [encodeRegs, placeIndex]

@[simp] theorem eval_phaseTerm (r : Fin (Cfg.width k) → ℕ) (p v a : ℕ) :
    (phaseTerm (k := k)).eval (withSymbol (encodeRegs r p v) a) = p := by
  simp [phaseTerm, Term.eval, withSymbol]

@[simp] theorem eval_placeTerm (r : Fin (Cfg.width k) → ℕ) (p v a : ℕ) :
    (placeTerm (k := k)).eval (withSymbol (encodeRegs r p v) a) = v := by
  simp [placeTerm, Term.eval, withSymbol]

@[simp] theorem eval_symbolTerm (r : Fin (width k) → ℕ) (a : ℕ) :
    (symbolTerm (k := k)).eval (withSymbol r a) = a := by
  simp [symbolTerm, Term.eval, withSymbol]

@[simp] theorem eval_inputCodeTerm (r : Fin (Cfg.width k) → ℕ) (p v a : ℕ) :
    (inputCodeTerm (k := k)).eval (withSymbol (encodeRegs r p v) a) = r 1 := by
  simp [inputCodeTerm, Term.eval, withSymbol]

theorem next_load (r : Fin (Cfg.width k) → ℕ) (place : ℕ) (b : Bool) :
    next (terms tm eQ) (encodeRegs r 0 place) b.toNat =
      encodeRegs (Function.update r 1 (r 1 + (b.toNat + 1) * place)) 0 (place * 4) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · cases b <;>
      simp only [next, terms, Fin.lastCases_last, Term.eval_iteEq,
        eval_phaseTerm, eval_placeTerm, eval_symbolTerm, Term.eval, Op.eval,
        Bool.toNat_false, Bool.toNat_true, ite_true, ite_false,
          show (0 : ℕ) ≠ 2 by decide, show (1 : ℕ) ≠ 2 by decide]
    all_goals simp only [encodeRegs, Fin.snoc_last]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · cases b <;>
        simp only [next, terms, Fin.lastCases_castSucc, Fin.lastCases_last,
          Term.eval_iteEq, eval_phaseTerm, eval_symbolTerm, Term.eval,
          Bool.toNat_false, Bool.toNat_true, ite_true, ite_false,
          show (0 : ℕ) ≠ 2 by decide, show (1 : ℕ) ≠ 2 by decide]
      all_goals simp only [encodeRegs, Fin.snoc_castSucc, Fin.snoc_last]
    · cases b <;>
        simp only [next, terms, Fin.lastCases_castSucc, configTerm, Term.eval_iteEq,
          eval_phaseTerm, eval_symbolTerm, Term.eval, Bool.toNat_false, Bool.toNat_true,
          ite_true, ite_false, show (0 : ℕ) ≠ 2 by decide,
        show (1 : ℕ) ≠ 2 by decide]
      all_goals
        by_cases hj : j = 1
        · simp only [hj, ite_true]
          simp only [Term.eval, Op.eval, eval_inputCodeTerm, eval_symbolTerm, eval_placeTerm]
          simp only [encodeRegs, Fin.snoc_castSucc, Function.update_self]
        · simp only [hj, ite_false]
          simp only [Term.eval, withSymbol, Fin.lastCases_castSucc, sourceIndex,
            encodeRegs, Fin.snoc_castSucc, Function.update_of_ne hj]

theorem next_separator (r : Fin (Cfg.width k) → ℕ) (place : ℕ) :
    next (terms tm eQ) (encodeRegs r 0 place) 2 = encodeRegs r 1 place := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [next, terms, Fin.lastCases_last, Term.eval_iteEq,
      eval_phaseTerm, eval_placeTerm, eval_symbolTerm, Term.eval, ite_true]
    simp only [encodeRegs, Fin.snoc_last]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [next, terms, Fin.lastCases_castSucc, Fin.lastCases_last,
        Term.eval_iteEq, eval_phaseTerm, eval_symbolTerm, Term.eval, ite_true]
      simp only [encodeRegs, Fin.snoc_castSucc, Fin.snoc_last]
    · simp only [next, terms, Fin.lastCases_castSucc, configTerm, Term.eval_iteEq,
        eval_phaseTerm, eval_symbolTerm, Term.eval, ite_true]
      simp only [withSymbol, Fin.lastCases_castSucc, sourceIndex, encodeRegs,
        Fin.snoc_castSucc]

theorem transition_values (c : Cfg tm) (p v : ℕ) (b : Bool) :
    withSymbol (encode tm eQ c p v) b.toNat ∘ transitionIndex =
      Arithmetic.values tm eQ c b := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [transitionIndex, withSymbol, encode, encodeRegs, sourceIndex,
      Arithmetic.values]

theorem next_run (c : Cfg tm) (place : ℕ) (b : Bool) :
    next (terms tm eQ) (encode tm eQ c 1 place) b.toNat =
      encode tm eQ (Cfg.step b c) 1 place := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [next, terms, Fin.lastCases_last, Term.eval_iteEq, encode,
      eval_phaseTerm, eval_placeTerm, Term.eval, Nat.one_ne_zero, ite_false]
    simp only [encodeRegs, Fin.snoc_last]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [next, terms, Fin.lastCases_castSucc, Fin.lastCases_last,
        Term.eval_iteEq, encode, eval_phaseTerm, Term.eval, Nat.one_ne_zero, ite_false]
      simp only [encodeRegs, Fin.snoc_castSucc, Fin.snoc_last]
    · simp only [next, terms, Fin.lastCases_castSucc, configTerm,
        Term.eval_iteEq, encode, eval_phaseTerm, Term.eval, Nat.one_ne_zero, ite_false]
      rw [Term.eval_rename]
      change (Arithmetic.transition tm eQ j).eval
        (withSymbol (encode tm eQ c 1 place) b.toNat ∘ transitionIndex) = _
      rw [transition_values, Arithmetic.eval_transition]
      simp only [encodeRegs, Fin.snoc_castSucc]

end PCP.ReferenceNTM.PairedStream
