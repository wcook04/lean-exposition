import PCP.Complexity.CodeStep
import PCP.Complexity.Recode

/-!
# From a machine certificate to `Computable`

Everything the simulator needs is now proved separately: `BoundedEval.lean` retains a configuration
reached before the budget, `Codec.lean` makes the external codecs effective, and `CodeStep.lean`
gives a primitive-recursive numerical evaluator with a transition square.  This module joins them.

The chain is

```text
a ↦ ea a ↦ codeInit ↦ iterate for `time.eval (ea a).length` steps ↦ readOutput ↦ db
```

and the only thing that varies at run time is `ea a`.  **The budget is computed from the encoded
input length alone.** It never consults the certificate's `steps`, its `outputsFun`, or `f a`; those
appear only in the correctness proof.

## Scope

This is a *qualitative* bridge: it produces `Computable f`, and the simulator is primitive recursive
in its inputs.  It does **not** certify a polynomial-time TM2 interpreter, and it contributes
nothing to the finite-witness-checker closure field of NP-1.

An arbitrary witness is recoded first (`recodeWitness`), so no finiteness assumption is placed on
the original machine's auxiliary alphabets — only the external output alphabet is finite, and that
comes from its own equivalence with `Sym`.
-/

namespace PCP.Machine

open Turing

variable {tm : FinTM2}

/-! ## B3A. The numerical initializer -/

@[simp] theorem initList_stk_k₀ (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    (initList tm l).stk tm.k₀ = l := by
  unfold initList
  exact dite_pos_eq rfl _ _ l rfl

@[simp] theorem initList_stk_of_ne {tm : FinTM2} {k : tm.K} (h : k ≠ tm.k₀)
    (l : List (tm.Γ tm.k₀)) : (initList tm l).stk k = [] := by
  unfold initList
  exact dite_neg_eq h _ _ [] rfl

namespace MachineCode

variable (C : MachineCode tm)

section Init

variable (eIn : tm.Γ tm.k₀ ≃ Sym)

/-- The coded initial configuration, built **directly from an external tape** — no source
configuration and no certificate is run-time data. -/
def codeInit (xs : List Sym) : C.CodeCfg :=
  (some (C.labelEquiv tm.main), C.stateEquiv tm.initialState,
    C.setStack (fun _ => []) (C.stackEquiv tm.k₀) (xs.map (C.inputCode eIn)))

theorem primrec_codeInit : Primrec (C.codeInit eIn) :=
  Primrec.pair (Primrec.const _) (Primrec.pair (Primrec.const _)
    (C.primrec_setStack.comp (Primrec.pair (Primrec.const fun _ => [])
      (Primrec.pair (Primrec.const (C.stackEquiv tm.k₀))
        (Primrec.list_map Primrec.id ((C.primrec_inputCode eIn).comp Primrec.snd).to₂)))))

/-- **The input boundary equation.**  Holds for every raw external tape, the empty one included, and
does not assume the input and output stacks are distinct. -/
theorem codeInit_eq (xs : List Sym) :
    C.codeInit eIn xs = C.encodeCfg (initList tm (xs.map eIn.symm)) := by
  have hstk : C.setStack (fun _ => []) (C.stackEquiv tm.k₀) (xs.map (C.inputCode eIn))
      = C.encodeStacks (initList tm (xs.map eIn.symm)).stk := by
    funext j
    by_cases h : j = C.stackEquiv tm.k₀
    · subst h
      rw [C.setStack_self, C.encodeStacks_stackEquiv, initList_stk_k₀]
      change xs.map (C.inputCode eIn) = (xs.map eIn.symm).map C.symbolCode
      rw [List.map_map]
      rfl
    · have hk : C.stackEquiv.symm j ≠ tm.k₀ := fun hkk => h (by rw [← hkk, Equiv.apply_symm_apply])
      rw [C.setStack_of_ne h]
      change ([] : List ℕ) = C.codeStack _ ((initList tm _).stk (C.stackEquiv.symm j))
      rw [initList_stk_of_ne hk]
      rfl
  change (some (C.labelEquiv tm.main), C.stateEquiv tm.initialState,
    C.setStack (fun _ => []) (C.stackEquiv tm.k₀) (xs.map (C.inputCode eIn))) = _
  rw [hstk]
  rfl

end Init

/-! ## B3B. Checked decoding of the whole output list

Order and multiplicity are preserved and a single bad ordinal rejects the entire list.  Nothing here
filters, which would silently drop an invalid symbol and turn a malformed tape into a plausible
answer. -/

section Output

variable (eOut : tm.Γ tm.k₁ ≃ Sym)

/-- Decode a coded stack, propagating a failed lookup. -/
def decodeOutput : List ℕ → Option (List Sym)
  | [] => some []
  | n :: ns => (C.outputDecode eOut n).bind fun c => (decodeOutput ns).map fun cs => c :: cs

@[simp] theorem decodeOutput_nil : C.decodeOutput eOut [] = some [] := rfl

theorem decodeOutput_cons (n : ℕ) (ns : List ℕ) :
    C.decodeOutput eOut (n :: ns)
      = (C.outputDecode eOut n).bind fun c => (C.decodeOutput eOut ns).map fun cs => c :: cs := rfl

theorem decodeOutput_eq_foldr : ∀ l : List ℕ,
    C.decodeOutput eOut l
      = l.foldr (fun n acc => (C.outputDecode eOut n).bind fun c => acc.map fun cs => c :: cs)
          (some [])
  | [] => rfl
  | n :: ns => by rw [decodeOutput_cons, List.foldr_cons, decodeOutput_eq_foldr ns]

theorem primrec_decodeOutput : Primrec (C.decodeOutput eOut) := by
  have hstep : Primrec₂ fun (l : List ℕ) (x : ℕ × Option (List Sym)) =>
      (C.outputDecode eOut x.1).bind fun c => x.2.map fun cs => c :: cs :=
    Primrec.to₂ (Primrec.option_bind
      ((C.primrec_outputDecode eOut).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.to₂ (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.to₂ (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)))))
  exact (Primrec.list_foldr Primrec.id (Primrec.const (some [])) hstep).of_eq
    fun l => (C.decodeOutput_eq_foldr eOut l).symm

/-- **The output boundary equation.**  Every encoded stack decodes, in order, to its source list. -/
@[simp] theorem decodeOutput_codeStack : ∀ ys : List (tm.Γ tm.k₁),
    C.decodeOutput eOut (C.codeStack tm.k₁ ys) = some (ys.map eOut)
  | [] => rfl
  | y :: ys => by
      rw [codeStack_cons, decodeOutput_cons, C.outputDecode_symbolCode, Option.bind_some,
        decodeOutput_codeStack ys, Option.map_some, List.map_cons]

/-- Read the coded output stack of a coded configuration. -/
def readOutput (c : C.CodeCfg) : Option (List Sym) :=
  C.decodeOutput eOut (c.2.2 (C.stackEquiv tm.k₁))

theorem primrec_readOutput : Primrec (C.readOutput eOut) :=
  (C.primrec_decodeOutput eOut).comp
    (Primrec.fin_app.comp (Primrec.snd.comp Primrec.snd) (Primrec.const (C.stackEquiv tm.k₁)))

theorem readOutput_encodeCfg (c : tm.Cfg) :
    C.readOutput eOut (C.encodeCfg c) = some ((c.stk tm.k₁).map eOut) := by
  rw [readOutput, encodeCfg_stacks, C.encodeStacks_stackEquiv, C.decodeOutput_codeStack]

end Output

end MachineCode

/-! ## B3C. The fixed time polynomial -/

/-- Evaluating a **fixed** polynomial is primitive recursive.  No run-time encoding of polynomial
objects is involved: `p` is a parameter of the proof. -/
theorem primrec_polyEval (p : Polynomial ℕ) : Primrec fun n : ℕ => p.eval n := by
  induction p using Polynomial.induction_on with
  | C a => exact (Primrec.const a).of_eq fun n => by simp
  | add p q hp hq => exact (Primrec.nat_add.comp hp hq).of_eq fun n => by simp
  | monomial d a ih =>
      exact (Primrec.nat_mul.comp ih Primrec.id).of_eq fun n => by
        simp [pow_succ]; ring

namespace MachineCode

variable (C : MachineCode tm) (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym)

/-- **The simulator on raw external tapes.**  The budget is `p.eval xs.length`: a function of the
input alone. -/
def runTape (p : Polynomial ℕ) (xs : List Sym) : Option (List Sym) :=
  C.readOutput eOut ((keepStep C.codeStep)^[p.eval xs.length] (C.codeInit eIn xs))

theorem primrec_runTape (p : Polynomial ℕ) : Primrec (C.runTape eIn eOut p) :=
  (C.primrec_readOutput eOut).comp
    (C.primrec_iterate_keepStep.comp
      ((primrec_polyEval p).comp Primrec.list_length) (C.primrec_codeInit eIn))

end MachineCode

/-! ## B3C, continued: assembly -/

variable {α β : Type} {ea : α → List Sym} {eb : β → List Sym} {f : α → β}

/-- **The simulator computes the witness's function.**  Proved before any totalization, so no
conclusion depends on the fallback value chosen below. -/
theorem runTape_eq (h : TM2ComputableInPolyTime ea eb f) (C : MachineCode h.tm) (a : α) :
    C.runTape h.inputAlphabet h.outputAlphabet h.time (ea a) = some (eb (f a)) := by
  have hin : (ea a).map h.inputAlphabet.symm = (ea a).map h.inputAlphabet.invFun := rfl
  rw [MachineCode.runTape, C.codeInit_eq, hin,
    C.iterate_keepStep_codeStep_boundedEval, boundedEval_polyTime h a,
    C.readOutput_encodeCfg, haltList_stk_k₁, List.map_map]
  exact congrArg some (by simp [Function.comp_def])

/-- The simulator, totalized and composed with the boundary codecs.  The success theorem above is
proved *before* this fallback is chosen, so nothing concludes from `[]`. -/
theorem computable_of_runTape {α β : Type} [Primcodable α] [Primcodable β]
    {ea : α → List Sym} {eb : β → List Sym} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (C : MachineCode h.tm) (hea : Computable ea)
    {db : List Sym → β} (hdb : Computable db) (hleft : ∀ b, db (eb b) = b) :
    Computable f := by
  have hrun : Computable fun a =>
      db ((C.runTape h.inputAlphabet h.outputAlphabet h.time (ea a)).getD []) :=
    hdb.comp (((Primrec.option_getD.comp
      (C.primrec_runTape h.inputAlphabet h.outputAlphabet h.time)
      (Primrec.const [])).to_comp).comp hea)
  refine hrun.of_eq fun a => ?_
  rw [runTape_eq h C a, Option.getD_some, hleft]

/-- **The bridge.**  A polynomial-time machine certificate for `f`, an *effective* input encoder,
and an *effective* left inverse of the output encoder give `Computable f`.

No finiteness is assumed of the original machine's auxiliary alphabets: an arbitrary witness is
recoded first, and the only finiteness used is that of the external output alphabet `Sym`, which
comes from the witness's own equivalence.  Effective *decoding* of inputs and effective *encoding*
of outputs are not needed in this direction. -/
theorem computable_of_polyTime {α β : Type} [Primcodable α] [Primcodable β]
    {ea : α → List Sym} {eb : β → List Sym} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (hea : Computable ea)
    {db : List Sym → β} (hdb : Computable db) (hleft : ∀ b, db (eb b) = b) :
    Computable f :=
  haveI : Finite (h.tm.Γ h.tm.k₁) := Finite.of_equiv Sym h.outputAlphabet.symm
  have hout : (Set.univ : Set (h.tm.Γ h.tm.k₁)).Finite := Set.finite_univ
  computable_of_runTape (recodeWitness h hout)
    (MachineCode.of _ (recodeWitness_alphabets_finite h hout)) hea hdb hleft

end PCP.Machine
