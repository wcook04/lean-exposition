import PCP.Complexity.CallPrepare

/-!
# Answer-tag dispatch

The algorithm's answer arrives on the caller's destination stack.  With an **empty** destination
before the call it is exactly `encodeAnswer (alg x r answers)`; with a nonempty one the end of a
binary query numeral has no delimiter separating it from the suffix, so nothing here claims a
decoder could find the boundary.  The dispatch theorems below therefore leave the tail as data and
never measure it.

## What dispatch may touch

The only tape operation is the **pop of the destination head**.  Everything else is finite control:
the remaining depth and the decision bit live in the caller's payload `P`, reached through the two
supplied functions `depthZero` and `setDec`, so nothing unbounded enters a finite type and the
address stays on a stack.

## The depth-zero rejection is an execution fact

`dispatch_step_rejected` is a **one-step execution** of the actual dispatch statement: at depth zero
a query tag lands directly on `rejected`, for an arbitrary numeral tail, leaving that tail and every
witness stack untouched — and in particular never reaching `lookup`.  That is stronger than any
statement about returned values, which is what `PCP/Complexity/Checker.lean` can offer.

Stopping at `rejected` is not cleanup: draining the tail later is allowed and must be charged by its
encoded length, and its drain program must not route through `lookup` either.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

section

variable (tm : FinTM2) (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
  (P : Type) [Fintype P]

/-- The Boolean a decision answer carries. -/
def answerBit : Option Sym → Bool
  | some (.bit b) => b
  | _ => false

/-- The dispatch statement, run at `resume`.  `setDec` records a decision in the caller's payload;
`depthZero` reports whether the remaining query budget is exhausted. -/
def dispatchStmt (setDec : P → Bool → P) (depthZero : P → Bool) : PrepStmt tm G Γg P :=
  pop (.inr (.inl .dst)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => decide (p.2.1 = some Sym.sep))
      (branch (fun p => depthZero p.2.2)
        (load (fun p => (p.1, (none, setDec p.2.2 false))) (goto (fun _ => .inr .rejected)))
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .lookup))))
      (load (fun p => (p.1, (none, setDec p.2.2 (answerBit p.2.1))))
        (goto (fun _ => .inr .decided)))

/-- Route `resume` to dispatch; everything else to the supplied continuation. -/
def dispatchRoute (setDec : P → Bool → P) (depthZero : P → Bool)
    (rest : CallLabel → PrepStmt tm G Γg P) : CallLabel → PrepStmt tm G Γg P
  | .resume => dispatchStmt tm G Γg P setDec depthZero
  | l => rest l

variable {tm G Γg P}

section Steps

variable (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : P)
  (setDec : P → Bool → P) (depthZero : P → Bool) (rest : CallLabel → PrepStmt tm G Γg P)

/-- A decision answer: the bit is recorded and control reaches `decided`. -/
theorem dispatch_step_decided (v : tm.σ) (temp : Option Sym) (pay : P) (b : Bool)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp tail scratch : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P (dispatchRoute tm G Γg P setDec depthZero rest))).step
        (prepCfg eIn eOut p₀
            (dispatchRoute tm G Γg P setDec depthZero rest)
            (some (.inr .resume)) v temp pay S inp (Sym.bit b :: tail) scratch t g)
      = some (prepCfg eIn eOut p₀
          (dispatchRoute tm G Γg P setDec depthZero rest)
            (some (.inr CallLabel.decided)) v none (setDec pay b) S inp tail scratch t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P
          (dispatchRoute tm G Γg P setDec depthZero rest))).m
      (Sum.inr CallLabel.resume)) (v, (temp, pay))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp (Sym.bit b :: tail) scratch
          (prepFrame G Γg t g)))) = _
  simp only [callTM, parentTM, callProgram, prepCont, dispatchRoute, dispatchStmt, answerBit,
    Turing.TM2.stepAux, embedStacks_inr, callFrame, prepFrame, List.head?_cons, List.tail_cons]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.decided), (v, (none, setDec pay b)), T⟩ :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P (dispatchRoute tm G Γg P setDec depthZero rest))).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-- **Depth-zero query rejection, as an execution.**  The tag alone decides it: control goes
straight to `rejected` with `false` recorded, the numeral `tail` is left untouched, every witness
stack is untouched, and `lookup` is never entered — for an arbitrary tail, whatever its contents or
length. -/
theorem dispatch_step_rejected (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp tail scratch : List Sym) (g : ∀ j : G, List (Γg j)) (h : depthZero pay = true) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P (dispatchRoute tm G Γg P setDec depthZero rest))).step
        (prepCfg eIn eOut p₀
            (dispatchRoute tm G Γg P setDec depthZero rest)
            (some (.inr .resume)) v temp pay S inp (Sym.sep :: tail) scratch t g)
      = some (prepCfg eIn eOut p₀
          (dispatchRoute tm G Γg P setDec depthZero rest)
            (some (.inr CallLabel.rejected)) v none (setDec pay false) S inp tail scratch t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P
          (dispatchRoute tm G Γg P setDec depthZero rest))).m
      (Sum.inr CallLabel.resume)) (v, (temp, pay))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp (Sym.sep :: tail) scratch
          (prepFrame G Γg t g)))) = _
  simp only [callTM, parentTM, callProgram, prepCont, dispatchRoute, dispatchStmt, answerBit,
    Turing.TM2.stepAux, embedStacks_inr, callFrame, prepFrame, List.head?_cons, List.tail_cons, h]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.rejected), (v, (none, setDec pay false)), T⟩ :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P (dispatchRoute tm G Γg P setDec depthZero rest))).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-- A query at positive depth reaches `lookup`, with the numeral still on the destination. -/
theorem dispatch_step_lookup (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp tail scratch : List Sym) (g : ∀ j : G, List (Γg j)) (h : depthZero pay = false) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P (dispatchRoute tm G Γg P setDec depthZero rest))).step
        (prepCfg eIn eOut p₀
            (dispatchRoute tm G Γg P setDec depthZero rest)
            (some (.inr .resume)) v temp pay S inp (Sym.sep :: tail) scratch t g)
      = some (prepCfg eIn eOut p₀
          (dispatchRoute tm G Γg P setDec depthZero rest)
            (some (.inr CallLabel.lookup)) v none (pay) S inp tail scratch t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P
          (dispatchRoute tm G Γg P setDec depthZero rest))).m
      (Sum.inr CallLabel.resume)) (v, (temp, pay))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp (Sym.sep :: tail) scratch
          (prepFrame G Γg t g)))) = _
  simp only [callTM, parentTM, callProgram, prepCont, dispatchRoute, dispatchStmt, answerBit,
    Turing.TM2.stepAux, embedStacks_inr, callFrame, prepFrame, List.head?_cons, List.tail_cons, h]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.lookup), (v, (none, pay)), T⟩ :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P (dispatchRoute tm G Γg P setDec depthZero rest))).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

end Steps

end

end PCP.Machine
