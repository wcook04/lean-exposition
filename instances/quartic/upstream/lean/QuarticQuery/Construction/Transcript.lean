module

public import QuarticQuery.Statement

/-!
# Evaluation transcripts

A fixed input has exactly one gate-consistent transcript: the true evaluation of
the circuit. Gates only read strictly earlier gates, so this is strong induction
on the gate index, the "topological order" of Lemma 2.2.
-/

public section

namespace QuarticQuery

variable {ι : Type}

/-- A predecessor value reads only strictly earlier gates. -/
theorem predecessorValue_congr (C : Circuit ι) (x : BitInput ι) {tr tr' : Fin C.size → Bool}
    (g : Fin C.size) (hagree : ∀ e : Fin C.size, e.val < g.val → tr e = tr' e)
    (p : Option (ι ⊕ Fin g.val)) :
    predecessorValue C x tr g p = predecessorValue C x tr' g p := by
  rcases p with _ | q | e
  · rfl
  · rfl
  · exact hagree _ e.isLt

/-- Ledger: def-transcript. Two consistent transcripts of one input agree. -/
theorem GateConsistent.unique {C : Circuit ι} {x : BitInput ι} {tr tr' : Fin C.size → Bool}
    (h : GateConsistent C x tr) (h' : GateConsistent C x tr') : tr = tr' := by
  have key : ∀ n, ∀ g : Fin C.size, g.val = n → tr g = tr' g := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro g hg
      have hagree : ∀ e : Fin C.size, e.val < g.val → tr e = tr' e :=
        fun e he => ih e.val (hg ▸ he) e rfl
      rw [h g, h' g, predecessorValue_congr C x g hagree,
        predecessorValue_congr C x g hagree]
  exact funext fun g => key _ g rfl

/-- The true value of a gate. -/
def circuitEval (C : Circuit ι) (x : BitInput ι) (g : Fin C.size) : Bool :=
  let tr : Fin C.size → Bool :=
    fun e => if _he : e.val < g.val then circuitEval C x e else false
  (C.gate g).table (predecessorValue C x tr g (C.gate g).left)
    (predecessorValue C x tr g (C.gate g).right)
termination_by g.val
decreasing_by assumption

/-- Ledger: def-eval-transcript. The true evaluation is consistent. -/
theorem circuitEval_gateConsistent (C : Circuit ι) (x : BitInput ι) :
    GateConsistent C x (circuitEval C x) := by
  intro g
  rw [circuitEval]
  have hagree : ∀ e : Fin C.size, e.val < g.val →
      (fun e : Fin C.size => if he : e.val < g.val then circuitEval C x e else false) e
        = circuitEval C x e := fun e he => by simp [he]
  simp only [predecessorValue_congr C x g hagree]

/-- Ledger: def-eval-transcript. A transcript is consistent exactly when it is
the true evaluation, on every input and with no promise. -/
theorem gateConsistent_iff_eq_circuitEval {C : Circuit ι} {x : BitInput ι}
    {tr : Fin C.size → Bool} : GateConsistent C x tr ↔ tr = circuitEval C x :=
  ⟨fun h => h.unique (circuitEval_gateConsistent C x),
    fun h => h ▸ circuitEval_gateConsistent C x⟩

/-- Ledger: def-transcript. -/
theorem existsUnique_gateConsistent (C : Circuit ι) (x : BitInput ι) :
    ∃! tr, GateConsistent C x tr :=
  ⟨circuitEval C x, circuitEval_gateConsistent C x,
    fun _ h => gateConsistent_iff_eq_circuitEval.mp h⟩

end QuarticQuery
