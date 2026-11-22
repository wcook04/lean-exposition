module

public import QuarticQuery.Upper.AssemblyFormula

/-!
Exact gate-to-coordinate bridge for the product trial state.
Compiled as part of the `QuarticQuery` library target.
No endpoint assumption or admitted proof is used.
-/

@[expose] public section

namespace QuarticQuery.Upper

variable {N : ℕ} {Z : Type} [Fintype Z]

abbrev MarkRouteBasis (N : ℕ) (Z : Type) :=
  (Fin N → Bool) × RouteData N Z

def markWhole (S : Z → Bool) (p : MarkRouteBasis N Z) :
    MarkRouteBasis N Z :=
  ((fun j => xor (p.1 j) (S (p.2.2 j))), p.2)

theorem markWhole_involutive (S : Z → Bool) :
    Function.Involutive (markWhole (N := N) S) := by
  classical
  intro p
  apply Prod.ext
  · funext j
    simp [markWhole, Bool.xor_assoc]
  · rfl

noncomputable def markWholeGate (S : Z → Bool) :
    Reg (MarkRouteBasis N Z) ≃ₗᵢ[ℂ]
      Reg (MarkRouteBasis N Z) :=
  regCongr ⟨markWhole S, markWhole S, markWhole_involutive S,
    markWhole_involutive S⟩

/-- O starts at `o`, every flag at false, and trials have independent
unnormalised amplitude vectors `v i` (including any label amplitude). -/
noncomputable def startTrials (o : Z) (v : Fin N → Reg Z) :
    Reg (MarkRouteBasis N Z) :=
  by
    classical
    exact WithLp.toLp 2 fun p =>
      if p.2.1 = o ∧ (∀ i, p.1 i = false) then
        ∏ i, (v i).ofLp (p.2.2 i)
      else 0

noncomputable def assembledTrials (o : Z) (S : Z → Bool)
    (v : Fin N → Reg Z) : Reg (MarkRouteBasis N Z) :=
  routeFlagsGate (markWholeGate S (startTrials o v))

/-- The success projection is a coordinate mask on the immutable flag record. -/
noncomputable def assembledSuccess (o : Z) (S : Z → Bool)
    (v : Fin N → Reg Z) : Reg (MarkRouteBasis N Z) :=
  WithLp.toLp 2 fun p =>
    if (firstSuccess p.1).isSome then (assembledTrials o S v).ofLp p else 0

/-- Reassociate the immutable flags and post-route trial coordinates into the
auxiliary subsystem; the fixed original output coordinate comes last. -/
def retainedReassoc :
    MarkRouteBasis N Z ≃ Σ _ : ((Fin N → Bool) × (Fin N → Z)), Z where
  toFun p := ⟨(p.1, p.2.2), p.2.1⟩
  invFun p := (p.1.1, (p.2, p.1.2))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

noncomputable def assembledAux (o : Z) (S : Z → Bool)
    (v : Fin N → Reg Z) (s : Fin N → ℂ) :
    Reg ((Fin N → Bool) × (Fin N → Z)) :=
  WithLp.toLp 2 fun a => routedAuxCoeff o S v s a.1 a.2

end QuarticQuery.Upper
